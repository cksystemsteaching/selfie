import os
import re
import shlex
import sys
from pathlib import Path
from typing import List, Tuple

from .model import Check, CheckResult
from .output_processing import (filter_status_messages,
                                has_no_compile_warnings, has_no_bootstrapping_compile_warnings, 
                                is_interleaved_output, is_permutation_of)
from .print import print_processing, print_warning, stop_processing_spinner
from .system import INSTRUCTIONSIZE, WORDSIZE, read_data, read_instruction

if sys.version_info < (3, 3):
    from subprocess import Popen, PIPE, STDOUT
    print_warning('python V3.3 or newer is recommended\n' +
                  'mipster execution timeout is disabled with this python version\n')
else:
    from subprocess import Popen, TimeoutExpired, PIPE, STDOUT
    if sys.platform == "linux":
        import errno
        import select

assignment_name = ''


def set_assignment_name(name):
    global assignment_name
    assignment_name = name


def set_home_path(path):
    global home_path
    home_path = path


class TimeoutException(Exception):
    def __init__(self, command, timeout, output): # , error_output):
        Exception.__init__(self, 'The command \"' + command +
                           '\" has timed out after ' + str(timeout) + 's')

        self.output = output
        # self.error_output = error_output


def insert_assignment_path(command):
    matches = re.finditer(r'<assignment>([^\s]+)', command)

    if matches is None:
        return command

    result = []
    idx = 0

    working_dir_path = Path.cwd()

    assignment_path = home_path / 'assignments' / assignment_name

    # try to build a relative path from the current working directory
    # to the grading script location
    try:
        assignment_path = assignment_path.relative_to(working_dir_path)
    except ValueError:
        # assignment_path is not a sub directory of working_dir_path
        pass  # assignment path has to be a absolute path

    for match in matches:
        file = match.group(1)

        result.append(command[idx:match.start()])
        result.append('"' + str(assignment_path / file) + '"')

        idx = match.end()

    result.append(command[idx:len(command)])

    return ''.join(result)


def set_up():
    execute('make clean')
    execute('make selfie')


def execute(command, timeout=60):
    if sys.version_info >= (3, 3) and sys.platform == "linux":
        # open ptys
        out_m, out_s = os.openpty()
        err_m, err_s = os.openpty()
        in_m, in_s = os.openpty()

        # open process, attaching ptys to stdout/stderr
        process = Popen(shlex.split(command), stdout=out_s, stderr=err_s, stdin=in_s)

        # close slave fds
        for fd in [out_s, err_s, in_s]: os.close(fd)
    else:
        # combine stdout and stderr in one output
        process = Popen(shlex.split(command), stdout=PIPE, stderr=STDOUT)

    timedout = False

    # read output
    try:
        if sys.version_info < (3, 3):
            outdata, _ = process.communicate()
        elif sys.platform != "linux":
            outdata, _ = process.communicate(timeout=timeout)
        else:
            try:
                outdata = bytes()
                fds = [out_m, err_m]
                while len(fds) > 0:
                    # wait for a pty to become ready
                    ready, _, _ = select.select(fds, [], [], timeout)
                    for fd in ready:
                        try:
                            # read its data
                            data = os.read(fd, 4096)
                        except OSError as e:
                            if e.errno == errno.EIO:
                                fds.remove(fd)
                            else:
                                raise
                        else:
                            if data:
                                outdata += data
                            else:
                                fds.remove(fd)
                process.wait()
            finally:
                # cleanup
                for fd in [out_m, err_m, in_m]: os.close(fd)
    except TimeoutExpired:
        process.kill()
        outdata, _ = process.communicate()

        timedout = True

    # decode output data
    output = outdata.decode(sys.stdout.encoding)

    if timedout:
        raise TimeoutException(command, timeout, output)

    return (process.returncode, output)


def check_instruction_encoding(instruction, file) -> List[Check]:
    msg = instruction[0] + ' has right RISC-V encoding'

    command = './selfie -c <assignment>{} -o .tmp.bin'.format(file)
    command = insert_assignment_path(command)

    def execute_check() -> CheckResult:
        try:
            exit_code, output = execute(command)

            instruction_value = instruction[1]
            instruction_mask = instruction[2]

            if exit_code == 0:
                exit_code = 1

                try:
                    with open('.tmp.bin', 'rb') as f:
                        # Read the code start/length out of the program header
                        # (p_filesz in the ELF program header)
                        # -> Ignore 12 words
                        #    (8 ELF header + 1 partial ELF program header)
                        # CAUTION: These offset values do currently work with
                        #          Selfie's ELF64 binaries, only!
                        ignored_elf_header_size = 9 * WORDSIZE

                        # Between code start and length, fields p_vaddr
                        # and p_paddr are located
                        ignored_elf_pheader_seek = 2 * WORDSIZE

                        f.seek(ignored_elf_header_size)

                        code_start = read_data(f)
                        f.read(ignored_elf_pheader_seek)
                        code_length = read_data(f)

                        # ignore all pading bytes
                        f.seek(code_start)

                        # read all RISC-V instructions from binary
                        read_instructions = map(lambda x: read_instruction(
                            f), range(int(code_length / INSTRUCTIONSIZE)))

                        if any(map(lambda x: x & instruction_mask == instruction_value, read_instructions)):
                            # at least one instruction has the right encoding
                            exit_code = 0

                    if os.path.isfile('.tmp.bin'):
                        os.remove('.tmp.bin')

                    return CheckResult(exit_code == 0, msg, output,
                                  'No instruction matching the RISC-V encoding found')

                except FileNotFoundError:
                    return CheckResult(False, msg, '',
                                        'The binary file has not been created by selfie')
            else:
                return CheckResult(
                    False, msg, output, 'Selfie returned an error when executing "' + command + '"')
        except OSError as e:
            # the program to execute can not be found (e.g. selfie is not built)
            return CheckResult(False, msg, str(e), 'Failed to execute "{}"'.format(
                command), True, command, mandatory=False)

    return [Check(msg, command, execute_check)]


def check_assembler_instruction_format(instruction, file) -> List[Check]:
    msg = instruction[0] + ' RISC-V instruction has right assembly instruction format'

    command = './selfie -c <assignment>{} -s .tmp.s'.format(file)
    command = insert_assignment_path(command)

    def execute_check() -> CheckResult:
        try:
            exit_code, output = execute(command)

            if exit_code == 0:
                exit_code = 1

                try:
                    with open('.tmp.s', 'rt') as f:
                        for line in f:
                            if re.match(instruction[3], line) != None:
                                # at least one assembler instruction has the right encoding
                                exit_code = 0

                        return CheckResult(exit_code == 0, msg, output,
                                      'No assembler instruction matching the RISC-V encoding found')

                    if os.path.isfile('.tmp.s'):
                        os.remove('.tmp.s')

                except FileNotFoundError:
                    return CheckResult(
                        False, msg, output, 'The assembler file has not been created by selfie')
            else:
                return CheckResult(
                    False, msg, output, 'Selfie returned an error when executing "' + command + '"')
        except OSError as e:
            # the program to execute can not be found (e.g. selfie is not built)
            return CheckResult(False, msg, str(e), 'Failed to execute "{}"'.format(
                command), True, command, mandatory=False)

    return [Check(msg, command, execute_check)]


def check_execution(command, msg, success_criteria=True, should_succeed=True, mandatory=False, timeout=60) -> List[Check]:
    secure_command = insert_assignment_path(command)

    def execute_check() -> CheckResult:
        try:
            returncode, output = execute(secure_command, timeout)

            # if returncode != 0 and len(output) == 0:
                # output = error_output

            if type(success_criteria) is bool:
                if should_succeed:
                    warning = 'Execution terminated with wrong exit code {} instead of 0'.format(
                        returncode)
                else:
                    warning = 'Execution terminated with wrong exit code {}'.format(
                        returncode)

                return CheckResult(returncode == 0, msg, output, warning,
                                    should_succeed, secure_command, mandatory)

            elif type(success_criteria) is int:
                return CheckResult(returncode == success_criteria, msg, output,
                                    'Execution terminated with wrong exit code {} instead of {}'.format(returncode, success_criteria), should_succeed, secure_command, mandatory)

            elif type(success_criteria) is str:
                filtered_output = filter_status_messages(output)

                return CheckResult(filtered_output == success_criteria, msg, output,
                                    'The actual printed output does not match', should_succeed, secure_command, mandatory)

            elif callable(success_criteria):
                result, warning = success_criteria(returncode, output)

                return CheckResult(result, msg, output, warning,
                                    should_succeed, secure_command, mandatory)
        except TimeoutException as e:
            return CheckResult(False, msg, e.output, str(
                e), should_succeed, secure_command, mandatory)
        except OSError as e:
            # the program to execute can not be found (e.g. selfie is not built)
            return CheckResult(False, msg, str(e), 'Failed to execute "{}"'.format(
                secure_command), should_succeed, secure_command, mandatory)

    return [Check(msg, secure_command, execute_check)]


def check_compilable(file, msg, should_succeed=True) -> List[Check]:
    return check_execution('./selfie -c <assignment>{}'.format(file), msg, success_criteria=lambda code,
                          out: has_no_compile_warnings(code, out), should_succeed=should_succeed)


def check_riscv_instruction(instruction, file) -> List[Check]:
    return check_instruction_encoding(instruction, file) + \
           check_assembler_instruction_format(instruction, file)


def check_mipster_execution(file, success_criteria, msg) -> List[Check]:
    return check_execution('./selfie -c <assignment>{} -m 128'.format(file),
                          msg, success_criteria=success_criteria)


def check_hypster_execution(file, success_criteria, msg) -> List[Check]:
    return check_execution('./selfie -c selfie.c -m 128 -c <assignment>{} -y 64'.format(file),
                          msg, success_criteria=success_criteria)


def check_interleaved_output(command, interleaved_msg, number_of_interleaved, msg) -> List[Check]:
    return check_execution(command, msg, success_criteria=lambda code, out: is_interleaved_output(
        out, interleaved_msg, number_of_interleaved))


def check_compile_warnings(file, msg, mandatory=False) -> List[Check]:
    return check_execution('./selfie -c {}'.format(file), msg,
                          success_criteria=has_no_compile_warnings, mandatory=mandatory)

def check_bootstrapping_compile_warnigns(msg, mandatory=False) -> List[Check]:
    execute('make clean')
    return check_execution('make selfie', msg, 
                        success_criteria=has_no_bootstrapping_compile_warnings, mandatory=mandatory)
