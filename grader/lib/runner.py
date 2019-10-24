import re
import sys
import os
import shlex
from .output_processing import is_interleaved_output, has_compiled, has_no_compile_warnings, is_permutation_of, filter_status_messages
from .system import REGISTERSIZE, INSTRUCTIONSIZE, read_data, read_instruction
from .print import print_processing, stop_processing_spinner
from .grade import record_result
import lib.cli as cli

if sys.version_info < (3, 3):
    from subprocess import Popen, PIPE
    print('warning: python V3.3 or newer is recommended')
    print('mipster execution timeout is disabled with this python version\n')
else:
    from subprocess import Popen, TimeoutExpired, PIPE

home_path = os.path.abspath(os.getcwd())

class TimeoutException(Exception):
    def __init__(self, command, timeout, output, error_output):
        Exception.__init__(self, 'The command \"' + command +
                           '\" has timed out after ' + str(timeout) + 's')

        self.output = output
        self.error_output = error_output


def insert_home_path(command):
    return re.sub(r'(grader/([^\s]*))', r'"' + home_path + r'/grader/assignments/' + cli.assignment_path + r'/\2"', command)


def set_up():
    execute('make clean')
    execute('make selfie')


def execute(command, timeout=60):
    command = insert_home_path(command)

    process = Popen(shlex.split(command), stdout=PIPE, stderr=PIPE)

    timedout = False

    if sys.version_info < (3, 3):
        stdoutdata, stderrdata = process.communicate()
    else:
        try:
            stdoutdata, stderrdata = process.communicate(timeout=timeout)
        except TimeoutExpired:
            process.kill()
            stdoutdata, stderrdata = process.communicate()

            timedout = True

    output = stdoutdata.decode(sys.stdout.encoding)
    error_output = stderrdata.decode(sys.stderr.encoding)

    if timedout:
        raise TimeoutException(command, timeout, output, error_output)

    return (process.returncode, output, error_output)


def test_instruction_encoding(instruction, file):
    msg = instruction[0] + ' has right RISC-V encoding'

    print_processing(msg)

    command = './selfie -c grader/{} -o .tmp.bin'.format(file)

    try:
        exit_code, output, _ = execute(command)

        instruction_value = instruction[1]
        instruction_mask = instruction[2]

        if exit_code == 0:
            exit_code = 1

            try:
                with open('.tmp.bin', 'rb') as f:
                    ignored_elf_header_size = 14 * REGISTERSIZE

                    f.read(ignored_elf_header_size)

                    code_start = read_data(f)
                    code_length = read_data(f)

                    # ignore all pading bytes
                    no_of_bytes_until_code = code_start - ignored_elf_header_size - 2 * REGISTERSIZE

                    if no_of_bytes_until_code < 0:
                        no_of_bytes_until_code = 0

                    f.read(no_of_bytes_until_code)

                    # read all RISC-V instructions from binary
                    read_instructions = map(lambda x: read_instruction(
                        f), range(int(code_length / INSTRUCTIONSIZE)))

                    if any(map(lambda x: x & instruction_mask == instruction_value, read_instructions)):
                        # at least one instruction has the right encoding
                        exit_code = 0

                if os.path.isfile('.tmp.bin'):
                    os.remove('.tmp.bin')

                record_result(exit_code == 0, msg, output,
                              'No instruction matching the RISC-V encoding found')

            except FileNotFoundError:
                record_result(False, msg, '',
                              'The binary file has not been created by selfie')
        else:
            record_result(
                False, msg, output, 'Selfie returned an error when executing "' + command + '"')
    except OSError as e:
        # the program to execute can not be found (e.g. selfie is not built)
        record_result(False, msg, str(e), 'Failed to execute "{}"'.format(
            command), True, command, mandatory=False)
    finally:
        stop_processing_spinner()


def test_assembler_instruction_format(instruction, file):
    msg = instruction[0] + \
        ' RISC-V instruction has right assembly instruction format'

    print_processing(msg)

    command = './selfie -c grader/{} -s .tmp.s'.format(file)

    try:
        exit_code, output, _ = execute(command)

        if exit_code == 0:
            exit_code = 1

            try:
                with open('.tmp.s', 'rt') as f:
                    for line in f:
                        if re.match(instruction[3], line) != None:
                            # at least one assembler instruction has the right encoding
                            exit_code = 0

                    record_result(exit_code == 0, msg, output,
                                  'No assembler instruction matching the RISC-V encoding found')

                if os.path.isfile('.tmp.s'):
                    os.remove('.tmp.s')

            except FileNotFoundError:
                record_result(
                    False, msg, output, 'The assembler file has not been created by selfie')
        else:
            record_result(
                False, msg, output, 'Selfie returned an error when executing "' + command + '"')
    except OSError as e:
        # the program to execute can not be found (e.g. selfie is not built)
        record_result(False, msg, str(e), 'Failed to execute "{}"'.format(
            command), True, command, mandatory=False)
    finally:
        stop_processing_spinner()


def test_execution(command, msg, success_criteria=True, should_succeed=True, mandatory=False):
    print_processing(msg)

    try:
        returncode, output, error_output = execute(command)

        if returncode != 0 and len(output) == 0:
            output = error_output

        if type(success_criteria) is bool:
            if should_succeed:
                warning = 'Execution terminated with wrong exit code {} instead of 0'.format(
                    returncode)
            else:
                warning = 'Execution terminated with wrong exit code {}'.format(
                    returncode)

            record_result(returncode == 0, msg, output, warning,
                          should_succeed, command, mandatory)

        elif type(success_criteria) is int:
            record_result(returncode == success_criteria, msg, output,
                          'Execution terminated with wrong exit code {} instead of {}'.format(returncode, success_criteria), should_succeed, command, mandatory)

        elif type(success_criteria) is str:
            filtered_output = filter_status_messages(output)

            record_result(filtered_output == success_criteria, msg, output,
                          'The actual printed output does not match', should_succeed, command, mandatory)

        elif callable(success_criteria):
            result, warning = success_criteria(returncode, output)

            record_result(result, msg, output, warning,
                          should_succeed, command, mandatory)
    except TimeoutException as e:
        record_result(False, msg, e.output, str(
            e), should_succeed, command, mandatory)
    except OSError as e:
        # the program to execute can not be found (e.g. selfie is not built)
        record_result(False, msg, str(e), 'Failed to execute "{}"'.format(
            command), should_succeed, command, mandatory)
    finally:
        stop_processing_spinner()


def test_compilable(file, msg, should_succeed=True):
    test_execution('./selfie -c grader/{}'.format(file), msg, success_criteria=lambda code,
                   out: has_compiled(code, out), should_succeed=should_succeed)


def test_riscv_instruction(instruction, file):
    test_instruction_encoding(instruction, file)
    test_assembler_instruction_format(instruction, file)


def test_mipster_execution(file, result, msg):
    test_execution('./selfie -c grader/{} -m 128'.format(file),
                   msg, success_criteria=result)


def test_hypster_execution(file, result, msg):
    test_execution('./selfie -c selfie.c -m 128 -c grader/{} -y 64'.format(file),
                   msg, success_criteria=result)


def test_interleaved_output(command, interleaved_msg, number_of_interleaved, msg):
    test_execution(command, msg, success_criteria=lambda code, out: is_interleaved_output(
        out, interleaved_msg, number_of_interleaved))


def test_compile_warnings(file, msg, mandatory=False):
    test_execution('./selfie -c {}'.format(file), msg,
                   success_criteria=has_no_compile_warnings, mandatory=mandatory)
