import sys
import shlex
from io import BytesIO, TextIOWrapper
from os import WEXITSTATUS, listdir, system
from subprocess import Popen, PIPE
from os.path import isfile, join
from unittest.mock import patch

import self as grader


def list_files(path, extension=''):
    return [f for f in listdir(path) if isfile(join(path, f)) and f.endswith(extension)]


class CaptureOutput:
    def __init__(self):
        self.patcher = patch('lib.print.println')
        self.output = ''
        self.loud_output = ''
        self.combined_output = ''

    def println(self, msg='', end='\n', loud=False):
        self.combined_output = self.combined_output + msg + end

        if loud:
            self.loud_output = self.loud_output + msg + end
        else:
            self.output = self.output + msg + end

    def __enter__(self):
        self.mock = self.patcher.start()
        self.mock.side_effect = self.println
        return self

    def __exit__(self, exc_type, exc_val, exc_trace):
        self.output = ''
        self.loud_output = ''
        self.combined_output = ''
        self.patcher.stop()

    def get_quiet_output(self):
        return self.output

    def get_loud_output(self):
        return self.loud_output

    def get_output(self):
        return self.combined_output


class Console():
    def __init__(self):
        self.console_output = TextIOWrapper(BytesIO(), sys.stdout.encoding)

    def __enter__(self):
        sys.stdout = self.console_output
        return self

    def __exit__(self, type, value, traceback):
        self.console_output.close()
        sys.stdout = sys.__stdout__

    def get_output(self):
        self.console_output.seek(0)
        return self.console_output.read()


def assemble_for_selfie(file):
    system('riscv64-linux-gnu-as tests/' + file + ' -o .instruction.o')
    system('riscv64-linux-gnu-ld .instruction.o -o .instruction.bin >/dev/null 2>&1')
    system('cat tests/elf-header.m .instruction.bin > .tmp.bin')
    system('rm .instruction.o .instruction.bin')


def compile_with_gcc(file):
    return_value = WEXITSTATUS(system(
        'gcc -w -D\'uint64_t=unsigned long\' ' + file + ' -o .prog >/dev/null 2>&1'))

    if return_value != 0:
        system('rm -rf ./.prog')

    return return_value


def compile_with_gcc_and_run(file):
    system('gcc -w -D\'uint64_t=unsigned long\' ' + file + ' -o .prog')

    process = Popen(shlex.split('./.prog'), stdout=PIPE, stderr=PIPE)

    stdoutdata, stderrdata = process.communicate()

    output = stdoutdata.decode(sys.stdout.encoding)
    error_output = stderrdata.decode(sys.stderr.encoding)

    system('rm ./.prog')

    return (process.returncode, output, error_output)


not_compilable = [
    'assembler-parser',
    'self-assembler',
    'processes',
    'lock',
    'threads',
    'treiber-stack'
]

compilable_assignments = [
    a for a in grader.assignments if a.name not in not_compilable]


def run_compilable_assignments(prev=None, after=None):
    for assignment in compilable_assignments:
        if prev != None:
            prev(assignment)

        with CaptureOutput() as capture:
            grader.main([sys.argv[0], assignment.name])

            output = capture.get_output()

            if after != None:
                after(output)


def for_all_test_results(output, function):
    failed = '\033[91m[FAILED]\033[0m'
    passed = '\033[92m[PASSED]\033[0m'

    for line in output.splitlines():
        if line.startswith(failed):
            function(False, line.split(failed)[1])
        elif line.startswith(passed):
            function(True, line.split(passed)[1])
