import sys
from os import listdir, system, WEXITSTATUS
from os.path import isfile, join
from io import TextIOWrapper, BytesIO

def list_files(path, extension=''):
  return [f for f in listdir(path) if isfile(join(path, f)) and f.endswith(extension)]

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
  system('riscv64-linux-gnu-as grader/tests/' + file + ' -o .instruction.o')
  system('riscv64-linux-gnu-ld .instruction.o -o .instruction.bin --oformat=binary >/dev/null 2>&1')
  system('cat grader/tests/elf-header.m .instruction.bin > .tmp.bin')
  system('rm .instruction.o .instruction.bin')

def compile_with_gcc(file):
  return_value = WEXITSTATUS(system('gcc -w -D\'uint64_t=unsigned long long\' grader/' + file + ' -o .prog >/dev/null 2>&1'))
  
  if return_value != 0:
    system('rm -rf ./.prog')
  
  return return_value

def compile_with_gcc_and_run(file):
  system('gcc -w -D\'uint64_t=unsigned long long\' grader/' + file + ' -o .prog')
  return_value = WEXITSTATUS(system('./.prog'))
  system('rm ./.prog')
  return return_value

def for_all_test_results(output, function):
  failed = '\033[91m[FAILED]\033[0m'
  passed = '\033[92m[PASSED]\033[0m'

  for line in output.splitlines():
    if line.startswith(failed):
      function(False, line.split(failed)[1])
    elif line.startswith(passed):
      function(True, line.split(passed)[1])
