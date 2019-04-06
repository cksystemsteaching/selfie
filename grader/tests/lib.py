import os
import sys
from io import TextIOWrapper, BytesIO

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
  os.system('riscv64-linux-gnu-as grader/tests/' + file + ' -o .instruction.o')
  os.system('riscv64-linux-gnu-ld .instruction.o -o .instruction.bin --oformat=binary >/dev/null 2>&1')
  os.system('cat grader/tests/elf-header.m .instruction.bin > .tmp.bin')
  os.system('rm .instruction.o .instruction.bin')

def compile_with_gcc(file):
  return_value = os.WEXITSTATUS(os.system('gcc -w -D\'uint64_t=unsigned long long\' grader/' + file + ' -o .prog >/dev/null 2>&1'))
  
  if return_value != 0:
    os.system('rm ./.prog')
  
  return return_value

def compile_with_gcc_and_run(file):
  os.system('gcc -w -D\'uint64_t=unsigned long long\' grader/' + file + ' -o .prog')
  return_value = os.WEXITSTATUS(os.system('./.prog'))
  os.system('rm ./.prog')
  return return_value

def for_all_test_results(output, function):
  failed = '\033[91m[FAILED]\033[0m'
  passed = '\033[92m[PASSED]\033[0m'

  for line in output.splitlines():
    if line.startswith(failed):
      function(False, line.split(failed)[1])
    elif line.startswith(passed):
      function(True, line.split(passed)[1])
