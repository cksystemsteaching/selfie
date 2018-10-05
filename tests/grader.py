import sys
import os
import re
from subprocess import Popen, PIPE

number_of_tests_passed = 0
number_of_tests_failed = 0

INSTRUCTIONSIZE = 4  # in bytes
ELF_HEADER_LEN = 120
TMP_FILE = '.tmp.bin'

OP_OP = 51

F3_SLL = 1
F3_SRL = 5

F7_SLL = 0
F7_SRL = 0

def encode_r_format(funct7, funct3, opcode):
  return (((((funct7 << 5) << 5) << 3) + funct3 << 5) << 7) + opcode

R_FORMAT_MASK = 0b11111110000000000111000001111111
SLL_INSTRUCTION = encode_r_format(F7_SLL, F3_SLL, OP_OP)
SRL_INSTRUCTION = encode_r_format(F7_SRL, F3_SRL, OP_OP)


def record_result(result, msg, output, warning=None):
  global number_of_tests_passed, number_of_tests_failed

  if result == True:
    number_of_tests_passed += 1

    print("\033[92m[PASSED]\033[0m " + msg)
  else:
    number_of_tests_failed += 1

    print("\033[91m[FAILED]\033[0m " + msg)
    if warning != None:
      print("\033[93m > " + warning + " <\033[0m")
    print(' >> ' + output[:-1].replace('\n', '\n >> '))


def test_compilable(file, msg):
  p = Popen(['./selfie', '-c', 'tests/' + file], stdout=PIPE, stderr=PIPE, stdin=PIPE)

  output = p.stdout.read().decode(sys.stdout.encoding)
  p.wait()

  exit_code = p.returncode
  warning = None

  if exit_code == 0:
    match = re.search('(syntax error [^\n]*)', output)

    if match != None:
      exit_code = 1
      warning = match.group(0)

  record_result(exit_code == 0, msg, output, warning)


def test_instruction_format(file, instruction, instruction_mask, msg):
  p = Popen(['./selfie', '-c', 'tests/' + file, '-o', TMP_FILE], stdout=PIPE, stderr=PIPE, stdin=PIPE)

  output = p.stdout.read().decode(sys.stdout.encoding)
  p.wait()

  exit_code = p.returncode
  warning = None

  if exit_code == 0:
    exit_code = 1

    with open(TMP_FILE, 'rb') as f:
      f.read(ELF_HEADER_LEN)

      for raw_word in iter(lambda: f.read(INSTRUCTIONSIZE), b''):
        word = int.from_bytes(raw_word, byteorder='little', signed=True)

        if word & instruction_mask == instruction:
          # at least one instruction has the right encoding
          exit_code = 0
          warning = 'No instruction matching the RISC-V encoding found'

  os.remove(TMP_FILE)
  record_result(exit_code == 0, msg, output)


def test_execution(file, result, msg):
  p = Popen(['./selfie', '-c', 'tests/' + file, '-m', '128'], stdout=PIPE, stderr=PIPE, stdin=PIPE)

  output = p.stdout.read().decode(sys.stdout.encoding)
  p.wait()

  if p.returncode != result:
    warning = 'Execution terminated with wrong exit code {} instead of {}'.format(p.returncode, result)
  else:
    warning = None

  record_result(p.returncode == result, msg, output, warning)


def test_shift(direction):
  if direction == 'left':
    instruction = SLL_INSTRUCTION
  else:
    instruction = SRL_INSTRUCTION

  literal_file = 'bitwise-' + direction + '-shift-literals.c'
  variable_file = 'bitwise-' + direction + '-shift-variables.c'

  test_compilable(literal_file, 
    'bitwise-' + direction + '-shift operator with literals compiled')
  test_instruction_format(literal_file, instruction, R_FORMAT_MASK, 
    'bitwise-' + direction + '-shift operator has right RISC-V encoding')
  test_execution(literal_file, 2, 
    'bitwise-' + direction + '-shift operator calculates the right result for literals when executed with MIPSTER')
  test_compilable(variable_file, 
    'bitwise-' + direction + '-shift operator with variables compiled')
  test_instruction_format(variable_file, instruction, R_FORMAT_MASK, 
    'bitwise-' + direction + '-shift operator has right RISC-V encoding')
  test_execution(variable_file, 2, 
    'bitwise-' + direction + '-shift operator calculates the right result for variables when executed with MIPSTER')


def test_structs():
  test_compilable('struct-declaration.c',
    'empty struct declarations compiled')
  test_compilable('struct-member-declaration.c',
    'struct declaration with trivial members compiled')
  test_compilable('struct-initialization.c',
    'empty struct with initialization compiled')
  test_compilable('struct-member-initialization.c',
    'initialization of trivial struct members compiled')
  test_execution('struct-member-initialization.c', 123,
    'read and write operations of trivial struct member works when executed with MIPSTER')


def grade():
  number_of_tests_passed, number_of_tests_failed

  number_of_tests = number_of_tests_passed + number_of_tests_failed

  print('tests passed: {:02.1f}%'.format(number_of_tests_passed / number_of_tests * 100))


if __name__ == "__main__":
  test_shift(direction='left')
  test_shift(direction='right')
  test_structs()

  grade()

