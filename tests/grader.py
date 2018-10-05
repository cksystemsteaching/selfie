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


def record_result(result, msg, output):
  global number_of_tests_passed, number_of_tests_failed

  if result == True:
    number_of_tests_passed += 1

    print("\033[92m[PASSED]\033[0m " + msg)
  else:
    number_of_tests_failed += 1

    print("\033[91m[FAILED]\033[0m " + msg)
    print(' >>> ' + output[:-1].replace('\n', '\n >>> '))


def test_compilable(file, msg):
  p = Popen(['./selfie', '-c', 'tests/' + file], stdout=PIPE, stderr=PIPE, stdin=PIPE)

  output = p.stdout.read().decode(sys.stdout.encoding)
  p.wait()

  exit_code = p.returncode

  if exit_code == 0:
    if output.find('syntax error') >= 0:
      exit_code = 1

  record_result(exit_code == 0, msg, output)


def test_instruction_format(file, instruction, instruction_mask, msg):
  p = Popen(['./selfie', '-c', 'tests/' + file, '-o', TMP_FILE], stdout=PIPE, stderr=PIPE, stdin=PIPE)

  output = p.stdout.read().decode(sys.stdout.encoding)
  p.wait()

  exit_code = p.returncode

  if exit_code == 0:
    exit_code = 1

    with open(TMP_FILE, 'rb') as f:
      f.read(ELF_HEADER_LEN)

      for raw_word in iter(lambda: f.read(INSTRUCTIONSIZE), b''):
        word = int.from_bytes(raw_word, byteorder='little', signed=True)

        if word & instruction_mask == instruction:
          # at least one instruction has the right encoding
          exit_code = 0

  os.remove(TMP_FILE)
  record_result(exit_code == 0, msg, output)


def test_execution(file, result, msg):
  p = Popen(['./selfie', '-c', 'tests/' + file, '-m', '128'], stdout=PIPE, stderr=PIPE, stdin=PIPE)

  output = p.stdout.read().decode(sys.stdout.encoding)
  p.wait()

  record_result(p.returncode == result, msg, output)


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


def grade():
  number_of_tests_passed, number_of_tests_failed

  number_of_tests = number_of_tests_passed + number_of_tests_failed

  print('tests passed: {:02.1f}%'.format(number_of_tests_passed / number_of_tests * 100))


if __name__ == "__main__":
  test_shift(direction='left')
  test_shift(direction='right')
  
  grade()

