import sys
import os
import re
import math
from subprocess import Popen, PIPE

number_of_positive_tests_passed = 0
number_of_positive_tests_failed = 0
number_of_negative_tests_passed = 0
number_of_negative_tests_failed = 0

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


def print_passed(msg):
  print("\033[92m[PASSED]\033[0m " + msg)


def print_failed(msg, warning, output, command):
  print("\033[91m[FAILED]\033[0m " + msg)
  if command != None:
    print(command)
  if warning != None:
    print("\033[93m > " + warning + " <\033[0m")
  print(' >> ' + output[:-1].replace('\n', '\n >> '))


def record_result(result, msg, output, warning, should_succeed=True, command=None):
  global number_of_positive_tests_passed, number_of_positive_tests_failed
  global number_of_negative_tests_passed, number_of_negative_tests_failed

  if result == True:
    if should_succeed:
      number_of_positive_tests_passed += 1
      print_passed(msg)
    else:
      number_of_negative_tests_failed += 1
      print_failed(msg, warning, output, command)
  else:
    if should_succeed:
      number_of_positive_tests_failed += 1
      print_failed(msg, warning, output, command)
    else:
      number_of_negative_tests_passed += 1
      print_passed(msg)


def test_compilable(file, msg, should_succeed=True):
  p = Popen(['./selfie', '-c', 'grader/' + file], stdout=PIPE, stderr=PIPE, stdin=PIPE)

  output = p.stdout.read().decode(sys.stdout.encoding)
  p.wait()

  exit_code = p.returncode
  warning = None

  succeeded = (should_succeed and exit_code == 0) or (should_succeed == False and exit_code != 0)

  match = re.search('(syntax error [^\n]*)', output)

  if match != None:
    if should_succeed == False:
      succeeded = True
    else:
      succeeded = False
      warning = match.group(0)

  record_result(succeeded, msg, output, warning, should_succeed)


def test_instruction_format(file, instruction, instruction_mask, msg):
  p = Popen(['./selfie', '-c', 'grader/' + file, '-o', TMP_FILE], stdout=PIPE, stderr=PIPE, stdin=PIPE)

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

  os.remove(TMP_FILE)

  if exit_code != 0:
    warning = 'No instruction matching the RISC-V encoding found'

  record_result(exit_code == 0, msg, output, warning)


def test_mipster_execution(file, result, msg):
  p = Popen(['./selfie', '-c', 'grader/' + file, '-m', '128'], stdout=PIPE, stderr=PIPE, stdin=PIPE)

  output = p.stdout.read().decode(sys.stdout.encoding)
  p.wait()

  if p.returncode != result:
    warning = 'Mipster execution terminated with wrong exit code {} instead of {}'.format(p.returncode, result)
  else:
    warning = None

  record_result(p.returncode == result, msg, output, warning)


def test_execution(command, msg, should_succeed=True):
  p = Popen(command.split(' '), stdout=PIPE, stderr=PIPE, stdin=PIPE)

  output = p.stdout.read().decode(sys.stdout.encoding)
  p.wait()

  if should_succeed:
    warning = f'Execution terminated with wrong exit code {p.returncode} instead of 0'
  else:
    warning = f'Execution terminated with wrong exit code {p.returncode}'

  record_result(p.returncode == 0, msg, output, warning, should_succeed, command)


def test_hex_literal():
  test_compilable('hex-integer-literal.c', 
    'hex integer literal with all characters compiled')
  test_mipster_execution('hex-integer-literal.c', 1,
    'hex integer literal with all characters has the right value')
  test_compilable('hex-integer-literal-max.c',
    'maximum hex integer literal compiled')
  test_mipster_execution('hex-integer-literal-max.c', 1,
    'maximum hex integer literal has the right value')
  test_compilable('hex-integer-literal-max.c',
    'minimum hex integer literal compiled')
  test_mipster_execution('hex-integer-literal-max.c', 1,
    'minimum hex integer literal has the right value')
  test_compilable('hex-integer-literal-invalid.c', 
    'out of bounds hex integer literal has not compiled', should_succeed=False)


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
  test_mipster_execution(literal_file, 2,
    'bitwise-' + direction + '-shift operator calculates the right result for literals when executed with MIPSTER')
  test_compilable(variable_file,
    'bitwise-' + direction + '-shift operator with variables compiled')
  test_instruction_format(variable_file, instruction, R_FORMAT_MASK,
    'bitwise-' + direction + '-shift operator has right RISC-V encoding')
  test_mipster_execution(variable_file, 2,
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
  test_mipster_execution('struct-member-initialization.c', 123,
    'read and write operations of trivial struct member works when executed with MIPSTER')
  test_compilable('struct-nested-declaration.c',
    'struct declaration with struct members compiled')
  test_compilable('struct-nested-initialization.c',
    'struct initialization with struct members compiled')
  test_mipster_execution('struct-nested-initialization.c', 123,
    'read and write operations of nested struct member works when executed with MIPSTER')
  test_compilable('struct-as-parameter.c',
    'struct as function parameter compiled')
  test_mipster_execution('struct-as-parameter.c', 1,
    'read and write operations of structs as parameter work when executed with MIPSTER')


def test_assembler(stage):
  if stage >= 1:
    test_execution('./selfie -c selfie.c -s selfie.s -a selfie.s',
      'selfie can parse its own implementation in assembly')
    test_execution('./selfie -a grader/assembler-missing-address.s',
      'assembly file with a missing address is not parseable', should_succeed=False)
    test_execution('./selfie -a grader/assembler-missing-instruction.s',
      'assembly file with a missing instruction is not parseable', should_succeed=False)
    test_execution('./selfie -a grader/assembler-missing-literal.s',
      'assembly file with a missing literal is not parseable', should_succeed=False)

  if stage >= 2:
    test_execution('./selfie -c selfie.c -s selfie1.s -a selfie1.s -m 10 -a selfie1.s -s selfie2.s',
      'selfie can assemble its own disassembly file')
    test_execution('diff -q selfie1.s selfie2.s',
      'both assembly files are exaclty the same')


def grade():
  global number_of_positive_tests_passed, number_of_positive_tests_failed
  global number_of_negative_tests_passed, number_of_negative_tests_failed

  number_of_tests =  number_of_positive_tests_passed + number_of_positive_tests_failed
  number_of_tests += number_of_negative_tests_passed + number_of_negative_tests_failed

  number_of_tests_passed = number_of_positive_tests_passed + number_of_negative_tests_passed

  if number_of_tests == 0:
    print('nothing to grade')
    return

  passed = number_of_tests_passed / number_of_tests

  print('tests passed:  {:02.1f}%'.format(passed * 100))

  if passed == 1.0:
    grade = 2
    color = 92
  elif passed >= 0.5:
    grade = 3
    color = 93
  elif passed > 0.0:
    grade = 4
    color = 93
  else:
    grade = 5
    color = 91

  if number_of_positive_tests_passed == 0:
    print('warning:       you have not passed at least one positive test')
    grade = 5
    color = 91

  print(f'your grade is: \033[{color}m\033[1m{grade}\033[0m')


if __name__ == "__main__":
  if len(sys.argv) <= 1:
    print('usage: python3 self.py { test_name }')
    exit()

  tests = sys.argv
  tests.remove(tests[0])

  for test in tests:
    if test == 'hex-literal':
      test_hex_literal()
    elif test == 'shift':
      test_shift(direction='left')
      test_shift(direction='right')
    elif test == 'struct':
      test_structs()
    elif re.match(r'^assembler-([1-2])$', test):
      stage = re.search(r'^assembler-([1-2])$', test).group(1)

      test_assembler(int(stage))
    else:
      print(f'unknown test: {test}')

  grade()

