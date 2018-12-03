import sys
import os
import re
import math
from subprocess import Popen, PIPE

number_of_positive_tests_passed = [0]
number_of_positive_tests_failed = [0]
number_of_negative_tests_passed = [0]
number_of_negative_tests_failed = [0]

GRADER_PATH = ''

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
      number_of_positive_tests_passed[-1] += 1
      print_passed(msg)
    else:
      number_of_negative_tests_failed[-1] += 1
      print_failed(msg, warning, output, command)
  else:
    if should_succeed:
      number_of_positive_tests_failed[-1] += 1
      print_failed(msg, warning, output, command)
    else:
      number_of_negative_tests_passed[-1] += 1
      print_passed(msg)


def execute(command):
  Popen(command, stdout=PIPE, stderr=PIPE, stdin=PIPE, shell=True).wait()


def set_up():
  execute('make clean && make selfie')


def test_compilable(file, msg, should_succeed=True):
  p = Popen(['./selfie', '-c', GRADER_PATH + file], stdout=PIPE, stderr=PIPE, stdin=PIPE)

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
  p = Popen(['./selfie', '-c', GRADER_PATH + file, '-o', TMP_FILE], stdout=PIPE, stderr=PIPE, stdin=PIPE)

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
  p = Popen(['./selfie', '-c', GRADER_PATH + file, '-m', '128'], stdout=PIPE, stderr=PIPE, stdin=PIPE)

  output = p.stdout.read().decode(sys.stdout.encoding)
  p.wait()

  if p.returncode != result:
    warning = 'Mipster execution terminated with wrong exit code {} instead of {}'.format(p.returncode, result)
  else:
    warning = None

  record_result(p.returncode == result, msg, output, warning)


def test_hypster_execution(file, result, msg):
  p = Popen(['./selfie', '-c', 'selfie.c', '-m', '128', '-c', GRADER_PATH + file, '-y', '64'], stdout=PIPE, stderr=PIPE, stdin=PIPE)

  output = p.stdout.read().decode(sys.stdout.encoding)
  p.wait()

  if p.returncode != result:
    warning = 'Hypster execution terminated with wrong exit code {} instead of {}'.format(p.returncode, result)
  else:
    warning = None

  record_result(p.returncode == result, msg, output, warning)


def test_execution(command, msg, should_succeed=True):
  p = Popen(command, stdout=PIPE, stderr=PIPE, stdin=PIPE, shell=True)

  output = p.stdout.read().decode(sys.stdout.encoding)
  p.wait()

  if should_succeed:
    warning = f'Execution terminated with wrong exit code {p.returncode} instead of 0'
  else:
    warning = f'Execution terminated with wrong exit code {p.returncode}'

  record_result(p.returncode == 0, msg, output, warning, should_succeed, command)

class Memoize:
  def __init__(self, fn):
    self.fn = fn
    self.memo = {}

  def __call__(self, *args):
    h = len(args[1]) + sum([i * 100 * x for i,x in enumerate(map(lambda s: len(s), args[0]), 1000)])
    if h not in self.memo:
      self.memo[h] = self.fn(*args)
    return self.memo[h]

@Memoize
def isInterleaved(strings, interleaved):
  if all(len(string) == 0 for string in strings) and len(interleaved) == 0:
    return True
  
  if len(interleaved) == 0:
    return False

  for i, string in enumerate(filter(lambda s: len(s) > 0, strings)):
    tmp = strings.copy()
    tmp[i] = tmp[i][1:]
    if interleaved[0] == string[0] and isInterleaved(tmp, interleaved[1:]):
      return True

  return False


def test_interleaved_output(command, interleaved_msg, number_of_interleaved, msg):
  p = Popen(command, stdout=PIPE, stderr=PIPE, stdin=PIPE, shell=True)
  p.wait()

  output = p.stdout.read().decode(sys.stdout.encoding)

  if p.returncode != 0:
    record_result(False, msg, output, '', True, command)
  else:
    strings = [interleaved_msg[:] for i in range(0, number_of_interleaved)]

    filtered_output = re.sub(r'([a-zA-Z]:\\|(./)?selfie)[^\n]*\n', '', output)
    filtered_output = filtered_output.replace('\n', '')

    if len(filtered_output.replace(interleaved_msg, '')) == 0:
      record_result(False, msg, output, 'The output strings are ordered sequentially', True, command)
    else:
      record_result(isInterleaved(strings, filtered_output), msg, output, 'The output strings are not interleaved')


def test_hex_literal():
  set_up()

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
  set_up()

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
  set_up()

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
  set_up()

  if stage >= 1:
    start_stage(1)
    test_execution('./selfie -c selfie.c -s selfie.s -a selfie.s',
      'selfie can parse its own implementation in assembly')
    test_execution(f'./selfie -a {GRADER_PATH}assembler-missing-address.s',
      'assembly file with a missing address is not parseable', should_succeed=False)
    test_execution(f'./selfie -a {GRADER_PATH}assembler-missing-instruction.s',
      'assembly file with a missing instruction is not parseable', should_succeed=False)
    test_execution(f'./selfie -a {GRADER_PATH}assembler-missing-literal.s',
      'assembly file with a missing literal is not parseable', should_succeed=False)

  if stage >= 2:
    start_stage(2)
    test_execution('./selfie -c selfie.c -s selfie1.s -a selfie1.s -m 10 -a selfie1.s -s selfie2.s '
     + '&& diff -q selfie1.s selfie2.s',
      'selfie can assemble its own binary file and both assembly files are exactly the same')


def test_concurrent_machines():
  set_up()

  test_interleaved_output('./selfie -c manuscript/code/hello-world.c -x 10', 'Hello World!    ', 10,
    '10 Mipster machines are running concurrently')
  test_interleaved_output('./selfie -c selfie.c -m 10 -c manuscript/code/hello-world.c -z 10', 'Hello World!    ', 10,
    '10 Hypster machines are running concurrently')


def test_fork_and_wait():
  set_up()

  test_mipster_execution('fork-wait.c', 70,
    'fork creates a child process, where the parent can wait for the child process with MIPSTER')
  test_hypster_execution('fork-wait.c', 70,
    'fork creates a child process, where the parent can wait for the child process with HYPSTER')


def start_stage(stage):
  global number_of_positive_tests_passed, number_of_positive_tests_failed
  global number_of_negative_tests_passed, number_of_negative_tests_failed

  print(f'==== STAGE {stage} ====')

  if stage == 1:
    return

  number_of_positive_tests_passed.append(0)
  number_of_negative_tests_passed.append(0)
  number_of_positive_tests_failed.append(0)
  number_of_negative_tests_failed.append(0)


def grade():
  global number_of_positive_tests_passed, number_of_positive_tests_failed
  global number_of_negative_tests_passed, number_of_negative_tests_failed

  grade_is_negative = False

  for stage in range(0, len(number_of_positive_tests_passed)):
    if len(number_of_positive_tests_passed) > 1:
      name = f' of stage {stage + 1} '
    else:
      name = ' '

    number_of_tests =  number_of_positive_tests_passed[stage] + number_of_positive_tests_failed[stage]
    number_of_tests += number_of_negative_tests_passed[stage] + number_of_negative_tests_failed[stage]

    number_of_tests_passed = number_of_positive_tests_passed[stage] + number_of_negative_tests_passed[stage]

    if number_of_tests == 0:
      print('nothing to grade')
      return

    passed = number_of_tests_passed / number_of_tests

    print('tests{}passed: {:02.1f}%'.format(name, passed * 100))

    if number_of_positive_tests_passed[stage] == 0:
      print('warning: you have not passed at least one positive test')
      grade_is_negative = True


  number_of_tests_passed = sum(number_of_positive_tests_passed) + sum(number_of_negative_tests_passed)

  number_of_tests =  sum(number_of_positive_tests_passed) + sum(number_of_positive_tests_failed)
  number_of_tests += sum(number_of_negative_tests_passed) + sum(number_of_negative_tests_failed)

  passed = number_of_tests_passed / number_of_tests

  if grade_is_negative:
    grade = 5
    color = 91
  elif passed == 1.0:
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

  print(f'your grade is: \033[{color}m\033[1m{grade}\033[0m')


if __name__ == "__main__":
  if len(sys.argv) <= 1:
    print('usage: python3 self.py { test_name }')
    exit()

  GRADER_PATH = os.path.dirname(sys.argv[0]) + '/'

  tests = sys.argv[1:]

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
    elif test == 'concurrent-machines':
      test_concurrent_machines()
    elif test == 'fork-wait':
      test_fork_and_wait()
    else:
      print(f'unknown test: {test}')

  grade()

