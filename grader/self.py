import sys
import os
import re
import math
from subprocess import Popen, PIPE

number_of_positive_tests_passed = [0]
number_of_positive_tests_failed = [0]
number_of_negative_tests_passed = [0]
number_of_negative_tests_failed = [0]

home_path = ''

INSTRUCTIONSIZE = 4  # in bytes
ELF_HEADER_LEN = 120

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


def filter_status_messages(selfie_output):
  return re.sub(r'([a-zA-Z]:\\|(./)?selfie)[^\n]*\n', '', selfie_output).replace('\n', '')


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
  command = command.replace('grader/', home_path + 'grader/')
  command = command.replace('manuscript/code/', home_path + 'manuscript/code/')

  process = Popen(command, stdout=PIPE, shell=True)
  output = process.communicate()[0].decode(sys.stdout.encoding)

  return (process.returncode, output)


def set_up():
  execute('make clean && make selfie')


def has_compiled(returncode, output, should_succeed=True):
  warning = None

  succeeded = (should_succeed and returncode == 0) or (should_succeed == False and returncode != 0)

  match = re.search('(syntax error [^\n]*)', output)

  if match != None:
    if should_succeed == False:
      succeeded = True
    else:
      succeeded = False
      warning = match.group(0)

  return (succeeded, warning)


def test_instruction_format(file, instruction, instruction_mask, msg):
  exit_code, output = execute(f'./selfie -c grader/{file} -o .tmp.bin')
  warning = None

  if exit_code == 0:
    exit_code = 1

    with open('.tmp.bin', 'rb') as f:
      f.read(ELF_HEADER_LEN)

      for raw_word in iter(lambda: f.read(INSTRUCTIONSIZE), b''):
        word = int.from_bytes(raw_word, byteorder='little', signed=True)

        if word & instruction_mask == instruction:
          # at least one instruction has the right encoding
          exit_code = 0

  os.remove('.tmp.bin')

  if exit_code != 0:
    warning = 'No instruction matching the RISC-V encoding found'

  record_result(exit_code == 0, msg, output, warning)


def test_execution(command, msg, success_criteria=True):
  returncode, output = execute(command)

  if type(success_criteria) is bool:
    should_succeed = success_criteria

    if should_succeed:
      warning = f'Execution terminated with wrong exit code {returncode} instead of 0'
    else:
      warning = f'Execution terminated with wrong exit code {returncode}'

    record_result(returncode == 0, msg, output, warning, should_succeed, command)

  elif type(success_criteria) is int:
    record_result(returncode == success_criteria, msg, output,
      f'Execution terminated with wrong exit code {returncode} instead of {success_criteria}', True, command)

  elif type(success_criteria) is str:
    filtered_output = filter_status_messages(output)

    record_result(filtered_output == success_criteria, msg, output, 'The actual printed output does not match', True, command)

  elif callable(success_criteria):
    result, warning = success_criteria(returncode, output)

    record_result(result, msg, output, warning, True, command)


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


def is_interleaved_output(returncode, output, interleaved_msg, number_of_interleaved):
  strings = [interleaved_msg[:] for i in range(0, number_of_interleaved)]

  filtered_output = filter_status_messages(output)

  if filtered_output == interleaved_msg * number_of_interleaved:
    return (False, 'The output strings are ordered sequentially')
  else:
    return (isInterleaved(strings, filtered_output), 'The output strings are not interleaved')


def test_compilable(file, msg, should_succeed=True):
  test_execution(f'./selfie -c grader/{file}', msg, success_criteria=lambda code, out: has_compiled(code, out, should_succeed=should_succeed))


def test_mipster_execution(file, result, msg):
  test_execution(f'./selfie -c grader/{file} -m 128', msg, success_criteria=result)


def test_hypster_execution(file, result, msg):
  test_execution(f'./selfie -c selfie.c -m 128 -c grader/{file} -y 64', msg, success_criteria=result)


def test_interleaved_output(command, interleaved_msg, number_of_interleaved, msg):
  test_execution(command, msg, success_criteria=lambda code, out: is_interleaved_output(code, out, interleaved_msg, number_of_interleaved))


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
    start_stage(1)
    test_execution('./selfie -c selfie.c -s selfie.s -a selfie.s',
      'selfie can parse its own implementation in assembly')
    test_execution('./selfie -a grader/assembler-missing-address.s',
      'assembly file with a missing address is not parseable', success_criteria=False)
    test_execution('./selfie -a grader/assembler-missing-instruction.s',
      'assembly file with a missing instruction is not parseable', success_criteria=False)
    test_execution('./selfie -a grader/assembler-missing-literal.s',
      'assembly file with a missing literal is not parseable', success_criteria=False)

  if stage >= 2:
    start_stage(2)
    test_execution('./selfie -c selfie.c -s selfie1.s -a selfie1.s -m 128 -a selfie1.s -s selfie2.s '
     + '&& diff -q selfie1.s selfie2.s',
      'selfie can assemble its own binary file and both assembly files are exactly the same')


def test_concurrent_machines():
  test_interleaved_output('./selfie -c manuscript/code/hello-world.c -x 10', 'Hello World!    ', 10,
    '10 Mipster machines are running concurrently')
  test_interleaved_output('./selfie -c selfie.c -m 128 -c manuscript/code/hello-world.c -z 10', 'Hello World!    ', 10,
    '10 Hypster machines are running concurrently')


def test_fork_and_wait():
  test_execution('./selfie -c grader/fork-wait.c -m 128',
    'fork creates a child process, where the parent can wait for the child process with MIPSTER', success_criteria=70)
  test_execution('./selfie -c selfie.c -m 128 -c grader/fork-wait.c -y 64',
    'fork creates a child process, where the parent can wait for the child process with HYPSTER', success_criteria=70)


def test_lock():
  test_execution('./selfie -c grader/hello-world-without-lock.c -m 128',
    '16 processes are running concurrently on MIPSTER',
    success_criteria=lambda code, out: is_interleaved_output(code, out, 'Hello World!    ', 8))
  test_execution('./selfie -c selfie.c -m 128 -c grader/hello-world-without-lock.c -y 10',
    '16 processes are running concurrently on HYPSTER',
    success_criteria=lambda code, out: is_interleaved_output(code, out, 'Hello World!    ', 8))
  test_execution('./selfie -c grader/hello-world-with-lock.c -m 128',
    '16 processes are printing in sequential order with the use of locks on MIPSTER',
    success_criteria='Hello World!    ' * 8)
  test_execution('./selfie -c selfie.c -m 128 -c grader/hello-world-with-lock.c -y 10',
    '16 processes are printing in sequential order with the use of locks on HYPSTER',
    success_criteria='Hello World!    ' * 8)


def test_thread():
  test_execution('./selfie -c grader/thread-implementation.c -m 128',
    'creates a thread, where the parent can join the thread with MIPSTER', success_criteria=70)
  test_execution('./selfie -c selfie.c -m 128 -c grader/thread-implementation.c -y 64',
    'creates a thread, where the parent can join the thread with HYPSTER', success_criteria=70)
  test_execution('./selfie -c grader/thread-data-shared.c -m 128',
    'data section is shared for threads on MIPSTER',
    success_criteria=1)
  test_execution('./selfie -c selfie.c -m 128 -c grader/thread-data-shared.c -y 64',
    'data section is shared for threads on HYPSTER',
    success_criteria=1)
  test_execution('./selfie -c grader/thread-heap-shared.c -m 128',
    'heap data is shared for threads on MIPSTER',
    success_criteria=1)
  test_execution('./selfie -c selfie.c -m 128 -c grader/thread-heap-shared.c -y 64',
    'heap data is shared for threads on HYPSTER',
    success_criteria=1)


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
    print('usage: python3 grader/self.py { test_name }')
    exit()

  sys.setrecursionlimit(5000)

  home_path = os.path.dirname(sys.argv[0]) + '/../'

  tests = sys.argv[1:]

  for test in tests:
    set_up()

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
    elif test == 'lock':
      test_lock()
    elif test == 'thread':
      test_thread()
    else:
      print(f'unknown test: {test}')

  grade()

