#!/usr/bin/env python3
"""
Copyright (c) 2015-2019, the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is governed
by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the Department of
Computer Sciences of the University of Salzburg in Austria. For further
information and code please refer to:

http://selfie.cs.uni-salzburg.at

This is the automatic grader of the selfie project.
Students may use the grader for self-grading their solutions.
"""

from __future__ import print_function
import sys
import os
import re
import math
import struct

if sys.version_info < (3, 3):
  from subprocess import Popen, PIPE
  print('warning: python V3.3 or newer is recommended')
  print('mipster execution timeout is disabled with this python version\n')
else:
  from subprocess import Popen, TimeoutExpired, PIPE

number_of_positive_tests_passed = [0]
number_of_positive_tests_failed = [0]
number_of_negative_tests_passed = [0]
number_of_negative_tests_failed = [0]

failed_mandatory_test = False

def reset_assignment_results():
  global number_of_positive_tests_passed, number_of_positive_tests_failed
  global number_of_negative_tests_passed, number_of_negative_tests_failed
  global failed_mandatory_test

  number_of_positive_tests_passed = [0]
  number_of_positive_tests_failed = [0]
  number_of_negative_tests_passed = [0]
  number_of_negative_tests_failed = [0]

  failed_mandatory_test = False

home_path = ''

DEFAULT_BULK_GRADE_DIRECTORY = os.path.abspath('./.repositories')

bulk_grade_mode = False
file_with_commit_links = None
bulk_grade_directory = DEFAULT_BULK_GRADE_DIRECTORY

INSTRUCTIONSIZE = 4  # in bytes
REGISTERSIZE    = 8  # in bytes

OP_OP  = 51
OP_AMO = 47
OP_IMM = 19

F3_SLL  = 1
F3_SRL  = 5
F3_OR   = 6
F3_AND  = 7
F3_XORI = 4
F3_LR   = 3
F3_SC   = 3

F5_LR  = 2
F5_SC  = 3

F7_SLL = 0
F7_SRL = 0
F7_AND = 0
F7_OR  = 0

def read_instruction(file):
  b = file.read(INSTRUCTIONSIZE)

  if len(b) != INSTRUCTIONSIZE:
    return 0

  return struct.unpack('<i', b)[0]

def read_data(file):
  b = file.read(REGISTERSIZE)

  if len(b) != REGISTERSIZE:
    return 0

  return struct.unpack('<Q', b)[0]

def encode_i_format(immediate, funct3, opcode):
  return ((((immediate << 5) << 3) + funct3 << 5) << 7) + opcode

def encode_r_format(funct7, funct3, opcode):
  return (((((funct7 << 5) << 5) << 3) + funct3 << 5) << 7) + opcode

def encode_amo_format(funct5, funct3):
  return (((((funct5 << 7) << 5) << 3) + funct3 << 5) << 7) + OP_AMO

NOT_FORMAT_MASK = 0b11111111111100000111000001111111
R_FORMAT_MASK   = 0b11111110000000000111000001111111
AMO_FORMAT_MASK = 0b11111000000000000111000001111111
LR_FORMAT_MASK  = 0b11111001111100000111000001111111

REGISTER_REGEX = '(zero|ra|sp|gp|tp|t[0-6]|s[0-9]|s10|s11|a[0-7])'

SLL_INSTRUCTION = ('bitwise-left-shift', encode_r_format(F7_SLL, F3_SLL, OP_OP), R_FORMAT_MASK,
                  '^sll\\s+' + REGISTER_REGEX + ',' + REGISTER_REGEX + ',' + REGISTER_REGEX + '$')
SRL_INSTRUCTION = ('bitwise-right-shift', encode_r_format(F7_SRL, F3_SRL, OP_OP), R_FORMAT_MASK,
                  '^srl\\s+' + REGISTER_REGEX + ',' + REGISTER_REGEX + ',' + REGISTER_REGEX + '$')
OR_INSTRUCTION  = ('bitwise-or', encode_r_format(F7_OR, F3_OR, OP_OP), R_FORMAT_MASK,
                  '^or\\s+' + REGISTER_REGEX + ',' + REGISTER_REGEX + ',' + REGISTER_REGEX + '$')
AND_INSTRUCTION = ('bitwise-and', encode_r_format(F7_AND, F3_AND, OP_OP), R_FORMAT_MASK,
                  '^and\\s+' + REGISTER_REGEX + ',' + REGISTER_REGEX + ',' + REGISTER_REGEX + '$')
NOT_INSTRUCTION = ('bitwise-not', encode_i_format(4095, F3_XORI, OP_IMM), NOT_FORMAT_MASK,
                  '^xori\\s+' + REGISTER_REGEX + ',' + REGISTER_REGEX + ',-1$')
LR_INSTRUCTION  = ('load-reserved', encode_amo_format(F5_LR, F3_LR), LR_FORMAT_MASK,
                  '^lr\\.d\\s+' + REGISTER_REGEX + ',\\(' + REGISTER_REGEX + '\\)$')
SC_INSTRUCTION  = ('store-conditional', encode_amo_format(F5_SC, F3_SC), AMO_FORMAT_MASK,
                  '^sc\\.d\\s+' + REGISTER_REGEX + ',' + REGISTER_REGEX + ',\\(' + REGISTER_REGEX + '\\)$')

class DummyWriter:
  def __getattr__( self, name ):
    return sys.__stdout__.__getattribute__(name)

  def write(self, text):
    return

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


def record_result(result, msg, output, warning, should_succeed=True, command=None, mandatory=False):
  global number_of_positive_tests_passed, number_of_positive_tests_failed
  global number_of_negative_tests_passed, number_of_negative_tests_failed
  global failed_mandatory_test

  if result:
    if should_succeed:
      if not mandatory:
        number_of_positive_tests_passed[-1] += 1
      
      print_passed(msg)
    else:
      if mandatory:
        failed_mandatory_test = True
      else:
        number_of_negative_tests_failed[-1] += 1
      
      print_failed(msg, warning, output, command)
  else:
    if should_succeed:
      if mandatory:
        failed_mandatory_test = True
      else:
        number_of_positive_tests_failed[-1] += 1
      
      print_failed(msg, warning, output, command)
    else:
      if not mandatory:
        number_of_negative_tests_passed[-1] += 1
      
      print_passed(msg)


class TimeoutException(Exception):
  def __init__(self, command, timeout, output, error_output):
    Exception.__init__(self, 'The command \"' + command + '\" has timed out after ' + str(timeout) + 's')

    self.output = output
    self.error_output = error_output


def execute(command, timeout=10):
  command = command.replace('grader/', home_path + '/grader/')
  command = command.replace('manuscript/code/', home_path + '/manuscript/code/')

  process = Popen(command.split(' '), stdout=PIPE, stderr=PIPE)

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


def set_up():
  execute('make clean')
  execute('make selfie')


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


def has_no_compile_warnings(return_value, output):
  if return_value != 0:
    warning = 'selfie terminates with an error code of {} during self-compilation'.format(return_value)
    succeeded = False
  else:
    syntax_error_matcher = re.search('(syntax error [^\n]*)', output)
    type_warning_matcher = re.search('(warning [^\n]*)', output)

    if syntax_error_matcher != None:
      warning = syntax_error_matcher.group(0)
      succeeded = False
    elif type_warning_matcher != None:
      warning = type_warning_matcher.group(0)
      succeeded = False
    else:
      warning = None
      succeeded = True

  return (succeeded, warning)


def test_instruction_encoding(instruction, file):
  msg = instruction[0] + ' has right RISC-V encoding'

  command = './selfie -c grader/{} -o .tmp.bin'.format(file)

  try:
    exit_code, output, _ = execute(command)

    instruction_value = instruction[1]
    instruction_mask  = instruction[2]

    if exit_code == 0:
      exit_code = 1

      try:
        with open('.tmp.bin', 'rb') as f:
          ignored_elf_header_size = 14 * REGISTERSIZE

          f.read(ignored_elf_header_size)

          code_start  = read_data(f)
          code_length = read_data(f)

          # ignore all pading bytes
          no_of_bytes_until_code = code_start - ignored_elf_header_size - 2 * REGISTERSIZE

          if no_of_bytes_until_code < 0: 
            no_of_bytes_until_code = 0

          f.read(no_of_bytes_until_code)

          # read all RISC-V instructions from binary
          read_instructions = map(lambda x: read_instruction(f), range(int(code_length / INSTRUCTIONSIZE)))

          if any(map(lambda x: x & instruction_mask == instruction_value, read_instructions)):
            # at least one instruction has the right encoding
            exit_code = 0
        
        if os.path.isfile('.tmp.bin'):
          os.remove('.tmp.bin')

        record_result(exit_code == 0, msg, output, 'No instruction matching the RISC-V encoding found')

      except FileNotFoundError:
        record_result(False, msg, '', 'The binary file has not been created by selfie')
    else:
      record_result(False, msg, output, 'Selfie returned an error when executing "' + command + '"')
  except FileNotFoundError as e:
    # the program to execute can not be found (e.g. selfie is not built)
    record_result(False, msg, '', str(e), True, command, mandatory=False)



def test_assembler_instruction_format(instruction, file):
  msg = instruction[0] + ' RISC-V instruction has right assembly instruction format'

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

          record_result(exit_code == 0, msg, output, 'No assembler instruction matching the RISC-V encoding found')

        if os.path.isfile('.tmp.s'):
          os.remove('.tmp.s')

      except FileNotFoundError:
        record_result(False, msg, output, 'The assembler file has not been created by selfie')
    else:
      record_result(False, msg, output, 'Selfie returned an error when executing "' + command + '"')
  except FileNotFoundError as e:
    # the program to execute can not be found (e.g. selfie is not built)
    record_result(False, msg, '', str(e), True, command, mandatory=False)




def test_execution(command, msg, success_criteria=True, mandatory=False):
  try:
    returncode, output, _ = execute(command)

    if type(success_criteria) is bool:
      should_succeed = success_criteria

      if should_succeed:
        warning = 'Execution terminated with wrong exit code {} instead of 0'.format(returncode)
      else:
        warning = 'Execution terminated with wrong exit code {}'.format(returncode)

      record_result(returncode == 0, msg, output, warning, should_succeed, command, mandatory)

    elif type(success_criteria) is int:
      record_result(returncode == success_criteria, msg, output,
        'Execution terminated with wrong exit code {} instead of {}'.format(returncode, success_criteria), True, command, mandatory)

    elif type(success_criteria) is str:
      filtered_output = filter_status_messages(output)

      record_result(filtered_output == success_criteria, msg, output, 'The actual printed output does not match', True, command, mandatory)

    elif callable(success_criteria):
      result, warning = success_criteria(returncode, output)

      record_result(result, msg, output, warning, True, command, mandatory)
  except TimeoutException as e:
    record_result(False, msg, e.output, str(e), True, command, mandatory)
  except FileNotFoundError as e:
    # the program to execute can not be found (e.g. selfie is not built)
    record_result(False, msg, '', str(e), True, command, mandatory)
  


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


def is_permutation_of(returncode, output, numbers):
  filtered_output = filter_status_messages(output)

  printed_numbers = list(map(lambda x: int(x), filter(lambda s: len(s) > 0 and s.isdigit(), filtered_output.split(' '))))

  if (len(printed_numbers) != len(numbers)):
    return (False, 'The amount of printed numbers ({}) is not equal to the amount of numbers needed to be printed ({})'.format(len(printed_numbers), len(numbers)))

  for number in numbers:
    if number in printed_numbers:
      printed_numbers.remove(number)
    else:
      return (False, 'The printed numbers are not a permutation of {numbers}')

  return (len(printed_numbers) == 0, 'The printed numbers are not a permutation of {numbers}')


def test_compilable(file, msg, should_succeed=True):
  test_execution('./selfie -c grader/{}'.format(file), msg, success_criteria=lambda code, out: has_compiled(code, out, should_succeed=should_succeed))


def test_riscv_instruction(instruction, file):
  test_instruction_encoding(instruction, file)
  test_assembler_instruction_format(instruction, file)


def test_mipster_execution(file, result, msg):
  test_execution('./selfie -c grader/{} -m 128'.format(file), msg, success_criteria=result)


def test_hypster_execution(file, result, msg):
  test_execution('./selfie -c selfie.c -m 128 -c grader/{} -y 64'.format(file), msg, success_criteria=result)


def test_interleaved_output(command, interleaved_msg, number_of_interleaved, msg):
  test_execution(command, msg, success_criteria=lambda code, out: is_interleaved_output(code, out, interleaved_msg, number_of_interleaved))
 

def test_compile_warnings(file, msg, mandatory=False):
  test_execution('./selfie -c {}'.format(file), msg, success_criteria=has_no_compile_warnings, mandatory=mandatory)


def test_hex_literal():
  test_compilable('hex-integer-literal.c',
    'hex integer literal with all characters compiled')
  test_mipster_execution('hex-integer-literal.c', 1,
    'hex integer literal with all characters has the right value')
  test_compilable('hex-integer-literal-max.c',
    'maximum hex integer literal compiled')
  test_mipster_execution('hex-integer-literal-max.c', 1,
    'maximum hex integer literal has the right value')
  test_compilable('hex-integer-literal-min.c',
    'minimum hex integer literal compiled')
  test_mipster_execution('hex-integer-literal-min.c', 1,
    'minimum hex integer literal has the right value')


def test_bitwise_shift(stage):
  if stage >= 1:
    start_stage(1)

    for direction in ['right', 'left']:

      literal_file = 'bitwise-' + direction + '-shift-literals.c'
      variable_file = 'bitwise-' + direction + '-shift-variables.c'
      invalid_file = 'bitwise-' + direction + '-shift-invalid.c'

      test_compilable(literal_file,
        'bitwise-' + direction + '-shift operator with literals does compile')
      test_compilable(variable_file,
        'bitwise-' + direction + '-shift operator with variables does compile')
      test_compilable(invalid_file,
        'bitwise-' + direction + '-shift operator with invalid syntax does not compile', should_succeed=False)

  if stage >= 2:
    start_stage(2)

    for instruction in [SRL_INSTRUCTION, SLL_INSTRUCTION]:

      literal_file = instruction[0] + '-literals.c'
      variable_file = instruction[0] + '-variables.c'

      test_riscv_instruction(instruction, literal_file)
      test_riscv_instruction(instruction, variable_file)
      test_mipster_execution(literal_file, 2,
        'bitwise-' + direction + '-shift operator calculates the right result for literals when executed with MIPSTER')
      test_mipster_execution(variable_file, 2,
        'bitwise-' + direction + '-shift operator calculates the right result for variables when executed with MIPSTER')
    
    test_mipster_execution('bitwise-shift-precedence.c', 42,
      'bitwise shift operators respect the precedence of the C operators: <<, >>')



def test_bitwise_and_or_not():
  for instruction in [AND_INSTRUCTION, OR_INSTRUCTION, NOT_INSTRUCTION]:
    operation = instruction[0]

    literal_file = operation + '-literals.c'
    variable_file = operation + '-variables.c'
    invalid_file = operation + '-invalid.c'

    test_compilable(literal_file,
      operation + ' operator with literals does compile')
    test_compilable(variable_file,
      operation + ' operator with variables does compile')
    test_compilable(invalid_file,
      operation + ' operator with invalid syntax does not compile', should_succeed=False)
    test_mipster_execution(literal_file, 42,
      operation + ' operator calculates the right result for literals when executed with MIPSTER')
    test_mipster_execution(variable_file, 42,
      operation + ' operator calculates the right result for variables when executed with MIPSTER')
    test_riscv_instruction(instruction, literal_file)
    test_riscv_instruction(instruction, variable_file)

  test_mipster_execution('bitwise-and-or-not-precedence.c', 42,
    'bitwise and, or & not '  + ' operators respect the precedence of the C operators: &,|,~')
  test_mipster_execution('bitwise-and-or-not-other-precedence.c', 42,
    'bitwise and, or & not '  + ' operators respect the precedence of the C operators: +,-')



def test_for_loop():
  test_compilable('for-loop-invalid-missing-assignment.c', 
    'for loop with missing assignment do not compile', should_succeed=False)
  test_compilable('for-loop-single-statement.c',
    'for loop with one statement do compile')
  test_compilable('for-loop-multiple-statements.c',
    'for loop with multiple statements do compile')
  test_compilable('for-loop-nested.c', 
    'nested for loops do compile')
  test_mipster_execution('for-loop-single-statement.c', 3,
    'for loop with one statement are implement with the right semantics')
  test_mipster_execution('for-loop-multiple-statements.c', 3,
    'for loop with multiple statements are implemented with the right semantics')
  test_mipster_execution('for-loop-multiple-statements.c', 3,
    'for loop with multiple statements are implemented with the right semantics')
  test_mipster_execution('for-loop-nested.c', 9,
    'nested for loops are implemented with the right semantics')



def test_array(part):
  if part == 1:
    test_compilable('array-global-declaration.c', 
      'array declaration do compile')
    test_compilable('array-assignment.c',
      'assignments on arrays do compile')
    test_compilable('array-invalid-assignment.c',
      'invalid assignments to an array do not compile', should_succeed=False)
    test_compilable('array-call-by-reference.c',
      'arrays in the function signature do compile')
    test_mipster_execution('array-assignment.c', 10,
      'arrays assignments are implemented with the right semantics')
    test_mipster_execution('array-call-by-reference.c', 4,
      'array assignments in functions are implemented with the right semantics')

  if part == 2:
    test_compilable('array-multidimensional.c',
      'multidimensional array declarations do compile')
    test_mipster_execution('array-multidimensional.c', 4,
      'multidimensional arrays assignments are implemented with the right semantics')
    test_compilable('array-access-order.c',
      'access to start-address of multidimensional is possible')
    test_mipster_execution('array-access-order.c', 0,
      'access to multidimensional arrays is implemented in row-major order')



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
    test_execution('./selfie -c selfie.c -s selfie1.s -a selfie1.s -m 128 -a selfie1.s -s selfie2.s ',
      'selfie can assemble its own binary file')
    test_execution('diff -q selfie1.s selfie2.s', 'both assembly files are exactly the same')


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



def test_treiber_stack():
  test_riscv_instruction(LR_INSTRUCTION, 'load-reserved.c')
  test_riscv_instruction(SC_INSTRUCTION, 'store-conditional.c')
  test_execution('./selfie -c treiber-stack.c grader/treiber-stack-push.c -m 128',
    'all pushed elements are actually in the treiber-stack',
    success_criteria=lambda code, out: is_permutation_of(code, out, [0, 1, 2, 3, 4, 5, 6, 7]))
  test_execution('./selfie -c treiber-stack.c grader/treiber-stack-pop.c -m 128',
    'all treiber-stack elements can be popped ',
    success_criteria=lambda code, out: is_permutation_of(code, out, [0, 1, 2, 3, 4, 5, 6, 7]))


def test_base(mandatory=True):
  test_execution('make selfie', 'cc compiles selfie.c', mandatory=mandatory)
  test_compile_warnings('selfie.c', 'self-compilation does not lead to warnings or syntax errors', mandatory=mandatory)


def start_stage(stage):
  global number_of_positive_tests_passed, number_of_positive_tests_failed
  global number_of_negative_tests_passed, number_of_negative_tests_failed

  print('==== STAGE {} ===='.format(stage))

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
      name = ' of stage {} '.format(stage + 1)
    else:
      name = ' '

    number_of_tests =  number_of_positive_tests_passed[stage] + number_of_positive_tests_failed[stage]
    number_of_tests += number_of_negative_tests_passed[stage] + number_of_negative_tests_failed[stage]

    number_of_tests_passed = number_of_positive_tests_passed[stage] + number_of_negative_tests_passed[stage]

    if number_of_tests == 0:
      return

    passed = number_of_tests_passed / float(number_of_tests)

    print('tests{}passed: {:02.1f}%'.format(name, passed * 100))

    if number_of_positive_tests_passed[stage] == 0:
      print('warning: you have not passed at least one positive test')
      grade_is_negative = True


  number_of_tests_passed = sum(number_of_positive_tests_passed) + sum(number_of_negative_tests_passed)

  number_of_tests =  sum(number_of_positive_tests_passed) + sum(number_of_positive_tests_failed)
  number_of_tests += sum(number_of_negative_tests_passed) + sum(number_of_negative_tests_failed)

  passed = number_of_tests_passed / float(number_of_tests)

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

  if failed_mandatory_test:
    print('warning: you have failed a mandatory test')
    grade = 5

  print('your grade is: \033[{}m\033[1m'.format(color), end='')
  print_loud('{}'.format(grade), end='')
  print('\033[0m')

  reset_assignment_results()


def enter_quiet_mode():
  sys.stdout = DummyWriter()


def enable_bulk_grader(file):
  global bulk_grade_mode, file_with_commit_links

  if not os.path.exists(file):
    print('the file "' + file + '" does not exist')
    exit(1)

  if not os.path.isfile(file):
    print('the path "' + file + '" is not a file')
    exit(1)
  
  bulk_grade_mode = True
  file_with_commit_links = os.path.abspath(file)


def set_bulk_grade_directory(directory):
  global bulk_grade_directory

  bulk_grade_directory = os.path.abspath(directory)



def print_loud(msg, end='\n'):
  quiet_writer = sys.stdout
  sys.stdout = sys.__stdout__

  print(msg, end=end)

  sys.stdout = quiet_writer


def print_usage():
  print('usage: python3 grader/self.py { option } { test }\n')

  print('options:')

  width = max(map(lambda x: 0 if x[2] is None else len(x[2]), defined_options))

  for option in defined_options:
    print('  {0} {1:{width}}  {2}'.format(option[0], option[2] if option[2] is not None else '', option[3], width=width))

  print('\ntests: ')

  for test in defined_tests:
    print('  {}'.format(test[0]))


defined_tests = [
    ('base', lambda: test_base(mandatory=False)),
    ('hex-literal', test_hex_literal),
    ('bitwise-shift-1', lambda: test_bitwise_shift(1)),
    ('bitwise-shift-2', lambda: test_bitwise_shift(2)),
    ('bitwise-and-or-not', test_bitwise_and_or_not),
    ('for-loop', test_for_loop),
    ('array-1', lambda: test_array(1)),
    ('array-2', lambda: test_array(2)),
    ('struct', test_structs),
    ('assembler-1', lambda: test_assembler(1)),
    ('assembler-2', lambda: test_assembler(2)),
    ('concurrent-machines', test_concurrent_machines),
    ('fork-wait', test_fork_and_wait),
    ('lock', test_lock),
    ('thread', test_thread),
    ('treiber-stack', test_treiber_stack)
  ]


defined_options = [
    ('-q', enter_quiet_mode, None, 'only the grade is printed'),
    ('-h', print_usage, None, 'this help text'),
    ('-b', enable_bulk_grader, '<file>', 'bulk grade assignments defined by a file with github commit links'),
    ('-d', set_bulk_grade_directory, '<directory>', 'path where all bulk graded repositories should be saved')
  ]

def parse_options(args):
  i = 0

  options = list(map(lambda x: x[0], defined_options))

  while len(args) > i and args[i][0] == '-':
    if args[i] in options:
      index = options.index(args[i])

      if defined_options[index][2] is None:
        defined_options[index][1]()
      else:
        i += 1

        if len(args) > i:
          defined_options[index][1](args[i])
        else:
          print('option flag "' + defined_options[index][0] + '" needs an argument ' + defined_options[index][2])
          exit(1)
    else:
      print('unknown option: ' + args[i])
      exit(1)
    
    i += 1

  return args[i:]


def parse_tests(args):
  tests = list(map(lambda x: x[0], defined_tests))

  to_execute = []

  for arg in args:
    if arg in tests:
      to_execute.append(defined_tests[tests.index(arg)])
    else:
      print('unknown test: {}'.format(arg))
      exit(1)
  
  return to_execute


def validate_options_for(tests):
  if bulk_grade_mode and len(tests) == 0:
    print('please specify a test used for bulk grading')
  else:
    return

  exit(1)


def do_bulk_grading(tests):
  enter_quiet_mode()

  if not os.path.exists(bulk_grade_directory):
    os.mkdir(bulk_grade_directory)

  working_directory = os.getcwd()

  os.chdir(bulk_grade_directory)
  
  with open(file_with_commit_links, 'rt') as file:
    for line in file.readlines():
      matcher = re.match('^https://github.com/([^/]+)/([^/]+)/commit/([0-9a-f]+)$', line)

      if matcher is None:
        print('the link "' + line + '" is not a valid github commit link')
        exit(1)

      user   = matcher.group(1)
      repo   = matcher.group(2)
      commit = matcher.group(3)

      clone_dir = os.path.join(bulk_grade_directory, '{}/{}'.format(user, repo))

      if not os.path.exists(clone_dir):
        os.system('git clone -q https://github.com/{}/{} {}/{}'.format(user, repo, user, repo))

      os.chdir(clone_dir)
      
      # remove all changes in local repository
      os.system('git reset --hard -q')

      # fetch updates from github repository
      os.system('git fetch -q')

      # change the local repository state using the commit ID
      os.system('git checkout -q {}'.format(commit))

      print_loud('{}/{}: '.format(user, repo), end='')
      check_assignments(tests)
      print_loud('')

      os.chdir(bulk_grade_directory)

  os.chdir(working_directory)

  if bulk_grade_directory is DEFAULT_BULK_GRADE_DIRECTORY:
    os.system('rm -rf {}'.format(bulk_grade_directory))


def check_assignments(assignments):
  if len(assignments) > 0:
    if defined_tests[0] not in assignments:
      print('executing mandatory test \'{}\''.format(defined_tests[0][0]))
      test_base(mandatory=True)

  for test in assignments:
    print('executing test \'{}\''.format(test[0]))
    test[1]()

  if len(assignments) > 0:
    grade()


def main(argv):
  global home_path

  if len(argv) <= 1:
    print_usage()
    exit()

  sys.setrecursionlimit(5000)

  home_path = os.path.abspath(os.getcwd())

  args = parse_options(argv[1:])

  tests = parse_tests(args)

  validate_options_for(tests)

  if bulk_grade_mode:
    do_bulk_grading(tests)
  else:
    check_assignments(tests)


if __name__ == "__main__":
  main(sys.argv)

