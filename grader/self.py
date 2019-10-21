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

from lib.cli import process_arguments
from lib.output_processing import *
from lib.runner import (test_assembler_instruction_format, test_compilable,
                        test_compile_warnings, test_execution,
                        test_hypster_execution, test_interleaved_output,
                        test_mipster_execution, test_riscv_instruction)
from lib.system import (AND_INSTRUCTION, LR_INSTRUCTION, NOT_INSTRUCTION,
                        OR_INSTRUCTION, SC_INSTRUCTION, SLL_INSTRUCTION,
                        SRL_INSTRUCTION)


def test_self_compilation(mandatory=False):
    test_execution('make clean selfie',
                   'cc compiles selfie.c', mandatory=mandatory)
    test_compile_warnings(
        'selfie.c', 'self-compilation does not lead to warnings or syntax errors', mandatory=mandatory)


def test_print_name():
    test_execution('./selfie -c selfie.c -m 128',
                   'selfie prints first and second name',
                   success_criteria=lambda code, out: contains_name(out))


def test_hex_literal():
    test_compilable('all-digit-characters.c',
                    'hex integer literal with all characters compiled')
    test_mipster_execution('all-digit-characters.c', 42,
                           'hex integer literal with all characters has the right value')
    test_compilable('max-value.c',
                    'maximum hex integer literal compiled')
    test_mipster_execution('max-value.c', 42,
                           'maximum hex integer literal has the right value')
    test_compilable('min-value.c',
                    'minimum hex integer literal compiled')
    test_mipster_execution('min-value.c', 42,
                           'minimum hex integer literal has the right value')


def test_bitwise_shift_compilation():
    for direction in ['right', 'left']:

        literal_file = direction + '-shift-with-literals.c'
        variable_file = direction + '-shift-with-variables.c'
        invalid_file = 'invalid-' + direction + '-shift.c'

        test_compilable(literal_file,
                        'bitwise-' + direction + '-shift operator with literals does compile')
        test_compilable(variable_file,
                        'bitwise-' + direction + '-shift operator with variables does compile')
        test_compilable(invalid_file,
                        'bitwise-' + direction + '-shift operator with invalid syntax does not compile', should_succeed=False)


def test_bitwise_shift_execution():
    for direction, instruction in [('right', SRL_INSTRUCTION), ('left', SLL_INSTRUCTION)]:

        literal_file = instruction[0] + '-with-literals.c'
        variable_file = instruction[0] + '-with-variables.c'

        test_riscv_instruction(instruction, literal_file)
        test_riscv_instruction(instruction, variable_file)
        test_mipster_execution(literal_file, 42,
                               'bitwise-' + direction + '-shift operator calculates the right result for literals when executed with MIPSTER')
        test_mipster_execution(variable_file, 42,
                               'bitwise-' + direction + '-shift operator calculates the right result for variables when executed with MIPSTER')

    test_mipster_execution('precedence.c', 42,
                           'bitwise shift operators respect the precedence of the C operators: <<, >>')


def test_bitwise_and_or_not():
    for instruction in [AND_INSTRUCTION, OR_INSTRUCTION, NOT_INSTRUCTION]:
        operation = instruction[0]

        literal_file = operation + '-with-literals.c'
        variable_file = operation + '-with-variables.c'
        invalid_file = 'invalid-' + operation + '.c'

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

    test_mipster_execution('precedence.c', 42,
                           'bitwise and, or & not ' + ' operators respect the precedence of the C operators: &,|,~')
    test_mipster_execution('precedence2.c', 42,
                           'bitwise and, or & not ' + ' operators respect the precedence of the C operators: +,-')


def test_for_loop():
    test_compilable('missing-assignment.c',
                    'for loop with missing assignment do not compile', should_succeed=False)
    test_compilable('single-statement.c',
                    'for loop with one statement do compile')
    test_compilable('multiple-statements.c',
                    'for loop with multiple statements do compile')
    test_compilable('nested.c',
                    'nested for loops do compile')
    test_mipster_execution('single-statement.c', 42,
                           'for loop with one statement are implement with the right semantics')
    test_mipster_execution('multiple-statements.c', 42,
                           'for loop with multiple statements are implemented with the right semantics')
    test_mipster_execution('nested.c', 42,
                           'nested for loops are implemented with the right semantics')


def test_array():
    test_compilable('global-declaration.c',
                    'array declaration do compile')
    test_compilable('assignment.c',
                    'assignments on arrays do compile')
    test_compilable('invalid-assignment.c',
                    'invalid assignments to an array do not compile', should_succeed=False)
    test_compilable('call-by-reference.c',
                    'arrays in the function signature do compile')
    test_mipster_execution('assignment.c', 42,
                           'arrays assignments are implemented with the right semantics')
    test_mipster_execution('call-by-reference.c', 42,
                           'array assignments in functions are implemented with the right semantics')


def test_multidimensional_array():
    test_compilable('multidimensional.c',
                    'multidimensional array declarations do compile')
    test_mipster_execution('multidimensional.c', 42,
                           'multidimensional arrays assignments are implemented with the right semantics')
    test_compilable('access-order.c',
                    'access to start-address of multidimensional is possible')
    test_mipster_execution('access-order.c', 0,
                           'access to multidimensional arrays is implemented in row-major order')


def test_struct_declaration():
    test_compilable('declaration.c',
                    'empty struct declarations compiled')
    test_compilable('definition.c',
                    'struct definition with global and local scope compiled')
    test_compilable('member-declaration.c',
                    'struct declaration with trivial members compiled')
    test_compilable('nested-declaration.c',
                    'struct declaration with struct members compiled')


def test_struct_execution():
    test_compilable('initialization.c',
                    'empty struct with initialization compiled')
    test_compilable('member-initialization.c',
                    'initialization of trivial struct members compiled')
    test_mipster_execution('member-initialization.c', 42,
                           'read and write operations of trivial struct member works when executed with MIPSTER')
    test_compilable('nested-initialization.c',
                    'struct initialization with struct members compiled')
    test_mipster_execution('nested-initialization.c', 42,
                           'read and write operations of nested struct member works when executed with MIPSTER')
    test_compilable('as-parameter.c',
                    'struct as function parameter compiled')
    test_mipster_execution('as-parameter.c', 42,
                           'read and write operations of structs as parameter work when executed with MIPSTER')


def test_assembler_parser():
    test_execution('./selfie -c selfie.c -s selfie.s -a selfie.s',
                   'selfie can parse its own implementation in assembly')
    test_execution('./selfie -a grader/missing-address.s',
                   'assembly file with a missing address is not parseable', success_criteria=False)
    test_execution('./selfie -a grader/missing-instruction.s',
                   'assembly file with a missing instruction is not parseable', success_criteria=False)
    test_execution('./selfie -a grader/missing-literal.s',
                   'assembly file with a missing literal is not parseable', success_criteria=False)


def test_self_assemblation():
    test_execution('./selfie -c selfie.c -s selfie1.s -a selfie1.s -m 128 -a selfie1.s -s selfie2.s ',
                   'selfie can assemble its own binary file')
    test_execution('diff -q selfie1.s selfie2.s',
                   'both assembly files are exactly the same')


def test_concurrent_machines():
    test_interleaved_output('./selfie -c grader/hello-world.c -x 10', 'Hello World!    ', 10,
                            '10 Mipster machines are running concurrently')
    test_interleaved_output('./selfie -c selfie.c -m 128 -c grader/hello-world.c -z 10', 'Hello World!    ', 10,
                            '10 Hypster machines are running concurrently')


def test_fork_and_wait():
    test_execution('./selfie -c grader/syscalls.c -m 128',
                   'fork creates a child process, where the parent can wait for the child process with MIPSTER', success_criteria=70)
    test_execution('./selfie -c selfie.c -m 128 -c grader/syscalls.c -y 64',
                   'fork creates a child process, where the parent can wait for the child process with HYPSTER', success_criteria=70)


def test_lock():
    test_execution('./selfie -c grader/print-without-lock.c -m 128',
                   '16 processes are running concurrently on MIPSTER',
                   success_criteria=lambda code, out: is_interleaved_output(out, 'Hello World!    ', 8))
    test_execution('./selfie -c selfie.c -m 128 -c grader/print-without-lock.c -y 10',
                   '16 processes are running concurrently on HYPSTER',
                   success_criteria=lambda code, out: is_interleaved_output(out, 'Hello World!    ', 8))
    test_execution('./selfie -c grader/print-with-lock.c -m 128',
                   '16 processes are printing in sequential order with the use of locks on MIPSTER',
                   success_criteria='Hello World!    ' * 8)
    test_execution('./selfie -c selfie.c -m 128 -c grader/print-with-lock.c -y 10',
                   '16 processes are printing in sequential order with the use of locks on HYPSTER',
                   success_criteria='Hello World!    ' * 8)


def test_thread():
    test_execution('./selfie -c grader/syscalls.c -m 128',
                   'creates a thread, where the parent can join the thread with MIPSTER', success_criteria=70)
    test_execution('./selfie -c selfie.c -m 128 -c grader/syscalls.c -y 64',
                   'creates a thread, where the parent can join the thread with HYPSTER', success_criteria=70)
    test_mipster_execution('grader/shared-data.c', 42,
                           'data section is shared for threads on MIPSTER')
    test_hypster_execution('grader/shared-data.c', 42,
                           'data section is shared for threads on HYPSTER')
    test_mipster_execution('grader/shared-heap.c', 42,
                           'heap data is shared for threads on MIPSTER')
    test_hypster_execution('grader/shared-heap.c', 42,
                           'heap data is shared for threads on HYPSTER')


def test_treiber_stack():
    test_riscv_instruction(LR_INSTRUCTION, 'load-reserved.c')
    test_riscv_instruction(SC_INSTRUCTION, 'store-conditional.c')
    test_execution('./selfie -c treiber-stack.c grader/stack-push.c -m 128',
                   'all pushed elements are actually in the treiber-stack',
                   success_criteria=lambda code, out: is_permutation_of(out, [0, 1, 2, 3, 4, 5, 6, 7]))
    test_execution('./selfie -c treiber-stack.c grader/stack-pop.c -m 128',
                   'all treiber-stack elements can be popped ',
                   success_criteria=lambda code, out: is_permutation_of(out, [0, 1, 2, 3, 4, 5, 6, 7]))


def name(assignment):
    return assignment[0]


def category(assignment):
    return assignment[1]


def directory(assignment):
    return assignment[2]


def test(assignment):
    return assignment[3]


assignments = [
    ('self-compile', 'General', '', test_self_compilation),
    ('print-name', 'General', '', test_print_name),
    ('hex-literal', 'Compiler', 'hex-literal', test_hex_literal),
    ('bitwise-shift-compilation', 'Compiler',
     'bitwise-shift', test_bitwise_shift_compilation),
    ('bitwise-shift-execution', 'Compiler',
     'bitwise-shift', test_bitwise_shift_execution),
    ('bitwise-and-or-not', 'Compiler', 'bitwise-logic', test_bitwise_and_or_not),
    ('for-loop', 'Compiler', 'for-loop', test_for_loop),
    ('array', 'Compiler', 'array', test_array),
    ('array-multidimensional', 'Compiler', 'array', test_multidimensional_array),
    ('struct-declaration', 'Compiler', 'struct', test_struct_declaration),
    ('struct-execution', 'Compiler', 'struct', test_struct_execution),
    ('assembler-parser', 'OS', 'assembler', test_assembler_parser),
    ('self-assembler', 'OS', 'assembler', test_self_assemblation),
    ('concurrent-machines', 'OS', 'concurrent-machines', test_concurrent_machines),
    ('fork-wait', 'OS', 'fork-wait', test_fork_and_wait),
    ('lock', 'OS', 'lock', test_lock),
    ('thread', 'OS', 'thread', test_thread),
    ('treiber-stack', 'OS', 'treiber-stack', test_treiber_stack)
]


def main(args):
    process_arguments(args, assignments)


if __name__ == "__main__":
    try:
        main(sys.argv)
    except KeyboardInterrupt:
        print('\naborting...')
