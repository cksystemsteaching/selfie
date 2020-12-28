#!/usr/bin/env python3
"""
Copyright (c) 2015-2020, the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is governed
by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the Department of
Computer Sciences of the University of Salzburg in Austria. For further
information and code please refer to:

http://selfie.cs.uni-salzburg.at

This is the automatic grader of the selfie project.
Students may use the grader for self-grading their solutions.
"""

import sys
from typing import Callable, Optional, List, Set, Tuple, Any
from lib.functional import flatmap
from lib.cli import process_arguments
from lib.model import Assignment, Check
from lib.output_processing import is_interleaved_output, is_permutation_of, contains_name
from lib.checks import (check_assembler_instruction_format, check_compilable,
                        check_compile_warnings, check_execution,
                        check_hypster_execution, check_interleaved_output,
                        check_mipster_execution, check_riscv_instruction)
from lib.system import (AND_INSTRUCTION, LR_INSTRUCTION, NOT_INSTRUCTION,
                        OR_INSTRUCTION, SC_INSTRUCTION, SLL_INSTRUCTION,
                        SRL_INSTRUCTION)

REPO_BLOB_BASE_URI = 'https://github.com/cksystemsteaching/selfie/blob/master/'


def check_self_compilation(mandatory=False) -> List[Check]:
    return check_execution('make self', 'selfie compiles selfie.c', mandatory=mandatory) + \
        check_compile_warnings(
            'selfie.c', 'self-compilation does not lead to warnings or syntax errors', mandatory=mandatory)


def check_print_your_name() -> List[Check]:
    return check_execution('./selfie -c selfie.c -m 1',
                           'selfie prints first and second name',
                           success_criteria=lambda code, out: contains_name(out))


def check_hex_literal() -> List[Check]:
    return check_compilable('all-digit-characters.c',
                            'hex integer literal with all characters compiled') + \
        check_mipster_execution('all-digit-characters.c', 42,
                                'hex integer literal with all characters has the right value') + \
        check_compilable('max-value.c',
                         'maximum hex integer literal compiled') + \
        check_mipster_execution('max-value.c', 42,
                                'maximum hex integer literal has the right value') + \
        check_compilable('min-value.c',
                         'minimum hex integer literal compiled') + \
        check_mipster_execution('min-value.c', 42,
                                'minimum hex integer literal has the right value')


def check_bitwise_shift_compilation() -> List[Check]:
    def check_direction(direction: str) -> List[Check]:
        literal_file = direction + '-shift-with-literals.c'
        variable_file = direction + '-shift-with-variables.c'
        invalid_file = 'invalid-' + direction + '-shift.c'

        return check_compilable(literal_file, 'bitwise-' + direction +
                                '-shift operator with literals does compile') + \
            check_compilable(variable_file,
                             'bitwise-' + direction + '-shift operator with variables does compile') + \
            check_compilable(invalid_file,
                             'bitwise-' + direction + '-shift operator with invalid syntax does not compile', should_succeed=False)

    return list(flatmap(check_direction, ['right', 'left']))


def check_bitwise_shift_execution() -> List[Check]:
    def check_instruction(direction: str, instruction: Tuple[str, Any]) -> List[Check]:
        literal_file = instruction[0] + '-with-literals.c'
        variable_file = instruction[0] + '-with-variables.c'

        return check_riscv_instruction(instruction, literal_file) + \
            check_riscv_instruction(instruction, variable_file) + \
            check_mipster_execution(literal_file, 42,
                                    'bitwise-' + direction + '-shift operator calculates the right result for literals when executed with MIPSTER') + \
            check_mipster_execution(variable_file, 42,
                                    'bitwise-' + direction + '-shift operator calculates the right result for variables when executed with MIPSTER')

    instructions = [('right', SRL_INSTRUCTION), ('left', SLL_INSTRUCTION)]

    return list(flatmap(lambda i: check_instruction(i[0], i[1]), instructions)) + \
        check_mipster_execution('precedence.c', 42,
                                'bitwise shift operators respect the precedence of the C operators: <<, >>')


def check_bitwise_and_or_not() -> List[Check]:
    def check_instruction(instruction) -> List[Check]:
        operation = instruction[0]

        literal_file = operation + '-with-literals.c'
        variable_file = operation + '-with-variables.c'
        invalid_file = 'invalid-' + operation + '.c'

        return check_compilable(literal_file,
                                operation + ' operator with literals does compile') + \
            check_compilable(variable_file,
                             operation + ' operator with variables does compile') + \
            check_compilable(invalid_file,
                             operation + ' operator with invalid syntax does not compile', should_succeed=False) + \
            check_mipster_execution(literal_file, 42,
                                    operation + ' operator calculates the right result for literals when executed with MIPSTER') + \
            check_mipster_execution(variable_file, 42,
                                    operation + ' operator calculates the right result for variables when executed with MIPSTER') + \
            check_riscv_instruction(instruction, literal_file) + \
            check_riscv_instruction(instruction, variable_file)

    return list(flatmap(check_instruction, [AND_INSTRUCTION, OR_INSTRUCTION, NOT_INSTRUCTION])) + \
        check_mipster_execution('precedence.c', 42,
                                'bitwise and, or & not ' + ' operators respect the precedence of the C operators: &,|,~') + \
        check_mipster_execution('precedence2.c', 42,
                                'bitwise and, or & not ' + ' operators respect the precedence of the C operators: +,-')


def check_for_loop() -> List[Check]:
    return check_compilable('missing-assignment.c',
                            'for loop with missing assignment do not compile', should_succeed=False) + \
        check_compilable('single-statement.c',
                         'for loop with one statement do compile') + \
        check_compilable('multiple-statements.c',
                         'for loop with multiple statements do compile') + \
        check_compilable('nested.c',
                         'nested for loops do compile') + \
        check_mipster_execution('single-statement.c', 42,
                                'for loop with one statement are implement with the right semantics') + \
        check_mipster_execution('multiple-statements.c', 42,
                                'for loop with multiple statements are implemented with the right semantics') + \
        check_mipster_execution('nested.c', 42,
                                'nested for loops are implemented with the right semantics')


def check_array() -> List[Check]:
    return check_compilable('global-declaration.c',
                            'array declaration do compile') + \
        check_compilable('assignment.c',
                         'assignments on arrays do compile') + \
        check_compilable('invalid-assignment.c',
                         'invalid assignments to an array do not compile', should_succeed=False) + \
        check_compilable('call-by-reference.c',
                         'arrays in the function signature do compile') + \
        check_mipster_execution('assignment.c', 42,
                                'arrays assignments are implemented with the right semantics') + \
        check_mipster_execution('call-by-reference.c', 42,
                                'array assignments in functions are implemented with the right semantics')


def check_multidimensional_array() -> List[Check]:
    return check_compilable('multidimensional.c',
                            'multidimensional array declarations do compile') + \
        check_mipster_execution('multidimensional.c', 42,
                                'multidimensional arrays assignments are implemented with the right semantics') + \
        check_compilable('access-order.c',
                         'access to start-address of multidimensional is possible') + \
        check_mipster_execution('access-order.c', 0,
                                'access to multidimensional arrays is implemented in row-major order')


def check_struct_declaration() -> List[Check]:
    return check_compilable('declaration.c',
                            'empty struct declarations compiled') + \
        check_compilable('definition.c',
                         'struct definition with global and local scope compiled') + \
        check_compilable('member-declaration.c',
                         'struct declaration with trivial members compiled') + \
        check_compilable('nested-declaration.c',
                         'struct declaration with struct members compiled')


def check_struct_execution() -> List[Check]:
    return check_compilable('initialization.c',
                            'empty struct with initialization compiled') + \
        check_compilable('member-initialization.c',
                         'initialization of trivial struct members compiled') + \
        check_mipster_execution('member-initialization.c', 42,
                                'read and write operations of trivial struct member works when executed with MIPSTER') + \
        check_compilable('nested-initialization.c',
                         'struct initialization with struct members compiled') + \
        check_mipster_execution('nested-initialization.c', 42,
                                'read and write operations of nested struct member works when executed with MIPSTER') + \
        check_compilable('as-parameter.c',
                         'struct as function parameter compiled') + \
        check_mipster_execution('as-parameter.c', 42,
                                'read and write operations of structs as parameter work when executed with MIPSTER')


def check_assembler_parser() -> List[Check]:
    return check_execution('./selfie -c selfie.c -s selfie.s -a selfie.s',
                           'selfie can parse its own implementation in assembly') + \
        check_execution('./selfie -a <assignment>valid-registers-add.s',
                        'assembly file with valid register access for RISC-U add instruction') + \
        check_execution('./selfie -a <assignment>valid-registers-addi.s',
                        'assembly file with valid register access for RISC-U addi instruction') + \
        check_execution('./selfie -a <assignment>valid-hex.s',
                        'assembly file with valid hex numbers') + \
        check_execution('./selfie -a <assignment>invalid-argument-add.s',
                        'assembly file with a invalid argument is not parseable', should_succeed=False) + \
        check_execution('./selfie -a <assignment>missing-instruction.s',
                        'assembly file with a missing instruction is not parseable', should_succeed=False) + \
        check_execution('./selfie -a <assignment>missing-literal.s',
                        'assembly file with a missing literal is not parseable', should_succeed=False)


def check_self_assemblation() -> List[Check]:
    return check_execution('./selfie -c selfie.c -s selfie1.s',
                           'preparation: selfie can compile and assemble its own source', mandatory=True) + \
        check_execution('./selfie -a selfie1.s -o selfie1.m -m 128 -c selfie.c -o selfie2.m',
                        'selfie can re-assemble its own binary file', mandatory=True) + \
        check_execution('diff -q selfie1.m selfie2.m',
                        'both binary files are exactly the same', mandatory=True)


def check_processes() -> List[Check]:
    return check_interleaved_output('./selfie -c <assignment>hello-world.c -x 10', 'Hello World!    ', 10,
                                    '10 Mipster processes are running concurrently') + \
        check_interleaved_output('./selfie -c selfie.c -m 128 -c <assignment>hello-world.c -z 10', 'Hello World!    ', 10,
                                 '10 Hypster processes are running concurrently')


def check_fork_and_wait() -> List[Check]:
    return check_compilable('parallel-print.c', 'fork and wait compiled') + \
        check_mipster_execution('parallel-print.c',
                                lambda code, out: is_permutation_of(
                                    out, [0, 1, 2, 3, 4, 5, 6, 7]),
                                'fork creates a child process, where the parent can wait for the child process with MIPSTER') + \
        check_hypster_execution('parallel-print.c',
                                lambda code, out: is_permutation_of(
                                    out, [0, 1, 2, 3, 4, 5, 6, 7]),
                                'fork creates a child process, where the parent can wait for the child process with HYPSTER')


def check_fork_wait_exit() -> List[Check]:
    return check_mipster_execution('sum-exit-code.c', 28,
                                   'exit code is returned as status parameter from wait with MIPSTER') + \
        check_hypster_execution('sum-exit-code.c', 28,
                                'exit code is returned as status parameter from wait with HYPSTER') + \
        check_mipster_execution('unmapped-page-wait.c', 42,
                                'wait system call maps page to unmapped virtual address') + \
        check_mipster_execution('invalid-address.c', 42,
                                'wait system call correctly handles invalid addresses') + \
        check_mipster_execution('null-ptr.c', 42,
                                'wait system call returns PID when NULL is passed');


def check_lock() -> List[Check]:
    return check_execution('./selfie -c <assignment>print-without-lock.c -m 128',
                           '16 processes are running concurrently on MIPSTER',
                           success_criteria=lambda code, out: is_interleaved_output(out, 'Hello World!    ', 8)) + \
        check_execution('./selfie -c selfie.c -m 128 -c <assignment>print-without-lock.c -y 10',
                        '16 processes are running concurrently on HYPSTER',
                        success_criteria=lambda code, out: is_interleaved_output(out, 'Hello World!    ', 8)) + \
        check_execution('./selfie -c <assignment>print-with-lock.c -m 128',
                        '16 processes are printing in sequential order with the use of locks on MIPSTER',
                        success_criteria='Hello World!    ' * 8) + \
        check_execution('./selfie -c selfie.c -m 128 -c <assignment>print-with-lock.c -y 10',
                        '16 processes are printing in sequential order with the use of locks on HYPSTER',
                        success_criteria='Hello World!    ' * 8) + \
        check_execution('./selfie -c <assignment>release-after-exit.c -m 128',
                        'Lock is granted to a process after a terminated process did not release its lock',
                        success_criteria='Hello child!    Hello parent!   ', timeout=5)


def check_threads() -> List[Check]:
    return check_execution('./selfie -c <assignment>syscalls.c -m 128',
                           'creates a thread, where the parent can join the thread with MIPSTER', success_criteria=70) + \
        check_execution('./selfie -c selfie.c -m 128 -c <assignment>syscalls.c -y 64',
                        'creates a thread, where the parent can join the thread with HYPSTER', success_criteria=70) + \
        check_mipster_execution('shared-data.c', 42,
                                'data section is shared for threads on MIPSTER') + \
        check_hypster_execution('shared-data.c', 42,
                                'data section is shared for threads on HYPSTER') + \
        check_mipster_execution('shared-heap.c', 42,
                                'heap data is shared for threads on MIPSTER') + \
        check_hypster_execution('shared-heap.c', 42,
                                'heap data is shared for threads on HYPSTER')


def check_treiber_stack() -> List[Check]:
    return check_riscv_instruction(LR_INSTRUCTION, 'load-reserved.c') + \
        check_riscv_instruction(SC_INSTRUCTION, 'store-conditional.c') + \
        check_execution('./selfie -c treiber-stack.c <assignment>stack-push.c -m 128',
                        'all pushed elements are actually in the treiber-stack',
                        success_criteria=lambda code, out: is_permutation_of(out, [0, 1, 2, 3, 4, 5, 6, 7])) + \
        check_execution('./selfie -c treiber-stack.c <assignment>stack-pop.c -m 128',
                        'all treiber-stack elements can be popped ',
                        success_criteria=lambda code, out: is_permutation_of(out, [0, 1, 2, 3, 4, 5, 6, 7]))


baseline_assignment = Assignment(
    'self-compile', 'General', '', '', check_self_compilation)

assignments: Set[Assignment] = {
    baseline_assignment,
    Assignment('print-your-name', 'General', '',
               REPO_BLOB_BASE_URI + 'grader/compiler-assignments.md#assignment-print-your-name',
               check_print_your_name),
    Assignment('hex-literal', 'Compiler', 'hex-literal',
               REPO_BLOB_BASE_URI + 'grader/compiler-assignments.md#assignment-hex-literal',
               check_hex_literal),
    Assignment('bitwise-shift-compilation', 'Compiler', 'bitwise-shift',
               REPO_BLOB_BASE_URI + 'grader/compiler-assignments.md#assignment-bitwise-shift-compilation',
               check_bitwise_shift_compilation),
    Assignment('bitwise-shift-execution', 'Compiler', 'bitwise-shift',
               REPO_BLOB_BASE_URI + 'grader/compiler-assignments.md#assignment-bitwise-shift-execution',
               check_bitwise_shift_execution),
    Assignment('bitwise-and-or-not', 'Compiler', 'bitwise-logic',
               REPO_BLOB_BASE_URI + 'grader/compiler-assignments.md#assignment-bitwise-and-or-not',
               check_bitwise_and_or_not),
    Assignment('for-loop', 'Compiler', 'for-loop',
               REPO_BLOB_BASE_URI + 'grader/compiler-assignments.md#assignment-for-loop',
               check_for_loop),
    Assignment('array', 'Compiler', 'array',
               REPO_BLOB_BASE_URI + 'grader/compiler-assignments.md#assignment-array',
               check_array),
    Assignment('array-multidimensional', 'Compiler', 'array',
               REPO_BLOB_BASE_URI + 'grader/compiler-assignments.md#assignment-array-multidimensional',
               check_multidimensional_array),
    Assignment('struct-declaration', 'Compiler', 'struct',
               REPO_BLOB_BASE_URI + 'grader/compiler-assignments.md#assignment-struct-declaration',
               check_struct_declaration),
    Assignment('struct-execution', 'Compiler', 'struct',
               REPO_BLOB_BASE_URI + 'grader/compiler-assignments.md#assignment-struct-execution',
               check_struct_execution),
    Assignment('assembler-parser', 'Systems', 'assembler',
               REPO_BLOB_BASE_URI + 'grader/systems-assignments.md#assignment-assembler-parser',
               check_assembler_parser),
    Assignment('self-assembler', 'Systems', 'assembler',
               REPO_BLOB_BASE_URI + 'grader/systems-assignments.md#assignment-self-assembler',
               check_self_assemblation),
    Assignment('processes', 'Systems', 'processes',
               REPO_BLOB_BASE_URI + 'grader/systems-assignments.md#assignment-processes',
               check_processes),
    Assignment('fork-wait', 'Systems', 'fork-wait',
               REPO_BLOB_BASE_URI + 'grader/systems-assignments.md#assignment-fork-wait',
               check_fork_and_wait),
    Assignment('fork-wait-exit', 'Systems', 'fork-wait',
               REPO_BLOB_BASE_URI + 'grader/systems-assignments.md#assignment-fork-wait-exit',
               check_fork_wait_exit),
    Assignment('lock', 'Systems', 'lock',
               REPO_BLOB_BASE_URI + 'grader/systems-assignments.md#assignment-lock',
               check_lock),
    Assignment('threads', 'Systems', 'threads',
               REPO_BLOB_BASE_URI + 'grader/systems-assignments.md#assignment-threads',
               check_threads),
    Assignment('treiber-stack', 'Systems', 'treiber-stack',
               REPO_BLOB_BASE_URI + 'grader/systems-assignments.md#assignment-treiber-stack',
               check_treiber_stack)
}


def main(args: List[str]) -> None:
    process_arguments(args, assignments, baseline_assignment)


if __name__ == "__main__":
    try:
        main(sys.argv)
    except KeyboardInterrupt:
        print('\naborting...')
