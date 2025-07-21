#!/usr/bin/env python3

# Copyright (c) the Selfie Project authors. All rights reserved.
# Please see the AUTHORS file for details. Use of this source code is
# governed by a BSD license that can be found in the LICENSE file.

# Selfie is a project of the Computational Systems Group at the
# Department of Computer Sciences of the University of Salzburg
# in Austria. For further information and code please refer to:

# selfie.cs.uni-salzburg.at

# Bitwuzla interface for BTOR2

# ------------------------------------------------------------

import btor2

# requires bitwuzla and the bitwuzla Python API:
# cd bitwuzla
# pip install .

try:
    import bitwuzla
    is_bitwuzla_present = True
except ImportError:
    print("bitwuzla is not available")
    is_bitwuzla_present = False

class Bitwuzla:
    def __init__(self):
        self.bitwuzla = None

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            self.bitwuzla = self.model_bitwuzla(tm)
        return self.bitwuzla

class Bool:
    def model_bitwuzla(self, tm):
        return tm.mk_bool_sort()

class Bitvec:
    def model_bitwuzla(self, tm):
        return tm.mk_bv_sort(self.size)

class Array:
    def model_bitwuzla(self, tm):
        return tm.mk_array_sort(self.array_size_line.get_bitwuzla(tm),
            self.element_size_line.get_bitwuzla(tm))

class Expression:
    def __init__(self):
        self.bitwuzla_lambda = None

    def get_bitwuzla_lambda(self, tm):
        if self.bitwuzla_lambda is None:
            domain = self.get_domain()
            if domain:
                self.bitwuzla_lambda = tm.mk_term(bitwuzla.Kind.LAMBDA,
                    [*[state.get_bitwuzla(tm) for state in domain], self.get_bitwuzla(tm)])
            else:
                self.bitwuzla_lambda = self.get_bitwuzla(tm)
        return self.bitwuzla_lambda

class Constant:
    def model_bitwuzla(self, tm):
        if isinstance(self.sid_line, Bool):
            return tm.mk_true() if bool(self.value) else tm.mk_false()
        else:
            return tm.mk_bv_value(self.sid_line.get_bitwuzla(tm), self.value)

class Constant_Array:
    def model_bitwuzla(self, tm):
        return tm.mk_const_array(self.sid_line.get_bitwuzla(tm), self.constant_line.get_bitwuzla(tm))

class Input:
    def model_bitwuzla(self, tm):
        return tm.mk_const(self.sid_line.get_bitwuzla(tm), self.name)

    def get_bitwuzla_name(self, step, tm):
        return self.get_bitwuzla(tm)

    def get_bitwuzla_instance(self, step, tm):
        return self.get_bitwuzla(tm)

class State:
    def __init__(self):
        self.cache_bitwuzla_name = {}

    def model_bitwuzla(self, tm):
        if self.init_line is None:
            return tm.mk_const(self.sid_line.get_bitwuzla(tm), self.name)
        else:
            return tm.mk_var(self.sid_line.get_bitwuzla(tm), self.name)

    def get_bitwuzla_name(self, step, tm):
        if step == -1:
            step = 0
        if step not in self.cache_bitwuzla_name:
            self.cache_bitwuzla_name[step] = tm.mk_const(self.sid_line.get_bitwuzla(tm),
                self.get_step_name(step))
        return self.cache_bitwuzla_name[step]

    def get_bitwuzla_instance(self, step, tm):
        if self.next_line is None:
            # all instances of an untransitioned state are
            # the state itself, if uninitialized, or its initial state
            return self.instance.get_bitwuzla_instance(-1, tm)
        else:
            return self.instance.get_bitwuzla_instance(step, tm)

class Ext:
    def model_bitwuzla(self, tm):
        if self.op == btor2.OP_SEXT:
            bitwuzla_op = bitwuzla.Kind.BV_SIGN_EXTEND
        else:
            assert self.op == btor2.OP_UEXT
            bitwuzla_op = bitwuzla.Kind.BV_ZERO_EXTEND
        return tm.mk_term(bitwuzla_op, [self.arg1_line.get_bitwuzla(tm)], [self.w])

class Slice:
    def model_bitwuzla(self, tm):
        return tm.mk_term(bitwuzla.Kind.BV_EXTRACT, [self.arg1_line.get_bitwuzla(tm)], [self.u, self.l])

class Unary:
    def model_bitwuzla(self, tm):
        if self.op == btor2.OP_NOT:
            if isinstance(self.sid_line, Bool):
                bitwuzla_op = bitwuzla.Kind.NOT
            else:
                bitwuzla_op = bitwuzla.Kind.BV_NOT
        elif self.op == btor2.OP_INC:
            bitwuzla_op = bitwuzla.Kind.BV_INC
        elif self.op == btor2.OP_DEC:
            bitwuzla_op = bitwuzla.Kind.BV_DEC
        else:
            assert self.op == btor2.OP_NEG
            bitwuzla_op = bitwuzla.Kind.BV_NEG
        return tm.mk_term(bitwuzla_op, [self.arg1_line.get_bitwuzla(tm)])

class Implies:
    def model_bitwuzla(self, tm):
        return tm.mk_term(bitwuzla.Kind.IMPLIES,
            [self.arg1_line.get_bitwuzla(tm), self.arg2_line.get_bitwuzla(tm)])

class Comparison:
    def model_bitwuzla(self, tm):
        if self.op == btor2.OP_EQ:
            bitwuzla_op = bitwuzla.Kind.EQUAL
        elif self.op == btor2.OP_NEQ:
            bitwuzla_op = bitwuzla.Kind.DISTINCT
        elif self.op == btor2.OP_SGT:
            bitwuzla_op = bitwuzla.Kind.BV_SGT
        elif self.op == btor2.OP_UGT:
            bitwuzla_op = bitwuzla.Kind.BV_UGT
        elif self.op == btor2.OP_SGTE:
            bitwuzla_op = bitwuzla.Kind.BV_SGE
        elif self.op == btor2.OP_UGTE:
            bitwuzla_op = bitwuzla.Kind.BV_UGE
        elif self.op == btor2.OP_SLT:
            bitwuzla_op = bitwuzla.Kind.BV_SLT
        elif self.op == btor2.OP_ULT:
            bitwuzla_op = bitwuzla.Kind.BV_ULT
        elif self.op == btor2.OP_SLTE:
            bitwuzla_op = bitwuzla.Kind.BV_SLE
        else:
            assert self.op == btor2.OP_ULTE
            bitwuzla_op = bitwuzla.Kind.BV_ULE
        return tm.mk_term(bitwuzla_op,
            [self.arg1_line.get_bitwuzla(tm), self.arg2_line.get_bitwuzla(tm)])

class Logical:
    def model_bitwuzla(self, tm):
        if isinstance(self.sid_line, Bool):
            if self.op == btor2.OP_AND:
                bitwuzla_op = bitwuzla.Kind.AND
            elif self.op == btor2.OP_OR:
                bitwuzla_op = bitwuzla.Kind.OR
            else:
                assert self.op == btor2.OP_XOR
                bitwuzla_op = bitwuzla.Kind.XOR
        else:
            if self.op == btor2.OP_AND:
                bitwuzla_op = bitwuzla.Kind.BV_AND
            elif self.op == btor2.OP_OR:
                bitwuzla_op = bitwuzla.Kind.BV_OR
            else:
                assert self.op == btor2.OP_XOR
                bitwuzla_op = bitwuzla.Kind.BV_XOR
        return tm.mk_term(bitwuzla_op,
            [self.arg1_line.get_bitwuzla(tm), self.arg2_line.get_bitwuzla(tm)])

class Computation:
    def model_bitwuzla(self, tm):
        if self.op == btor2.OP_SLL:
            bitwuzla_op = bitwuzla.Kind.BV_SHL
        elif self.op == btor2.OP_SRL:
            bitwuzla_op = bitwuzla.Kind.BV_SHR
        elif self.op == btor2.OP_SRA:
            bitwuzla_op = bitwuzla.Kind.BV_ASHR
        elif self.op == btor2.OP_ADD:
            bitwuzla_op = bitwuzla.Kind.BV_ADD
        elif self.op == btor2.OP_SUB:
            bitwuzla_op = bitwuzla.Kind.BV_SUB
        elif self.op == btor2.OP_MUL:
            bitwuzla_op = bitwuzla.Kind.BV_MUL
        elif self.op == btor2.OP_SDIV:
            bitwuzla_op = bitwuzla.Kind.BV_SDIV
        elif self.op == btor2.OP_UDIV:
            bitwuzla_op = bitwuzla.Kind.BV_UDIV
        elif self.op == btor2.OP_SREM:
            bitwuzla_op = bitwuzla.Kind.BV_SREM
        else:
            assert self.op == btor2.OP_UREM
            bitwuzla_op = bitwuzla.Kind.BV_UREM
        return tm.mk_term(bitwuzla_op,
            [self.arg1_line.get_bitwuzla(tm), self.arg2_line.get_bitwuzla(tm)])

class Concat:
    def model_bitwuzla(self, tm):
        return tm.mk_term(bitwuzla.Kind.BV_CONCAT,
            [self.arg1_line.get_bitwuzla(tm), self.arg2_line.get_bitwuzla(tm)])

class Read:
    def model_bitwuzla(self, tm):
        return tm.mk_term(bitwuzla.Kind.ARRAY_SELECT,
            [self.arg1_line.get_bitwuzla(tm), self.arg2_line.get_bitwuzla(tm)])

class Ite:
    def model_bitwuzla(self, tm):
        return tm.mk_term(bitwuzla.Kind.ITE, [self.arg1_line.get_bitwuzla(tm),
            self.arg2_line.get_bitwuzla(tm), self.arg3_line.get_bitwuzla(tm)])

    def get_bitwuzla_step(self, step, tm):
        # only needed for branching
        self.set_step(step)
        return self.get_instance().get_bitwuzla_instance(step, tm)

class Write:
    def model_bitwuzla(self, tm):
        return tm.mk_term(bitwuzla.Kind.ARRAY_STORE,
            [self.arg1_line.get_bitwuzla(tm),
            self.arg2_line.get_bitwuzla(tm),
            self.arg3_line.get_bitwuzla(tm)])

class Init:
    def get_bitwuzla_step(self, step, tm):
        assert step == 0, f"bitwuzla init with {step} != 0"
        self.set_step(0)
        if Bitwuzla_Solver.PROPAGATE is not None:
            return tm.mk_true()
        else:
            return tm.mk_term(bitwuzla.Kind.EQUAL,
                [self.state_line.get_bitwuzla_name(0, tm),
                self.state_line.get_bitwuzla_instance(-1, tm)])

class Next:
    def __init__(self):
        self.cache_bitwuzla_next_state = {}
        self.cache_bitwuzla_is_state_changing = {}
        self.cache_bitwuzla_state_is_not_changing = {}

    def get_bitwuzla_step(self, step, tm):
        if step not in self.cache_bitwuzla_next_state:
            self.set_step(step)
            if Bitwuzla_Solver.PROPAGATE is not None:
                self.cache_bitwuzla_next_state[step] = tm.mk_true()
            else:
                self.cache_bitwuzla_next_state[step] = tm.mk_term(bitwuzla.Kind.EQUAL,
                    [self.state_line.get_bitwuzla_name(step + 1, tm),
                    self.state_line.get_bitwuzla_instance(step, tm)])
        return self.cache_bitwuzla_next_state[step]

    def is_bitwuzla_state_changing(self, step, tm):
        if step not in self.cache_bitwuzla_is_state_changing:
            self.set_step(step)
            if self.get_step(step).is_equal(self.get_step(step - 1)):
                self.cache_bitwuzla_is_state_changing[step] = tm.mk_false()
            else:
                self.cache_bitwuzla_is_state_changing[step] = tm.mk_term(bitwuzla.Kind.DISTINCT,
                    [self.state_line.get_bitwuzla_instance(step, tm),
                    self.state_line.get_bitwuzla_instance(step - 1, tm)])
        return self.cache_bitwuzla_is_state_changing[step]

    def bitwuzla_state_is_not_changing(self, step, tm):
        if step not in self.cache_bitwuzla_state_is_not_changing:
            if Bitwuzla_Solver.PROPAGATE is not None:
                self.set_step(step)
                self.cache_bitwuzla_state_is_not_changing[step] = tm.mk_term(bitwuzla.Kind.EQUAL,
                    [self.state_line.get_bitwuzla_instance(step, tm),
                    self.state_line.get_bitwuzla_instance(step - 1, tm)])
            else:
                self.state_line.set_instance(self.state_line, step)
                self.cache_bitwuzla_state_is_not_changing[step] = tm.mk_term(bitwuzla.Kind.EQUAL,
                    [self.state_line.get_bitwuzla_name(step + 1, tm),
                    self.state_line.get_bitwuzla_name(step, tm)])
        return self.cache_bitwuzla_state_is_not_changing[step]

class Property:
    def get_bitwuzla_step(self, step, tm):
        self.set_step(step)
        return self.get_instance().get_bitwuzla_instance(step, tm)

class Instance:
    def __init__(self):
        self.cache_bitwuzla_instance = {}

    def get_bitwuzla_select(self, step, tm):
        if step not in self.cache_bitwuzla_instance:
            instance = self.get_instance(step).get_expression()
            assert step not in self.cache_bitwuzla_instance
            domain = instance.get_domain()
            if domain:
                self.cache_bitwuzla_instance[step] = tm.mk_term(bitwuzla.Kind.APPLY,
                    [instance.get_bitwuzla_lambda(tm),
                    *[state.get_bitwuzla_name(step, tm) for state in domain]])
            else:
                self.cache_bitwuzla_instance[step] = instance.get_bitwuzla_lambda(tm)
        return self.cache_bitwuzla_instance[step]

    def get_bitwuzla_substitute(self, step, tm):
        if step not in self.cache_bitwuzla_instance:
            instance = self.get_instance(step).get_expression()
            assert step not in self.cache_bitwuzla_instance
            self.cache_bitwuzla_instance[step] = instance.get_bitwuzla(tm)
            domain = instance.get_domain()
            if domain:
                current_states = [state.get_bitwuzla(tm) for state in domain]
                next_states = [state.get_bitwuzla_name(step, tm) for state in domain]
                renaming = dict(zip(current_states, next_states))

                self.cache_bitwuzla_instance[step] = tm.substitute_term(self.cache_bitwuzla_instance[step], renaming)
        return self.cache_bitwuzla_instance[step]

    def get_bitwuzla_instance(self, step, tm):
        if Bitwuzla_Solver.LAMBDAS:
            return self.get_bitwuzla_select(step, tm)
        else:
            return self.get_bitwuzla_substitute(step, tm)

class Bitwuzla_Solver:
    PROPAGATE = None
    LAMBDAS = True

    def __init__(self, print_message, PROPAGATE, LAMBDAS):
        self.print_message = print_message
        Bitwuzla_Solver.PROPAGATE = PROPAGATE
        Bitwuzla_Solver.LAMBDAS = LAMBDAS
        self.tm = bitwuzla.TermManager()
        self.options = bitwuzla.Options()
        self.options.set(bitwuzla.Option.PRODUCE_MODELS, True)
        self.solver = bitwuzla.Bitwuzla(self.tm, self.options)

    def push(self):
        self.solver.push()

    def pop(self):
        self.solver.pop()

    def assert_this(self, assertions, step):
        for assertion in assertions:
            self.solver.assert_formula(assertion.get_bitwuzla_step(step, self.tm))

    def assert_not_this(self, assertions, step):
        for assertion in assertions:
            self.solver.assert_formula(self.tm.mk_term(bitwuzla.Kind.NOT, [assertion.get_bitwuzla_step(step, self.tm)]))

    def simplify(self):
        # possibly increases performance
        self.prove()

    def prove(self):
        return self.solver.check_sat()

    def is_SAT(self, result):
        return result is bitwuzla.Result.SAT

    def is_UNSAT(self, result):
        return result is bitwuzla.Result.UNSAT

    def assert_is_state_changing(self, next_line, step):
        self.solver.assert_formula(next_line.is_bitwuzla_state_changing(step, self.tm))

    def assert_state_is_not_changing(self, next_line, step):
        self.solver.assert_formula(next_line.bitwuzla_state_is_not_changing(step, self.tm))

    def print_pc(self, pc, step, level):
        self.prove()
        pc_value = int(self.solver.get_value(pc.get_bitwuzla_instance(step - 1, self.tm)).value(16), 16)
        self.print_message(f"{pc}\n", step, level)
        self.print_message("%s = 0x%X\n" % (pc.get_bitwuzla_name(step, self.tm), pc_value), step, level)

    def print_inputs(self, inputs, step, level):
        for input_variable in inputs.values():
            # only print value of uninitialized states
            self.print_message(f"{input_variable}\n", step, level)
            self.print_message("%s = %s\n" % (input_variable.get_bitwuzla_name(step, self.tm),
                self.solver.get_value(input_variable.get_bitwuzla_instance(step - 1, self.tm))),
                step, level)

    def eval_inputs(self, inputs, step):
        input_values = dict()
        for input_variable in inputs.values():
            bwz_inst = input_variable.get_bitwuzla_instance(step - 1, self.tm)
            if isinstance(input_variable.sid_line, Array):
                # Mimic the output of the BVDD naming scheme for consistency
                for index in range(2**input_variable.sid_line.array_size_line.size):
                    input_values[f"{input_variable.symbol}-{index}"] = self.solver.get_value(bwz_inst[index])
            else:
                input_values[input_variable.symbol] = self.solver.get_value(bwz_inst)

        return input_values