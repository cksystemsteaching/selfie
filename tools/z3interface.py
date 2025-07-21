#!/usr/bin/env python3

# Copyright (c) the Selfie Project authors. All rights reserved.
# Please see the AUTHORS file for details. Use of this source code is
# governed by a BSD license that can be found in the LICENSE file.

# Selfie is a project of the Computational Systems Group at the
# Department of Computer Sciences of the University of Salzburg
# in Austria. For further information and code please refer to:

# selfie.cs.uni-salzburg.at

# Z3 interface for BTOR2

# ------------------------------------------------------------

import btor2

# requires Z3 and the Z3 Python API:
# pip install z3-solver

try:
    import z3
    is_Z3_present = True
except ImportError:
    print("Z3 is not available")
    is_Z3_present = False

class Z3:
    def __init__(self):
        self.z3 = None

    def get_z3(self):
        if self.z3 is None:
            self.z3 = self.model_z3()
        return self.z3

class Bool:
    def model_z3(self):
        return z3.BoolSort()

class Bitvec:
    def model_z3(self):
        return z3.BitVecSort(self.size)

class Array:
    def model_z3(self):
        return z3.ArraySort(self.array_size_line.get_z3(), self.element_size_line.get_z3())

class Expression:
    def __init__(self):
        self.z3_lambda = None

    def get_z3_lambda(self):
        if self.z3_lambda is None:
            domain = self.get_domain()
            if domain:
                self.z3_lambda = z3.Lambda([state.get_z3() for state in domain], self.get_z3())
            else:
                self.z3_lambda = self.get_z3()
        return self.z3_lambda

class Constant:
    def model_z3(self):
        if isinstance(self.sid_line, Bool):
            return z3.BoolVal(bool(self.value))
        else:
            return z3.BitVecVal(self.value, self.sid_line.size)

class Constant_Array:
    def model_z3(self):
        return z3.K(self.sid_line.array_size_line.get_z3(), self.constant_line.get_z3())

class Variable:
    def model_z3(self):
        return z3.Const(self.name, self.sid_line.get_z3())

class Input:
    def get_z3_name(self, step):
        return self.get_z3()

    def get_z3_instance(self, step):
        return self.get_z3()

class State:
    def __init__(self):
        self.cache_z3_name = {}

    def get_z3_name(self, step):
        if step == -1:
            step = 0
        if step not in self.cache_z3_name:
            self.cache_z3_name[step] = z3.Const(self.get_step_name(step), self.sid_line.get_z3())
        return self.cache_z3_name[step]

    def get_z3_instance(self, step):
        if self.next_line is None:
            # all instances of an untransitioned state are
            # the state itself, if uninitialized, or its initial state
            return self.instance.get_z3_instance(-1)
        else:
            return self.instance.get_z3_instance(step)

class Ext:
    def model_z3(self):
        if self.op == btor2.OP_SEXT:
            return z3.SignExt(self.w, self.arg1_line.get_z3())
        else:
            assert self.op == btor2.OP_UEXT
            return z3.ZeroExt(self.w, self.arg1_line.get_z3())

class Slice:
    def model_z3(self):
        return z3.Extract(self.u, self.l, self.arg1_line.get_z3())

class Unary:
    def model_z3(self):
        z3_arg1 = self.arg1_line.get_z3()
        if self.op == btor2.OP_NOT:
            if isinstance(self.sid_line, Bool):
                return z3.Not(z3_arg1)
            else:
                return ~z3_arg1
        elif self.op == btor2.OP_INC:
            return z3_arg1 + 1
        elif self.op == btor2.OP_DEC:
            return z3_arg1 - 1
        else:
            assert self.op == btor2.OP_NEG
            return -z3_arg1

class Implies:
    def model_z3(self):
        return z3.Implies(self.arg1_line.get_z3(), self.arg2_line.get_z3())

class Comparison:
    def model_z3(self):
        z3_arg1 = self.arg1_line.get_z3()
        z3_arg2 = self.arg2_line.get_z3()
        if self.op == btor2.OP_EQ:
            return z3_arg1 == z3_arg2
        elif self.op == btor2.OP_NEQ:
            return z3_arg1 != z3_arg2
        elif self.op == btor2.OP_SGT:
            return z3_arg1 > z3_arg2
        elif self.op == btor2.OP_UGT:
            return z3.UGT(z3_arg1, z3_arg2)
        elif self.op == btor2.OP_SGTE:
            return z3_arg1 >= z3_arg2
        elif self.op == btor2.OP_UGTE:
            return z3.UGE(z3_arg1, z3_arg2)
        elif self.op == btor2.OP_SLT:
            return z3_arg1 < z3_arg2
        elif self.op == btor2.OP_ULT:
            return z3.ULT(z3_arg1, z3_arg2)
        elif self.op == btor2.OP_SLTE:
            return z3_arg1 <= z3_arg2
        else:
            assert self.op == btor2.OP_ULTE
            return z3.ULE(z3_arg1, z3_arg2)

class Logical:
    def model_z3(self):
        z3_arg1 = self.arg1_line.get_z3()
        z3_arg2 = self.arg2_line.get_z3()
        if isinstance(self.sid_line, Bool):
            if self.op == btor2.OP_AND:
                return z3.And(z3_arg1, z3_arg2)
            elif self.op == btor2.OP_OR:
                return z3.Or(z3_arg1, z3_arg2)
            else:
                assert self.op == btor2.OP_XOR
                return z3.Xor(z3_arg1, z3_arg2)
        else:
            if self.op == btor2.OP_AND:
                return z3_arg1 & z3_arg2
            elif self.op == btor2.OP_OR:
                return z3_arg1 | z3_arg2
            else:
                assert self.op == btor2.OP_XOR
                return z3_arg1 ^ z3_arg2

class Computation:
    def model_z3(self):
        z3_arg1 = self.arg1_line.get_z3()
        z3_arg2 = self.arg2_line.get_z3()
        if self.op == btor2.OP_SLL:
            return z3_arg1 << z3_arg2
        elif self.op == btor2.OP_SRL:
            return z3.LShR(z3_arg1, z3_arg2)
        elif self.op == btor2.OP_SRA:
            return z3_arg1 >> z3_arg2
        elif self.op == btor2.OP_ADD:
            return z3_arg1 + z3_arg2
        elif self.op == btor2.OP_SUB:
            return z3_arg1 - z3_arg2
        elif self.op == btor2.OP_MUL:
            return z3_arg1 * z3_arg2
        elif self.op == btor2.OP_SDIV:
            return z3_arg1 / z3_arg2
        elif self.op == btor2.OP_UDIV:
            return z3.UDiv(z3_arg1, z3_arg2)
        elif self.op == btor2.OP_SREM:
            return z3.SRem(z3_arg1, z3_arg2)
        else:
            assert self.op == btor2.OP_UREM
            return z3.URem(z3_arg1, z3_arg2)

class Concat:
    def model_z3(self):
        return z3.Concat(self.arg1_line.get_z3(), self.arg2_line.get_z3())

class Read:
    def model_z3(self):
        return z3.Select(self.arg1_line.get_z3(), self.arg2_line.get_z3())

class Ite:
    def model_z3(self):
        return z3.If(self.arg1_line.get_z3(), self.arg2_line.get_z3(), self.arg3_line.get_z3())

    def get_z3_step(self, step):
        # only needed for branching
        self.set_step(step)
        return self.get_instance().get_z3_instance(step)

class Write:
    def model_z3(self):
        return z3.Store(self.arg1_line.get_z3(), self.arg2_line.get_z3(), self.arg3_line.get_z3())

class Init:
    def get_z3_step(self, step):
        assert step == 0, f"z3 init with {step} != 0"
        self.set_step(0)
        if Z3_Solver.PROPAGATE is not None:
            return z3.BoolVal(True)
        else:
            return self.state_line.get_z3_name(0) == self.state_line.get_z3_instance(-1)

class Next:
    def __init__(self):
        self.cache_z3_next_state = {}
        self.cache_z3_is_state_changing = {}
        self.cache_z3_state_is_not_changing = {}

    def get_z3_step(self, step):
        if step not in self.cache_z3_next_state:
            self.set_step(step)
            if Z3_Solver.PROPAGATE is not None:
                self.cache_z3_next_state[step] = z3.BoolVal(True)
            else:
                self.cache_z3_next_state[step] = self.state_line.get_z3_name(step + 1) == self.state_line.get_z3_instance(step)
        return self.cache_z3_next_state[step]

    def is_z3_state_changing(self, step):
        if step not in self.cache_z3_is_state_changing:
            self.set_step(step)
            if self.get_step(step).is_equal(self.get_step(step - 1)):
                self.cache_z3_is_state_changing[step] = z3.BoolVal(False)
            else:
                self.cache_z3_is_state_changing[step] = self.state_line.get_z3_instance(step) != self.state_line.get_z3_instance(step - 1)
        return self.cache_z3_is_state_changing[step]

    def z3_state_is_not_changing(self, step):
        if step not in self.cache_z3_state_is_not_changing:
            if Z3_Solver.PROPAGATE is not None:
                self.set_step(step)
                self.cache_z3_state_is_not_changing[step] = self.state_line.get_z3_instance(step) == self.state_line.get_z3_instance(step - 1)
            else:
                self.state_line.set_instance(self.state_line, step)
                self.cache_z3_state_is_not_changing[step] = self.state_line.get_z3_name(step + 1) == self.state_line.get_z3_name(step)
        return self.cache_z3_state_is_not_changing[step]

class Property:
    def get_z3_step(self, step):
        self.set_step(step)
        return self.get_instance().get_z3_instance(step)

class Instance:
    def __init__(self):
        self.cache_z3_instance = {}

    def get_z3_select(self, step):
        if step not in self.cache_z3_instance:
            instance = self.get_instance(step).get_expression()
            assert step not in self.cache_z3_instance
            domain = instance.get_domain()
            if domain:
                self.cache_z3_instance[step] = z3.Select(instance.get_z3_lambda(),
                    *[state.get_z3_name(step) for state in domain])
            else:
                self.cache_z3_instance[step] = instance.get_z3_lambda()
        return self.cache_z3_instance[step]

    def get_z3_substitute(self, step):
        if step not in self.cache_z3_instance:
            instance = self.get_instance(step).get_expression()
            assert step not in self.cache_z3_instance
            self.cache_z3_instance[step] = instance.get_z3()
            domain = instance.get_domain()
            if domain:
                current_states = [state.get_z3() for state in domain]
                next_states = [state.get_z3_name(step) for state in domain]
                renaming = list(zip(current_states, next_states))

                self.cache_z3_instance[step] = z3.substitute(self.cache_z3_instance[step], renaming)
        return self.cache_z3_instance[step]

    def get_z3_instance(self, step):
        if Z3_Solver.LAMBDAS:
            return self.get_z3_select(step)
        else:
            return self.get_z3_substitute(step)

class Z3_Solver:
    PROPAGATE = None
    LAMBDAS = True

    def __init__(self, print_message, PROPAGATE, LAMBDAS):
        self.print_message = print_message
        Z3_Solver.PROPAGATE = PROPAGATE
        Z3_Solver.LAMBDAS = LAMBDAS
        self.solver = z3.Solver()

    def push(self):
        self.solver.push()

    def pop(self):
        self.solver.pop()

    def assert_this(self, assertions, step):
        for assertion in assertions:
            self.solver.add(assertion.get_z3_step(step))

    def assert_not_this(self, assertions, step):
        for assertion in assertions:
            self.solver.add(assertion.get_z3_step(step) == False)

    def simplify(self):
        # no effective simplification yet found in Z3
        pass

    def prove(self):
        return self.solver.check()

    def is_SAT(self, result):
        return result == z3.sat

    def is_UNSAT(self, result):
        return result == z3.unsat

    def assert_is_state_changing(self, next_line, step):
        self.solver.add(next_line.is_z3_state_changing(step))

    def assert_state_is_not_changing(self, next_line, step):
        self.solver.add(next_line.z3_state_is_not_changing(step))

    def print_pc(self, pc, step, level):
        self.prove()
        model = self.solver.model()
        self.print_message(f"{pc}\n", step, level)
        self.print_message("%s = 0x%X\n" % (pc.get_z3_name(step),
            int(model.evaluate(pc.get_z3_instance(step - 1)).as_long())), step, level)

    def print_inputs(self, inputs, step, level):
        model = self.solver.model()
        for input_variable in inputs.values():
            # only print value of uninitialized states
            self.print_message(f"{input_variable}\n", step, level)
            self.print_message("%s = %s\n" % (input_variable.get_z3_name(step),
                model.evaluate(input_variable.get_z3_instance(step - 1))), step, level)

    def eval_inputs(self, inputs, step):
        model = self.solver.model()

        input_values = dict()
        for input_variable in inputs.values():
            z3_inst = input_variable.get_z3_instance(step - 1)
            if isinstance(input_variable.sid_line, Array):
                # Mimic the output of the BVDD naming scheme for consistency
                for index in range(2**input_variable.sid_line.array_size_line.size):
                    input_values[f"{input_variable.symbol}-{index}"] = model.evaluate(z3_inst[index], model_completion=True).as_long()
            else:
                input_values[input_variable.symbol] = model.evaluate(z3_inst, model_completion=True).as_long()

        return input_values