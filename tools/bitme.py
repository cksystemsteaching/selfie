#!/usr/bin/env python3

# for debugging segfaults: import faulthandler; faulthandler.enable()

# requires Z3 and the Z3 Python API:
# pip install z3-solver

try:
    import z3
    is_Z3_present = True
except ImportError:
    print("Z3 is not available")
    is_Z3_present = False

# requires bitwuzla and the bitwuzla Python API:
# cd bitwuzla
# pip install .

try:
    import bitwuzla
    is_bitwuzla_present = True
except ImportError:
    print("bitwuzla is not available")
    is_bitwuzla_present = False

import math

class model_error(Exception):
    def __init__(self, expected, line_no):
        super().__init__(f"model error in line {line_no}: {expected} expected")

class Z3():
    def __init__(self):
        self.z3 = None

class Bitwuzla():
    def __init__(self):
        self.bitwuzla = None

class Line(Z3, Bitwuzla):
    lines = dict()

    def __init__(self, nid, comment, line_no):
        Z3.__init__(self)
        Bitwuzla.__init__(self)
        self.nid = nid
        self.comment = comment
        self.line_no = line_no
        self.new_line()

    def __repr__(self):
        return self.__str__()

    def new_line(self):
        assert self not in Line.lines
        Line.lines[self.nid] = self

    def is_defined(nid):
        return nid in Line.lines

    def get(nid):
        assert nid in Line.lines
        return Line.lines[nid]

class Sort(Line):
    keyword = 'sort'

    def __init__(self, nid, comment, line_no):
        super().__init__(nid, comment, line_no)

    def match_sorts(self, sort):
        return type(self) == type(sort)

class Bitvector(Sort):
    keyword = 'bitvec'

    def __init__(self, nid, size, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.size = size

    def __str__(self):
        return f"{self.nid} {Sort.keyword} {Bitvec.keyword} {self.size} {self.comment}"

    def match_init_sorts(self, sort):
        return self.match_sorts(sort)

class Bool(Bitvector):
    def __init__(self, nid, comment, line_no):
        super().__init__(nid, 1, comment, line_no)

    def match_sorts(self, sort):
        return super().match_sorts(sort)

    def get_z3(self):
        if self.z3 is None:
            self.z3 = z3.BoolSort()
        return self.z3

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            self.bitwuzla = tm.mk_bool_sort()
        return self.bitwuzla

class Bitvec(Bitvector):
    def __init__(self, nid, size, comment, line_no):
        super().__init__(nid, size, comment, line_no)

    def match_sorts(self, sort):
        return super().match_sorts(sort) and self.size == sort.size

    def get_z3(self):
        if self.z3 is None:
            self.z3 = z3.BitVecSort(self.size)
        return self.z3

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            self.bitwuzla = tm.mk_bv_sort(self.size)
        return self.bitwuzla

class Array(Sort):
    keyword = 'array'

    def __init__(self, nid, array_size_line, element_size_line, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.array_size_line = array_size_line
        self.element_size_line = element_size_line
        if not isinstance(array_size_line, Bitvec):
            raise model_error("array size bitvector", line_no)
        if not isinstance(element_size_line, Bitvec):
            raise model_error("element size bitvector", line_no)

    def __str__(self):
        return f"{self.nid} {Sort.keyword} {Array.keyword} {self.array_size_line.nid} {self.element_size_line.nid} {self.comment}"

    def match_sorts(self, sort):
        return (super().match_sorts(sort)
            and self.array_size_line.match_sorts(sort.array_size_line)
            and self.element_size_line.match_sorts(sort.element_size_line))

    def match_init_sorts(self, sort):
        # allow constant arrays: array init with bitvector
        return (self.match_sorts(sort)
            or (isinstance(sort, Bitvec) and self.element_size_line.match_sorts(sort)))

    def get_z3(self):
        if self.z3 is None:
            self.z3 = z3.ArraySort(self.array_size_line.get_z3(),
                self.element_size_line.get_z3())
        return self.z3

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            self.bitwuzla = tm.mk_array_sort(self.array_size_line.get_bitwuzla(tm),
                self.element_size_line.get_bitwuzla(tm))
        return self.bitwuzla

class Expression(Line):
    def __init__(self, nid, sid_line, domain, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.sid_line = sid_line
        self.domain = domain
        if not isinstance(sid_line, Sort):
            raise model_error("sort", line_no)

class Constant(Expression):
    def __init__(self, nid, sid_line, value, comment, line_no):
        super().__init__(nid, sid_line, dict(), comment, line_no)
        self.value = value
        if value >= 2**sid_line.size:
            raise model_error(f"{value} in range of {sid_line.size}-bit bitvector", line_no)

    def get_z3(self):
        if self.z3 is None:
            if isinstance(self.sid_line, Bool):
                self.z3 = z3.BoolVal(bool(self.value))
            else:
                self.z3 = z3.BitVecVal(self.value, self.sid_line.size)
        return self.z3

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            if isinstance(self.sid_line, Bool):
                self.bitwuzla = tm.mk_true() if bool(self.value) else tm.mk_false()
            else:
                self.bitwuzla = tm.mk_bv_value(self.sid_line.get_bitwuzla(tm), self.value)
        return self.bitwuzla

class Zero(Constant):
    keyword = 'zero'

    def __init__(self, nid, sid_line, comment, line_no):
        super().__init__(nid, sid_line, 0, comment, line_no)

    def __str__(self):
        return f"{self.nid} {Zero.keyword} {self.sid_line.nid} {self.comment}"

class One(Constant):
    keyword = 'one'

    def __init__(self, nid, sid_line, comment, line_no):
        super().__init__(nid, sid_line, 1, comment, line_no)

    def __str__(self):
        return f"{self.nid} {One.keyword} {self.sid_line.nid} {self.comment}"

class Constd(Constant):
    keyword = 'constd'

    def __init__(self, nid, sid_line, value, comment, line_no):
        super().__init__(nid, sid_line, value, comment, line_no)

    def __str__(self):
        return f"{self.nid} {Constd.keyword} {self.sid_line.nid} {self.value} {self.comment}"

class Const(Constant):
    keyword = 'const'

    def __init__(self, nid, sid_line, value, comment, line_no):
        super().__init__(nid, sid_line, value, comment, line_no)

    def __str__(self):
        size = self.sid_line.size
        return f"{self.nid} {Const.keyword} {self.sid_line.nid} {self.value:0{size}b} {self.comment}"

class Consth(Constant):
    keyword = 'consth'

    def __init__(self, nid, sid_line, value, comment, line_no):
        super().__init__(nid, sid_line, value, comment, line_no)

    def __str__(self):
        size = math.ceil(self.sid_line.size / 4)
        return f"{self.nid} {Consth.keyword} {self.sid_line.nid} {self.value:0{size}X} {self.comment}"

class Variable(Expression):
    keywords = {'input', 'state'}

    inputs = dict()

    def __init__(self, nid, sid_line, domain, symbol, comment, line_no):
        super().__init__(nid, sid_line, domain, comment, line_no)
        self.symbol = symbol

    def new_input(self):
        assert self not in Variable.inputs
        Variable.inputs[self.nid] = self

class Input(Variable):
    keyword = 'input'

    def __init__(self, nid, sid_line, symbol, comment, line_no):
        super().__init__(nid, sid_line, dict(), symbol, comment, line_no)
        self.name = f"input{self.nid}"
        self.new_input()

    def __str__(self):
        return f"{self.nid} {Input.keyword} {self.sid_line.nid} {self.symbol} {self.comment}"

    def get_z3(self):
        if self.z3 is None:
            self.z3 = z3.Const(self.name, self.sid_line.get_z3())
        return self.z3

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            self.bitwuzla = tm.mk_const(self.sid_line.get_bitwuzla(tm), self.name)
        return self.bitwuzla

class State(Variable):
    keyword = 'state'

    states = dict()

    pc = None

    def __init__(self, nid, sid_line, symbol, comment, line_no):
        super().__init__(nid, sid_line, {nid:self}, symbol, comment, line_no)
        self.name = f"state{nid}"
        self.init_line = self
        self.next_line = self
        self.step_z3 = 0
        self.current_z3 = None
        self.next_z3 = None
        self.step_bitwuzla = 0
        self.current_bitwuzla = None
        self.next_bitwuzla = None
        self.new_state()
        # rotor-dependent program counter declaration
        if comment == "; program counter":
            State.pc = self

    def __str__(self):
        return f"{self.nid} {State.keyword} {self.sid_line.nid} {self.symbol} {self.comment}"

    def new_state(self):
        assert self not in State.states
        State.states[self.nid] = self

    def get_z3(self):
        if self.z3 is None:
            self.z3 = z3.Const(self.name, self.sid_line.get_z3())
        return self.z3

    def get_z3_lambda(term):
        return z3.Lambda([state.get_z3() for state in State.states.values()], term)

    def get_step_name(self, step):
        return f"{self.name}-{step}"

    def get_z3_state(self, step):
        return z3.Const(self.get_step_name(step), self.sid_line.get_z3())

    def get_z3_step(self, step):
        assert self.step_z3 <= step <= self.step_z3 + 2
        if step == self.step_z3:
            if self.current_z3 is None:
                self.current_z3 = self.get_z3_state(step)
            return self.current_z3
        elif step == self.step_z3 + 1:
            if self.next_z3 is None:
                self.next_z3 = self.get_z3_state(step)
            return self.next_z3
        elif step == self.step_z3 + 2:
            self.current_z3 = self.next_z3
            self.next_z3 = self.get_z3_state(step)
            self.step_z3 += 1
            return self.next_z3

    def get_z3_select(term, step):
        return z3.Select(term, *[state.get_z3_step(step) for state in State.states.values()])

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            self.bitwuzla = tm.mk_var(self.sid_line.get_bitwuzla(tm), self.name)
        return self.bitwuzla

    def get_bitwuzla_lambda(term, tm):
        return tm.mk_term(bitwuzla.Kind.LAMBDA,
            [*[state.get_bitwuzla(tm) for state in State.states.values()], term])

    def get_bitwuzla_state(self, step, tm):
        return tm.mk_const(self.sid_line.get_bitwuzla(tm), self.get_step_name(step))

    def get_bitwuzla_step(self, step, tm):
        assert self.step_bitwuzla <= step <= self.step_bitwuzla + 2
        if step == self.step_bitwuzla:
            if self.current_bitwuzla is None:
                self.current_bitwuzla = self.get_bitwuzla_state(step, tm)
            return self.current_bitwuzla
        elif step == self.step_bitwuzla + 1:
            if self.next_bitwuzla is None:
                self.next_bitwuzla = self.get_bitwuzla_state(step, tm)
            return self.next_bitwuzla
        elif step == self.step_bitwuzla + 2:
            self.current_bitwuzla = self.next_bitwuzla
            self.next_bitwuzla = self.get_bitwuzla_state(step, tm)
            self.step_bitwuzla += 1
            return self.next_bitwuzla

    def get_bitwuzla_select(term, step, tm):
        return tm.mk_term(bitwuzla.Kind.APPLY,
            [term, *[state.get_bitwuzla_step(step, tm) for state in State.states.values()]])

class Indexed(Expression):
    def __init__(self, nid, sid_line, arg1_line, comment, line_no):
        super().__init__(nid, sid_line, arg1_line.domain, comment, line_no)
        self.arg1_line = arg1_line
        if not isinstance(arg1_line, Expression):
            raise model_error("expression operand", line_no)
        if not isinstance(sid_line, Bitvec):
            raise model_error("bitvector result", line_no)
        if not isinstance(arg1_line.sid_line, Bitvec):
            raise model_error("bitvector operand", line_no)

class Ext(Indexed):
    keywords = {'sext', 'uext'}

    def __init__(self, nid, op, sid_line, arg1_line, w, comment, line_no):
        super().__init__(nid, sid_line, arg1_line, comment, line_no)
        self.op = op
        self.w = w
        if sid_line.size != arg1_line.sid_line.size + w:
            raise model_error("compatible bitvector sorts", line_no)

    def __str__(self):
        return f"{self.nid} {self.op} {self.sid_line.nid} {self.arg1_line.nid} {self.w} {self.comment}"

    def get_z3(self):
        if self.z3 is None:
            if self.op == 'sext':
                self.z3 = z3.SignExt(self.w, self.arg1_line.get_z3())
            elif self.op == 'uext':
                self.z3 = z3.ZeroExt(self.w, self.arg1_line.get_z3())
        return self.z3

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            if self.op == 'sext':
                bitwuzla_op = bitwuzla.Kind.BV_SIGN_EXTEND
            elif self.op == 'uext':
                bitwuzla_op = bitwuzla.Kind.BV_ZERO_EXTEND
            self.bitwuzla = tm.mk_term(bitwuzla_op,
                [self.arg1_line.get_bitwuzla(tm)], [self.w])
        return self.bitwuzla

class Slice(Indexed):
    keyword = 'slice'

    def __init__(self, nid, sid_line, arg1_line, u, l, comment, line_no):
        super().__init__(nid, sid_line, arg1_line, comment, line_no)
        self.u = u
        self.l = l
        if u >= arg1_line.sid_line.size:
            raise model_error("upper bit in range", line_no)
        if u < l:
            raise model_error("upper bit >= lower bit", line_no)
        if sid_line.size != u - l + 1:
            raise model_error("compatible bitvector sorts", line_no)

    def __str__(self):
        return f"{self.nid} {Slice.keyword} {self.sid_line.nid} {self.arg1_line.nid} {self.u} {self.l} {self.comment}"

    def get_z3(self):
        if self.z3 is None:
            self.z3 = z3.Extract(self.u, self.l, self.arg1_line.get_z3())
        return self.z3

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            self.bitwuzla = tm.mk_term(bitwuzla.Kind.BV_EXTRACT,
                [self.arg1_line.get_bitwuzla(tm)], [self.u, self.l])
        return self.bitwuzla

class Unary(Expression):
    keywords = {'not', 'inc', 'dec', 'neg'}

    def __init__(self, nid, op, sid_line, arg1_line, comment, line_no):
        super().__init__(nid, sid_line, arg1_line.domain, comment, line_no)
        self.op = op
        self.arg1_line = arg1_line
        if not isinstance(arg1_line, Expression):
            raise model_error("expression operand", line_no)
        if op == 'not' and not isinstance(sid_line, Bitvector):
            raise model_error("Boolean or bitvector result", line_no)
        if op != 'not' and not isinstance(sid_line, Bitvec):
            raise model_error("bitvector result", line_no)
        if not sid_line.match_sorts(arg1_line.sid_line):
            raise model_error("compatible sorts", line_no)

    def __str__(self):
        return f"{self.nid} {self.op} {self.sid_line.nid} {self.arg1_line.nid} {self.comment}"

    def get_z3(self):
        if self.z3 is None:
            if self.op == 'not':
                if isinstance(self.sid_line, Bool):
                    self.z3 = z3.Not(self.arg1_line.get_z3())
                else:
                    self.z3 = ~self.arg1_line.get_z3()
            elif self.op == 'inc':
                self.z3 = self.arg1_line.get_z3() + 1
            elif self.op == 'dec':
                self.z3 = self.arg1_line.get_z3() - 1
            elif self.op == 'neg':
                self.z3 = -self.arg1_line.get_z3()
        return self.z3

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            if self.op == 'not':
                if isinstance(self.sid_line, Bool):
                    bitwuzla_op = bitwuzla.Kind.NOT
                else:
                    bitwuzla_op = bitwuzla.Kind.BV_NOT
            elif self.op == 'inc':
                bitwuzla_op = bitwuzla.Kind.BV_INC
            elif self.op == 'dec':
                bitwuzla_op = bitwuzla.Kind.BV_DEC
            elif self.op == 'neg':
                bitwuzla_op = bitwuzla.Kind.BV_NEG
            self.bitwuzla = tm.mk_term(bitwuzla_op, [self.arg1_line.get_bitwuzla(tm)])
        return self.bitwuzla

class Binary(Expression):
    keywords = {'implies', 'eq', 'neq', 'sgt', 'ugt', 'sgte', 'ugte', 'slt', 'ult', 'slte', 'ulte', 'and', 'or', 'xor', 'sll', 'srl', 'sra', 'add', 'sub', 'mul', 'sdiv', 'udiv', 'srem', 'urem', 'concat', 'read'}

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, comment, line_no):
        super().__init__(nid, sid_line, arg1_line.domain | arg2_line.domain, comment, line_no)
        self.op = op
        self.arg1_line = arg1_line
        self.arg2_line = arg2_line
        if not isinstance(arg1_line, Expression):
            raise model_error("expression left operand", line_no)
        if not isinstance(arg2_line, Expression):
            raise model_error("expression right operand", line_no)

    def __str__(self):
        return f"{self.nid} {self.op} {self.sid_line.nid} {self.arg1_line.nid} {self.arg2_line.nid} {self.comment}"

class Implies(Binary):
    keyword = 'implies'

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, comment, line_no):
        super().__init__(nid, op, sid_line, arg1_line, arg2_line, comment, line_no)
        if not isinstance(sid_line, Bool):
            raise model_error("Boolean result", line_no)
        if not sid_line.match_sorts(arg1_line.sid_line):
            raise model_error("compatible result and first operand sorts", line_no)
        if not arg1_line.sid_line.match_sorts(arg2_line.sid_line):
            raise model_error("compatible first and second operand sorts", line_no)

    def get_z3(self):
        if self.z3 is None:
            self.z3 = z3.Implies(self.arg1_line.get_z3(), self.arg2_line.get_z3())
        return self.z3

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            self.bitwuzla = tm.mk_term(bitwuzla.Kind.IMPLIES,
                [self.arg1_line.get_bitwuzla(tm), self.arg2_line.get_bitwuzla(tm)])
        return self.bitwuzla

class Comparison(Binary):
    keywords = {'eq', 'neq', 'sgt', 'ugt', 'sgte', 'ugte', 'slt', 'ult', 'slte', 'ulte'}

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, comment, line_no):
        super().__init__(nid, op, sid_line, arg1_line, arg2_line, comment, line_no)
        if not isinstance(sid_line, Bool):
            raise model_error("Boolean result", line_no)
        if not isinstance(arg1_line.sid_line, Bitvec):
            raise model_error("bitvector first operand", line_no)
        if not arg1_line.sid_line.match_sorts(arg2_line.sid_line):
            raise model_error("compatible first and second operand sorts", line_no)

    def get_z3(self):
        if self.z3 is None:
            if self.op == 'eq':
                self.z3 = self.arg1_line.get_z3() == self.arg2_line.get_z3()
            elif self.op == 'neq':
                self.z3 = self.arg1_line.get_z3() != self.arg2_line.get_z3()
            elif self.op == 'sgt':
                self.z3 = self.arg1_line.get_z3() > self.arg2_line.get_z3()
            elif self.op == 'ugt':
                self.z3 = z3.UGT(self.arg1_line.get_z3(), self.arg2_line.get_z3())
            elif self.op == 'sgte':
                self.z3 = self.arg1_line.get_z3() >= self.arg2_line.get_z3()
            elif self.op == 'ugte':
                self.z3 = z3.UGE(self.arg1_line.get_z3(), self.arg2_line.get_z3())
            elif self.op == 'slt':
                self.z3 = self.arg1_line.get_z3() < self.arg2_line.get_z3()
            elif self.op == 'ult':
                self.z3 = z3.ULT(self.arg1_line.get_z3(), self.arg2_line.get_z3())
            elif self.op == 'slte':
                self.z3 = self.arg1_line.get_z3() <= self.arg2_line.get_z3()
            elif self.op == 'ulte':
                self.z3 = z3.ULE(self.arg1_line.get_z3(), self.arg2_line.get_z3())
        return self.z3

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            if self.op == 'eq':
                bitwuzla_op = bitwuzla.Kind.EQUAL
            elif self.op == 'neq':
                bitwuzla_op = bitwuzla.Kind.DISTINCT
            elif self.op == 'sgt':
                bitwuzla_op = bitwuzla.Kind.BV_SGT
            elif self.op == 'ugt':
                bitwuzla_op = bitwuzla.Kind.BV_UGT
            elif self.op == 'sgte':
                bitwuzla_op = bitwuzla.Kind.BV_SGE
            elif self.op == 'ugte':
                bitwuzla_op = bitwuzla.Kind.BV_UGE
            elif self.op == 'slt':
                bitwuzla_op = bitwuzla.Kind.BV_SLT
            elif self.op == 'ult':
                bitwuzla_op = bitwuzla.Kind.BV_ULT
            elif self.op == 'slte':
                bitwuzla_op = bitwuzla.Kind.BV_SLE
            elif self.op == 'ulte':
                bitwuzla_op = bitwuzla.Kind.BV_ULE
            self.bitwuzla = tm.mk_term(bitwuzla_op,
                [self.arg1_line.get_bitwuzla(tm), self.arg2_line.get_bitwuzla(tm)])
        return self.bitwuzla

class Logical(Binary):
    keywords = {'and', 'or', 'xor'}

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, comment, line_no):
        super().__init__(nid, op, sid_line, arg1_line, arg2_line, comment, line_no)
        if not isinstance(sid_line, Bitvector):
            raise model_error("Boolean or bitvector result", line_no)
        if not sid_line.match_sorts(arg1_line.sid_line):
            raise model_error("compatible result and first operand sorts", line_no)
        if not arg1_line.sid_line.match_sorts(arg2_line.sid_line):
            raise model_error("compatible first and second operand sorts", line_no)

    def get_z3(self):
        if self.z3 is None:
            if isinstance(self.sid_line, Bool):
                if self.op == 'and':
                    self.z3 = z3.And(self.arg1_line.get_z3(), self.arg2_line.get_z3())
                elif self.op == 'or':
                    self.z3 = z3.Or(self.arg1_line.get_z3(), self.arg2_line.get_z3())
                elif self.op == 'xor':
                    self.z3 = z3.Xor(self.arg1_line.get_z3(), self.arg2_line.get_z3())
            else:
                if self.op == 'and':
                    self.z3 = self.arg1_line.get_z3() & self.arg2_line.get_z3()
                elif self.op == 'or':
                    self.z3 = self.arg1_line.get_z3() | self.arg2_line.get_z3()
                elif self.op == 'xor':
                    self.z3 = self.arg1_line.get_z3() ^ self.arg2_line.get_z3()
        return self.z3

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            if isinstance(self.sid_line, Bool):
                if self.op == 'and':
                    bitwuzla_op = bitwuzla.Kind.AND
                elif self.op == 'or':
                    bitwuzla_op = bitwuzla.Kind.OR
                elif self.op == 'xor':
                    bitwuzla_op = bitwuzla.Kind.XOR
            else:
                if self.op == 'and':
                    bitwuzla_op = bitwuzla.Kind.BV_AND
                elif self.op == 'or':
                    bitwuzla_op = bitwuzla.Kind.BV_OR
                elif self.op == 'xor':
                    bitwuzla_op = bitwuzla.Kind.BV_XOR
            self.bitwuzla = tm.mk_term(bitwuzla_op,
                [self.arg1_line.get_bitwuzla(tm), self.arg2_line.get_bitwuzla(tm)])
        return self.bitwuzla

class Computation(Binary):
    keywords = {'sll', 'srl', 'sra', 'add', 'sub', 'mul', 'sdiv', 'udiv', 'srem', 'urem'}

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, comment, line_no):
        super().__init__(nid, op, sid_line, arg1_line, arg2_line, comment, line_no)
        if not isinstance(sid_line, Bitvec):
            raise model_error("bitvector result", line_no)
        if not sid_line.match_sorts(arg1_line.sid_line):
            raise model_error("compatible result and first operand sorts", line_no)
        if not arg1_line.sid_line.match_sorts(arg2_line.sid_line):
            raise model_error("compatible first and second operand sorts", line_no)

    def get_z3(self):
        if self.z3 is None:
            if self.op == 'sll':
                self.z3 = self.arg1_line.get_z3() << self.arg2_line.get_z3()
            elif self.op == 'srl':
                self.z3 = z3.LShR(self.arg1_line.get_z3(), self.arg2_line.get_z3())
            elif self.op == 'sra':
                self.z3 = self.arg1_line.get_z3() >> self.arg2_line.get_z3()
            elif self.op == 'add':
                self.z3 = self.arg1_line.get_z3() + self.arg2_line.get_z3()
            elif self.op == 'sub':
                self.z3 = self.arg1_line.get_z3() - self.arg2_line.get_z3()
            elif self.op == 'mul':
                self.z3 = self.arg1_line.get_z3() * self.arg2_line.get_z3()
            elif self.op == 'sdiv':
                self.z3 = self.arg1_line.get_z3() / self.arg2_line.get_z3()
            elif self.op == 'udiv':
                self.z3 = z3.UDiv(self.arg1_line.get_z3(), self.arg2_line.get_z3())
            elif self.op == 'srem':
                self.z3 = z3.SRem(self.arg1_line.get_z3(), self.arg2_line.get_z3())
            elif self.op == 'urem':
                self.z3 = z3.URem(self.arg1_line.get_z3(), self.arg2_line.get_z3())
        return self.z3

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            if self.op == 'sll':
                bitwuzla_op = bitwuzla.Kind.BV_SHL
            elif self.op == 'srl':
                bitwuzla_op = bitwuzla.Kind.BV_SHR
            elif self.op == 'sra':
                bitwuzla_op = bitwuzla.Kind.BV_ASHR
            elif self.op == 'add':
                bitwuzla_op = bitwuzla.Kind.BV_ADD
            elif self.op == 'sub':
                bitwuzla_op = bitwuzla.Kind.BV_SUB
            elif self.op == 'mul':
                bitwuzla_op = bitwuzla.Kind.BV_MUL
            elif self.op == 'sdiv':
                bitwuzla_op = bitwuzla.Kind.BV_SDIV
            elif self.op == 'udiv':
                bitwuzla_op = bitwuzla.Kind.BV_UDIV
            elif self.op == 'srem':
                bitwuzla_op = bitwuzla.Kind.BV_SREM
            elif self.op == 'urem':
                bitwuzla_op = bitwuzla.Kind.BV_UREM
            self.bitwuzla = tm.mk_term(bitwuzla_op,
                [self.arg1_line.get_bitwuzla(tm), self.arg2_line.get_bitwuzla(tm)])
        return self.bitwuzla

class Concat(Binary):
    keyword = 'concat'

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, comment, line_no):
        super().__init__(nid, op, sid_line, arg1_line, arg2_line, comment, line_no)
        if not isinstance(sid_line, Bitvec):
            raise model_error("bitvector result", line_no)
        if not isinstance(arg1_line.sid_line, Bitvec):
            raise model_error("bitvector first operand", line_no)
        if not isinstance(arg2_line.sid_line, Bitvec):
            raise model_error("bitvector second operand", line_no)
        if sid_line.size != arg1_line.sid_line.size + arg2_line.sid_line.size:
            raise model_error("compatible bitvector result", line_no)

    def get_z3(self):
        if self.z3 is None:
            self.z3 = z3.Concat(self.arg1_line.get_z3(), self.arg2_line.get_z3())
        return self.z3

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            self.bitwuzla = tm.mk_term(bitwuzla.Kind.BV_CONCAT,
                [self.arg1_line.get_bitwuzla(tm), self.arg2_line.get_bitwuzla(tm)])
        return self.bitwuzla

class Read(Binary):
    keyword = 'read'

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, comment, line_no):
        super().__init__(nid, op, sid_line, arg1_line, arg2_line, comment, line_no)
        if not isinstance(arg1_line.sid_line, Array):
            raise model_error("array first operand", line_no)
        if not arg1_line.sid_line.array_size_line.match_sorts(arg2_line.sid_line):
            raise model_error("compatible first operand array size and second operand sorts", line_no)
        if not sid_line.match_sorts(arg1_line.sid_line.element_size_line):
            raise model_error("compatible result and first operand element size sorts", line_no)

    def get_z3(self):
        if self.z3 is None:
            self.z3 = z3.Select(self.arg1_line.get_z3(), self.arg2_line.get_z3())
        return self.z3

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            self.bitwuzla = tm.mk_term(bitwuzla.Kind.ARRAY_SELECT,
                [self.arg1_line.get_bitwuzla(tm), self.arg2_line.get_bitwuzla(tm)])
        return self.bitwuzla

class Ternary(Expression):
    keywords = {'ite', 'write'}

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, arg3_line, comment, line_no):
        super().__init__(nid, sid_line, arg1_line.domain | arg2_line.domain | arg3_line.domain, comment, line_no)
        self.op = op
        self.arg1_line = arg1_line
        self.arg2_line = arg2_line
        self.arg3_line = arg3_line
        if not isinstance(arg1_line, Expression):
            raise model_error("expression first operand", line_no)
        if not isinstance(arg2_line, Expression):
            raise model_error("expression second operand", line_no)
        if not isinstance(arg3_line, Expression):
            raise model_error("expression third operand", line_no)

    def __str__(self):
        return f"{self.nid} {self.op} {self.sid_line.nid} {self.arg1_line.nid} {self.arg2_line.nid} {self.arg3_line.nid} {self.comment}"

class Ite(Ternary):
    keyword = 'ite'

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, arg3_line, comment, line_no):
        super().__init__(nid, op, sid_line, arg1_line, arg2_line, arg3_line, comment, line_no)
        if not isinstance(arg1_line.sid_line, Bool):
            raise model_error("Boolean first operand", line_no)
        if not sid_line.match_sorts(arg2_line.sid_line):
            raise model_error("compatible result and second operand sorts", line_no)
        if not arg2_line.sid_line.match_sorts(arg3_line.sid_line):
            raise model_error("compatible second and third operand sorts", line_no)

    def get_z3(self):
        if self.z3 is None:
            self.z3 = z3.If(self.arg1_line.get_z3(),
                self.arg2_line.get_z3(), self.arg3_line.get_z3())
        return self.z3

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            self.bitwuzla = tm.mk_term(bitwuzla.Kind.ITE,
                [self.arg1_line.get_bitwuzla(tm),
                self.arg2_line.get_bitwuzla(tm),
                self.arg3_line.get_bitwuzla(tm)])
        return self.bitwuzla

class Write(Ternary):
    keyword = 'write'

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, arg3_line, comment, line_no):
        super().__init__(nid, op, sid_line, arg1_line, arg2_line, arg3_line, comment, line_no)
        if not isinstance(sid_line, Array):
            raise model_error("array result", line_no)
        if not sid_line.match_sorts(arg1_line.sid_line):
            raise model_error("compatible result and first operand sorts", line_no)
        if not arg1_line.sid_line.array_size_line.match_sorts(arg2_line.sid_line):
            raise model_error("compatible first operand array size and second operand sorts", line_no)
        if not arg1_line.sid_line.element_size_line.match_sorts(arg3_line.sid_line):
            raise model_error("compatible first operand element size and third operand sorts", line_no)

    def get_z3(self):
        if self.z3 is None:
            self.z3 = z3.Store(self.arg1_line.get_z3(),
                self.arg2_line.get_z3(), self.arg3_line.get_z3())
        return self.z3

    def get_bitwuzla(self, tm):
        if self.bitwuzla is None:
            self.bitwuzla = tm.mk_term(bitwuzla.Kind.ARRAY_STORE,
                [self.arg1_line.get_bitwuzla(tm),
                self.arg2_line.get_bitwuzla(tm),
                self.arg3_line.get_bitwuzla(tm)])
        return self.bitwuzla

class Init(Line):
    keyword = 'init'

    inits = dict()

    def __init__(self, nid, sid_line, state_line, exp_line, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.sid_line = sid_line
        self.state_line = state_line
        self.exp_line = exp_line
        if not isinstance(sid_line, Sort):
            raise model_error("sort", line_no)
        if not isinstance(state_line, State):
            raise model_error("state left operand", line_no)
        if not isinstance(exp_line, Expression):
            raise model_error("expression right operand", line_no)
        if not self.sid_line.match_sorts(state_line.sid_line):
            raise model_error("compatible line and state sorts", line_no)
        if not state_line.sid_line.match_init_sorts(exp_line.sid_line):
            raise model_error("compatible state and expression sorts", line_no)
        if state_line.nid < exp_line.nid:
            raise model_error("state after expression", line_no)
        if self.state_line.init_line == self.state_line:
            self.state_line.init_line = self
        else:
            raise model_error("uninitialized state", line_no)
        self.new_init()

    def __str__(self):
        return f"{self.nid} {Init.keyword} {self.sid_line.nid} {self.state_line.nid} {self.exp_line.nid} {self.comment}"

    def new_init(self):
        assert self not in Init.inits
        Init.inits[self.nid] = self

    def set_z3(self, step):
        if self.z3 is None:
            if isinstance(self.sid_line, Array) and isinstance(self.exp_line.sid_line, Bitvec):
                # initialize with constant array
                self.z3 = self.state_line.get_z3_step(0) == z3.K(self.sid_line.array_size_line.get_z3(),
                    self.exp_line.get_z3())
            else:
                self.z3 = self.state_line.get_z3_step(0) == State.get_z3_select(State.get_z3_lambda(self.exp_line.get_z3()), 0)

    def set_bitwuzla(self, step, tm):
        if self.bitwuzla is None:
            if isinstance(self.sid_line, Array) and isinstance(self.exp_line.sid_line, Bitvec):
                # initialize with constant array
                self.bitwuzla = tm.mk_term(bitwuzla.Kind.EQUAL,
                    [self.state_line.get_bitwuzla_step(0, tm),
                    tm.mk_const_array(self.sid_line.get_bitwuzla(tm),
                        self.exp_line.get_bitwuzla(tm))])
            else:
                self.bitwuzla = tm.mk_term(bitwuzla.Kind.EQUAL,
                    [self.state_line.get_bitwuzla_step(0, tm), State.get_bitwuzla_select(State.get_bitwuzla_lambda(self.exp_line.get_bitwuzla(tm), tm), 0, tm)])

class Next(Line):
    keyword = 'next'

    nexts = dict()

    def __init__(self, nid, sid_line, state_line, exp_line, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.sid_line = sid_line
        self.state_line = state_line
        self.exp_line = exp_line
        self.z3_lambda_line = None
        self.bitwuzla_lambda_line = None
        if not isinstance(sid_line, Sort):
            raise model_error("sort", line_no)
        if not isinstance(state_line, State):
            raise model_error("state left operand", line_no)
        if not isinstance(exp_line, Expression):
            raise model_error("expression right operand", line_no)
        if not self.sid_line.match_sorts(state_line.sid_line):
            raise model_error("compatible line and state sorts", line_no)
        if not state_line.sid_line.match_sorts(exp_line.sid_line):
            raise model_error("compatible state and expression sorts", line_no)
        if self.state_line.next_line == self.state_line:
            self.state_line.next_line = self
        else:
            raise model_error("untransitioned state", line_no)
        self.new_next()

    def __str__(self):
        return f"{self.nid} {Next.keyword} {self.sid_line.nid} {self.state_line.nid} {self.exp_line.nid} {self.comment}"

    def new_next(self):
        assert self not in Next.nexts
        Next.nexts[self.nid] = self

    def set_z3(self, step):
        if self.z3_lambda_line is None:
            self.z3_lambda_line = State.get_z3_lambda(self.exp_line.get_z3())
        self.z3 = self.state_line.get_z3_step(step + 1) == State.get_z3_select(self.z3_lambda_line, step)

    def set_bitwuzla(self, step, tm):
        if self.bitwuzla_lambda_line is None:
            self.bitwuzla_lambda_line = State.get_bitwuzla_lambda(self.exp_line.get_bitwuzla(tm), tm)
        self.bitwuzla = tm.mk_term(bitwuzla.Kind.EQUAL,
            [self.state_line.get_bitwuzla_step(step + 1, tm),
                State.get_bitwuzla_select(self.bitwuzla_lambda_line, step, tm)])

class Property(Line):
    keywords = {'constraint', 'bad'}

    def __init__(self, nid, property_line, symbol, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.property_line = property_line
        self.symbol = symbol
        self.z3_lambda_line = None
        self.bitwuzla_lambda_line = None
        if not isinstance(property_line, Expression):
            raise model_error("expression operand", line_no)
        if not isinstance(property_line.sid_line, Bool):
            raise model_error("Boolean operand", line_no)

    def set_z3(self, step):
        if self.z3_lambda_line is None:
            self.z3_lambda_line = State.get_z3_lambda(self.property_line.get_z3())
        self.z3 = State.get_z3_select(self.z3_lambda_line, step)

    def set_bitwuzla(self, step, tm):
        if self.bitwuzla_lambda_line is None:
            self.bitwuzla_lambda_line = State.get_bitwuzla_lambda(self.property_line.get_bitwuzla(tm), tm)
        self.bitwuzla = State.get_bitwuzla_select(self.bitwuzla_lambda_line, step, tm)

class Constraint(Property):
    keyword = 'constraint'

    constraints = dict()

    def __init__(self, nid, property_line, symbol, comment, line_no):
        super().__init__(nid, property_line, symbol, comment, line_no)
        self.new_constraint()

    def __str__(self):
        return f"{self.nid} {Constraint.keyword} {self.property_line.nid} {self.symbol} {self.comment}"

    def new_constraint(self):
        assert self not in Constraint.constraints
        Constraint.constraints[self.nid] = self

class Bad(Property):
    keyword = 'bad'

    bads = dict()

    def __init__(self, nid, property_line, symbol, comment, line_no):
        super().__init__(nid, property_line, symbol, comment, line_no)
        self.new_bad()

    def __str__(self):
        return f"{self.nid} {Bad.keyword} {self.property_line.nid} {self.symbol} {self.comment}"

    def new_bad(self):
        assert self not in Bad.bads
        Bad.bads[self.nid] = self

def get_class(keyword):
    if keyword == Zero.keyword:
        return Zero
    elif keyword == One.keyword:
        return One
    elif keyword == Constd.keyword:
        return Constd
    elif keyword == Const.keyword:
        return Const
    elif keyword == Consth.keyword:
        return Consth
    elif keyword == Input.keyword:
        return Input
    elif keyword == State.keyword:
        return State
    elif keyword in Ext.keywords:
        return Ext
    elif keyword == Slice.keyword:
        return Slice
    elif keyword in Unary.keywords:
        return Unary
    elif keyword == Implies.keyword:
        return Implies
    elif keyword in Comparison.keywords:
        return Comparison
    elif keyword in Logical.keywords:
        return Logical
    elif keyword in Computation.keywords:
        return Computation
    elif keyword == Concat.keyword:
        return Concat
    elif keyword == Read.keyword:
        return Read
    elif keyword == Ite.keyword:
        return Ite
    elif keyword == Write.keyword:
        return Write
    elif keyword == Init.keyword:
        return Init
    elif keyword == Next.keyword:
        return Next
    elif keyword == Constraint.keyword:
        return Constraint
    elif keyword == Bad.keyword:
        return Bad

import re

class syntax_error(Exception):
    def __init__(self, expected, line_no):
        super().__init__(f"syntax error in line {line_no}: {expected} expected")

def tokenize_btor2(line):
    # comment, non-comment no-space printable string,
    # signed integer, binary number, hexadecimal number
    btor2_token_pattern = r"(;.*|[^; \n\r]+|-?\d+|[0-1]|[0-9a-fA-F]+)"
    tokens = re.findall(btor2_token_pattern, line)
    return tokens

def get_token(tokens, expected, line_no):
    try:
        return tokens.pop(0)
    except:
        raise syntax_error(expected, line_no)

def get_decimal(tokens, expected, line_no):
    token = get_token(tokens, expected, line_no)
    if token.isdecimal():
        return int(token)
    else:
        raise syntax_error(expected, line_no)

def get_nid_line(tokens, clss, expected, line_no):
    nid = get_decimal(tokens, expected, line_no)
    if Line.is_defined(nid):
        line = Line.get(nid)
        if isinstance(line, clss):
            return line
        else:
            raise syntax_error(expected, line_no)
    else:
        raise syntax_error(f"defined {expected}", line_no)

def get_bool_or_bitvec_sid_line(tokens, line_no):
    return get_nid_line(tokens, Bitvector, "Boolean or bitvector sort nid", line_no)

def get_bitvec_sid_line(tokens, line_no):
    return get_nid_line(tokens, Bitvec, "bitvector sort nid", line_no)

def get_sid_line(tokens, line_no):
    return get_nid_line(tokens, Sort, "sort nid", line_no)

def get_state_line(tokens, line_no):
    return get_nid_line(tokens, State, "state nid", line_no)

def get_exp_line(tokens, line_no):
    return get_nid_line(tokens, Expression, "expression nid", line_no)

def get_number(tokens, base, expected, line_no):
    token = get_token(tokens, expected, line_no)
    try:
        if (base == 10):
            return int(token)
        else:
            return int(token, base)
    except ValueError:
        raise syntax_error(expected, line_no)

def get_symbol(tokens):
    try:
        return get_token(tokens, None, None)
    except:
        return ""

def get_comment(tokens, line_no):
    comment = get_symbol(tokens)
    if comment != "":
        if comment[0] != ';':
            raise syntax_error("comment", line_no)
    return comment

def parse_sort_line(tokens, nid, line_no):
    token = get_token(tokens, "bitvector or array", line_no)
    if token == Bitvec.keyword:
        size = get_decimal(tokens, "bitvector size", line_no)
        comment = get_comment(tokens, line_no)
        # rotor-dependent Boolean declaration
        if comment == "; Boolean" and size == 1:
            return Bool(nid, comment, line_no)
        else:
            return Bitvec(nid, size, comment, line_no)
    elif token == Array.keyword:
        array_size_line = get_bitvec_sid_line(tokens, line_no)
        element_size_line = get_bitvec_sid_line(tokens, line_no)
        comment = get_comment(tokens, line_no)
        return Array(nid, array_size_line, element_size_line, comment, line_no)
    else:
        raise syntax_error("bitvector or array", line_no)

def parse_zero_one_line(tokens, nid, op, line_no):
    sid_line = get_bool_or_bitvec_sid_line(tokens, line_no)
    comment = get_comment(tokens, line_no)
    return get_class(op)(nid, sid_line, comment, line_no)

def parse_constant_line(tokens, nid, op, line_no):
    sid_line = get_bool_or_bitvec_sid_line(tokens, line_no)
    if op == Constd.keyword:
        value = get_number(tokens, 10, "signed integer", line_no)
    elif op == Const.keyword:
        value = get_number(tokens, 2, "binary number", line_no)
    elif op == Consth.keyword:
        value = get_number(tokens, 16, "hexadecimal number", line_no)
    comment = get_comment(tokens, line_no)
    return get_class(op)(nid, sid_line, value, comment, line_no)

def parse_symbol_comment(tokens, line_no):
    symbol = get_symbol(tokens)
    comment = get_comment(tokens, line_no)
    if symbol != "":
        if symbol[0] == ';':
            return "", symbol
    return symbol, comment

def parse_variable_line(tokens, nid, op, line_no):
    sid_line = get_sid_line(tokens, line_no)
    symbol, comment = parse_symbol_comment(tokens, line_no)
    return get_class(op)(nid, sid_line, symbol, comment, line_no)

def parse_ext_line(tokens, nid, op, line_no):
    sid_line = get_sid_line(tokens, line_no)
    arg1_line = get_exp_line(tokens, line_no)
    w = get_decimal(tokens, "bit width", line_no)
    comment = get_comment(tokens, line_no)
    return Ext(nid, op, sid_line, arg1_line, w, comment, line_no)

def parse_slice_line(tokens, nid, line_no):
    sid_line = get_sid_line(tokens, line_no)
    arg1_line = get_exp_line(tokens, line_no)
    u = get_decimal(tokens, "upper bit", line_no)
    l = get_decimal(tokens, "lower bit", line_no)
    comment = get_comment(tokens, line_no)
    return Slice(nid, sid_line, arg1_line, u, l, comment, line_no)

def parse_unary_line(tokens, nid, op, line_no):
    sid_line = get_sid_line(tokens, line_no)
    arg1_line = get_exp_line(tokens, line_no)
    comment = get_comment(tokens, line_no)
    return Unary(nid, op, sid_line, arg1_line, comment, line_no)

def parse_binary_line(tokens, nid, op, line_no):
    sid_line = get_sid_line(tokens, line_no)
    arg1_line = get_exp_line(tokens, line_no)
    arg2_line = get_exp_line(tokens, line_no)
    comment = get_comment(tokens, line_no)
    return get_class(op)(nid, op, sid_line, arg1_line, arg2_line, comment, line_no)

def parse_ternary_line(tokens, nid, op, line_no):
    sid_line = get_sid_line(tokens, line_no)
    arg1_line = get_exp_line(tokens, line_no)
    arg2_line = get_exp_line(tokens, line_no)
    arg3_line = get_exp_line(tokens, line_no)
    comment = get_comment(tokens, line_no)
    return get_class(op)(nid, op, sid_line, arg1_line, arg2_line, arg3_line, comment, line_no)

def parse_init_next_line(tokens, nid, op, line_no):
    sid_line = get_sid_line(tokens, line_no)
    state_line = get_state_line(tokens, line_no)
    exp_line = get_exp_line(tokens, line_no)
    comment = get_comment(tokens, line_no)
    return get_class(op)(nid, sid_line, state_line, exp_line, comment, line_no)

def parse_property_line(tokens, nid, op, line_no):
    property_line = get_exp_line(tokens, line_no)
    symbol, comment = parse_symbol_comment(tokens, line_no)
    return get_class(op)(nid, property_line, symbol, comment, line_no)

current_nid = 0

def parse_btor2_line(line, line_no):
    global current_nid
    if line.strip():
        tokens = tokenize_btor2(line)
        token = get_token(tokens, None, None)
        if token[0] != ';':
            if token.isdecimal():
                nid = int(token)
                if nid > current_nid:
                    current_nid = nid
                    token = get_token(tokens, "keyword", line_no)
                    if token == Sort.keyword:
                        return parse_sort_line(tokens, nid, line_no)
                    elif token in {Zero.keyword, One.keyword}:
                        return parse_zero_one_line(tokens, nid, token, line_no)
                    elif token in {Constd.keyword, Const.keyword, Consth.keyword}:
                        return parse_constant_line(tokens, nid, token, line_no)
                    elif token in Variable.keywords:
                        return parse_variable_line(tokens, nid, token, line_no)
                    elif token in Ext.keywords:
                        return parse_ext_line(tokens, nid, token, line_no)
                    elif token == Slice.keyword:
                        return parse_slice_line(tokens, nid, line_no)
                    elif token in Unary.keywords:
                        return parse_unary_line(tokens, nid, token, line_no)
                    elif token in Binary.keywords:
                        return parse_binary_line(tokens, nid, token, line_no)
                    elif token in Ternary.keywords:
                        return parse_ternary_line(tokens, nid, token, line_no)
                    elif token in {Init.keyword, Next.keyword}:
                        return parse_init_next_line(tokens, nid, token, line_no)
                    elif token in Property.keywords:
                        return parse_property_line(tokens, nid, token, line_no)
                    else:
                        raise syntax_error(f"unknown operator {token}", line_no)
                raise syntax_error("increasing nid", line_no)
            raise syntax_error("nid", line_no)
    return line.strip()

def parse_btor2(modelfile):
    line_no = 1
    for line in modelfile:
        try:
            parse_btor2_line(line, line_no)
            line_no += 1
        except Exception as message:
            print(message)
            exit(1)

    for state in State.states.values():
        if state.init_line == state:
            # state has no init
            state.new_input()

def new_problem(set_solver):
    for init in Init.inits.values():
        set_solver(init)
    for constraint in Constraint.constraints.values():
        set_solver(constraint)
    for bad in Bad.bads.values():
        set_solver(bad)
    for next_line in Next.nexts.values():
        set_solver(next_line)

def new_z3():
    new_problem(lambda line: line.set_z3(0))

def new_bitwuzla(tm):
    new_problem(lambda line: line.set_bitwuzla(0, tm))

def bmc_z3(kmin, kmax, print_pc):
    s = z3.Solver()

    for init in Init.inits.values():
        s.add(init.z3)

    step = 0

    while step <= kmax:
        print(step)

        if print_pc and State.pc:
            s.check()
            m = s.model()
            for d in m.decls():
                if str(State.pc.next_line.current_step) in str(d.name()):
                    pc = int(m[d].as_long())
                    print(State.pc.next_line.state_line)
                    print("%s = 0x%X" % (d.name(), pc))

        for constraint in Constraint.constraints.values():
            s.add(constraint.z3)

        if step >= kmin:
            for bad in Bad.bads.values():
                s.push()
                s.add(bad.z3)
                result = s.check()
                if result == z3.sat:
                    print("v" * 80)
                    print(f"sat: {bad}")
                    m = s.model()
                    for input_variable in Variable.inputs.values():
                        # only print value of uninitialized states
                        print(input_variable)
                        i = sorted([(d.name(), m[d])
                            for d in m.decls() if str(input_variable.z3) in str(d.name())])
                        if i is not None:
                            print("%s = %s" % (i[0][0], i[0][1]))
                    print("^" * 80)
                s.pop()
                if result == z3.unsat:
                    s.add(bad.z3 == False)
        else:
            for bad in Bad.bads.values():
                s.add(bad.z3 == False)

        for next_line in Next.nexts.values():
            s.add(next_line.z3)

        for constraint in Constraint.constraints.values():
            constraint.set_z3(step + 1)
        for bad in Bad.bads.values():
            bad.set_z3(step + 1)
        for next_line in Next.nexts.values():
            next_line.set_z3(step + 1)

        step += 1

def bmc_bitwuzla(tm, options, kmin, kmax, print_pc):
    s = bitwuzla.Bitwuzla(tm, options)

    for init in Init.inits.values():
        s.assert_formula(init.bitwuzla)

    step = 0

    while step <= kmax:
        print(step)

        if print_pc and State.pc:
            s.check_sat()
            pc = int(s.get_value(State.pc.next_line.current_step).value(16), 16)
            print(State.pc.next_line.state_line)
            print("%s = 0x%X" % (State.pc.next_line.current_step, pc))

        for constraint in Constraint.constraints.values():
            s.assert_formula(constraint.bitwuzla)

        if step >= kmin:
            for bad in Bad.bads.values():
                result = s.check_sat(bad.bitwuzla)
                if result is bitwuzla.Result.SAT:
                    print("v" * 80)
                    print(f"sat: {bad}")
                    for input_variable in Variable.inputs.values():
                        # only print value of uninitialized states
                        print(input_variable)
                        print("%s = %s" % (input_variable.get_bitwuzla_step(step, tm),
                            s.get_value(input_variable.get_bitwuzla_step(step, tm))))
                    print("^" * 80)
                elif result is bitwuzla.Result.UNSAT:
                    s.assert_formula(tm.mk_term(bitwuzla.Kind.NOT, [bad.bitwuzla]))
        else:
            for bad in Bad.bads.values():
                s.assert_formula(tm.mk_term(bitwuzla.Kind.NOT, [bad.bitwuzla]))

        for next_line in Next.nexts.values():
            s.assert_formula(next_line.bitwuzla)

        for constraint in Constraint.constraints.values():
            constraint.set_bitwuzla(step + 1, tm)
        for bad in Bad.bads.values():
            bad.set_bitwuzla(step + 1, tm)
        for next_line in Next.nexts.values():
            next_line.set_bitwuzla(step + 1, tm)

        step += 1

import argparse

def main():
    parser = argparse.ArgumentParser(prog='bitme',
        description="What the program does",
        epilog="Text at the bottom of help")

    parser.add_argument('modelfile')

    parser.add_argument('-kmin', nargs=1, type=int)
    parser.add_argument('-kmax', nargs=1, type=int)

    parser.add_argument('--print-pc', action='store_true')

    args = parser.parse_args()

    with open(args.modelfile) as modelfile:
        parse_btor2(modelfile)

    if args.kmin or args.kmax:
        kmin = args.kmin[0] if args.kmin else 0
        kmax = args.kmax[0] if args.kmax else 0

        kmax = max(kmin, kmax)

        use_Z3 = True

        if is_Z3_present and use_Z3:
            new_z3()
            bmc_z3(kmin, kmax, args.print_pc)

        if is_bitwuzla_present:
            tm = bitwuzla.TermManager()
            options = bitwuzla.Options()
            options.set(bitwuzla.Option.PRODUCE_MODELS, True)

            new_bitwuzla(tm)
            bmc_bitwuzla(tm, options, kmin, kmax, args.print_pc)

if __name__ == '__main__':
    main()