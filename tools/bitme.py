#!/usr/bin/env python3

from z3 import *

import math

class model_error(Exception):
    def __init__(self, expected, line_no):
        super().__init__(f"model error in line {line_no}: {expected} expected")

class Line:
    lines = dict()

    def __init__(self, nid, comment, line_no):
        self.nid = nid
        self.comment = comment
        self.line_no = line_no
        self.new_line()

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
    defined = False

    def __init__(self, nid, comment, line_no):
        super().__init__(nid, 1, comment, line_no)
        self.z3 = z3.BoolSort()
        Bool.defined = True

    def match_sorts(self, sort):
        return super().match_sorts(sort)

class Bitvec(Bitvector):
    def __init__(self, nid, size, comment, line_no):
        super().__init__(nid, size, comment, line_no)
        self.z3 = z3.BitVecSort(size)

    def match_sorts(self, sort):
        return super().match_sorts(sort) and self.size == sort.size

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
        self.z3 = z3.ArraySort(array_size_line.z3, element_size_line.z3)

    def __str__(self):
        return f"{self.nid} {Sort.keyword} {Array.keyword} {self.array_size_line.nid} {self.element_size_line.nid} {self.comment}"

    def match_sorts(self, sort):
        return super().match_sorts(sort) and self.array_size_line.match_sorts(sort.array_size_line) and self.element_size_line.match_sorts(sort.element_size_line)

    def match_init_sorts(self, sort):
        return self.match_sorts(sort) or (isinstance(sort, Bitvec) and self.element_size_line.match_sorts(sort))

class Expression(Line):
    def __init__(self, nid, sid_line, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.sid_line = sid_line
        if not isinstance(sid_line, Sort):
            raise model_error("sort", line_no)

class Constant(Expression):
    def __init__(self, nid, sid_line, value, comment, line_no):
        super().__init__(nid, sid_line, comment, line_no)
        self.value = value
        if value >= 2**sid_line.size:
            raise model_error(f"{value} in range of {sid_line.size}-bit bitvector", line_no)
        if isinstance(sid_line, Bool):
            self.z3 = z3.BoolVal(bool(value))
        else:
            self.z3 = z3.BitVecVal(value, sid_line.size)

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

    def __init__(self, nid, sid_line, symbol, comment, line_no):
        super().__init__(nid, sid_line, comment, line_no)
        self.symbol = symbol

class Input(Variable):
    keyword = 'input'

    def __init__(self, nid, sid_line, symbol, comment, line_no):
        super().__init__(nid, sid_line, symbol, comment, line_no)
        self.z3 = z3.Const(f"input{nid}", sid_line.z3)

    def __str__(self):
        return f"{self.nid} {Input.keyword} {self.sid_line.nid} {self.symbol} {self.comment}"

class State(Variable):
    keyword = 'state'

    states = dict()

    def __init__(self, nid, sid_line, symbol, comment, line_no):
        super().__init__(nid, sid_line, symbol, comment, line_no)
        self.init_line = self
        self.next_line = self
        self.z3 = z3.Const(f"state{nid}", sid_line.z3)
        self.new_state()

    def __str__(self):
        return f"{self.nid} {State.keyword} {self.sid_line.nid} {self.symbol} {self.comment}"

    def new_state(self):
        assert self not in State.states
        State.states[self.nid] = self

class Indexed(Expression):
    def __init__(self, nid, sid_line, arg1_line, comment, line_no):
        super().__init__(nid, sid_line, comment, line_no)
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
        if op == 'sext':
            self.z3 = z3.SignExt(w, arg1_line.z3)
        elif op == 'uext':
            self.z3 = z3.ZeroExt(w, arg1_line.z3)

    def __str__(self):
        return f"{self.nid} {self.op} {self.sid_line.nid} {self.arg1_line.nid} {self.w} {self.comment}"

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
        self.z3 = z3.Extract(u, l, arg1_line.z3)

    def __str__(self):
        return f"{self.nid} {Slice.keyword} {self.sid_line.nid} {self.arg1_line.nid} {self.u} {self.l} {self.comment}"

class Unary(Expression):
    keywords = {'not', 'inc', 'dec', 'neg'}

    def __init__(self, nid, op, sid_line, arg1_line, comment, line_no):
        super().__init__(nid, sid_line, comment, line_no)
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
        if op == 'not':
            if isinstance(sid_line, Bool):
                self.z3 = z3.Not(arg1_line.z3)
            else:
                self.z3 = ~arg1_line.z3
        elif op == 'inc':
            self.z3 = arg1_line.z3 + 1
        elif op == 'dec':
            self.z3 = arg1_line.z3 - 1
        elif op == 'neg':
            self.z3 = -arg1_line.z3

    def __str__(self):
        return f"{self.nid} {self.op} {self.sid_line.nid} {self.arg1_line.nid} {self.comment}"

class Binary(Expression):
    keywords = {'implies', 'eq', 'neq', 'sgt', 'ugt', 'sgte', 'ugte', 'slt', 'ult', 'slte', 'ulte', 'and', 'or', 'xor', 'sll', 'srl', 'sra', 'add', 'sub', 'mul', 'sdiv', 'udiv', 'srem', 'urem', 'concat', 'read'}

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, comment, line_no):
        super().__init__(nid, sid_line, comment, line_no)
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
        self.z3 = z3.Implies(arg1_line.z3, arg2_line.z3)

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
        if op == 'eq':
            self.z3 = arg1_line.z3 == arg2_line.z3
        elif op == 'neq':
            self.z3 = arg1_line.z3 != arg2_line.z3
        elif op == 'sgt':
            self.z3 = arg1_line.z3 > arg2_line.z3
        elif op == 'ugt':
            self.z3 = z3.UGT(arg1_line.z3, arg2_line.z3)
        elif op == 'sgte':
            self.z3 = arg1_line.z3 >= arg2_line.z3
        elif op == 'ugte':
            self.z3 = z3.UGE(arg1_line.z3, arg2_line.z3)
        elif op == 'slt':
            self.z3 = arg1_line.z3 < arg2_line.z3
        elif op == 'ult':
            self.z3 = z3.ULT(arg1_line.z3, arg2_line.z3)
        elif op == 'slte':
            self.z3 = arg1_line.z3 <= arg2_line.z3
        elif op == 'ulte':
            self.z3 = z3.ULE(arg1_line.z3, arg2_line.z3)

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
        if isinstance(sid_line, Bool):
            if op == 'and':
                self.z3 = z3.And(arg1_line.z3, arg2_line.z3)
            elif op == 'or':
                self.z3 = z3.Or(arg1_line.z3, arg2_line.z3)
            elif op == 'xor':
                self.z3 = z3.Xor(arg1_line.z3, arg2_line.z3)
        else:
            if op == 'and':
                self.z3 = arg1_line.z3 & arg2_line.z3
            elif op == 'or':
                self.z3 = arg1_line.z3 | arg2_line.z3
            elif op == 'xor':
                self.z3 = arg1_line.z3 ^ arg2_line.z3

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
        if op == 'sll':
            self.z3 = arg1_line.z3 << arg2_line.z3
        elif op == 'srl':
            self.z3 = z3.LShR(arg1_line.z3, arg2_line.z3)
        elif op == 'sra':
            self.z3 = arg1_line.z3 >> arg2_line.z3
        elif op == 'add':
            self.z3 = arg1_line.z3 + arg2_line.z3
        elif op == 'sub':
            self.z3 = arg1_line.z3 - arg2_line.z3
        elif op == 'mul':
            self.z3 = arg1_line.z3 * arg2_line.z3
        elif op == 'sdiv':
            self.z3 = arg1_line.z3 / arg2_line.z3
        elif op == 'udiv':
            self.z3 = z3.UDiv(arg1_line.z3, arg2_line.z3)
        elif op == 'srem':
            self.z3 = z3.SRem(arg1_line.z3, arg2_line.z3)
        elif op == 'urem':
            self.z3 = z3.URem(arg1_line.z3, arg2_line.z3)

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
        self.z3 = z3.Concat(arg1_line.z3, arg2_line.z3)

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
        self.z3 = z3.Select(arg1_line.z3, arg2_line.z3)

class Ternary(Expression):
    keywords = {'ite', 'write'}

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, arg3_line, comment, line_no):
        super().__init__(nid, sid_line, comment, line_no)
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
        self.z3 = z3.If(arg1_line.z3, arg2_line.z3, arg3_line.z3)

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
        self.z3 = z3.Store(arg1_line.z3, arg2_line.z3, arg3_line.z3)

class Init(Line):
    keyword = 'init'

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
        if not state_line.sid_line.match_init_sorts(exp_line.sid_line):
            raise model_error("compatible sorts", line_no)
        if self.state_line.init_line == self.state_line:
            self.state_line.init_line = self
        else:
            raise model_error("uninitialized state", line_no)

    def __str__(self):
        return f"{self.nid} {Init.keyword} {self.sid_line.nid} {self.state_line.nid} {self.exp_line.nid} {self.comment}"

class Next(Line):
    keyword = 'next'

    nexts = dict()

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
        if not state_line.sid_line.match_sorts(exp_line.sid_line):
            raise model_error("compatible sorts", line_no)
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

class Property(Line):
    keywords = {'constraint', 'bad'}

    def __init__(self, nid, property_line, symbol, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.property_line = property_line
        self.symbol = symbol
        if not isinstance(property_line, Expression):
            raise model_error("expression operand", line_no)
        if not isinstance(property_line.sid_line, Bool):
            raise model_error("Boolean operand", line_no)

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
        if not Bool.defined and size == 1:
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

import argparse

def main():
    parser = argparse.ArgumentParser(prog='bitme',
        description="What the program does",
        epilog="Text at the bottom of help")

    parser.add_argument('modelfile')

    args = parser.parse_args()

    with open(args.modelfile) as modelfile:
        line_no = 1
        for line in modelfile:
            try:
                print(parse_btor2_line(line, line_no))
                line_no = line_no + 1
            except Exception as message:
                print(message)
                exit(1)

if __name__ == '__main__':
    main()