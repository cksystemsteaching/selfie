#!/usr/bin/env python3

# Copyright (c) the Selfie Project authors. All rights reserved.
# Please see the AUTHORS file for details. Use of this source code is
# governed by a BSD license that can be found in the LICENSE file.

# Selfie is a project of the Computational Systems Group at the
# Department of Computer Sciences of the University of Salzburg
# in Austria. For further information and code please refer to:

# selfie.cs.uni-salzburg.at

# BTOR2 parser

# ------------------------------------------------------------

import math

# supported BTOR2 keywords and operators

def init_btor2_keywords_operators():
    global BITVEC
    global ARRAY

    global OP_SORT

    global OP_ZERO
    global OP_ONE

    global OP_CONST
    global OP_CONSTD
    global OP_CONSTH
    global OP_INPUT
    global OP_STATE

    global OP_INIT
    global OP_NEXT

    global OP_SEXT
    global OP_UEXT
    global OP_SLICE

    global OP_NOT
    global OP_INC
    global OP_DEC
    global OP_NEG

    global OP_IMPLIES
    global OP_EQ
    global OP_NEQ
    global OP_SGT
    global OP_UGT
    global OP_SGTE
    global OP_UGTE
    global OP_SLT
    global OP_ULT
    global OP_SLTE
    global OP_ULTE

    global OP_AND
    global OP_OR
    global OP_XOR

    global OP_SLL
    global OP_SRL
    global OP_SRA

    global OP_ADD
    global OP_SUB
    global OP_MUL
    global OP_SDIV
    global OP_UDIV
    global OP_SREM
    global OP_UREM

    global OP_CONCAT
    global OP_READ

    global OP_ITE
    global OP_WRITE

    global OP_BAD
    global OP_CONSTRAINT

    BITVEC = 'bitvec'
    ARRAY  = 'array'

    OP_SORT = 'sort'

    OP_ZERO = 'zero'
    OP_ONE  = 'one'

    OP_CONST  = 'const'
    OP_CONSTD = 'constd'
    OP_CONSTH = 'consth'
    OP_INPUT  = 'input'
    OP_STATE  = 'state'

    OP_INIT  = 'init'
    OP_NEXT  = 'next'

    OP_SEXT  = 'sext'
    OP_UEXT  = 'uext'
    OP_SLICE = 'slice'

    OP_NOT = 'not'
    OP_INC = 'inc'
    OP_DEC = 'dec'
    OP_NEG = 'neg'

    OP_IMPLIES = 'implies'
    OP_EQ      = 'eq'
    OP_NEQ     = 'neq'
    OP_SGT     = 'sgt'
    OP_UGT     = 'ugt'
    OP_SGTE    = 'sgte'
    OP_UGTE    = 'ugte'
    OP_SLT     = 'slt'
    OP_ULT     = 'ult'
    OP_SLTE    = 'slte'
    OP_ULTE    = 'ulte'

    OP_AND = 'and'
    OP_OR  = 'or'
    OP_XOR = 'xor'

    OP_SLL = 'sll'
    OP_SRL = 'srl'
    OP_SRA = 'sra'

    OP_ADD  = 'add'
    OP_SUB  = 'sub'
    OP_MUL  = 'mul'
    OP_SDIV = 'sdiv'
    OP_UDIV = 'udiv'
    OP_SREM = 'srem'
    OP_UREM = 'urem'

    OP_CONCAT = 'concat'
    OP_READ   = 'read'

    OP_ITE   = 'ite'
    OP_WRITE = 'write'

    OP_BAD        = 'bad'
    OP_CONSTRAINT = 'constraint'

init_btor2_keywords_operators()

class model_error(Exception):
    def __init__(self, expected, line_no):
        super().__init__(f"model error in line {line_no}: {expected} expected")

class Line:
    lines = {}

    count = 0

    def __init__(self, nid, comment, line_no):
        self.nid = nid
        self.comment = "; " + comment if comment and comment[0] != ';' else comment
        self.line_no = line_no
        self.new_line()

    def __repr__(self):
        return self.__str__()

    def new_line(self):
        if self.nid is not None:
            assert self.nid not in Line.lines, f"nid {self.nid} already defined @ {self.line_no}"
            Line.lines[self.nid] = self
        type(self).count += 1

    def is_defined(nid):
        return nid in Line.lines

    def get(nid):
        assert Line.is_defined(nid), f"undefined nid {self.nid} @ {self.line_no}"
        return Line.lines[nid]

class Sort(Line):
    keyword = OP_SORT

    def __init__(self, nid, comment, line_no):
        super().__init__(nid, comment, line_no)

    def match_sorts(self, sort):
        return type(self) is type(sort)

class Bitvector(Sort):
    keyword = BITVEC

    def __init__(self, nid, size, comment, line_no):
        assert size > 0
        super().__init__(nid, comment, line_no)
        self.size = size

    def __str__(self):
        return f"{self.nid} {Sort.keyword} {Bitvec.keyword} {self.size} {self.comment}"

    def match_init_sorts(self, sort):
        return self.match_sorts(sort)

    def is_mapped_array(self):
        return False

    def is_unsigned_value(self, value):
        return 0 <= value < 2**self.size

    def is_signed_value(self, value):
        return -2**(self.size - 1) <= value < 2**(self.size - 1)

    def is_value(self, value):
        return self.is_unsigned_value(value) or self.is_signed_value(value)

    def get_unsigned_value(self, value):
        assert self.is_value(value)
        return 2**self.size + value if value < 0 else value

    def get_signed_value(self, value):
        assert self.is_value(value)
        return value - 2**self.size if value >= 2**(self.size - 1) else value

class Bool(Bitvector):
    boolean = None

    def __init__(self, nid, comment, line_no):
        super().__init__(nid, 1, comment, line_no)
        assert Bool.boolean is None
        Bool.boolean = self

class Bitvec(Bitvector):
    def __init__(self, nid, size, comment, line_no):
        super().__init__(nid, size, comment, line_no)

    def match_sorts(self, sort):
        return super().match_sorts(sort) and self.size == sort.size

class Array(Sort):
    keyword = ARRAY

    # map arrays up to size bound to bitvectors

    ARRAY_SIZE_BOUND = 0 # array size in bits

    number_of_variable_arrays = 0
    number_of_mapped_arrays = 0

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

    def is_mapped_array(self):
        return self.array_size_line.size <= Array.ARRAY_SIZE_BOUND

    def accommodate_array_indexes(nid):
        if Array.ARRAY_SIZE_BOUND == 0:
            return nid
        else:
            # shift left by log10(2**n + 1) decimal digits where n is the array index space
            return nid * 10**(math.floor(math.log10(2**Array.ARRAY_SIZE_BOUND + 1)) + 1)

class Expression(Line):
    total_number_of_generated_expressions = 0

    def __init__(self, nid, sid_line, domain, depth, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.sid_line = sid_line
        self.domain = domain
        self.depth = depth
        if not isinstance(sid_line, Sort):
            raise model_error("sort", line_no)

    def print_deep(self):
        print(self)

    def get_domain(self):
        # filter out uninitialized states
        return [state for state in self.domain if state.init_line is not None]

class Constant(Expression):
    def __init__(self, nid, sid_line, value, comment, line_no):
        super().__init__(nid, sid_line, {}, 0, comment, line_no)
        if not sid_line.is_value(value):
            raise model_error(f"{value} in range of {sid_line.size}-bit bitvector", line_no)
        self.print_value = value
        self.signed_value = sid_line.get_signed_value(value)
        self.value = sid_line.get_unsigned_value(value)

    def print_deep(self):
        print(self)

    def get_mapped_array_expression_for(self, index):
        return self

class Zero(Constant):
    keyword = OP_ZERO

    def __init__(self, nid, sid_line, symbol, comment, line_no):
        super().__init__(nid, sid_line, 0, comment, line_no)
        self.symbol = symbol

    def __str__(self):
        if self.symbol:
            return f"{self.nid} {Zero.keyword} {self.sid_line.nid} {self.symbol} {self.comment}"
        else:
            return f"{self.nid} {Zero.keyword} {self.sid_line.nid} {self.comment}"

class One(Constant):
    keyword = OP_ONE

    def __init__(self, nid, sid_line, symbol, comment, line_no):
        super().__init__(nid, sid_line, 1, comment, line_no)
        self.symbol = symbol

    def __str__(self):
        if self.symbol:
            return f"{self.nid} {One.keyword} {self.sid_line.nid} {self.symbol} {self.comment}"
        else:
            return f"{self.nid} {One.keyword} {self.sid_line.nid} {self.comment}"

class Constd(Constant):
    keyword = OP_CONSTD

    def __init__(self, nid, sid_line, value, comment, line_no):
        super().__init__(nid, sid_line, value, comment, line_no)

    def __str__(self):
        return f"{self.nid} {Constd.keyword} {self.sid_line.nid} {self.print_value} {self.comment}"

class Const(Constant):
    keyword = OP_CONST

    def __init__(self, nid, sid_line, value, comment, line_no):
        super().__init__(nid, sid_line, value, comment, line_no)

    def __str__(self):
        size = self.sid_line.size
        return f"{self.nid} {Const.keyword} {self.sid_line.nid} {self.value:0{size}b} {self.comment}"

class Consth(Constant):
    keyword = OP_CONSTH

    def __init__(self, nid, sid_line, value, comment, line_no):
        super().__init__(nid, sid_line, value, comment, line_no)

    def __str__(self):
        size = math.ceil(self.sid_line.size / 4)
        return f"{self.nid} {Consth.keyword} {self.sid_line.nid} {self.value:0{size}X} {self.comment}"

class Constant_Array(Expression):
    def __init__(self, sid_line, constant_line):
        super().__init__(None, sid_line, {}, 0, constant_line.comment, constant_line.line_no)
        self.nid = constant_line.nid # reuse nid of constant_line
        self.constant_line = constant_line
        if not isinstance(sid_line, Array):
            raise model_error("array sort", line_no)
        if not isinstance(constant_line, Constant):
            raise model_error("bitvector constant", line_no)
        if not sid_line.element_size_line.match_sorts(constant_line.sid_line):
            raise model_error("compatible sorts", line_no)

    def __str__(self):
        return f"{self.nid} {"consta"} {self.sid_line.nid} {self.constant_line.nid} {self.comment}"

    def get_mapped_array_expression_for(self, index):
        if index is not None:
            assert self.sid_line.is_mapped_array()
            return self.constant_line
        else:
            assert not self.sid_line.is_mapped_array()
            return self

class Variable(Expression):
    keywords = {OP_INPUT, OP_STATE}

    inputs = {}

    bvdd_input = {}
    bvdd_index = {}

    def __init__(self, nid, sid_line, domain, symbol, comment, line_no, index):
        super().__init__(nid, sid_line, domain, 0, comment, line_no)
        self.symbol = symbol
        if isinstance(sid_line, Array):
            Array.number_of_variable_arrays += 1
        self.new_mapped_array(index)

    def __lt__(self, variable):
        # ordering variables for constructing model input
        return self.nid < variable.nid

    def new_mapped_array(self, index):
        self.index = index
        if index is not None:
            if not isinstance(self.sid_line, Bitvector):
                raise model_error("bitvector", self.line_no)
        elif self.sid_line.is_mapped_array():
            Array.number_of_mapped_arrays += 1
            self.array = {}
            for index in range(2**self.sid_line.array_size_line.size):
                self.array[index] = type(self)(self.nid + index + 1, self.sid_line.element_size_line,
                    f"{self.symbol}-{index}", f"{self.comment} @ index {index}", self.line_no, index)

    def new_input(self, index):
        if index is not None or not self.sid_line.is_mapped_array():
            assert self.nid not in Variable.inputs, f"variable nid {self.nid} already defined @ {self.line_no}"
            Variable.inputs[self.nid] = self

            if isinstance(self.sid_line, Bitvector) and self.sid_line.size == 8:
                Variable.bvdd_input[len(Variable.bvdd_input)] = self
                Variable.bvdd_index[self] = len(Variable.bvdd_index)

    def get_mapped_array_expression_for(self, index):
        if index is not None:
            assert self.sid_line.is_mapped_array()
            return self.array[index]
        else:
            assert not self.sid_line.is_mapped_array()
            return self

class Input(Variable):
    keyword = OP_INPUT

    def __init__(self, nid, sid_line, symbol, comment, line_no, index = None):
        super().__init__(nid, sid_line, {}, symbol, comment, line_no, index)
        self.name = f"input{self.nid}"
        self.new_input(index)

    def __str__(self):
        return f"{self.nid} {Input.keyword} {self.sid_line.nid} {self.symbol} {self.comment}"

class State(Variable):
    keyword = OP_STATE

    states = {}

    pc = None

    def __init__(self, nid, sid_line, symbol, comment, line_no, index = None):
        # domain is ordered set by using dictionary with None values
        super().__init__(nid, sid_line, {self:None}, symbol, comment, line_no, index)
        self.name = f"state{self.nid}"
        self.init_line = None
        self.next_line = None
        self.new_state(index)
        # rotor-dependent program counter declaration
        if comment == "; program counter":
            State.pc = self

    def __str__(self):
        return f"{self.nid} {State.keyword} {self.sid_line.nid} {self.symbol} {self.comment}"

    def new_state(self, index):
        if index is not None or not self.sid_line.is_mapped_array():
            assert self.nid not in State.states, f"state nid {self.nid} already defined @ {self.line_no}"
            State.states[self.nid] = self

    def remove_state(self):
        for key in State.states.keys():
            if State.states[key] is self:
                del State.states[key]
                return

    def get_mapped_array_expression_for(self, index):
        if isinstance(self.sid_line, Bitvector) or self.sid_line.is_mapped_array():
            if self.init_line is not None and self.next_line is not None and self.next_line.exp_line is self:
                # propagate initial value of initialized read-only bitvector states
                return self.init_line.exp_line.get_mapped_array_expression_for(index)
        return super().get_mapped_array_expression_for(index)

class Indexed(Expression):
    def __init__(self, nid, sid_line, arg1_line, comment, line_no):
        super().__init__(nid, sid_line, arg1_line.domain, arg1_line.depth + 1, comment, line_no)
        self.arg1_line = arg1_line
        if not isinstance(arg1_line, Expression):
            raise model_error("expression operand", line_no)
        if not isinstance(sid_line, Bitvec):
            raise model_error("bitvector result", line_no)
        if not isinstance(arg1_line.sid_line, Bitvec):
            raise model_error("bitvector operand", line_no)

    def get_mapped_array_expression_for(self, index):
        assert index is None
        arg1_line = self.arg1_line.get_mapped_array_expression_for(None)
        return self.copy(arg1_line)

class Ext(Indexed):
    keywords = {OP_SEXT, OP_UEXT}

    def __init__(self, nid, op, sid_line, arg1_line, w, comment, line_no):
        super().__init__(nid, sid_line, arg1_line, comment, line_no)
        assert op in Ext.keywords
        self.op = op
        self.w = w
        if sid_line.size != arg1_line.sid_line.size + w:
            raise model_error("compatible bitvector sorts", line_no)

    def __str__(self):
        return f"{self.nid} {self.op} {self.sid_line.nid} {self.arg1_line.nid} {self.w} {self.comment}"

    def copy(self, arg1_line):
        if self.arg1_line is not arg1_line:
            Expression.total_number_of_generated_expressions += 1
            return type(self)(Parser.next_nid(), self.op, self.sid_line, arg1_line, self.w, self.comment, self.line_no)
        else:
            return self

class Slice(Indexed):
    keyword = OP_SLICE

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

    def copy(self, arg1_line):
        if self.arg1_line is not arg1_line:
            Expression.total_number_of_generated_expressions += 1
            return type(self)(Parser.next_nid(), self.sid_line, arg1_line, self.u, self.l, self.comment, self.line_no)
        else:
            return self

class Unary(Expression):
    keywords = {OP_NOT, OP_INC, OP_DEC, OP_NEG}

    def __init__(self, nid, op, sid_line, arg1_line, comment, line_no):
        super().__init__(nid, sid_line, arg1_line.domain, arg1_line.depth + 1, comment, line_no)
        assert op in Unary.keywords
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

    def print_deep(self):
        self.arg1_line.print_deep()
        print(self)

    def copy(self, arg1_line):
        if self.arg1_line is not arg1_line:
            Expression.total_number_of_generated_expressions += 1
            return type(self)(Parser.next_nid(), self.op, self.sid_line, arg1_line, self.comment, self.line_no)
        else:
            return self

    def get_mapped_array_expression_for(self, index):
        assert index is None
        arg1_line = self.arg1_line.get_mapped_array_expression_for(None)
        return self.copy(arg1_line)

class Binary(Expression):
    keywords = {OP_IMPLIES, OP_EQ, OP_NEQ, OP_SGT, OP_UGT, OP_SGTE, OP_UGTE, OP_SLT, OP_ULT, OP_SLTE, OP_ULTE, OP_AND, OP_OR, OP_XOR, OP_SLL, OP_SRL, OP_SRA, OP_ADD, OP_SUB, OP_MUL, OP_SDIV, OP_UDIV, OP_SREM, OP_UREM, OP_CONCAT, OP_READ}

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, comment, line_no):
        super().__init__(nid, sid_line, arg1_line.domain | arg2_line.domain,
            max(arg1_line.depth, arg2_line.depth) + 1, comment, line_no)
        assert op in Binary.keywords
        self.op = op
        self.arg1_line = arg1_line
        self.arg2_line = arg2_line
        if not isinstance(arg1_line, Expression):
            raise model_error("expression left operand", line_no)
        if not isinstance(arg2_line, Expression):
            raise model_error("expression right operand", line_no)

    def __str__(self):
        return f"{self.nid} {self.op} {self.sid_line.nid} {self.arg1_line.nid} {self.arg2_line.nid} {self.comment}"

    def print_deep(self):
        self.arg1_line.print_deep()
        self.arg2_line.print_deep()
        print(self)

    def copy(self, arg1_line, arg2_line):
        if self.arg1_line is not arg1_line or self.arg2_line is not arg2_line:
            Expression.total_number_of_generated_expressions += 1
            return type(self)(Parser.next_nid(), self.op, self.sid_line, arg1_line, arg2_line, self.comment, self.line_no)
        else:
            return self

    def get_mapped_array_expression_for(self, index):
        assert index is None
        arg1_line = self.arg1_line.get_mapped_array_expression_for(None)
        arg2_line = self.arg2_line.get_mapped_array_expression_for(None)
        return self.copy(arg1_line, arg2_line)

class Implies(Binary):
    keyword = OP_IMPLIES

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, comment, line_no):
        assert op == Implies.keyword
        super().__init__(nid, Implies.keyword, sid_line, arg1_line, arg2_line, comment, line_no)
        if not isinstance(sid_line, Bool):
            raise model_error("Boolean result", line_no)
        if not sid_line.match_sorts(arg1_line.sid_line):
            raise model_error("compatible result and first operand sorts", line_no)
        if not arg1_line.sid_line.match_sorts(arg2_line.sid_line):
            raise model_error("compatible first and second operand sorts", line_no)

class Comparison(Binary):
    keywords = {OP_EQ, OP_NEQ, OP_SGT, OP_UGT, OP_SGTE, OP_UGTE, OP_SLT, OP_ULT, OP_SLTE, OP_ULTE}

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, comment, line_no):
        assert op in Comparison.keywords
        super().__init__(nid, op, sid_line, arg1_line, arg2_line, comment, line_no)
        if not isinstance(sid_line, Bool):
            raise model_error("Boolean result", line_no)
        if (op in {OP_SGT, OP_UGT, OP_SGTE, OP_UGTE, OP_SLT, OP_ULT, OP_SLTE, OP_ULTE} and
            not isinstance(arg1_line.sid_line, Bitvec)):
            raise model_error("bitvector first operand", line_no)
        if not arg1_line.sid_line.match_sorts(arg2_line.sid_line):
            raise model_error("compatible first and second operand sorts", line_no)

class Logical(Binary):
    keywords = {OP_AND, OP_OR, OP_XOR}

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, comment, line_no):
        assert op in Logical.keywords
        super().__init__(nid, op, sid_line, arg1_line, arg2_line, comment, line_no)
        if not isinstance(sid_line, Bitvector):
            raise model_error("Boolean or bitvector result", line_no)
        if not sid_line.match_sorts(arg1_line.sid_line):
            raise model_error("compatible result and first operand sorts", line_no)
        if not arg1_line.sid_line.match_sorts(arg2_line.sid_line):
            raise model_error("compatible first and second operand sorts", line_no)

class Computation(Binary):
    keywords = {OP_SLL, OP_SRL, OP_SRA, OP_ADD, OP_SUB, OP_MUL, OP_SDIV, OP_UDIV, OP_SREM, OP_UREM}

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, comment, line_no):
        assert op in Computation.keywords
        super().__init__(nid, op, sid_line, arg1_line, arg2_line, comment, line_no)
        if not isinstance(sid_line, Bitvec):
            raise model_error("bitvector result", line_no)
        if not sid_line.match_sorts(arg1_line.sid_line):
            raise model_error("compatible result and first operand sorts", line_no)
        if not arg1_line.sid_line.match_sorts(arg2_line.sid_line):
            raise model_error("compatible first and second operand sorts", line_no)

class Concat(Binary):
    keyword = OP_CONCAT

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, comment, line_no):
        assert op == Concat.keyword
        super().__init__(nid, Concat.keyword, sid_line, arg1_line, arg2_line, comment, line_no)
        if not isinstance(sid_line, Bitvec):
            raise model_error("bitvector result", line_no)
        if not isinstance(arg1_line.sid_line, Bitvec):
            raise model_error("bitvector first operand", line_no)
        if not isinstance(arg2_line.sid_line, Bitvec):
            raise model_error("bitvector second operand", line_no)
        if sid_line.size != arg1_line.sid_line.size + arg2_line.sid_line.size:
            raise model_error("compatible bitvector result", line_no)

class Read(Binary):
    keyword = OP_READ

    READ_ARRAY_ITERATIVELY = True

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, comment, line_no):
        assert op == Read.keyword
        super().__init__(nid, Read.keyword, sid_line, arg1_line, arg2_line, comment, line_no)
        if not isinstance(arg1_line.sid_line, Array):
            raise model_error("array first operand", line_no)
        if not arg1_line.sid_line.array_size_line.match_sorts(arg2_line.sid_line):
            raise model_error("compatible first operand array size and second operand sorts", line_no)
        if not sid_line.match_sorts(arg1_line.sid_line.element_size_line):
            raise model_error("compatible result and first operand element size sorts", line_no)
        self.read_cache = None

    def read_array_iterative(self, array_line, index_line):
        for index in range(2**array_line.sid_line.array_size_line.size):
            if index == 0:
                read_line = array_line.get_mapped_array_expression_for(0)
            else:
                read_line = Parser.parser.get_class(Ite)(Parser.next_nid(), self.sid_line,
                    Parser.parser.get_class(Comparison)(Parser.next_nid(), OP_EQ, Bool.boolean,
                        index_line,
                        Parser.parser.get_class(Constd)(Parser.next_nid(), index_line.sid_line,
                            index, f"index {index}", self.line_no),
                        f"is address equal to index {index}?", self.line_no),
                    array_line.get_mapped_array_expression_for(index),
                    read_line,
                    f"read value from {array_line.comment[2:]} @ address if equal to index {index}", self.line_no)
        return read_line

    def read_array_recursive(self, array_line, index_line, index_array, zero_line):
        assert 2 <= len(index_array) == 2**math.log2(len(index_array))
        if len(index_array) == 2:
            even_line = array_line.get_mapped_array_expression_for(index_array[0])
            odd_line = array_line.get_mapped_array_expression_for(index_array[1])
        else:
            even_line = self.read_array_recursive(array_line, index_line,
                index_array[0:len(index_array)//2], zero_line)
            odd_line = self.read_array_recursive(array_line, index_line,
                index_array[len(index_array)//2:len(index_array)], zero_line)
        address_bit = int(math.log2(len(index_array))) - 1
        return Parser.parser.get_class(Ite)(Parser.next_nid(), self.sid_line,
            Parser.parser.get_class(Comparison)(Parser.next_nid(), OP_EQ, Bool.boolean,
                Parser.parser.get_class(Slice)(Parser.next_nid(), zero_line.sid_line, index_line,
                    address_bit, address_bit,
                    f"extract {address_bit}-th address bit", self.line_no),
                zero_line,
                f"is {address_bit}-th address bit set?", self.line_no),
            even_line,
            odd_line,
            f"read value from {array_line.comment[2:]} @ reset or set {address_bit}-th address bit", self.line_no)

    def read_array(self, array_line, index_line):
        if array_line.sid_line.is_mapped_array():
            if isinstance(index_line, Constant):
                return array_line.get_mapped_array_expression_for(index_line.value)
            else:
                if Read.READ_ARRAY_ITERATIVELY:
                    return self.read_array_iterative(array_line, index_line)
                else:
                    return self.read_array_recursive(array_line, index_line,
                        list(range(2**array_line.sid_line.array_size_line.size)),
                        Parser.parser.get_class(Zero)(Parser.next_nid(),
                            Parser.parser.get_class(Bitvec)(Parser.next_nid(), 1, "1-bit bitvector for testing bits", self.line_no),
                            "", "zero value for testing bits", self.line_no))
        else:
            return self.copy(array_line.get_mapped_array_expression_for(None), index_line)

    def get_mapped_array_expression_for(self, index):
        assert index is None
        if self.read_cache is None: # avoids quadratic blowup in mapped array size
            arg1_line = self.arg1_line # map later when index is known
            arg2_line = self.arg2_line.get_mapped_array_expression_for(None)
            self.read_cache = self.read_array(arg1_line, arg2_line)
        return self.read_cache

class Ternary(Expression):
    keywords = {OP_ITE, OP_WRITE}

    def __init__(self, nid, op, sid_line, arg1_line, arg2_line, arg3_line, comment, line_no):
        super().__init__(nid, sid_line, arg1_line.domain | arg2_line.domain | arg3_line.domain,
            max(arg1_line.depth, arg2_line.depth, arg3_line.depth) + 1, comment, line_no)
        assert op in Ternary.keywords
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
    keyword = OP_ITE

    branching_conditions = None
    non_branching_conditions = None

    def __init__(self, nid, sid_line, arg1_line, arg2_line, arg3_line, comment, line_no):
        super().__init__(nid, Ite.keyword, sid_line, arg1_line, arg2_line, arg3_line, comment, line_no)
        if not isinstance(arg1_line.sid_line, Bool):
            raise model_error("Boolean first operand", line_no)
        if not sid_line.match_sorts(arg2_line.sid_line):
            raise model_error("compatible result and second operand sorts", line_no)
        if not arg2_line.sid_line.match_sorts(arg3_line.sid_line):
            raise model_error("compatible second and third operand sorts", line_no)
        self.ite_cache = {}
        if Ite.branching_conditions is None and comment == "; branch true condition":
            Ite.branching_conditions = self
        elif Ite.non_branching_conditions is None and comment == "; branch false condition":
            Ite.non_branching_conditions = self

    def copy(self, arg1_line, arg2_line, arg3_line):
        if self.arg1_line is not arg1_line or self.arg2_line is not arg2_line or self.arg3_line is not arg3_line:
            Expression.total_number_of_generated_expressions += 1
            return type(self)(Parser.next_nid(), arg2_line.sid_line, arg1_line, arg2_line, arg3_line, self.comment, self.line_no)
        else:
            return self

    def get_mapped_array_expression_for(self, index):
        if index not in self.ite_cache:
            arg1_line = self.arg1_line.get_mapped_array_expression_for(None)
            arg2_line = self.arg2_line.get_mapped_array_expression_for(index)
            arg3_line = self.arg3_line.get_mapped_array_expression_for(index)
            self.ite_cache[index] = self.copy(arg1_line, arg2_line, arg3_line)
        return self.ite_cache[index]

class Write(Ternary):
    keyword = OP_WRITE

    def __init__(self, nid, sid_line, arg1_line, arg2_line, arg3_line, comment, line_no):
        super().__init__(nid, Write.keyword, sid_line, arg1_line, arg2_line, arg3_line, comment, line_no)
        if not isinstance(sid_line, Array):
            raise model_error("array result", line_no)
        if not sid_line.match_sorts(arg1_line.sid_line):
            raise model_error("compatible result and first operand sorts", line_no)
        if not arg1_line.sid_line.array_size_line.match_sorts(arg2_line.sid_line):
            raise model_error("compatible first operand array size and second operand sorts", line_no)
        if not arg1_line.sid_line.element_size_line.match_sorts(arg3_line.sid_line):
            raise model_error("compatible first operand element size and third operand sorts", line_no)
        self.write_cache = {}

    def copy(self, arg1_line, arg2_line, arg3_line):
        if self.arg1_line is not arg1_line or self.arg2_line is not arg2_line or self.arg3_line is not arg3_line:
            Expression.total_number_of_generated_expressions += 1
            return type(self)(Parser.next_nid(), arg1_line.sid_line, arg1_line, arg2_line, arg3_line, self.comment, self.line_no)
        else:
            return self

    def write_array(self, array_line, index_line, value_line, index):
        if self.sid_line.is_mapped_array():
            assert index is not None
            if isinstance(index_line, Constant):
                if index_line.value == index:
                    return value_line
                else:
                    return array_line
            else:
                return Parser.parser.get_class(Ite)(Parser.next_nid(), value_line.sid_line,
                    Parser.parser.get_class(Comparison)(Parser.next_nid(), OP_EQ, Bool.boolean,
                        index_line,
                        Parser.parser.get_class(Constd)(Parser.next_nid(), index_line.sid_line,
                            index, f"index {index}", self.line_no),
                        f"is address equal to index {index}?", self.line_no),
                    value_line,
                    array_line,
                    f"write value to {array_line.comment[2:]} @ address if equal to index {index}", self.line_no)
        else:
            assert index is None
            return self.copy(array_line, index_line, value_line)

    def get_mapped_array_expression_for(self, index):
        if index not in self.write_cache:
            arg1_line = self.arg1_line.get_mapped_array_expression_for(index)
            arg2_line = self.arg2_line.get_mapped_array_expression_for(None)
            arg3_line = self.arg3_line.get_mapped_array_expression_for(None)
            self.write_cache[index] = self.write_array(arg1_line, arg2_line, arg3_line, index)
        return self.write_cache[index]

class Transitional(Line):
    def __init__(self, nid, sid_line, state_line, exp_line, symbol, comment, line_no, array_line, index):
        super().__init__(nid, comment, line_no)
        self.sid_line = sid_line
        self.state_line = state_line
        self.exp_line = exp_line
        self.symbol = symbol
        if not isinstance(sid_line, Sort):
            raise model_error("sort", line_no)
        if not isinstance(state_line, State):
            raise model_error("state operand", line_no)
        if not isinstance(exp_line, Expression):
            raise model_error("expression operand", line_no)
        if not self.sid_line.match_sorts(state_line.sid_line):
            raise model_error("compatible line and state sorts", line_no)
        if not state_line.sid_line.match_init_sorts(exp_line.sid_line):
            raise model_error("compatible state and expression sorts", line_no)
        self.new_mapped_array(array_line, index)

    def new_mapped_array(self, array_line, index):
        self.array_line = array_line
        self.index = index
        if index is not None:
            if not isinstance(self.sid_line, Bitvector):
                raise model_error("bitvector", self.line_no)
        elif self.sid_line.is_mapped_array():
            self.array = {}
            for index in self.state_line.array.keys():
                self.array[index] = type(self)(self.nid + index + 1, self.sid_line.element_size_line,
                    self.state_line.array[index], self.state_line.array[index], self.symbol,
                    f"{self.comment} @ index {index}", self.line_no, self, index)

    def set_mapped_array_expression(self):
        if self.index is None:
            self.exp_line = self.exp_line.get_mapped_array_expression_for(None)
        else:
            self.exp_line = self.array_line.exp_line.get_mapped_array_expression_for(self.index)

    def remove_transition(state_line, transitions):
        for key in transitions.keys():
            if transitions[key].state_line is state_line:
                del transitions[key]
                return

    def new_transition(self, transitions, index):
        if index is not None or not self.sid_line.is_mapped_array():
            assert self.nid not in transitions, f"transition nid {self.nid} already defined @ {self.line_no}"
            transitions[self.nid] = self

class Init(Transitional):
    keyword = OP_INIT

    inits = {}

    def __init__(self, nid, sid_line, state_line, exp_line, symbol, comment, line_no, array_line = None, index = None):
        if isinstance(state_line.sid_line, Array) and isinstance(exp_line, Constant):
            exp_line = Parser.parser.get_class(Constant_Array)(state_line.sid_line, exp_line)
        super().__init__(nid, sid_line, state_line, exp_line, symbol, comment, line_no, array_line, index)
        if state_line.nid < exp_line.nid:
            raise model_error("state after expression", line_no)
        if isinstance(state_line, Input):
            raise model_error("state, not input", line_no)
        if self.state_line.init_line is None:
            self.state_line.init_line = self
        else:
            raise model_error("uninitialized state", line_no)
        self.new_transition(Init.inits, index)

    def __str__(self):
        if self.symbol:
            return f"{self.nid} {Init.keyword} {self.sid_line.nid} {self.state_line.nid} {self.exp_line.nid} {self.symbol} {self.comment}"
        else:
            return f"{self.nid} {Init.keyword} {self.sid_line.nid} {self.state_line.nid} {self.exp_line.nid} {self.comment}"

class Next(Transitional):
    keyword = OP_NEXT

    nexts = {}

    def __init__(self, nid, sid_line, state_line, exp_line, symbol, comment, line_no, array_line = None, index = None):
        super().__init__(nid, sid_line, state_line, exp_line, symbol, comment, line_no, array_line, index)
        if self.state_line.next_line is None:
            self.state_line.next_line = self
        else:
            raise model_error("untransitioned state", line_no)
        self.new_transition(Next.nexts, index)

    def __str__(self):
        if self.symbol:
            return f"{self.nid} {Next.keyword} {self.sid_line.nid} {self.state_line.nid} {self.exp_line.nid} {self.symbol} {self.comment}"
        else:
            return f"{self.nid} {Next.keyword} {self.sid_line.nid} {self.state_line.nid} {self.exp_line.nid} {self.comment}"

class Property(Line):
    keywords = {OP_CONSTRAINT, OP_BAD}

    def __init__(self, nid, property_line, symbol, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.property_line = property_line
        self.symbol = symbol
        if not isinstance(property_line, Expression):
            raise model_error("expression operand", line_no)
        if not isinstance(property_line.sid_line, Bool):
            raise model_error("Boolean operand", line_no)

    def set_mapped_array_expression(self):
        self.property_line = self.property_line.get_mapped_array_expression_for(None)

class Constraint(Property):
    keyword = OP_CONSTRAINT

    constraints = {}

    def __init__(self, nid, property_line, symbol, comment, line_no):
        super().__init__(nid, property_line, symbol, comment, line_no)
        self.new_constraint()

    def __str__(self):
        return f"{self.nid} {Constraint.keyword} {self.property_line.nid} {self.symbol} {self.comment}"

    def new_constraint(self):
        assert self not in Constraint.constraints, f"constraint nid {self.nid} already defined @ {self.line_no}"
        Constraint.constraints[self.nid] = self

class Bad(Property):
    keyword = OP_BAD

    bads = {}

    def __init__(self, nid, property_line, symbol, comment, line_no):
        super().__init__(nid, property_line, symbol, comment, line_no)
        self.new_bad()

    def __str__(self):
        return f"{self.nid} {Bad.keyword} {self.property_line.nid} {self.symbol} {self.comment}"

    def new_bad(self):
        assert self.nid not in Bad.bads, f"bad nid {self.nid} already defined @ {self.line_no}"
        Bad.bads[self.nid] = self

# BTOR2 parser

class syntax_error(Exception):
    def __init__(self, expected, line_no):
        super().__init__(f"syntax error in line {line_no}: {expected} expected")

import re

class Parser:
    parser = None

    current_nid = 0

    def next_nid(nid = None):
        if nid is None:
            Parser.current_nid += 1
            return Parser.current_nid
        else:
            return nid

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
        token = Parser.get_token(tokens, expected, line_no)
        if token.isdecimal():
            return int(token)
        else:
            raise syntax_error(expected, line_no)

    def get_nid(tokens, expected, line_no):
        return Array.accommodate_array_indexes(Parser.get_decimal(tokens, expected, line_no))

    def get_nid_line(tokens, clss, expected, line_no):
        nid = Parser.get_nid(tokens, expected, line_no)
        if Line.is_defined(nid):
            line = Line.get(nid)
            if isinstance(line, clss):
                return line
            else:
                raise syntax_error(expected, line_no)
        else:
            raise syntax_error(f"defined {expected}", line_no)

    def get_bool_or_bitvec_sid_line(tokens, line_no):
        return Parser.get_nid_line(tokens, Bitvector, "Boolean or bitvector sort nid", line_no)

    def get_bitvec_sid_line(tokens, line_no):
        return Parser.get_nid_line(tokens, Bitvec, "bitvector sort nid", line_no)

    def get_sid_line(tokens, line_no):
        return Parser.get_nid_line(tokens, Sort, "sort nid", line_no)

    def get_state_line(tokens, line_no):
        return Parser.get_nid_line(tokens, State, "state nid", line_no)

    def get_exp_line(tokens, line_no):
        return Parser.get_nid_line(tokens, Expression, "expression nid", line_no)

    def get_number(tokens, base, expected, line_no):
        token = Parser.get_token(tokens, expected, line_no)
        try:
            if (base == 10):
                return int(token)
            else:
                return int(token, base)
        except ValueError:
            raise syntax_error(expected, line_no)

    def get_symbol(tokens):
        try:
            return Parser.get_token(tokens, None, None)
        except:
            return ""

    def get_comment(tokens, line_no):
        comment = Parser.get_symbol(tokens)
        if comment:
            if comment[0] != ';':
                raise syntax_error("comment", line_no)
        return comment

    def get_class(self, clss_or_keyword):
        if clss_or_keyword is Bool:
            return Bool
        elif clss_or_keyword is Bitvec:
            return Bitvec
        elif clss_or_keyword is Array:
            return Array
        elif clss_or_keyword is Constant_Array:
            return Constant_Array
        elif clss_or_keyword is Zero or clss_or_keyword == Zero.keyword:
            return Zero
        elif clss_or_keyword is One or clss_or_keyword == One.keyword:
            return One
        elif clss_or_keyword is Constd or clss_or_keyword == Constd.keyword:
            return Constd
        elif clss_or_keyword is Const or clss_or_keyword == Const.keyword:
            return Const
        elif clss_or_keyword is Consth or clss_or_keyword == Consth.keyword:
            return Consth
        elif clss_or_keyword is Input or clss_or_keyword == Input.keyword:
            return Input
        elif clss_or_keyword is State or clss_or_keyword == State.keyword:
            return State
        elif clss_or_keyword is Ext or clss_or_keyword in Ext.keywords:
            return Ext
        elif clss_or_keyword is Slice or clss_or_keyword == Slice.keyword:
            return Slice
        elif clss_or_keyword is Unary or clss_or_keyword in Unary.keywords:
            return Unary
        elif clss_or_keyword is Implies or clss_or_keyword == Implies.keyword:
            return Implies
        elif clss_or_keyword is Comparison or clss_or_keyword in Comparison.keywords:
            return Comparison
        elif clss_or_keyword is Logical or clss_or_keyword in Logical.keywords:
            return Logical
        elif clss_or_keyword is Computation or clss_or_keyword in Computation.keywords:
            return Computation
        elif clss_or_keyword is Concat or clss_or_keyword == Concat.keyword:
            return Concat
        elif clss_or_keyword is Read or clss_or_keyword == Read.keyword:
            return Read
        elif clss_or_keyword is Ite or clss_or_keyword == Ite.keyword:
            return Ite
        elif clss_or_keyword is Write or clss_or_keyword == Write.keyword:
            return Write
        elif clss_or_keyword is Init or clss_or_keyword == Init.keyword:
            return Init
        elif clss_or_keyword is Next or clss_or_keyword == Next.keyword:
            return Next
        elif clss_or_keyword is Constraint or clss_or_keyword == Constraint.keyword:
            return Constraint
        elif clss_or_keyword is Bad or clss_or_keyword == Bad.keyword:
            return Bad

    def new_boolean(self, nid = None, line_no = None):
        return self.get_class(Bool)(Parser.next_nid(nid), "Boolean", line_no)

    def new_bitvec(self, size_in_bits, comment, nid = None, line_no = None):
        return self.get_class(Bitvec)(Parser.next_nid(nid), size_in_bits, comment, line_no)

    def new_array(self, address_sid, element_sid, comment, nid = None, line_no = None):
        return self.get_class(Array)(Parser.next_nid(nid), address_sid, element_sid, comment, line_no)

    def new_zero_one(self, op, sid, symbol, comment, nid = None, line_no = None):
        assert op in {OP_ZERO, OP_ONE}
        return self.get_class(op)(Parser.next_nid(nid), sid, symbol, comment, line_no)

    def new_constant(self, op, sid, constant, comment, nid = None, line_no = None):
        assert op in {OP_CONSTD, OP_CONST, OP_CONSTH}
        if op == OP_CONSTD:
            if constant == 0:
                return self.get_class(Zero)(Parser.next_nid(nid), sid, "", comment, line_no)
            elif constant == 1:
                return self.get_class(One)(Parser.next_nid(nid), sid, "", comment, line_no)
        return self.get_class(op)(Parser.next_nid(nid), sid, constant, comment, line_no)

    def new_input(self, op, sid, symbol, comment, nid = None, line_no = None):
        assert op in Variable.keywords
        return self.get_class(op)(Parser.next_nid(nid), sid, symbol, comment, line_no)

    def new_ext(self, op, sid, value_nid, w, comment, nid = None, line_no = None):
        assert op in Ext.keywords
        return self.get_class(op)(Parser.next_nid(nid), op, sid, value_nid, w, comment, line_no)

    def new_slice(self, sid, value_nid, u, l, comment, nid = None, line_no = None):
        return self.get_class(Slice.keyword)(Parser.next_nid(nid), sid, value_nid, u, l, comment, line_no)

    def new_unary(self, op, sid, value_nid, comment, nid = None, line_no = None):
        assert op in Unary.keywords
        return self.get_class(op)(Parser.next_nid(nid), op, sid, value_nid, comment, line_no)

    def new_unary_boolean(self, op, value_nid, comment, nid = None, line_no = None):
        assert op == OP_NOT
        return self.get_class(op)(Parser.next_nid(nid), op, SID_BOOLEAN, value_nid, comment, line_no)

    def new_binary(self, op, sid, left_nid, right_nid, comment, nid = None, line_no = None):
        assert op in Binary.keywords
        return self.get_class(op)(Parser.next_nid(nid), op, sid, left_nid, right_nid, comment, line_no)

    def new_binary_boolean(self, op, left_nid, right_nid, comment, nid = None, line_no = None):
        assert op in Implies.keyword + Comparison.keywords + Logical.keywords
        return self.get_class(op)(Parser.next_nid(nid), op, SID_BOOLEAN, left_nid, right_nid, comment, line_no)

    def new_ternary(self, op, sid, first_nid, second_nid, third_nid, comment, nid = None, line_no = None):
        assert op in Ternary.keywords
        return self.get_class(op)(Parser.next_nid(nid), sid, first_nid, second_nid, third_nid, comment, line_no)

    def new_init(self, sid, state_nid, value_nid, comment, nid = None, line_no = None):
        return self.get_class(Init.keyword)(Parser.next_nid(nid), sid, state_nid, value_nid, comment, line_no)

    def new_next(self, sid, state_nid, value_nid, comment, nid = None, line_no = None):
        return self.get_class(Next.keyword)(Parser.next_nid(nid), sid, state_nid, value_nid, comment, line_no)

    def new_init_next(self, op, sid, state_nid, value_nid, symbol, comment, nid = None, line_no = None):
        return self.get_class(op)(Parser.next_nid(nid), sid, state_nid, value_nid, symbol, comment, line_no)

    def new_property(self, op, condition_nid, symbol, comment, nid = None, line_no = None):
        assert op in Property.keywords
        return self.get_class(op)(Parser.next_nid(nid), condition_nid, symbol, comment, line_no)

    def parse_sort_line(self, tokens, nid, line_no):
        token = Parser.get_token(tokens, "bitvector or array", line_no)
        if token == Bitvec.keyword:
            size = Parser.get_decimal(tokens, "bitvector size", line_no)
            comment = Parser.get_comment(tokens, line_no)
            # beator- and rotor-dependent Boolean declaration
            if comment == "; Boolean" and size == 1:
                return self.new_boolean(nid, line_no)
            else:
                return self.new_bitvec(size, comment, nid, line_no)
        elif token == Array.keyword:
            array_size_line = Parser.get_bitvec_sid_line(tokens, line_no)
            element_size_line = Parser.get_bitvec_sid_line(tokens, line_no)
            comment = Parser.get_comment(tokens, line_no)
            return self.new_array(array_size_line, element_size_line, comment, nid, line_no)
        else:
            raise syntax_error("bitvector or array", line_no)

    def parse_symbol_comment(self, tokens, line_no):
        symbol = Parser.get_symbol(tokens)
        comment = Parser.get_comment(tokens, line_no)
        if symbol:
            if symbol[0] == ';':
                return "", symbol
        return symbol, comment

    def parse_zero_one_line(self, tokens, nid, op, line_no):
        sid_line = Parser.get_bool_or_bitvec_sid_line(tokens, line_no)
        symbol, comment = self.parse_symbol_comment(tokens, line_no)
        return self.new_zero_one(op, sid_line, symbol, comment, nid, line_no)

    def parse_constant_line(self, tokens, nid, op, line_no):
        sid_line = Parser.get_bool_or_bitvec_sid_line(tokens, line_no)
        if op == Constd.keyword:
            value = Parser.get_number(tokens, 10, "signed integer", line_no)
        elif op == Const.keyword:
            value = Parser.get_number(tokens, 2, "binary number", line_no)
        elif op == Consth.keyword:
            value = Parser.get_number(tokens, 16, "hexadecimal number", line_no)
        comment = Parser.get_comment(tokens, line_no)
        return self.new_constant(op, sid_line, value, comment, nid, line_no)

    def parse_variable_line(self, tokens, nid, op, line_no):
        sid_line = Parser.get_sid_line(tokens, line_no)
        symbol, comment = self.parse_symbol_comment(tokens, line_no)
        return self.new_input(op, sid_line, symbol, comment, nid, line_no)

    def parse_ext_line(self, tokens, nid, op, line_no):
        sid_line = Parser.get_sid_line(tokens, line_no)
        arg1_line = Parser.get_exp_line(tokens, line_no)
        w = Parser.get_decimal(tokens, "bit width", line_no)
        comment = Parser.get_comment(tokens, line_no)
        return self.new_ext(op, sid_line, arg1_line, w, comment, nid, line_no)

    def parse_slice_line(self, tokens, nid, line_no):
        sid_line = Parser.get_sid_line(tokens, line_no)
        arg1_line = Parser.get_exp_line(tokens, line_no)
        u = Parser.get_decimal(tokens, "upper bit", line_no)
        l = Parser.get_decimal(tokens, "lower bit", line_no)
        comment = Parser.get_comment(tokens, line_no)
        return self.new_slice(sid_line, arg1_line, u, l, comment, nid, line_no)

    def parse_unary_line(self, tokens, nid, op, line_no):
        sid_line = Parser.get_sid_line(tokens, line_no)
        arg1_line = Parser.get_exp_line(tokens, line_no)
        comment = Parser.get_comment(tokens, line_no)
        return self.new_unary(op, sid_line, arg1_line, comment, nid, line_no)

    def parse_binary_line(self, tokens, nid, op, line_no):
        sid_line = Parser.get_sid_line(tokens, line_no)
        arg1_line = Parser.get_exp_line(tokens, line_no)
        arg2_line = Parser.get_exp_line(tokens, line_no)
        comment = Parser.get_comment(tokens, line_no)
        return self.new_binary(op, sid_line, arg1_line, arg2_line, comment, nid, line_no)

    def parse_ternary_line(self, tokens, nid, op, line_no):
        sid_line = Parser.get_sid_line(tokens, line_no)
        arg1_line = Parser.get_exp_line(tokens, line_no)
        arg2_line = Parser.get_exp_line(tokens, line_no)
        arg3_line = Parser.get_exp_line(tokens, line_no)
        comment = Parser.get_comment(tokens, line_no)
        return self.new_ternary(op, sid_line, arg1_line, arg2_line, arg3_line, comment, nid, line_no)

    def parse_init_next_line(self, tokens, nid, op, line_no):
        sid_line = Parser.get_sid_line(tokens, line_no)
        state_line = Parser.get_state_line(tokens, line_no)
        exp_line = Parser.get_exp_line(tokens, line_no)
        symbol, comment = self.parse_symbol_comment(tokens, line_no)
        return self.new_init_next(op, sid_line, state_line, exp_line, symbol, comment, nid, line_no)

    def parse_property_line(self, tokens, nid, op, line_no):
        property_line = Parser.get_exp_line(tokens, line_no)
        symbol, comment = self.parse_symbol_comment(tokens, line_no)
        return self.new_property(op, property_line, symbol, comment, nid, line_no)

    def parse_btor2_line(self, line, line_no):
        if line.strip():
            tokens = Parser.tokenize_btor2(line)
            token = Parser.get_token(tokens, None, None)
            if token[0] != ';':
                if token.isdecimal():
                    nid = Array.accommodate_array_indexes(int(token))
                    if nid > Parser.current_nid:
                        Parser.current_nid = nid
                        token = Parser.get_token(tokens, "keyword", line_no)
                        if token == Sort.keyword:
                            return self.parse_sort_line(tokens, nid, line_no)
                        elif token in {Zero.keyword, One.keyword}:
                            return self.parse_zero_one_line(tokens, nid, token, line_no)
                        elif token in {Constd.keyword, Const.keyword, Consth.keyword}:
                            return self.parse_constant_line(tokens, nid, token, line_no)
                        elif token in Variable.keywords:
                            return self.parse_variable_line(tokens, nid, token, line_no)
                        elif token in Ext.keywords:
                            return self.parse_ext_line(tokens, nid, token, line_no)
                        elif token == Slice.keyword:
                            return self.parse_slice_line(tokens, nid, line_no)
                        elif token in Unary.keywords:
                            return self.parse_unary_line(tokens, nid, token, line_no)
                        elif token in Binary.keywords:
                            return self.parse_binary_line(tokens, nid, token, line_no)
                        elif token in Ternary.keywords:
                            return self.parse_ternary_line(tokens, nid, token, line_no)
                        elif token in {Init.keyword, Next.keyword}:
                            return self.parse_init_next_line(tokens, nid, token, line_no)
                        elif token in Property.keywords:
                            return self.parse_property_line(tokens, nid, token, line_no)
                        else:
                            raise syntax_error(f"unknown operator {token}", line_no)
                    raise syntax_error("increasing nid", line_no)
                raise syntax_error("nid", line_no)
        return line.strip()

    def parse_btor2(self, modelfile, outputfile):
        Parser.parser = self

        print(f"model file: {modelfile.name}")

        lines = {}
        line_no = 1
        for line in modelfile:
            try:
                lines[line_no] = self.parse_btor2_line(line, line_no)
                line_no += 1
            except (model_error, syntax_error) as message:
                print(f"parsing exception: {message}")
                exit(1)

        # start: mapping arrays to bitvectors

        if Array.ARRAY_SIZE_BOUND > 0:
            for init in Init.inits.values():
                init.set_mapped_array_expression()
            for constraint in Constraint.constraints.values():
                constraint.set_mapped_array_expression()
            for bad in Bad.bads.values():
                bad.set_mapped_array_expression()
            for next_line in Next.nexts.values():
                next_line.set_mapped_array_expression()

            for state in list(State.states.values()):
                if isinstance(state.sid_line, Bitvector):
                    if state.init_line is not None and state.next_line is not None:
                        if state.init_line.exp_line is state.next_line.exp_line or state.next_line.exp_line is state:
                            # remove initialized read-only bitvector states
                            state.remove_state()
                            Transitional.remove_transition(state, Init.inits)
                            Transitional.remove_transition(state, Next.nexts)

            if Ite.branching_conditions and Ite.non_branching_conditions:
                Ite.branching_conditions = Ite.branching_conditions.get_mapped_array_expression_for(None)
                Ite.non_branching_conditions = Ite.non_branching_conditions.get_mapped_array_expression_for(None)

        # end: mapping arrays to bitvectors

        for state in State.states.values():
            if state.init_line is None:
                # state has no init
                state.new_input(state.index)

        are_there_uninitialized_states = False
        are_there_untransitioned_states = False
        are_there_state_transitions = False

        for state in State.states.values():
            if state.init_line is None:
                are_there_uninitialized_states = True
            if state.next_line is None:
                are_there_untransitioned_states = True
            else:
                are_there_state_transitions = True

        if are_there_state_transitions:
            print("sequential problem:")
        else:
            print("combinational problem:")

        for input_line in Input.inputs.values():
            if isinstance(input_line, Input):
                print(input_line)
        for state in State.states.values():
            print(state)

        if are_there_uninitialized_states:
            print("uninitialized states:")
            for state in State.states.values():
                if state.init_line is None:
                    print(state)
        if are_there_untransitioned_states:
            print("untransitioned states:")
            for state in State.states.values():
                if state.next_line is None:
                    print(state)

        if Ite.branching_conditions and Ite.non_branching_conditions:
            print("branching conditions:")
            print(Ite.branching_conditions)
            print(Ite.non_branching_conditions)

        print("model profile:")
        print(f"{len(Line.lines)} lines in total")
        print(f"{self.get_class(Input).count} input, ", end="")
        print(f"{self.get_class(State).count} state, ", end="")
        print(f"{self.get_class(Init).count} init, ", end="")
        print(f"{self.get_class(Next).count} next, ", end="")
        print(f"{self.get_class(Constraint).count} constraint, ", end="")
        print(f"{self.get_class(Bad).count} bad")
        print(f"{self.get_class(Bool).count} bool, ", end="")
        print(f"{self.get_class(Bitvec).count} bitvec, ", end="")
        print(f"{self.get_class(Array).count} array")
        print(f"{self.get_class(Zero).count} zero, ", end="")
        print(f"{self.get_class(One).count} one, ", end="")
        print(f"{self.get_class(Constd).count} constd, ", end="")
        print(f"{self.get_class(Const).count} const, ", end="")
        print(f"{self.get_class(Consth).count} consth")
        print(f"{self.get_class(Ext).count} ext, ", end="")
        print(f"{self.get_class(Slice).count} slice, ", end="")
        print(f"{self.get_class(Unary).count} unary")
        print(f"{self.get_class(Implies).count} implies, ", end="")
        print(f"{self.get_class(Comparison).count} comparison, ", end="")
        print(f"{self.get_class(Logical).count} logical, ", end="")
        print(f"{self.get_class(Computation).count} computation")
        print(f"{self.get_class(Concat).count} concat, ", end="")
        print(f"{self.get_class(Ite).count} ite, ", end="")
        print(f"{self.get_class(Read).count} read, ", end="")
        print(f"{self.get_class(Write).count} write")

        if Array.ARRAY_SIZE_BOUND > 0:
            print("array mapping profile:")
            print(f"out of {Array.number_of_variable_arrays} arrays {Array.number_of_mapped_arrays} mapped")
            print(f"{Expression.total_number_of_generated_expressions} generated expressions")
            Expression.total_number_of_generated_expressions = 0

        if outputfile:
            print(f"output file: {outputfile.name}")
            for line in lines.values():
                print(line, file=outputfile)

        return are_there_state_transitions