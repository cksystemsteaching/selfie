#!/usr/bin/env python3

import math, re

class syntax_error(Exception):
    def __init__(self, expected, line_no):
        super().__init__(f"syntax error in line {line_no}: {expected} expected")

current_nid = 0

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

class Bitvec(Sort):
    keyword = 'bitvec'

    def __init__(self, nid, size, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.size = size

    def __str__(self):
        return f"{self.nid} {Sort.keyword} {Bitvec.keyword} {self.size} {self.comment}"

class Array(Sort):
    keyword = 'array'

    def __init__(self, nid, array_size_sid, element_size_sid, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.array_size_line = Line.get(array_size_sid)
        self.element_size_line = Line.get(element_size_sid)

    def __str__(self):
        return f"{self.nid} {Sort.keyword} {Array.keyword} {self.array_size_line.nid} {self.element_size_line.nid} {self.comment}"

class Expression(Line):
    def __init__(self, nid, sid, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.sid_line = Line.get(sid)

class Constant(Expression):
    def __init__(self, nid, sid, value, comment, line_no):
        super().__init__(nid, sid, comment, line_no)
        self.value = value

class Zero(Constant):
    keyword = 'zero'

    def __init__(self, nid, sid, comment, line_no):
        super().__init__(nid, sid, 0, comment, line_no)

    def __str__(self):
        return f"{self.nid} {Zero.keyword} {self.sid_line.nid} {self.comment}"

class One(Constant):
    keyword = 'one'

    def __init__(self, nid, sid, comment, line_no):
        super().__init__(nid, sid, 1, comment, line_no)

    def __str__(self):
        return f"{self.nid} {One.keyword} {self.sid_line.nid} {self.comment}"

class Constd(Constant):
    keyword = 'constd'

    def __init__(self, nid, sid, value, comment, line_no):
        super().__init__(nid, sid, value, comment, line_no)

    def __str__(self):
        return f"{self.nid} {Constd.keyword} {self.sid_line.nid} {self.value} {self.comment}"

class Const(Constant):
    keyword = 'const'

    def __init__(self, nid, sid, value, comment, line_no):
        super().__init__(nid, sid, value, comment, line_no)

    def __str__(self):
        size = self.sid_line.size
        return f"{self.nid} {Const.keyword} {self.sid_line.nid} {self.value:0{size}b} {self.comment}"

class Consth(Constant):
    keyword = 'consth'

    def __init__(self, nid, sid, value, comment, line_no):
        super().__init__(nid, sid, value, comment, line_no)

    def __str__(self):
        size = math.ceil(self.sid_line.size / 4)
        return f"{self.nid} {Consth.keyword} {self.sid_line.nid} {self.value:0{size}X} {self.comment}"

class Variable(Expression):
    def __init__(self, nid, sid, symbol, comment, line_no):
        super().__init__(nid, sid, comment, line_no)
        self.symbol = symbol

class Input(Variable):
    keyword = 'input'

    def __init__(self, nid, sid, symbol, comment, line_no):
        super().__init__(nid, sid, symbol, comment, line_no)

    def __str__(self):
        return f"{self.nid} {Input.keyword} {self.sid_line.nid} {self.symbol} {self.comment}"

class State(Variable):
    keyword = 'state'

    states = dict()

    def __init__(self, nid, sid, symbol, comment, line_no):
        super().__init__(nid, sid, symbol, comment, line_no)
        self.new_state()

    def __str__(self):
        return f"{self.nid} {State.keyword} {self.sid_line.nid} {self.symbol} {self.comment}"

    def new_state(self):
        assert self not in State.states
        State.states[self.nid] = self

class Indexed(Expression):
    def __init__(self, nid, sid, arg1_nid, comment, line_no):
        super().__init__(nid, sid, comment, line_no)
        self.arg1_line = Line.get(arg1_nid)

class Ext(Indexed):
    keywords = {'sext', 'uext'}

    def __init__(self, nid, sid, op, arg1_nid, w, comment, line_no):
        super().__init__(nid, sid, arg1_nid, comment, line_no)
        self.op = op
        self.w = w

    def __str__(self):
        return f"{self.nid} {self.op} {self.sid_line.nid} {self.arg1_line.nid} {self.w} {self.comment}"

class Slice(Indexed):
    keyword = 'slice'

    def __init__(self, nid, sid, arg1_nid, u, l, comment, line_no):
        super().__init__(nid, sid, arg1_nid, comment, line_no)
        self.u = u
        self.l = l

    def __str__(self):
        return f"{self.nid} {Slice.keyword} {self.sid_line.nid} {self.arg1_line.nid} {self.u} {self.l} {self.comment}"

class Unary(Expression):
    keywords = {'not', 'inc', 'dec', 'neg'}

    def __init__(self, nid, sid, op, arg1_nid, comment, line_no):
        super().__init__(nid, sid, comment, line_no)
        self.op = op
        self.arg1_line = Line.get(arg1_nid)

    def __str__(self):
        return f"{self.nid} {self.op} {self.sid_line.nid} {self.arg1_line.nid} {self.comment}"

class Binary(Expression):
    keywords = {'implies', 'eq', 'neq', 'sgt', 'ugt', 'sgte', 'ugte', 'slt', 'ult', 'slte', 'ulte', 'and', 'or', 'xor', 'sll', 'srl', 'sra', 'add', 'sub', 'mul', 'sdiv', 'udiv', 'srem', 'urem', 'concat', 'read'}

    def __init__(self, nid, sid, op, arg1_nid, arg2_nid, comment, line_no):
        super().__init__(nid, sid, comment, line_no)
        self.op = op
        self.arg1_line = Line.get(arg1_nid)
        self.arg2_line = Line.get(arg2_nid)

    def __str__(self):
        return f"{self.nid} {self.op} {self.sid_line.nid} {self.arg1_line.nid} {self.arg2_line.nid} {self.comment}"

class Ternary(Expression):
    keywords = {'ite', 'write'}

    def __init__(self, nid, sid, op, arg1_nid, arg2_nid, arg3_nid, comment, line_no):
        super().__init__(nid, sid, comment, line_no)
        self.op = op
        self.arg1_line = Line.get(arg1_nid)
        self.arg2_line = Line.get(arg2_nid)
        self.arg3_line = Line.get(arg3_nid)

    def __str__(self):
        return f"{self.nid} {self.op} {self.sid_line.nid} {self.arg1_line.nid} {self.arg2_line.nid} {self.arg3_line.nid} {self.comment}"

class Init(Line):
    keyword = 'init'

    def __init__(self, nid, sid, state_nid, exp_nid, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.sid_line = Line.get(sid)
        self.state_line = Line.get(state_nid)
        self.exp_line = Line.get(exp_nid)

    def __str__(self):
        return f"{self.nid} {Init.keyword} {self.sid_line.nid} {self.state_line.nid} {self.exp_line.nid} {self.comment}"

class Next(Line):
    keyword = 'next'

    nexts = dict()

    def __init__(self, nid, sid, state_nid, exp_nid, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.sid_line = Line.get(sid)
        self.state_line = Line.get(state_nid)
        self.exp_line = Line.get(exp_nid)
        self.new_next()

    def __str__(self):
        return f"{self.nid} {Next.keyword} {self.sid_line.nid} {self.state_line.nid} {self.exp_line.nid} {self.comment}"

    def new_next(self):
        assert self not in Next.nexts
        Next.nexts[self.nid] = self

class Property(Line):
    def __init__(self, nid, property_nid, symbol, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.property_line = Line.get(property_nid)
        self.symbol = symbol

class Constraint(Property):
    keyword = 'constraint'

    constraints = dict()

    def __init__(self, nid, property_nid, symbol, comment, line_no):
        super().__init__(nid, property_nid, symbol, comment, line_no)
        self.new_constraint()

    def __str__(self):
        return f"{self.nid} {Constraint.keyword} {self.property_line.nid} {self.symbol} {self.comment}"

    def new_constraint(self):
        assert self not in Constraint.constraints
        Constraint.constraints[self.nid] = self

class Bad(Property):
    keyword = 'bad'

    bads = dict()

    def __init__(self, nid, property_nid, symbol, comment, line_no):
        super().__init__(nid, property_nid, symbol, comment, line_no)
        self.new_bad()

    def __str__(self):
        return f"{self.nid} {Bad.keyword} {self.property_line.nid} {self.symbol} {self.comment}"

    def new_bad(self):
        assert self not in Bad.bads
        Bad.bads[self.nid] = self

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

def get_nid(tokens, clss, expected, line_no):
    nid = get_decimal(tokens, expected, line_no)
    if Line.is_defined(nid):
        if isinstance(Line.get(nid), clss):
            return nid
        else:
            raise syntax_error(expected, line_no)
    else:
        raise syntax_error(f"defined {expected}", line_no)

def get_bitvec_sid(tokens, line_no):
    return get_nid(tokens, Bitvec, "bitvector sort nid", line_no)

def get_sid(tokens, line_no):
    return get_nid(tokens, Sort, "sort nid", line_no)

def get_state_nid(tokens, line_no):
    return get_nid(tokens, State, "state nid", line_no)

def get_exp_nid(tokens, line_no):
    return get_nid(tokens, Expression, "expression nid", line_no)

def get_number(tokens, sid, base, expected, line_no):
    token = get_token(tokens, expected, line_no)
    try:
        if (base == 10):
            value = int(token)
        else:
            value = int(token, base)
    except ValueError:
        raise syntax_error(expected, line_no)
    if value < 2**Line.get(sid).size:
        return value
    else:
        raise syntax_error(f"{value} in range of {Line.get(sid).size}-bit bitvector", line_no)

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
        return Bitvec(nid, size, comment, line_no)
    elif token == Array.keyword:
        array_size_sid = get_bitvec_sid(tokens, line_no)
        element_size_sid = get_bitvec_sid(tokens, line_no)
        comment = get_comment(tokens, line_no)
        return Array(nid, array_size_sid, element_size_sid, comment, line_no)
    else:
        raise syntax_error("bitvector or array", line_no)

def parse_zero_one_line(tokens, nid, clss, line_no):
    sid = get_bitvec_sid(tokens, line_no)
    comment = get_comment(tokens, line_no)
    return clss(nid, sid, comment, line_no)

def parse_constant_line(tokens, nid, clss, line_no):
    sid = get_bitvec_sid(tokens, line_no)
    if clss is Constd:
        value = get_number(tokens, sid, 10, "signed integer", line_no)
    elif clss is Const:
        value = get_number(tokens, sid, 2, "binary number", line_no)
    elif clss is Consth:
        value = get_number(tokens, sid, 16, "hexadecimal number", line_no)
    comment = get_comment(tokens, line_no)
    return clss(nid, sid, value, comment, line_no)

def parse_symbol_comment(tokens, line_no):
    symbol = get_symbol(tokens)
    comment = get_comment(tokens, line_no)
    if symbol != "":
        if symbol[0] == ';':
            return "", symbol
    return symbol, comment

def parse_variable_line(tokens, nid, clss, line_no):
    sid = get_sid(tokens, line_no)
    symbol, comment = parse_symbol_comment(tokens, line_no)
    return clss(nid, sid, symbol, comment, line_no)

def parse_ext_line(tokens, nid, op, line_no):
    sid = get_sid(tokens, line_no)
    arg1_nid = get_exp_nid(tokens, line_no)
    w = get_decimal(tokens, "bit width", line_no)
    comment = get_comment(tokens, line_no)
    return Ext(nid, sid, op, arg1_nid, w, comment, line_no)

def parse_slice_line(tokens, nid, line_no):
    sid = get_sid(tokens, line_no)
    arg1_nid = get_exp_nid(tokens, line_no)
    u = get_decimal(tokens, "upper bit", line_no)
    l = get_decimal(tokens, "lower bit", line_no)
    comment = get_comment(tokens, line_no)
    return Slice(nid, sid, arg1_nid, u, l, comment, line_no)

def parse_unary_line(tokens, nid, op, line_no):
    sid = get_sid(tokens, line_no)
    arg1_nid = get_exp_nid(tokens, line_no)
    comment = get_comment(tokens, line_no)
    return Unary(nid, sid, op, arg1_nid, comment, line_no)

def parse_binary_line(tokens, nid, op, line_no):
    sid = get_sid(tokens, line_no)
    arg1_nid = get_exp_nid(tokens, line_no)
    arg2_nid = get_exp_nid(tokens, line_no)
    comment = get_comment(tokens, line_no)
    return Binary(nid, sid, op, arg1_nid, arg2_nid, comment, line_no)

def parse_ternary_line(tokens, nid, op, line_no):
    sid = get_sid(tokens, line_no)
    arg1_nid = get_exp_nid(tokens, line_no)
    arg2_nid = get_exp_nid(tokens, line_no)
    arg3_nid = get_exp_nid(tokens, line_no)
    comment = get_comment(tokens, line_no)
    return Ternary(nid, sid, op, arg1_nid, arg2_nid, arg3_nid, comment, line_no)

def parse_init_next_line(tokens, nid, clss, line_no):
    sid = get_sid(tokens, line_no)
    state_nid = get_state_nid(tokens, line_no)
    exp_nid = get_exp_nid(tokens, line_no)
    comment = get_comment(tokens, line_no)
    return clss(nid, sid, state_nid, exp_nid, comment, line_no)

def parse_property_line(tokens, nid, clss, line_no):
    property_nid = get_exp_nid(tokens, line_no)
    symbol, comment = parse_symbol_comment(tokens, line_no)
    return clss(nid, property_nid, symbol, comment, line_no)

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
                    elif token == Zero.keyword:
                        return parse_zero_one_line(tokens, nid, Zero, line_no)
                    elif token == One.keyword:
                        return parse_zero_one_line(tokens, nid, One, line_no)
                    elif token == Constd.keyword:
                        return parse_constant_line(tokens, nid, Constd, line_no)
                    elif token == Const.keyword:
                        return parse_constant_line(tokens, nid, Const, line_no)
                    elif token == Consth.keyword:
                        return parse_constant_line(tokens, nid, Consth, line_no)
                    elif token == Input.keyword:
                        return parse_variable_line(tokens, nid, Input, line_no)
                    elif token == State.keyword:
                        return parse_variable_line(tokens, nid, State, line_no)
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
                    elif token == Init.keyword:
                        return parse_init_next_line(tokens, nid, Init, line_no)
                    elif token == Next.keyword:
                        return parse_init_next_line(tokens, nid, Next, line_no)
                    elif token == Constraint.keyword:
                        return parse_property_line(tokens, nid, Constraint, line_no)
                    elif token == Bad.keyword:
                        return parse_property_line(tokens, nid, Bad, line_no)
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
            except syntax_error as message:
                print(message)
                exit(1)

if __name__ == '__main__':
    main()