#!/usr/bin/env python3

import re

class syntax_error(Exception):
    def __init__(self, expected, line_no):
        super().__init__(f"syntax error in line {line_no}: {expected} expected")

current_nid = 0

lines = dict()

def new_line(line):
    global lines
    assert line not in lines
    lines[line.nid] = line
    return line

def retrieve_line(nid):
    global lines
    assert nid in lines
    return lines[nid]

class Line:
    def __init__(self, nid, comment, line_no):
        self.nid = nid
        self.comment = comment
        self.line_no = line_no
        new_line(self)

class Sort(Line):
    def __init__(self, nid, comment, line_no):
        super().__init__(nid, comment, line_no)

class Bitvec(Sort):
    def __init__(self, nid, size, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.size = size

    def __str__(self):
        return f"{self.nid} sort bitvec {self.size} {self.comment}"

class Array(Sort):
    def __init__(self, nid, array_size_sid, element_size_sid, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.array_size_line = retrieve_line(array_size_sid)
        self.element_size_line = retrieve_line(element_size_sid)

    def __str__(self):
        return f"{self.nid} sort array {self.array_size_line.nid} {self.element_size_line.nid} {self.comment}"

class Expression(Line):
    def __init__(self, nid, sid, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.sid_line = retrieve_line(sid)

class Constant(Expression):
    def __init__(self, nid, sid, value, comment, line_no):
        super().__init__(nid, sid, comment, line_no)
        self.value = value

class Zero(Constant):
    def __init__(self, nid, sid, comment, line_no):
        super().__init__(nid, sid, 0, comment, line_no)

    def __str__(self):
        return f"{self.nid} zero {self.sid_line.nid} {self.comment}"

class One(Constant):
    def __init__(self, nid, sid, comment, line_no):
        super().__init__(nid, sid, 1, comment, line_no)

    def __str__(self):
        return f"{self.nid} one {self.sid_line.nid} {self.comment}"

class Constd(Constant):
    def __init__(self, nid, sid, value, comment, line_no):
        super().__init__(nid, sid, value, comment, line_no)

    def __str__(self):
        return f"{self.nid} constd {self.sid_line.nid} {self.value} {self.comment}"

class Const(Constant):
    def __init__(self, nid, sid, value, comment, line_no):
        super().__init__(nid, sid, value, comment, line_no)

    def __str__(self):
        return f"{self.nid} const {self.sid_line.nid} {self.value:b} {self.comment}"

class Consth(Constant):
    def __init__(self, nid, sid, value, comment, line_no):
        super().__init__(nid, sid, value, comment, line_no)

    def __str__(self):
        return f"{self.nid} consth {self.sid_line.nid} {self.value:x} {self.comment}"

class Variable(Expression):
    def __init__(self, nid, sid, symbol, comment, line_no):
        super().__init__(nid, sid, comment, line_no)
        self.symbol = symbol

class Input(Variable):
    def __init__(self, nid, sid, symbol, comment, line_no):
        super().__init__(nid, sid, symbol, comment, line_no)

    def __str__(self):
        return f"{self.nid} input {self.sid_line.nid} {self.symbol} {self.comment}"

class State(Variable):
    def __init__(self, nid, sid, symbol, comment, line_no):
        super().__init__(nid, sid, symbol, comment, line_no)

    def __str__(self):
        return f"{self.nid} state {self.sid_line.nid} {self.symbol} {self.comment}"

class Init(Line):
    def __init__(self, nid, sid, state_nid, value_nid, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.sid_line = retrieve_line(sid)
        self.state_line = retrieve_line(state_nid)
        self.value_line = retrieve_line(value_nid)

    def __str__(self):
        return f"{self.nid} init {self.sid_line.nid} {self.state_line.nid} {self.value_line.nid} {self.comment}"

class Next(Line):
    def __init__(self, nid, sid, state_nid, value_nid, comment, line_no):
        super().__init__(nid, comment, line_no)
        self.sid_line = retrieve_line(sid)
        self.state_line = retrieve_line(state_nid)
        self.value_line = retrieve_line(value_nid)

    def __str__(self):
        return f"{self.nid} next {self.sid_line.nid} {self.state_line.nid} {self.value_line.nid} {self.comment}"

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

def get_nid(tokens, line, expected, line_no):
    global lines
    nid = get_decimal(tokens, expected, line_no)
    if nid in lines:
        if isinstance(retrieve_line(nid), line):
            return nid
        else:
            raise syntax_error(expected, line_no)
    else:
        raise syntax_error(f"defined {expected}", line_no)

def get_bitvec_sid(tokens, line_no):
    return get_nid(tokens, Bitvec, "bitvec sort nid", line_no)

def get_sid(tokens, line_no):
    return get_nid(tokens, Sort, "sort nid", line_no)

def get_state_nid(tokens, line_no):
    return get_nid(tokens, State, "state nid", line_no)

def get_value_nid(tokens, line_no):
    return get_nid(tokens, Expression, "value nid", line_no)

def get_number(tokens, base, expected, line_no):
    token = get_token(tokens, expected, line_no)
    try:
        # TODO: check value range
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
    token = get_token(tokens, "bitvec or array", line_no)
    if token == 'bitvec':
        size = get_decimal(tokens, "bitvec size", line_no)
        comment = get_comment(tokens, line_no)
        return Bitvec(nid, size, comment, line_no)
    elif token == 'array':
        array_size_sid = get_bitvec_sid(tokens, line_no)
        element_size_sid = get_bitvec_sid(tokens, line_no)
        comment = get_comment(tokens, line_no)
        return Array(nid, array_size_sid, element_size_sid, comment, line_no)
    else:
        raise syntax_error("bitvec or array", line_no)

def parse_zero_one_line(tokens, nid, value, line_no):
    sid = get_bitvec_sid(tokens, line_no)
    comment = get_comment(tokens, line_no)
    if (value == 0):
        return Zero(nid, sid, comment, line_no)
    else:
        return One(nid, sid, comment, line_no)

def parse_constd_line(tokens, nid, line_no):
    sid = get_bitvec_sid(tokens, line_no)
    value = get_number(tokens, 10, "signed integer", line_no)
    comment = get_comment(tokens, line_no)
    return Constd(nid, sid, value, comment, line_no)

def parse_const_line(tokens, nid, line_no):
    sid = get_bitvec_sid(tokens, line_no)
    value = get_number(tokens, 2, "binary number", line_no)
    comment = get_comment(tokens, line_no)
    return Const(nid, sid, value, comment, line_no)

def parse_consth_line(tokens, nid, line_no):
    sid = get_bitvec_sid(tokens, line_no)
    value = get_number(tokens, 16, "hexadecimal number", line_no)
    comment = get_comment(tokens, line_no)
    return Consth(nid, sid, value, comment, line_no)

def parse_symbol_comment(tokens, line_no):
    symbol = get_symbol(tokens)
    comment = get_comment(tokens, line_no)
    if symbol != "":
        if symbol[0] == ';':
            return "", symbol
    return symbol, comment

def parse_input_line(tokens, nid, line_no):
    sid = get_sid(tokens, line_no)
    symbol, comment = parse_symbol_comment(tokens, line_no)
    return Input(nid, sid, symbol, comment, line_no)

def parse_state_line(tokens, nid, line_no):
    sid = get_sid(tokens, line_no)
    symbol, comment = parse_symbol_comment(tokens, line_no)
    return State(nid, sid, symbol, comment, line_no)

def parse_init_line(tokens, nid, line_no):
    sid = get_sid(tokens, line_no)
    state_nid = get_state_nid(tokens, line_no)
    value_nid = get_value_nid(tokens, line_no)
    comment = get_comment(tokens, line_no)
    return Init(nid, sid, state_nid, value_nid, comment, line_no)

def parse_next_line(tokens, nid, line_no):
    sid = get_sid(tokens, line_no)
    state_nid = get_state_nid(tokens, line_no)
    value_nid = get_value_nid(tokens, line_no)
    comment = get_comment(tokens, line_no)
    return Next(nid, sid, state_nid, value_nid, comment, line_no)

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
                    if token == 'sort':
                        print(parse_sort_line(tokens, nid, line_no))
                    elif token == 'zero':
                        print(parse_zero_one_line(tokens, nid, 0, line_no))
                    elif token == 'one':
                        print(parse_zero_one_line(tokens, nid, 1, line_no))
                    elif token == 'constd':
                        print(parse_constd_line(tokens, nid, line_no))
                    elif token == 'const':
                        print(parse_const_line(tokens, nid, line_no))
                    elif token == 'consth':
                        print(parse_consth_line(tokens, nid, line_no))
                    elif token == 'input':
                        print(parse_input_line(tokens, nid, line_no))
                    elif token == 'state':
                        print(parse_state_line(tokens, nid, line_no))
                    elif token == 'init':
                        print(parse_init_line(tokens, nid, line_no))
                    elif token == 'next':
                        print(parse_next_line(tokens, nid, line_no))
                    return
                raise syntax_error("increasing nid", line_no)
            raise syntax_error("nid", line_no)

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
                parse_btor2_line(line, line_no)
                line_no = line_no + 1
            except syntax_error as message:
                print(message)
                exit(1)

if __name__ == '__main__':
    main()