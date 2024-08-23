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

class Bitvec:
    def __init__(self, nid, size, comment, line_no):
        self.nid = nid
        self.size = size
        self.comment = comment
        self.line_no = line_no
        new_line(self)

    def __str__(self):
        return f"{self.nid} sort bitvec {self.size} {self.comment}"

class Array:
    def __init__(self, nid, array_size_nid, element_size_nid, comment, line_no):
        self.nid = nid
        if isinstance(retrieve_line(array_size_nid), Bitvec):
            self.array_size_line = retrieve_line(array_size_nid)
        else:
            raise syntax_error("array size bitvec nid", line_no)
        if isinstance(retrieve_line(element_size_nid), Bitvec):
            self.element_size_line = retrieve_line(element_size_nid)
        else:
            raise syntax_error("element size bitvec nid", line_no)
        self.comment = comment
        self.line_no = line_no
        new_line(self)

    def __str__(self):
        return f"{self.nid} sort array {self.array_size_line.nid} {self.element_size_line.nid} {self.comment}"

class Const:
    def __init__(self, nid, op, sid, value, comment, line_no):
        self.nid = nid
        self.op = op
        if isinstance(retrieve_line(sid), Bitvec):
            self.sid_line = retrieve_line(sid)
        else:
            raise syntax_error(f"{op} bitvec nid", line_no)
        self.value = value
        self.comment = comment
        self.line_no = line_no
        new_line(self)

    def __str__(self):
        if (self.op in {'zero', 'one'}):
            return f"{self.nid} {self.op} {self.sid_line.nid} {self.comment}"
        elif (self.op == 'constd'):
            value = self.value
        elif (self.op == 'const'):
            value = f"{self.value:b}"
        elif (self.op == 'consth'):
            value = f"{self.value:x}"
        return f"{self.nid} {self.op} {self.sid_line.nid} {value} {self.comment}"

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

def get_nid(tokens, expected, line_no):
    global lines
    nid = get_decimal(tokens, expected, line_no)
    if nid in lines:
        return nid
    else:
        raise syntax_error(f"defined {expected}", line_no)

def get_number(tokens, base, expected, line_no):
    token = get_token(tokens, expected, line_no)
    try:
        if (base == 10):
            return int(token)
        else:
            return int(token, base)
    except ValueError:
        raise syntax_error(expected, line_no)

def get_comment(tokens):
    try:
        return get_token(tokens, None, None)
    except:
        return ""

def parse_sort_line(tokens, nid, line_no):
    token = get_token(tokens, "bitvec or array", line_no)
    if token == 'bitvec':
        size = get_decimal(tokens, "bitvec size", line_no)
        comment = get_comment(tokens)
        return Bitvec(nid, size, comment, line_no)
    elif token == 'array':
        array_size_nid = get_nid(tokens, "array size nid", line_no)
        element_size_nid = get_nid(tokens, "element size nid", line_no)
        comment = get_comment(tokens)
        return Array(nid, array_size_nid, element_size_nid, comment, line_no)
    else:
        raise syntax_error("bitvec or array", line_no)

def parse_zero_one_line(tokens, nid, value, line_no):
    sid = get_nid(tokens, "sort nid", line_no)
    comment = get_comment(tokens)
    if (value == 0):
        return Const(nid, 'zero', sid, value, comment, line_no)
    else:
        return Const(nid, 'one', sid, value, comment, line_no)

def parse_constd_line(tokens, nid, line_no):
    sid = get_nid(tokens, "sort nid", line_no)
    value = get_number(tokens, 10, "signed integer", line_no)
    comment = get_comment(tokens)
    return Const(nid, 'constd', sid, value, comment, line_no)

def parse_const_line(tokens, nid, line_no):
    sid = get_nid(tokens, "sort nid", line_no)
    value = get_number(tokens, 2, "binary number", line_no)
    comment = get_comment(tokens)
    return Const(nid, 'const', sid, value, comment, line_no)

def parse_consth_line(tokens, nid, line_no):
    sid = get_nid(tokens, "sort nid", line_no)
    value = get_number(tokens, 16, "hexadecimal number", line_no)
    comment = get_comment(tokens)
    return Const(nid, 'consth', sid, value, comment, line_no)

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