#!/usr/bin/env python3

import re

current_nid = 0

lines = dict()

def tokenize_btor2(line):
    btor2_token_pattern = r"(;.*|[^; \n\r]+|-?\d+|[0-1]|[0-9a-fA-F]+)"
    tokens = re.findall(btor2_token_pattern, line)
    return tokens

def syntax_error(expected, line_no):
    print("syntax error in line %u: %s expected" % (line_no, expected))
    return False

def get_token(tokens):
    return tokens.pop(0) if tokens else False

def get_comment(tokens):
    comment = get_token(tokens)
    return comment if comment else ""

def get_decimal(tokens, line_no):
    token = get_token(tokens)
    if token is not False:
        if token.isdecimal():
            return int(token)
    return syntax_error("decimal", line_no)

def get_nid(tokens, line_no):
    global lines
    nid = get_decimal(tokens, line_no)
    if nid is not False:
        if nid in lines:
            return nid
        return syntax_error("defined nid", line_no)
    return syntax_error("nid", line_no)

def define_nid(nid):
    global lines
    lines[nid] = nid

def parse_sort_line(tokens, nid, line_no):
    global lines
    token = get_token(tokens)
    if token is not False:
        if token == 'bitvec':
            size = get_decimal(tokens, line_no)
            if size is not False:
                comment = get_comment(tokens)
                define_nid(nid)
                print("%u sort bitvec %u %s" % (nid, size, comment))
                return nid
            return syntax_error("bitvec size", line_no)
        elif token == 'array':
            array_size = get_nid(tokens, line_no)
            if array_size is not False:
                element_size = get_nid(tokens, line_no)
                if element_size is not False:
                    comment = get_comment(tokens)
                    define_nid(nid)
                    print("%u sort array %u %u %s" % (nid, array_size, element_size, comment))
                    return nid
                return syntax_error("element size", line_no)
            return syntax_error("array size", line_no)
    return syntax_error("bitvec or array", line_no)

def parse_btor2_line(line, line_no):
    global current_nid
    if line.strip():
        tokens = tokenize_btor2(line)
        token = get_token(tokens)
        if token[0] != ';':
            if token.isdecimal():
                nid = int(token)
                if nid > current_nid:
                    current_nid = nid
                    token = get_token(tokens)
                    if token is not False:
                        if token == 'sort':
                            return parse_sort_line(tokens, nid, line_no)
                        return True
                    return syntax_error("keyword", line_no)
                return syntax_error("increasing nid", line_no)
            return syntax_error("nid", line_no)
    return True

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
            if parse_btor2_line(line, line_no):
                line_no = line_no + 1
            else:
                exit(1)

if __name__ == '__main__':
    main()