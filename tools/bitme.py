#!/usr/bin/env python3

import re

def tokenize_btor2(line):
    btor2_token_pattern = r"(;.*|[^; \n\r]+|-?\d+|[0-1]|[0-9a-fA-F]+)"
    tokens = re.findall(btor2_token_pattern, line)
    return tokens

def syntax_error(expected, line_no):
    print("syntax error in line %u: expected %s" % (line_no, expected))
    return False

def get_token(tokens):
    return tokens.pop(0) if tokens else False

def get_comment(tokens):
    comment = get_token(tokens)
    return comment if comment else ""

def parse_sort(tokens, nid, line_no):
    token = get_token(tokens)
    if token is not False:
        if token == 'bitvec':
            token = get_token(tokens)
            if token is not False:
                if token.isdecimal():
                    size = int(token)
                    comment = get_comment(tokens)
                    print("%u sort bitvec %u %s" % (nid, size, comment))
                    return True
            return syntax_error("bitvec size", line_no)
        elif token == 'array':
            token = get_token(tokens)
            if token is not False:
                if token.isdecimal():
                    array_size = int(token)
                    token = get_token(tokens)
                    if token is not False:
                        if token.isdecimal():
                            element_size = int(token)
                            comment = get_comment(tokens)
                            print("%u sort array %u %u %s" % (nid, array_size, element_size, comment))
                            return True
                    return syntax_error("element size", line_no)
            return syntax_error("array size", line_no)
    return syntax_error("bitvec or array", line_no)

def parse_btor2(line, line_no):
    if line.strip():
        tokens = tokenize_btor2(line)
        token = get_token(tokens)
        if token[0] != ';':
            if token.isdecimal():
                nid = int(token)
                token = get_token(tokens)
                if token is not False:
                    if token == 'sort':
                        return parse_sort(tokens, nid, line_no)
                    else:
                        return True
                return syntax_error("keyword", line_no)
            else:
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
            if parse_btor2(line, line_no):
                line_no = line_no + 1
            else:
                exit(1)

if __name__ == '__main__':
    main()