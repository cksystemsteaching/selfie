#!/usr/bin/env python3

import re

def tokenize_btor2(line):
    btor2_token_pattern = r"(;.*|[^; \n\r]+|-?\d+|[0-1]|[0-9a-fA-F]+)"
    tokens = re.findall(btor2_token_pattern, line)
    return tokens

def syntax_error(expected, line_no):
    print("syntax error in line %u: expected %s" % (line_no, expected))
    return False

def parse_sort(tokens, nid, line_no):
    try:
        token = tokens[1]
    except:
        return syntax_error("bitvec or array", line_no)
    if token == 'bitvec':
        try:
            token = tokens[2]
        except:
            return syntax_error("size", line_no)
        if token.isdecimal():
            size = int(token)
            print("%u sort bitvec %u" % (nid, size))
        else:
            return syntax_error("size", line_no)
    elif token == 'array':
        return True
    else:
        return syntax_error("bitvec or array", line_no)
    return True

def parse_btor2(line, line_no):
    if line.strip():
        tokens = tokenize_btor2(line)
        token = tokens[0]
        if token[0] != ';':
            if token.isdecimal():
                nid = int(token)
                try:
                    token = tokens[1]
                except:
                    return syntax_error("keyword", line_no)
                if token == 'sort':
                    return parse_sort(tokens[1:], nid, line_no)
            else:
                return syntax_error("nid", line_no)
    return True

import argparse

def main():
    parser = argparse.ArgumentParser(prog='bitme',
        description='What the program does',
        epilog='Text at the bottom of help')

    parser.add_argument('modelfile')

    args = parser.parse_args()

    with open(args.modelfile) as modelfile:
        line_no = 1
        for line in modelfile:
            if parse_btor2(line, line_no):
                line_no = line_no + 1
            else:
                exit(1)

if __name__ == "__main__":
    main()