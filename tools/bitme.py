#!/usr/bin/env python3

import re

def tokenize_btor2(line):
    btor2_token_pattern = r"(;.*|[^; \n\r]+|-?\d+|[0-1]|[0-9a-fA-F]+)"
    tokens = re.findall(btor2_token_pattern, line)
    return tokens

def parse_btor2(line, line_no):
    # parses line tokens in btor2 file and prints them as is
    if line.strip():
        for token in tokenize_btor2(line)[:-1]:
            print(token, end=" ")
        print(tokenize_btor2(line)[-1], end="")
    print()

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
            parse_btor2(line, line_no)
            line_no = line_no + 1

if __name__ == "__main__":
    main()