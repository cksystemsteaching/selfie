Copyright (c) 2015, the Selfie Project authors. All rights reserved. Please see the AUTHORS file for details. Use of this source code is governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the Department of Computer Sciences of the University of Salzburg in Austria. For further information and code please refer to:

http://selfie.cs.uni-salzburg.at

This is the grammar of the C Star (C*) programming language.

C* is a small Turing-complete subset of C that includes dereferencing (the * operator) but excludes data structures, Boolean expressions, and many other features. C* is supposed to be close to the minimum necessary for implementing a self-compiling, single-pass, recursive-descent compiler.

Keywords: int, while, if, else, return, void

```
digit            = "0" | ... | "9" .

integer          = digit { digit } .

letter           = "a" | ... | "z" | "A" | ... | "Z" .

identifier       = letter { letter | digit | "_" } .

type             = "int" [ "*" ] .

cast             = "(" type ")" .

call             = identifier "(" [ expression { "," expression } ] ")" .

factor           = [ cast ] 
                    ( [ "*" ] ( identifier | "(" expression ")" ) |
                      call |
                      integer |
                      """ { ascii_character } """ |
                      "'" ascii_character "'" ) .

term             = factor { ( "*" | "/" | "%" ) factor } .

simpleExpression = [ "-" ] term { ( "+" | "-" ) term } .

expression       = simpleExpression [ ( "==" | "!=" | "<" | ">" | "<=" | ">=" ) simpleExpression ] .

while            = "while" "(" expression ")" 
                             ( statement |
                               "{" { statement } "}" ) .

if               = "if" "(" expression ")" 
                             ( statement | 
                               "{" { statement } "}" ) 
                         [ "else"
                             ( statement |
                               "{" { statement } "}" ) ] .

return           = "return" [ expression ] .

statement        = ( [ "*" ] identifier | "*" "(" expression ")" ) "="
                      expression ";" |
                    call ";" | 
                    while | 
                    if | 
                    return ";" .

variable         = type identifier .

procedure        = "(" [ variable { "," variable } ] ")" 
                    ( ";" | "{" { variable ";" } { statement } "}" ) .

cstar            = { type identifier ";" | ( "void" | type ) identifier procedure } .
```