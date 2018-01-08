Copyright (c) 2015-2018, the Selfie Project authors. All rights reserved. Please see the AUTHORS file for details. Use of this source code is governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the Department of Computer Sciences of the University of Salzburg in Austria. For further information and code please refer to:

http://selfie.cs.uni-salzburg.at

This is the grammar of the C Star (C\*) programming language.

C\* is a tiny subset of the programming language C. C\* features global variable declarations with optional initialization as well as procedures with parameters and local variables. C\* has five statements (assignment, while loop, if-then-else, procedure call, and return) and standard arithmetic (`+`, `-`, `*`, `/`, `%`) and comparison (`==`, `!=`, `<`, `<=`, `>`, `>=`) operators. C\* includes the unary `*` operator for dereferencing pointers hence the name but excludes data types other than `uint64_t` and `uint64_t*`, bitwise and Boolean operators, and many other features. The C\* grammar is LL(1) with six keywords and 22 symbols. Whitespace is ignored including one-line comments (`//`).

C\* Keywords: `uint64_t`, `while`, `if`, `else`, `return`, `void`

C\* Symbols: `=`, `+`, `-`, `*`, `/`, `%`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `,`, `(`, `)`, `{`, `}`, `;`, `integer`, `character`, `string`, `identifier`

with:

```
integer    = digit { digit } .

character  = "'" printable_character "'" .

string     = """ { printable_character } """ .

identifier = letter { letter | digit | "_" } .
```

and:

```
digit  = "0" | ... | "9" .

letter = "a" | ... | "z" | "A" | ... | "Z" .
```

C\* Grammar:

```
cstar            = { type identifier [ "=" [ cast ] [ "-" ] literal ] ";" |
                   ( "void" | type ) identifier procedure } .

type             = "uint64_t" [ "*" ] .

cast             = "(" type ")" .

literal          = integer | character .

procedure        = "(" [ variable { "," variable } ] ")"
                    ( ";" | "{" { variable ";" } { statement } "}" ) .

variable         = type identifier .

statement        = call ";" | while | if | return ";" |
                   ( [ "*" ] identifier | "*" "(" expression ")" )
                     "=" expression ";" .

call             = identifier "(" [ expression { "," expression } ] ")" .

expression       = simpleExpression [ ( "==" | "!=" | "<" | ">" | "<=" | ">=" ) simpleExpression ] .

simpleExpression = [ "-" ] term { ( "+" | "-" ) term } .

term             = factor { ( "*" | "/" | "%" ) factor } .

factor           = [ cast ]
                    ( [ "*" ] ( identifier | "(" expression ")" ) |
                      call |
                      literal |
                      string ) .

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
```