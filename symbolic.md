Copyright (c) 2015-2018, the Selfie Project authors. All rights reserved. Please see the AUTHORS file for details. Use of this source code is governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the Department of Computer Sciences of the University of Salzburg in Austria. For further information and code please refer to:

http://selfie.cs.uni-salzburg.at

This is the grammar restriction on symbolic expressions handled by Monster, the selfie symbolic emulator.
It concerns expression containing one or more symbolic variables, that is to say somehow linked to an input.

```
symbolicExpression    =   ( simpleExpression [ ( "<" | ">" | "<=" | ">=" ) simpleExpression ] )
                        | ( minuendFreeExpression ( "==" | "!=" ) minuendFreeExpression ).

simpleExpression      = ["-"] ( sumExpression )
                            | ( term "-" sumExpression ).

sumExpression         =  term { "+" term }.

term                  =   ConcreteFactor [ ( "*" | "/" | "%" ) factor ]
                        | factor .

factor                = [ cast ] [ "-" ] [ "*" ]
                    ( identifier | call | literal | string | "(" expression ")" ) .

ConcreteFactor        = [ cast ] [ "-" ] [ "*" ]
                    ( identifier | call | literal | string ) .

```
