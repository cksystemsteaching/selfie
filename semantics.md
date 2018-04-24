Copyright (c) 2015-2018, the Selfie Project authors. All rights reserved. Please see the AUTHORS file for details. Use of this source code is governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the Department of Computer Sciences of the University of Salzburg in Austria. For further information and code please refer to:

http://selfie.cs.uni-salzburg.at

The following describes the semantical differences between C\* and C:  

## Interpretation of integer literals 

In C integer literals are interpreted as 32-bit signed integers by default, whereas in C\* the literals are interpreted as 64-bit unsigned integers. Therefore expressions including operators with different semantics for 32-bit signed and 64-bit unsigned integers and only literals as operands of those operators have different semantics in C and C\*. In the C\* grammar the following operators are affected by this, because they have different semantics for signed and unsigned operands: `/` `<` `<=` `>` `>=` 

### Operator: `/`

Code example:  

```  
uint64_t x;

x = 100 / (-20);
```

Result in C\* semantics:

`x == 0`

Result in C semantics:

`x == -5`

### Comparison operators

Code example:  

```  
uint64_t a;
uint64_t b;
uint64_t c;
uint64_t d;

a = 1 <  -1;
b = 1 <= -1;
c = 1 >  -1;
d = 1 >= -1;
```

Result in C\* semantics:

```
a == 1
b == 1
c == 0
d == 0
```

Result in C semantics:

```
a == 0
b == 0
c == 1
d == 1
```

## Interpretation of strings

The basic difference for strings between C and C\* is that strings in C are arrays of type `char` whereas strings in C\* are arrays of type `uint64_t` (each element of the array contains 8 characters). So, as long as the string is directly used in an expression it will behave different whereas pointers to strings behave in the same way.

Code example:

```
uint64_t x;

x = *("Hello World");
```

Result in C\* semantics:

`x == 0x6F77206F6C6C6548`

Result in C semantics:

`x == 0x48`

In C\* semantics dereferenciation of a string yields a concatenation of the ASCII codes of the first eight characters whereas the same yields in C semantics just the ASCII code of the first character.






