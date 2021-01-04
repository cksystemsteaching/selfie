Copyright (c) 2015-2021, the Selfie Project authors. All rights reserved. Please see the AUTHORS file for details. Use of this source code is governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the Department of Computer Sciences of the University of Salzburg in Austria. For further information and code please refer to:

http://selfie.cs.uni-salzburg.at

This document provides an overview of the differences in semantics between the programming language C\* in which selfie is written and the programming language C. Syntactically, C\* is a strict subset of C. Semantically, however, C\* differs from C in, for example, how integer literals and strings are handled. Note that the results presented here were obtained with tools that implement [C11](https://en.wikipedia.org/wiki/C11_(C_standard_revision)) semantics.

## Integer Literals

Integer literals in C\* are interpreted as 64-bit unsigned integers. In C, however, integer literals are interpreted as 32-bit signed integers. As a result, an expression may evaluate to different values in C\* and C if the expression involves integer literals and operators with different semantics for signed and unsigned operands, that is, `/`, `%`, `<`, `<=`, `>`, and `>=`.

#### Arithmetic:

```
uint64_t x;
uint64_t y;

x = 1 / -1;
y = 1 % -1;
```

C\*:

```
x == 0
y == 1
```

C:

```
x == -1
y == 0
```

#### Comparison:

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

C\*:

```
a == 1
b == 1
c == 0
d == 0
```

C:

```
a == 0
b == 0
c == 1
d == 1
```

## Strings

Strings in C\* are arrays of type `uint64_t` whereas strings in C are arrays of type `char`. Thus each element of a string in C\* contains 8 characters rather than just 1 character as in C. Dereferencing a string therefore results in different values in C\* and C.

#### Dereferencing:

```
uint64_t x;

x = *"Hello World!";
```

C\*:

```
x == 0x6F57206F6C6C6548
```

C:

```
x == 0x48
```

Note that `0x48` is ASCII for `H`. Moreover, `0x65`, `0x6C`, `0x6F`, `0x20`, and `0x57` are ASCII for `e`, `l`, `o`, ` `, and `W`, respectively.

## Library

### malloc

Per C standard, consecutive calls of `malloc` always have to return unique addresses independent of the actual size parameter. However, allocating memory in C\* with 0 as size parameter results in no memory allocation at all. Therefore, consecutive calls of `malloc` do always return the same address.

C\*:

```
malloc(0) == malloc(0)
```

C:

```
malloc(0) != malloc(0)
```