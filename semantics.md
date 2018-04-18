Copyright (c) 2015-2018, the Selfie Project authors. All rights reserved. Please see the AUTHORS file for details. Use of this source code is governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the Department of Computer Sciences of the University of Salzburg in Austria. For further information and code please refer to:

http://selfie.cs.uni-salzburg.at

The following table describes the semantical differences between C\* and C:  

## Operator: `/` 

Code example:  

```  
uint64_t x;

x = 100 / (-20);
```

Result in C\* semantics:

`x == 0`

Result in C semantics:

`x == -5`

Description:  
The differences between C\* and C semantics result in this case of a different interpretation of the integer literals. In C integer literals are by default interpreted as signed 32-bit integers whereas in C\* the literals are interpreted as 64-bit unsigned integers. Therefor in C a signed division is applied on the two literals and the result afterwards is casted to 64-bit unsigned integer (the type of the variable), while in C\* just an unsigned division is applied and no cast is necessary. So this semantical difference of the `/` operator appears just if both operands are literals.

## Operator: `-` (sign)

Code example:

```
uint64_t x;

x = ((-4 / 2) == ((-4) / 2));
```

Result in C\* semantics:

`x == 0`

Result in C semantics:

`x == 1`

Description:  
This difference results of a difference between the precedences of the sign `-` operator in C\* semantics and C semantics. In standard C the sign operator has a higher precedence than the division operator `/` whereas the sign operator has a lower precedence than the division operator in C\*. Therefore `-4 / 2` in C\* is interpreted such that at first the division is processed and afterwards the sign is applied on the result of the division.  

## Operators: `<` `<=` `>` `>=`

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

Description:  
These differences have the same reason as the semantical differences of the `/` operator. In C semantics the literals are treated as 32-bit signed integer and the cast is done after a signed comparison, whereas in C\* semantics the literals are treated as 64-bit unsigned integer and therefor the comparisons are unsigned ones. These differences also appear only for comparisons of two literals.