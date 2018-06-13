# Diff. monster / littlemonster

## aliases error

In `void getSymbol()`:
Because of the restriction that each condition should restrain only the last assignment.

## abstract operators
+ implementation of modular stride intervals
`adding step and restrictions`

+ restrictions being for:
  - `soundness`, control the overflows of the abstract representation domain.
  - `completeness`, is there an over-approximation (impossible concrete values)

+ add and sub with modular stride intervals
  `gcd function`

+ warnings when over-approximations are done
  `printOverApprox();`

## tainted analysis

 + flag `-t`: count symbolic operations

### soundness

 + addition/subtraction with different steps
 8 instructions:
 - 0x34AC(~1881) `*(s + a) = (*(s + a) - leftShift(loadCharacter(s, i), (i % SIZEOFUINT64) * 8)) + leftShift(c, (i % SIZEOFUINT64) * 8);              in storeCharacter`
 - 0xCCD0, 0xCCF8, 0xCD48(~4817) `return leftShift(leftShift(leftShift(leftShift(immediate, 5) + rs1, 3) + funct3, 5) + rd, 7) + opcode;    in encodeIFormat`
 - 0x390C(~1968) `n = n * 10 + c;    in atoi`
 - 0xC8E8, 0xC8C0(~4761) `return leftShift(leftShift(leftShift(leftShift(leftShift(funct7, 5) + rs2, 5) + rs1, 3) + funct3, 5) + rd, 7) + opcode;    in encodeRFormat`
 -  0xDC44(~5008) `return leftShift(leftShift(immediate, 5) + rd, 7) + opcode;    in encodeUFormat`

### completeness

+ operation with minuend operands
 3 instructions:
 - 0xAE08(~4254) `return initialValue;              in compile_initialization`
 - 0x2CD8(~1779) `return n % twoToThePowerOf(b);    in getBits`
 - 0x2BF8(~1768) `return n * twoToThePowerOf(b);    in leftShift`

-- --
