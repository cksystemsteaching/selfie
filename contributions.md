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

 + addition with different steps (todo)

### completeness

+ operation with minuend operands
 3 instructions:
 - 0xAE08(~4254) `return initialValue;              in compile_initialization`
 - 0x2CD8(~1779) `return n % twoToThePowerOf(b);    in getBits`
 - 0x2BF8(~1768) `return n * twoToThePowerOf(b);    in leftShift`

-- --
