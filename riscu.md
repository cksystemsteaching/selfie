Copyright (c) 2015-2021, the Selfie Project authors. All rights reserved. Please see the AUTHORS file for details. Use of this source code is governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the Department of Computer Sciences of the University of Salzburg in Austria. For further information and code please refer to:

http://selfie.cs.uni-salzburg.at

This document provides an overview of the RISC-U instruction set. RISC-U is a tiny subset of the 64-bit [RISC-V](https://en.wikipedia.org/wiki/RISC-V) instruction set. The selfie system implements a compiler that targets RISC-U as well as a RISC-U emulator that interprets RISC-U code. RISC-U consists of just 14 instructions listed below. For details on the exact encoding, decoding, and semantics of RISC-U code see the selfie implementation.

## Machine State

A RISC-U machine has a 64-bit program counter denoted `pc`, 32 general-purpose 64-bit registers numbered `0` to `31` and denoted `zero`, `ra`, `sp`, `gp`, `tp`, `t0`-`t2`, `s0`-`s1`, `a0`-`a7`, `s2`-`s11`, `t3`-`t6`, and 4GB of byte-addressed memory.

Register `zero` always contains the value 0. Any attempts to update the value in `zero` are ignored.

## Instructions

RISC-U instructions are encoded in 32 bits (4 bytes) each and stored next to each other in memory such that there are two instructions per 64-bit double word. Memory, however, can only be accessed at 64-bit double-word granularity.

The parameters `rd`, `rs1`, and `rs2` used in the specification of the RISC-U instructions below may denote any of the 32 general-purpose registers.

The parameter `imm` denotes a signed integer value represented by a fixed number of bits depending on the instruction.

#### Initialization

`lui rd,imm`: `rd = imm * 2^12; pc = pc + 4` with `-2^19 <= imm < 2^19`

`addi rd,rs1,imm`: `rd = rs1 + imm; pc = pc + 4` with `-2^11 <= imm < 2^11`

#### Memory

`ld rd,imm(rs1)`: `rd = memory[rs1 + imm]; pc = pc + 4` with `-2^11 <= imm < 2^11`

`sd rs2,imm(rs1)`: `memory[rs1 + imm] = rs2; pc = pc + 4` with `-2^11 <= imm < 2^11`

#### Arithmetic

`add rd,rs1,rs2`: `rd = rs1 + rs2; pc = pc + 4`

`sub rd,rs1,rs2`: `rd = rs1 - rs2; pc = pc + 4`

`mul rd,rs1,rs2`: `rd = rs1 * rs2; pc = pc + 4`

`divu rd,rs1,rs2`: `rd = rs1 / rs2; pc = pc + 4` where `rs1` and `rs2` are unsigned integers.

`remu rd,rs1,rs2`: `rd = rs1 % rs2; pc = pc + 4` where `rs1` and `rs2` are unsigned integers.

#### Comparison

`sltu rd,rs1,rs2`: `if (rs1 < rs2) { rd = 1 } else { rd = 0 } pc = pc + 4` where `rs1` and `rs2` are unsigned integers.

#### Control

`beq rs1,rs2,imm`: `if (rs1 == rs2) { pc = pc + imm } else { pc = pc + 4 }` with `-2^12 <= imm < 2^12` and `imm % 2 == 0`

`jal rd,imm`: `rd = pc + 4; pc = pc + imm` with `-2^20 <= imm < 2^20` and `imm % 2 == 0`

`jalr rd,imm(rs1)`: `tmp = ((rs1 + imm) / 2) * 2; rd = pc + 4; pc = tmp` with `-2^11 <= imm < 2^11`

#### System

`ecall`: system call number is in `a7`, parameters are in `a0-a2`, return value is in `a0`.