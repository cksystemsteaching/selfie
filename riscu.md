Copyright (c) 2015-2018, the Selfie Project authors. All rights reserved. Please see the AUTHORS file for details. Use of this source code is governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the Department of Computer Sciences of the University of Salzburg in Austria. For further information and code please refer to:

http://selfie.cs.uni-salzburg.at

This document provides an overview of the RISC-U instruction set. RISC-U is a tiny subset of the 64-bit [RISC-V](https://en.wikipedia.org/wiki/RISC-V) instruction set. The selfie system implements a compiler that targets RISC-U as well as a RISC-U emulator that interprets RISC-U code. RISC-U consists of just 14 instructions listed below. For details on the exact encoding, decoding, and semantics of RISC-U code see the selfie implementation.

## Machine State

A RISC-U machine has a 64-bit program counter denoted `$pc`, 32 64-bit registers, and 4GB of byte-addressed memory. RISC-U instructions are 32-bit, two per 64-bit double-word. Memory, however, is accessed at 64-bit double-word granularity only.

## Initialization

`lui $rd,imm: $rd = leftShift(imm, 12); $pc = $pc + 4`

`addi: $rd,$rs1,imm: $rd = $rs1 + imm; $pc = $pc + 4`

## Arithmetic

`add: $rd,$rs1,$rs2: $rd = $rs1 + $rs2; $pc = $pc + 4`

`sub: $rd,$rs1,$rs2: $rd = $rs1 - $rs2; $pc = $pc + 4`

`mul: $rd,$rs1,$rs2: $rd = $rs1 * $rs2; $pc = $pc + 4`

`divu: $rd,$rs1,$rs2: $rd = $rs1 / $rs2; $pc = $pc + 4`

`remu: $rd,$rs1,$rs2: $rd = $rs1 % $rs2; $pc = $pc + 4`

`sltu: $rd,$rs1,$rs2: if ($rs1 < $rs2) $rd = 1 else $rd = 0; $pc = $pc + 4`

## Memory

`ld: $rd,imm($rs1): $rd = memory[$rs1 + imm]; $pc = $pc + 4`

`sd: $rs2,imm($rs1): $memory[$rs1 + imm] = $rs2; $pc = $pc + 4`

## Control

`beq: $rs1,$rs2,imm: if ($rs1 == $rs2) $pc = $pc + imm else $pc = $pc + 4`

`jal: $rd,imm: $rd = $pc + 4; $pc = $pc + imm`

`jalr: $rd,imm($rs1): $rd = $pc + 4; $pc = $rs1 + imm`

## System

`ecall`