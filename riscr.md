Copyright (c) the Selfie Project authors. All rights reserved. Please see the AUTHORS file for details. Use of this source code is governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the Department of Computer Sciences of the University of Salzburg in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

This document provides an overview of the RISC-R instruction set. RISC-R is a reversible variant of [RISC-U](riscu.md): it keeps the 14 RISC-U instructions and their 32-bit RISC-V encodings but changes what they mean such that every instruction is a bijection on the machine state. Executing an instruction backward undoes it exactly, without any trace. Selfie's RISC-U emulator mipster also implements RISC-R, forward and backward, behind the `-riscr` option. RISC-R binaries are RISC-V ELF binaries with bit 8 of `e_flags` set; they do not run on RISC-V hardware and mipster refuses to load them without `-riscr`, and refuses RISC-U binaries with `-riscr`. For details on the exact semantics see the `do_riscr_*` procedures in the selfie implementation and the development plan in `projects/reversible.md`.

## Machine State

A RISC-R machine has the state of a RISC-U machine, a 64-bit program counter `pc`, 32 general-purpose 64-bit registers, and 4GB of byte-addressed memory, plus two tapes of 64-bit words: an input tape with a head and an output tape with a head. All registers, including `ra`, and both tapes are zero when a program starts. Register `zero` always contains the value 0; writes to `zero` are ignored, which makes instructions with `rd` equal to `zero` effective no-ops in both directions. The code segment is read-only, which is what makes the step function a bijection on the remaining state once the program is fixed.

Executing backward, mipster fetches the instruction at `pc - 4`, applies its inverse, and leaves `pc` at that instruction. Mipster runs a RISC-R binary forward and then backward with `-rev` instead of `-m`: after the program exits, mipster executes as many instructions backward as it executed forward, except the final `exit`, and arrives at the initial state. The `tests/riscr-test.c` harness checks this bit for bit on hand-written RISC-R code with `make riscr`.

## Instructions

The parameters `rd`, `rs1`, and `rs2` may denote any of the 32 general-purpose registers and `imm` a signed immediate as in RISC-U. In every instruction that updates `rd`, `rd` must be distinct from `rs1` and `rs2` unless `rd` is `zero`; otherwise the instruction throws an irreversible instruction exception. Each instruction below lists its forward semantics and, after the slash, how the inverse differs when executing backward. All pc updates are `pc = pc + 4` forward and `pc = pc - 4` backward unless stated otherwise.

#### Initialization

`lui rd,imm`: `rd = rd + imm * 2^12` / `rd = rd - imm * 2^12`

`addi rd,rs1,imm`: `rd = rd + (rs1 + imm)` / `rd = rd - (rs1 + imm)`

`lui` and `addi` with `rs1` equal to `zero` add constants; the inverse of a constant addition is available as a forward instruction with the negated immediate, so RISC-R code can uncompute constants.

#### Memory

`ld rd,imm(rs1)`: `tmp = memory[rs1 + imm]; memory[rs1 + imm] = rd; rd = tmp` / the same

`ld` exchanges `rd` with a memory word and is its own inverse. There is no store: to store a value, exchange it into a zeroed memory word; to load a value, exchange it with a zeroed register. `sd` throws an irreversible instruction exception.

#### Arithmetic

`add rd,rs1,rs2`: `rd = rd + (rs1 + rs2)` / `rd = rd - (rs1 + rs2)`

`sub rd,rs1,rs2`: `rd = rd + (rs1 - rs2)` / `rd = rd - (rs1 - rs2)`

`mul rd,rs1,rs2`: `rd = rd ^ (rs1 * rs2)` / the same

`divu rd,rs1,rs2`: `rd = rd ^ (rs1 / rs2)` / the same, where the values of `rs1` and `rs2` are interpreted as unsigned integers

`remu rd,rs1,rs2`: `rd = rd ^ (rs1 % rs2)` / the same, where the values of `rs1` and `rs2` are interpreted as unsigned integers

`add` and `sub` accumulate: `x += y` is `add x,y,zero` and `x -= y` is `sub x,zero,y`, and each is the other's inverse. Multiplication, division, and remainder have no inverse as instructions, so they are defined as exclusive or (`^`) into `rd`: executing the same instruction twice restores `rd`. Into a zeroed `rd` all five simply deposit their result.

#### Comparison

`sltu rd,rs1,rs2`: `if (rs1 < rs2) { rd = rd ^ 1 } ` / the same, where the values of `rs1` and `rs2` are interpreted as unsigned integers

Like `mul`, `sltu` is its own inverse, so a loop can compute its continuation flag into a zeroed register, branch on it, and uncompute it by executing the same `sltu` again.

#### Control

Control flow in RISC-R is paired: every taken branch or jump from an *origin* lands on a *come-from* instruction at the *target* that points back at the origin. Forward execution jumps over the come-from to `target + 4`; backward execution starts from the instruction before `pc`, which is then the come-from, and jumps onto the origin. The come-from is only ever executed forward when execution falls into it, which is why its condition must then be false, as in the Pendulum architecture. Mipster checks the pairing on every taken transfer in both directions and throws an irreversible instruction exception if it fails.

`beq rs1,rs2,imm`: `if (rs1 == rs2) { pc = pc + imm + 4 } else { pc = pc + 4 }` / `if (rs1 == rs2) { pc = pc - 4 + imm } else { pc = pc - 4 }` with `-2^12 <= imm < 2^12` and `imm % 2 == 0`

The come-from of a taken `beq` at `pc + imm` must be a `beq` with immediate `-imm` whose condition holds in the current state. The two branches may test different registers; in a loop the come-from at the loop head typically tests a flag that is zero on entry and one on every back-edge.

`jal rd,imm`: `rd = pc + 4; pc = pc + imm + 4` / `rd = pc - 4; pc = pc - 4 + imm` with `-2^20 <= imm < 2^20`, `imm % 2 == 0`, and `rd == 0` on entry

`jal` adds the return address into `rd`, which must be zero. For `rd` equal to `zero`, the come-from at `pc + imm` is a `jal zero` with immediate `-imm`, so unconditional jumps pair statically like branches. For any other `rd`, the come-from is `jalr rd,0(rd)`, which pairs dynamically through the link register, so a procedure can be called from many sites. Executing backward, `jal` lands on its come-from and stores the address of the `jal` itself in `rd`, which is exactly what the `jalr` forward had uncomputed.

`jalr rd,0(rd)`: `tmp = rd; rd = 0; pc = tmp + 4` / `tmp = rd - 4; rd = 0; pc = tmp` where `rd` must equal `rs1`, must not be `zero`, and the immediate must be 0

The register must hold the address of a `jal rd` whose target is this `jalr` (backward: the address of the instruction after that `jal`). `jalr` jumps over that `jal` and uncomputes the register. A procedure call therefore looks as follows, with no cleanup code at either end:

```
P:    jal ra,F-P        ; call: ra = P + 4, pc = F + 4
P+4:  jal ra,E-(P+4)    ; come-from of the return, skipped forward
P+8:  ...               ; continues here after the return with ra = 0
F:    jalr ra,0(ra)     ; come-from of the call, skipped forward
F+4:  ...               ; procedure body
E:    jalr ra,0(ra)     ; return: pc = ra + 4 = P + 8, ra = 0
```

Executing backward from `P + 8`, the `jal` at `P + 4` finds `ra == 0`, jumps onto `E`, and sets `ra = P + 4`; from `F + 4`, the `jalr` at `F` finds `ra == P + 4`, jumps onto `P`, and sets `ra = 0`.

#### System

`ecall`: system call number is in `a7`, arguments are in `a0-a2`, no return value: all registers are unchanged.

`exit` stops the machine without changing its state; it is never executed backward. `read(fd, buffer, size)` exchanges `size` bytes, rounded up to words, between memory at `buffer` and the input tape at its head, then moves the head forward; backward it moves the head back and exchanges again. The input tape is filled lazily from file descriptor `fd` the first time a position is read, so running backward and forward again replays the same input. `write(fd, buffer, size)` appends the words from memory to the output tape, moves the head forward, and also writes the bytes to `fd`; backward it moves the head back and erases the words, which are still in memory. `brk`, `openat`, and context switching are unsupported in RISC-R.

## Rules in One Place

1. `rd` is distinct from `rs1` and `rs2`, or `rd` is `zero`.
2. There is no `sd`; `ld` exchanges.
3. Every taken `beq`, `jal`, and `jalr` lands on a matching come-from and jumps over it.
4. `jal rd` with `rd` not `zero` requires `rd == 0`; `jalr` requires `rd == rs1 != zero` and immediate 0.
5. `exit`, `read`, and `write` are the only system calls.

Violating a rule throws an irreversible instruction exception at the address of the instruction.
