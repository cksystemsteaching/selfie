Copyright (c) the Selfie Project authors. All rights reserved. Please see the AUTHORS file for details. Use of this source code is governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the Department of Computer Sciences of the University of Salzburg in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

This document specifies cellfie, an instruction-level reversible cellular machine that runs [RISC-R](riscr.md). The tool is `tools/cellfie.c`, the development plan is `projects/reversible.md`. The machine is a grid of cells and one token. A cell holds one RISC-R instruction, one memory word, or a piece of wire. The token carries the program counter and the register file from cell to cell. The rule of the machine is RISC-R applied where the token is, plus the movement of the token, and it is a bijection on all states: running it backward needs no trace. For details on the exact semantics see the `cell_*` procedures and `model_rule` in `tools/cellfie.c`.

This is the state after milestones M6a and M7: all thirteen instructions and `exit`, wire, routers, and memory, and a hand-laid program on which the rule is compared with rotor's RISC-R model and with riscr. Tapes and the system calls `read`, `write`, `openat`, and `brk` are M6b and missing, see the last section.

## Machine State

The grid is a torus of `width` times `height` cells, both powers of two and at least 2. Row 0 is the northern row, column 0 the western column. Each cell has a kind, and depending on the kind an orientation, a mirror, and a 64-bit word.

The token is at one cell and has a heading, east, north, west, or south. It carries a 64-bit program counter `pc`, 32 registers of 64 bits, of which `zero` is always 0, and two more 64-bit words that are zero unless the token is in transit between two instruction cells or between an instruction cell and a memory cell: the *address* and the *datum*. In RISC-R terms, `pc` and the registers are the machine state, the memory cells are memory, and address and datum are what a processor calls its memory address and memory data register.

One *tick* is: the cell under the token acts on the token, then the token moves one cell along its heading. Nothing else changes in a tick, so simulating a tick costs one cell, whatever the size of the grid. Backward, a tick is: the token moves one cell back against its heading, then the cell there undoes what it did.

## Cells

Every cell maps the heading of a token to a heading and leaves a token it does not act on unchanged.

| Kind | Layout | What the cell does to the token |
| --- | --- | --- |
| blank | `.` | nothing: blank cells are wire, and two wires cross in a blank cell |
| mirror | `/` or `\` | turns the token: `/` exchanges east with north and west with south, `\` exchanges east with south and west with north |
| router | `R/p05`, `R\a03` | a mirror if the given bit of the token's `pc` (`p`) or address (`a`) is set, blank otherwise |
| memory | `M` and 16 hexadecimal digits | exchanges its word with the datum of the token |
| instruction | `E/00100a13` | applies its RISC-R instruction, see below |

A mirror is a permutation of the four headings and its own inverse. A router is a mirror or not depending on a word of the token that it does not change, so it is a permutation of the headings for every token. That is all there is to wire, and why wire is reversible: a router is a switch for a token coming one way and a merge for a token coming the other way, with the same bit telling which.

## Instruction Cells

An instruction cell has an orientation, the heading of its *path*, a mirror, and a RISC-R instruction in RISC-U encoding. Its *side* is the heading its mirror turns onto the path. With orientation east and mirror `/` the side is north: the cell exchanges tokens heading east and north. The cell acts on a token on its path or on its side, and a token with any other heading passes.

A token on the path executes the instruction. For most instructions it stays on the path:

| Instruction | On the path |
| --- | --- |
| `lui`, `addi`, `add`, `sub` | `rd += f`, backward `rd -= f`; `pc += 4` |
| `mul`, `divu`, `remu`, `sltu` | `rd ^= f` in both directions; `pc += 4` |
| `beq` with `rs1 != rs2` | `pc += 4` |
| `ld zero,imm(rs1)` | `pc += 4` |

Control flow and memory access are movement. For these the cell is a mirror: the token leaves the path sideways, travels along wire, and enters a cell from the side, which turns it onto the path of that cell.

| Instruction | On the path: the token leaves | On the side: the token arrives |
| --- | --- | --- |
| `beq` with `rs1 == rs2` | address `+= pc`; `pc += imm` | address `-= pc + imm`; `pc += 4` |
| `jal rd,imm` | `rd += pc + 4`; address `+= pc`; `pc += imm` | address `-= pc + imm`; `pc += 4` |
| `jalr rd,0(rd)` | `pc`, `rd`, address become `rd`, address, `pc` | address `-= rd - 4`; `pc += 4` |
| `ld rd,imm(rs1)` | datum and `rd` are exchanged; address `+= rs1 + imm` | datum and `rd` are exchanged; address `-= rs1 + imm`; `pc += 4` |

A token in transit between instructions has the address of its target in `pc` and the address of its origin as address, which is what routers need: on the way out of a region they merge by a bit of where the token comes from, on the way in they split by a bit of where it goes. The cell at the target uncomputes the origin from what it knows: a `beq` or `jal` from its own address and immediate, a `jalr` from its link register. This is RISC-R's pairing of every transfer with a come-from, as geometry: the instruction at the target of a taken `beq` must be a `beq` pointing back whose condition holds, and here it must be a cell whose side the wire from the origin leads to, and it is a mirror for the arriving token only if its condition holds. An origin and its come-from are the same kind of cell seen from its two ends, which is why RISC-R has no separate come-from instruction.

The procedure call of `riscr.md` looks the same on the grid. The `jal ra` at the call site leaves with the link in `ra` and arrives at the side of the `jalr ra,0(ra)` in front of the procedure, which uncomputes the origin from `ra`. The `jalr ra,0(ra)` at the end leaves for the address in `ra`, which becomes zero, and arrives at the side of the `jal ra` after the call site, whose immediate points back at it. With one call site the two wires are direct; with several, routers merge them by the address of the call site and split the returns by the `pc`.

An `ld` sends the token to memory and back: the token leaves with `rd` as datum and the address of the word, routers steer it by the bits of the address to the memory cell, which exchanges its word with the datum, and routers steer it back by the bits of its `pc` to the side of the `ld` cell it left.

A token that enters the side of a `beq` whose condition does not hold, or any side of an instruction that does not transfer, passes. An instruction that is not RISC-R has no effect at all, on the path and on the side: an unknown encoding, `sd`, an `rd` that is one of its sources, a `jalr` other than `jalr rd,0(rd)` with `rd` not `zero`. Neither has `ecall`, see the next section.

## Properties

The rule is defined on all states. Where a RISC-R program stops is not part of the rule but a property of the state, as the bad states of rotor's models are. A property holds when the token is on the path of an instruction cell, about to execute it, and

| Property | The instruction |
| --- | --- |
| `illegal-instruction` | is not RISC-R |
| `irreversible-link` | is `jal rd` with `rd` not zero |
| `division-by-zero` | is `divu` or `remu` with `rs2` zero |
| `exit` | is `ecall` with `a7` 93; the exit code is `a1` |
| `unsupported-syscall` | is any other `ecall` |

Cellfie's simulator stops running forward in such a state, before the tick. The properties are bad states in the model of the rule. They are not constraints: the rule is a bijection with them as without, a division by zero for instance leaves `rd` unchanged and the token moves on.

Cellfie's rule differs from riscr where riscr needs a rule of RISC-R to stay reversible. Riscr's `jalr` sets `rd` to zero, which is only reversible because the come-from is checked; the cell rotates `pc`, `rd`, and the address instead, which is the same when the address is zero, as it is on the path, and a bijection in any case. Riscr checks the come-from at the origin; a cell cannot see the other end of a wire, so a token that arrives where its come-from's condition does not hold passes through instead.

## Layouts

A layout is a text file in the run-length encoding of cellular automata, extended with cell contents. It holds the grid and the token, so it is the whole state of the machine, and cellfie writes any state as a layout in exactly one form: equal states are equal files.

```
#C comment
#T 0 1 E 0 0 0
#R 11 000000000000002a
x = 16, y = 8, rule = RISC-R
6.R/p043.R\p06R/p053.\$
E/00100a13E/00300293$
13./M0000000000000000R/a03!
```

Lines starting with `#C` are comments. `#T x y heading pc address datum` is the token, at the northwestern cell heading east with all words zero if missing; `#R register value` sets a register. Column, row, and register are decimal, all other numbers hexadecimal. The header gives the size of the grid, which is rounded up to powers of two, and the rule, `RISC-R`. Reversibility is a switch, and the rule in the header is where a layout says which way it is set; cells that follow RISC-U are not implemented yet, so cellfie refuses `RISC-U`.

The cells follow row by row. A decimal number in front of a cell repeats it, `$` ends a row, a number in front of `$` ends that many rows, the rest of a row is blank, and `!` ends the layout. Line breaks and spaces between cells are ignored. A router is `R`, its mirror, `p` or `a`, and the bit as two decimal digits. An instruction cell is its orientation `E`, `N`, `W`, or `S`, its mirror, and its instruction as eight hexadecimal digits.

`tests/cellfie-test.rle` is a hand-laid program with a loop, three exchanges with two memory words, and a procedure call, on a grid of 16 times 8 cells, with its wiring described in its comments. Its addresses are those of the RISC-R binary of the same program, which `tests/cellfie-test.c` writes: code from 0x10000, the two memory words at the start of the data segment at 0x11000.

## Running

`./cellfie -l layout -f ticks` runs at most that many ticks forward and stops where a property holds, `-b ticks` runs backward, and `-o layout` writes the state. `-rev ticks` runs forward and then as many ticks backward as it ran forward and checks that the grid and the token are restored bit for bit. Options are processed in order, as in selfie.

## Model

`./cellfie -btor2 width height` writes the rule for a grid of that size as BTOR2 model `cellfie-WxH.btor2`, and with `-inverse` before it the inverse rule as `cellfie-WxH-inverse.btor2`. Both have the same nine states: `token-x`, `token-y`, `token-heading`, `token-pc`, `token-address`, `token-data`, `token-registers`, `cell-kinds`, and `cell-words`. None is initialized: a layout is the initial state, and without one all states are free. The properties are the bad states of the rule; with `-noproperties` they are left out, which is the model `cellfie-WxH-noproperties.btor2` of the rule alone. The inverse rule has no properties.

A cell of `cell-kinds` is 8 bits: the kind in bits 0 to 2 (blank 0, mirror 1, router 2, memory 3, instruction 4, all others blank), the orientation in bits 3 and 4 (east 0, north 1, west 2, south 3), the mirror in bit 5 (`/` 0, `\` 1). A word of `cell-words` is the instruction in its lower half, the memory word, or the bit of a router in bits 0 to 5 with bit 6 set for the address.

`make cells` checks all of this:

1. The test layout runs until `exit` with exit code 42 after 176 ticks and 29 instructions, and 176 ticks backward restore the initial layout, in one run and across files, natively and with cellfie running on mipster.
2. `./cellfie -check N` compares one tick of the simulator with one step of the model, forward and backward, and the properties, on N random states with cells of all kinds, kinds and instructions that do not exist included.
3. Bitr proves that one step of the inverse rule after one step of the rule restores all nine states, and one step of the rule after one step of the inverse rule as well, from every state of the grid: `./bitr cellfie-16x8-noproperties.btor2 -identity cellfie-16x8-inverse.btor2`. There is no constraint to assume. The proof takes 80 paths and less than a second per direction, and 45 seconds for both on a grid of 64 times 64 cells.

Bitr loads layouts itself, with `-grid layout`, into the states of the model, with a reader of its own: `./bitr cellfie-16x8.btor2 -grid tests/cellfie-test.rle` stops at the bad state `exit` after 177 steps, the 176 ticks of the simulator and the step that stops.

The proof is about the model and the check ties the simulator to the model. Both were tested by mutation on November 23, 2026: each of thirteen wrong rules, four in the simulator and nine in the model, fails the check on 20,000 states. Of eight of the wrong models, the seven that are no bijections fail the proof, an `addi` whose `rd` is its source, a `jalr` that zeroes `rd`, and a memory cell that overwrites its word among them. The eighth, a router that ignores its mirror in both directions, is a different rule but still a bijection: it passes the proof and fails the check.

## Cellfie and RISC-R

That the rule is a bijection says nothing about whether it is RISC-R. `make product` checks that on the test program, three ways.

1. Riscr runs the binary `tests/cellfie-test.r` to exit code 42 in 30 instructions and back to its initial state; cellfie runs the layout to exit code 42 in 29 instructions before the `exit`, which the simulator does not execute.
2. Bitr stops in rotor's model of the binary after 30 instructions, as riscr does, and in cellfie's model with the layout after 177 steps, as the simulator does.
3. Bitr runs the two models as a product: `./bitr tests/cellfie-test-rotorized-riscr.btor2 -l tests/cellfie-test.r -product cellfie-16x8.btor2 -grid tests/cellfie-test.rle -abstraction tests/cellfie-test-abstraction.btor2`. Cellfie's model takes every step, rotor's model only the steps in which a RISC-R instruction begins. At each of the 29 instructions the two agree on the pc, all 32 registers, and both memory words, and they stop together, rotor's model at `exit(42)` and cellfie's at `exit`.

The *abstraction* is what relates the two models. It is a BTOR2 file without initial or next states, here `tests/cellfie-test-abstraction.btor2`, written by hand as the layout is. Its states are states of the two models by name, `core-0-pc` and `token-pc` for instance. Its output `step` holds when the cell under the token is an instruction cell and the token is on its path: that is where a RISC-R instruction begins. Its bad states are where the models differ in such a step: `pc-differs`, one `register-...-differs` per register, one `word-at-...-differs` per memory word, with the cell of each address in it, and `token-in-transit` if address or datum of the token are not zero. Memory is the one part that depends on the layout: a memory cell does not know its address, the wire that leads to it does.

The product is concrete: the program reads no input, so there is one run, and the check covers all of it rather than a bound. It was tested by mutation on November 23, 2026: another instruction in a cell, another memory word, another `sp`, the memory cells exchanged in the abstraction, a mirror missing on the call wire, a wrong immediate in a come-from, two wrong rules in cellfie's model, and another exit code in rotor's model each fail it, with the bad state that names the difference. A router on a wrong bit did not: the token took a detour of 30 ticks around the torus and arrived where it should, which is still the same program.

## Not There Yet

- Tapes and the system calls `read`, `write`, `openat`, and `brk` (M6b). They need a tour of the token between memory and tape, the head of a tape as a mark that the token carries from one tape cell to the next, and the program break somewhere, most likely in the token.
- RISC-U cells, which overwrite `rd` and join paths without a come-from. Their rule is no bijection, and bitr should find two states with the same successor.
- The comparison with RISC-R is one program and one run. The cell rule and rotor's model are not compared on all states: an instruction takes one step in one and a number of ticks without bound in the other, so that proof needs the cells of a transfer and the wire between them, not the rule alone.
- The abstraction is written by hand. The layout compiler will have to write it, since it places the memory cells.
- An `ld` at an address that is not word-aligned or that has no memory cell is not a property: routers ignore the bits they are not given, and a token that no router turns stays on its wire around the torus.
- The layout compiler from RISC-R binaries (M8). Routing is by hand so far.
