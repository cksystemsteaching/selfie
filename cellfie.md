Copyright (c) the Selfie Project authors. All rights reserved. Please see the AUTHORS file for details. Use of this source code is governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the Department of Computer Sciences of the University of Salzburg in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

This document specifies cellfie, an instruction-level reversible cellular machine that runs [RISC-R](riscr.md). The tool is `tools/cellfie.c`, the development plan is `projects/reversible.md`. The machine is a grid of cells and one token. A cell holds one RISC-R instruction, one memory word, or a piece of wire. The token carries the program counter and the register file from cell to cell. The rule of the machine is RISC-R applied where the token is, plus the movement of the token, and it is a bijection on all states: running it backward needs no trace. For details on the exact semantics see the `cell_*` procedures and `model_rule` in `tools/cellfie.c`.

This is the state after milestones M6, M7, M8, M10, M11, and M13: all thirteen instructions and the five system calls, wire, routers, memory and tape cells, two hand-laid programs on which the rule is compared with rotor's RISC-R model and with riscr, a layout compiler from RISC-R binaries, with which selfie-compiled programs are compared the same way, a hybrid simulator that runs all of selfie, construction by flight, and the layout compiler compiling, constructing, and landing in its own layout on cellfie. What is missing is in the last section.

## Machine State

The grid is a torus of `width` times `height` cells, both powers of two and at least 2. Row 0 is the northern row, column 0 the western column. Each cell has a kind, and depending on the kind an orientation, a mirror, and a 64-bit word. A memory, tape, or instruction cell may also have a *tag*, the address of its word or instruction. No cell acts on a tag or changes one: tags are there for the properties `invalid-address` and `invalid-pc` below.

The token is at one cell and has a heading, east, north, west, or south. It carries a 64-bit program counter `pc`, 32 registers of 64 bits, of which `zero` is always 0, and two more 64-bit words that are zero unless the token is in transit between two instruction cells or between an instruction cell and a memory cell: the *address* and the *datum*. In RISC-R terms, `pc` and the registers are the machine state, the memory cells are memory, and address and datum are what a processor calls its memory address and memory data register.

The token also carries the state of RISC-R's system calls: the program break, the next file descriptor, and for each of four file descriptors the head of its tape in words, the end of its file in bytes, whether its tape is an input tape, and whether the host can open its file. The words of the tapes are in cells. During a `read` or `write` the token carries two more numbers, zero otherwise: the *leg*, what it is on its way to, and the number of the *word* it transfers. The token is the processor and its kernel, the grid is code and storage.

One more word of the token, its *flight*, is zero unless the token is on its way to a cell of the grid to exchange a part of it, see Construction.

And the token carries a *pocket*: a second context, all of the above but where the token is and where it heads. No cell acts on the pocket. A program fills it, and a token that lands exchanges its context with it: that is how a program that was constructed gets a token, see The Pocket and Landing.

One *tick* is: the cell under the token acts on the token, then the token moves one cell along its heading. Nothing else changes in a tick, so simulating a tick costs one cell, whatever the size of the grid. Backward, a tick is: the token moves one cell back against its heading, then the cell there undoes what it did.

## Cells

Every cell maps the heading of a token to a heading and leaves a token it does not act on unchanged.

| Kind | Layout | What the cell does to the token |
| --- | --- | --- |
| blank | `.` | nothing: blank cells are wire, and two wires cross in a blank cell |
| mirror | `/` or `\` | turns the token: `/` exchanges east with north and west with south, `\` exchanges east with south and west with north |
| router | `R/p05`, `R\a03` | a mirror if the given bit of the token's `pc` (`p`) or address (`a`) is set, blank otherwise |
| memory | `M` and 16 hexadecimal digits | exchanges its word with the datum of the token |
| tape | `T` and 16 hexadecimal digits | flips the bits of its word by the datum of the token, which stays as it is |
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

A token that enters the side of a `beq` whose condition does not hold, or any side of an instruction that does not transfer, passes. An instruction that is not RISC-R has no effect at all, on the path and on the side: an unknown encoding, `sd`, an `rd` that is one of its sources, a `jalr` other than `jalr rd,0(rd)` with `rd` not `zero`. An `ecall` is a system call, see the next section.

## System Calls

An `ecall` cell makes the system call whose number is in `a7`, with arguments in `a1` to `a3` and the result added into `a0`, as `riscr.md` specifies and rotor's RISC-R model states. `exit` and unknown numbers have no effect, they are properties. `brk`, `openat`, and a `read` or `write` that fails or transfers nothing happen on the path, in one tick, with `pc += 4`:

| System call | On the path |
| --- | --- |
| `brk` | if `a0` is zero, the program break is not, and `a1` is a word-aligned address above it: `a1` becomes the program break and `a0` the previous one; if `a0` is not zero and below the program break, and `a1` is the word-aligned program break: `a0` becomes the program break and zero |
| `openat` | the kind of the tape of the next file descriptor is flipped if `a2` is `O_RDONLY` or 0; the descriptor, or -1 if the host cannot open the file, is added into `a0`; the next descriptor is one more |
| `read`, `write` that fails | -1, as a 32-bit number, is added into `a0`: the descriptor in `a1` is not allocated, is 3 or more and the host could not open it, is of the other kind of tape, or `a3` is 4GB or more |
| `read`, `write` of no byte | the result of a transfer of no word is added into `a0` |

`brk` is its own inverse, like `mul`: it exchanges the states before a successful `brk` with the states after one. RISC-R needs `a0` to be zero for `brk` to be reversible; here a `brk` with `a0` not zero undoes a `brk` if the state is one that a `brk` leaves, and does nothing otherwise, so the rule stays a bijection and the requirement is a property. `openat` does not read the name of the file: whether the host can open it is state, as in rotor's model.

A `read` or `write` of at least one byte is a tour of the token, with the cell as a mirror where it begins and ends. For each word of the buffer the token travels three *legs*, each to a cell and back to the side of the `ecall` cell, as an `ld` does once: to the buffer word, to the tape word, and to the buffer word again. Between two legs the token crosses the cell, which uncomputes the address of the leg it returns from and computes that of the next. After the last leg of the last word the head of the tape advances by the number of words, the result is added into `a0`, `pc += 4`, and the token joins the path.

| Leg | Address | `read` | `write` |
| --- | --- | --- | --- |
| buffer | `a2` plus 8 times the word | the memory cell takes the datum, zero, and gives its word | the same |
| tape | 2^63 for input and 2^62 for output tapes, plus 2^32 times `a1`, plus 8 times head plus word | a memory cell: gives its word and takes the buffer word | a tape cell: its bits are flipped by the buffer word |
| buffer | as before | the memory cell takes the tape word and gives zero | the memory cell takes its word back |

So a `read` exchanges buffer words with words of an input tape, and a `write` flips words of an output tape by buffer words and leaves the buffer as it is, which on a tape that is zero ahead of its head copies the buffer onto the tape. An input tape is a row of memory cells that hold the input, an output tape a row of tape cells, and the wire decides which cell has which address, as for memory. The result of a `write` is `a3`, that of a `read` the number of bytes from the head to the end of the file, at most `a3`, or `a3` if the end is -1, unknown.

The files themselves are not there: the input is in the layout, the output stays on its tape, and no file of the host is opened, read, or written.

## Properties

The rule is defined on all states. Where a RISC-R program stops is not part of the rule but a property of the state, as the bad states of rotor's models are. A property holds when the token is on the path of an instruction cell, about to execute it, and

| Property | The instruction |
| --- | --- |
| `illegal-instruction` | is not RISC-R |
| `irreversible-link` | is `jal rd` and the value of `rd` is not zero |
| `division-by-zero` | is `divu` or `remu` with `rs2` zero |
| `exit` | is `ecall` with `a7` 93; the exit code is `a1` |
| `irreversible-brk` | is `ecall` with `a7` 214, and `a0` is not zero or the program break is zero |
| `irreversible-tape` | is `ecall` with `a7` 63 or 64 and `a3` is 4GB or more |
| `irreversible-openat` | is `ecall` with `a7` 56 and all four file descriptors are allocated |
| `unsupported-syscall` | is any other `ecall` with `a7` not 93 |

Two more properties are about where the token is rather than what it is about to execute, and need tags. Wire delivers by the bits in which the cells at its ends differ, so a token with an address or `pc` that has no cell arrives at the cell of another one. A tagged cell knows better:

| Property | The token |
| --- | --- |
| `invalid-address` | is at a tagged memory or tape cell and its address is not the tag |
| `invalid-pc` | is on the path of a tagged instruction cell and its `pc` is not the tag; this one comes before the properties above |

A cell without a tag takes any token, as before, and so do the dynamics of a tagged cell: the tag changes what is reported, not what happens.

Cellfie's simulator stops running forward in such a state, before the tick. The properties are bad states in the model of the rule. They are not constraints: the rule is a bijection with them as without, a division by zero for instance leaves `rd` unchanged and the token moves on.

Cellfie's rule differs from riscr where riscr needs a rule of RISC-R to stay reversible. Riscr's `jalr` sets `rd` to zero, which is only reversible because the come-from is checked; the cell rotates `pc`, `rd`, and the address instead, which is the same when the address is zero, as it is on the path, and a bijection in any case. Riscr checks the come-from at the origin; a cell cannot see the other end of a wire, so a token that arrives where its come-from's condition does not hold passes through instead.

## Layouts

A layout is a text file in the run-length encoding of cellular automata, extended with cell contents. It holds the grid and the token, so it is the whole state of the machine, and cellfie writes any state as a layout in exactly one form: equal states are equal files.

```
#C comment
#T 0 1 E 0 0 0
#R 11 000000000000002a
#S 12000 3 0 0
#F 0 0 1 1 0
x = 16, y = 8, rule = RISC-R
6.R/p043.R\p06R/p053.\$
E/00100a13E/00300293$
13./M0000000000000000R/a03!
```

Lines starting with `#C` are comments. `#T x y heading pc address datum` is the token, at the northwestern cell heading east with all words zero if missing; `#R register value` sets a register. `#S break open-files leg word` is the program break, the next file descriptor, and the leg and word of a transfer, 0, 3, 0, and 0 if missing; a fifth number is the flight of a token in flight, see Construction. `#P pc address datum` is the pocket, and the lines `#R`, `#S`, and `#F` after it are the pocket's; without it the pocket is as a token without lines. `#F descriptor head end input open` is a file descriptor: the head of its tape, the end of its file, whether the tape is an input tape, and whether the host can open the file; all zero if missing, except that the tape of descriptor 0 is an input tape. Column, row, register, and descriptor are decimal, all other numbers hexadecimal. The header gives the size of the grid, which is rounded up to powers of two, and the rule, `RISC-R`. Reversibility is a switch, and the rule in the header is where a layout says which way it is set; cells that follow RISC-U are not implemented yet, so cellfie refuses `RISC-U`.

The cells follow row by row. A decimal number in front of a cell repeats it, `$` ends a row, a number in front of `$` ends that many rows, the rest of a row is blank, and `!` ends the layout. Line breaks and spaces between cells are ignored. A memory cell is `M` and a tape cell `T`, each with its word as sixteen hexadecimal digits. A memory, tape, or instruction cell is tagged by `@` and sixteen hexadecimal digits after it, as in `M0000000000000007@0000000000011000`. A router is `R`, its mirror, `p` or `a`, and the bit as two decimal digits. An instruction cell is its orientation `E`, `N`, `W`, or `S`, its mirror, and its instruction as eight hexadecimal digits.

`tests/cellfie-test.rle` is a hand-laid program with a loop, three exchanges with two memory words, and a procedure call, on a grid of 16 times 8 cells, with its wiring described in its comments. Its addresses are those of the RISC-R binary of the same program, which `tests/cellfie-test.c` writes: code from 0x10000, the two memory words at the start of the data segment at 0x11000. `tests/cellfie-io-test.rle` is a second one, on 32 times 8 cells, that makes every system call: it sets the program break, reads a byte from standard input, writes it to standard output, opens a file that does not exist, reads from it, and exits with the byte.

## Running

`./cellfie -l layout` loads a layout and `./cellfie -c binary` compiles one, see the layout compiler below. `-f ticks` runs at most that many ticks forward and stops where a property holds, `-b ticks` runs backward, and `-o layout` writes the state. `-rev ticks` runs forward and then as many ticks backward as it ran forward and checks that the grid and the token are restored bit for bit. Options are processed in order, as in selfie.

## Model

`./cellfie -btor2 width height` writes the rule for a grid of that size as BTOR2 model `cellfie-WxH.btor2`, and with `-inverse` before it the inverse rule as `cellfie-WxH-inverse.btor2`. Both have the same thirty-two states: `token-x`, `token-y`, `token-heading`, `token-pc`, `token-address`, `token-data`, `token-break`, `token-open-files`, `token-leg`, `token-word`, `token-registers`, `token-tape-heads`, `token-tape-ends`, `token-tape-inputs`, `token-tape-opens`, `cell-kinds`, `cell-words`, `cell-tags`, `token-flight`, and the thirteen of the pocket, `pocket-pc` to `pocket-tape-opens` and `pocket-flight`, named as the token's. None is initialized: a layout is the initial state, and without one all states are free. The properties are the bad states of the rule; with `-noproperties` they are left out, which is the model `cellfie-WxH-noproperties.btor2` of the rule alone. The inverse rule has no properties.

A cell of `cell-kinds` is 8 bits: the kind in bits 0 to 2 (blank 0, mirror 1, router 2, memory 3, instruction 4, tape 5, all others blank), the orientation in bits 3 and 4 (east 0, north 1, west 2, south 3), the mirror in bit 5 (`/` 0, `\` 1), and whether the cell is tagged in bit 6. A word of `cell-words` is the instruction in its lower half, the memory or tape word, or the bit of a router in bits 0 to 5 with bit 6 set for the address.

`make cells` checks all of this:

1. The first test layout runs until `exit` with exit code 42 after 176 ticks and 29 instructions, the second after 344 ticks and 26 instructions, and as many ticks backward restore the initial layouts, in one run and across files, the second from the middle of its `read`, natively and with cellfie running on mipster.
2. `./cellfie -check N` compares one tick of the simulator with one step of the model, forward and backward, and the properties, on N random states with cells of all kinds, kinds and instructions that do not exist included.
3. Bitr proves that one step of the inverse rule after one step of the rule restores all states, and one step of the rule after one step of the inverse rule as well, from every state of the grid: `./bitr cellfie-16x8-noproperties.btor2 -identity cellfie-16x8-inverse.btor2`. There is no constraint to assume. The proof takes about 160 paths and a second per direction.

Bitr loads layouts itself, with `-grid layout`, into the states of the model, with a reader of its own: `./bitr cellfie-16x8.btor2 -grid tests/cellfie-test.rle` stops at the bad state `exit` after 177 steps, the 176 ticks of the simulator and the step that stops.

The proof is about the model and the check ties the simulator to the model. Both were tested by mutation on November 23, 2026: each of thirteen wrong rules, four in the simulator and nine in the model, fails the check on 20,000 states. Of eight of the wrong models, the seven that are no bijections fail the proof, an `addi` whose `rd` is its source, a `jalr` that zeroes `rd`, and a memory cell that overwrites its word among them. The eighth, a router that ignores its mirror in both directions, is a different rule but still a bijection: it passes the proof and fails the check. For the system calls, each of ten more wrong rules, three in the simulator and seven in the model, fails the check, and each of the six of them that are no bijections fails the proof: a `brk` that only sets, a tape cell that overwrites, an `openat` that sets the kind of a tape, a transfer that begins with any word number, a head that does not advance, a failure that overwrites `a0`.

## Cellfie and RISC-R

That the rule is a bijection says nothing about whether it is RISC-R. `make product` checks that on the test program, three ways.

1. Riscr runs the binary `tests/cellfie-test.r` to exit code 42 in 30 instructions and back to its initial state; cellfie runs the layout to exit code 42 in 29 instructions before the `exit`, which the simulator does not execute.
2. Bitr stops in rotor's model of the binary after 30 instructions, as riscr does, and in cellfie's model with the layout after 177 steps, as the simulator does.
3. Bitr runs the two models as a product: `./bitr tests/cellfie-test-rotorized-riscr.btor2 -l tests/cellfie-test.r -product cellfie-16x8.btor2 -grid tests/cellfie-test.rle -abstraction tests/cellfie-test-abstraction.btor2`. Cellfie's model takes every step, rotor's model only the steps in which a RISC-R instruction begins. At each of the 29 instructions the two agree on the pc, all 32 registers, and both memory words, and they stop together, rotor's model at `exit(42)` and cellfie's at `exit`.

The *abstraction* is what relates the two models. It is a BTOR2 file without initial or next states, here `tests/cellfie-test-abstraction.btor2`, written by hand as the layout is. Its states are states of the two models by name, `core-0-pc` and `token-pc` for instance. Its output `step` holds when the cell under the token is an instruction cell and the token is on its path: that is where a RISC-R instruction begins. Its bad states are where the models differ in such a step: `pc-differs`, one `register-...-differs` per register, one `word-at-...-differs` per memory word, with the cell of each address in it, and `token-in-transit` if address or datum of the token are not zero. Memory is the one part that depends on the layout: a memory cell does not know its address, the wire that leads to it does.

The product is concrete: the program reads no input, so there is one run, and the check covers all of it rather than a bound. It was tested by mutation on November 23, 2026: another instruction in a cell, another memory word, another `sp`, the memory cells exchanged in the abstraction, a mirror missing on the call wire, a wrong immediate in a come-from, two wrong rules in cellfie's model, and another exit code in rotor's model each fail it, with the bad state that names the difference. A router on a wrong bit did not: the token took a detour of 30 ticks around the torus and arrived where it should, which is still the same program.

`make tapes` checks the same for the second program, with the byte `*` as input: riscr runs the binary to exit code 42 in 27 instructions and back, bitr stops in rotor's model after 27 instructions and in cellfie's model after 345 steps, and in the product the two models agree at each of the 26 instructions on the pc, all registers, the program break, the next file descriptor, the heads, ends, kinds, and host flags of all four tapes, the buffer word, the input word, and the output word. Seven changes to the layout or to cellfie's model each fail it; an output tape of memory cells, which makes `write` an exchange, fails at the buffer word right after the `write`.

That last one is what rotor's model did until this milestone: its `write` exchanged the buffer with the tape, which zeroes the buffer, where riscr and `riscr.md` leave the buffer as it is. Deciding what a tape cell does made the difference visible; the model was changed, see `riscr.md`.

## The Layout Compiler

`./cellfie -c binary` compiles a RISC-R binary into a layout that runs it, which `-o layout` writes. The compiler boots the binary as riscr and rotor do, with selfie's boot loader and the name of the binary as only argument, and lays out what it finds: the instructions, the data segment, the stack with the arguments on it, and the token with the `pc`, `sp`, and program break of the booted machine.

The instructions are the *path*: cells in the order of their addresses, in every other column, all oriented east, in one row or, see below, in one row per strip. Every instruction that transfers control, `beq`, `jal`, and `jalr`, has a `/` mirror: it sends the token north and receives it from the south. Every instruction that accesses memory, `ld` with `rd` not `zero` and `ecall`, has a `\` mirror: it sends the token south and receives it from the north. All other instructions need no wire.

All wire is *combs*. A comb is a binary tree over the addresses of its leaves, with one row per level. A node is a router in the column of its first leaf, on the highest bit in which the addresses below it differ, and a mirror in the column of the first leaf that has that bit set. A token that enters at the root is turned east by each router whose bit is set in its `pc` or address, and south or north again by the mirror, and so reaches the leaf with its address; a token that enters at a leaf is turned west by the same mirrors and routers and reaches the root. A comb is as high as its tree is deep, about the logarithm of the number of its leaves when the addresses are dense, and it has no cell where the addresses have a gap, so memory can be sparse.

Four combs are north and south of the path, of each strip of the path, and each strip of words, see below, has two:

| Comb | Leaves | Routers look at | A token travels |
| --- | --- | --- | --- |
| departures of control | the columns of `beq`, `jal`, `jalr` | the address, which is the origin | from the cell north to the root |
| returns from memory | the columns east of `ld` and `ecall` | the `pc` | from the root south, then west and south into the cell |
| the path | | | |
| arrivals of control | the columns east of `beq`, `jal`, `jalr` | the `pc`, which is the target | from the root north, then west and north into the cell |
| departures to memory | the columns of `ld` and `ecall` | the `pc` | from the cell south to the root |
| to the words of a strip | the columns of its words | the address | from the root south through the cell of the word |
| from the words of a strip | the same columns | the address | on south to the root |

The roots are connected through columns 0 to 2: the departures of control lead west to column 0 and south to the arrivals; the departures to memory lead west to column 1 and south to the strips of words; and from the strips of words wire leads north in column 2 to the returns. No transfer goes around the torus, so the size of the grid costs nothing. The first four combs share rows without sharing cells because departures use the columns of the cells and arrivals the columns in between. The wire has no direction of its own: an `ld` cell with the other mirror sends the token the other way round through the same cells, and the layout still runs the program.

### The Path in Two Dimensions

One row of instructions puts the last instruction as many columns from the roots of its combs as there are instructions, twice, and every transfer goes to a root and back. The compiler lays the path in strips as it lays the words: the lower bits of an instruction address, without the two that are zero, select the column, the bits above the strip. A strip of the path is a row of instructions with its own four combs, and it has ten kinds of rows, from north to south: the row in which control leaves the strip to the west; the row in which a token back from memory enters it from the west; the combs of departures of control and of returns from memory; the path, with a row north and south of it for the wire from the next column into a cell; the combs of arrivals of control and of departures to memory; the row in which control enters from the west; the row in which a token leaves west for memory; and the row in which the path returns: from the last instruction of a strip wire leads two columns east, south to that row, west to the column west of the strip, south to the path of the next strip, and east into its first instruction.

West of the strips are four combs on their side, over the strips that have a comb of the kind: one collects control from the strips, one delivers it to them, one collects the tokens for memory, and one delivers those that return. Their routers look at the bits of the `pc`, or of the address for the departures of control, that select the strip. The number of bits that select the column is again the one for which the width of a strip plus the height of all strips is least.

### Memory in Two Dimensions

One row of words puts the last word as many columns away as there are words. The compiler lays the words in *strips* instead. The lower bits of a word address, without the three that are zero, select the column, the bits above select the strip, and only strips that have a word exist. A strip is a row of words with the comb to them north of it and the comb from them south of it, entered from the west in its first row and left to the west in its last. The strips are stacked from north to south, and west of them are two more combs, on their side, with a column per level and the strips as leaves: one turns a token heading east south into the row of its strip, the other, the same cells some columns west and some rows south, turns a token heading west north on its way back. The number of bits that select the column is the one for which the width of a strip plus the height of all strips is least, which is how far the last word then is from the first.

A router turns a token if a bit is set, so in any comb the words with a bit set are further from the root than those without. The stack is where all those bits are set: it would be the last strips, and the top of the stack, where a program has its most used words, the last word of the last strip. So the stack is laid the other way round. On the way to it the comb over the strips is a stair of routers, each a column east and a row south of the one before: a token is turned south first, a router then turns it east if its bit is set, down the stair to the stack, and all others leave the stair south, each in the column of its router, to their strips. That frees the order: the strips of the stack are first, then all others by ascending address. Within the stack, strips and words descend by address by the same turn, which costs a column per router: the words of such a strip are in twice the columns, the word with offset *o* of 2^k in column popcount(*o*) + 2(2^k - 1 - *o*).

The token never turns back on any of this wire. To a word in column *w* and row *v* and back to the side of an instruction in column *x* it takes 2*x* + 2*w* + 2*v* + 2*h* - 4 ticks, with *h* the rows of a comb of a strip, whatever the combs in between look like.

The words that get a cell are the data segment, the regions of the heap given with `-heap offset words` before `-c`, each an offset in bytes from the start of the heap, `-stack words` words below the top of the stack, 64 by default, sixteen words each for the output tapes of standard output and standard error, as tape cells, and sixteen words for the input tape of standard input, as memory cells that hold the bytes of the file given with `-i file`. A translated program needs a region at offset 0 for its history stack and one at the size of the history stack for its own heap.

`-a abstraction heap-allowance stack-allowance` after `-c` writes the abstraction for bitr's product of the layout with rotor's model of the same binary, generated with these allowances in bytes: `step` and the bad states as in the hand-written ones, with one bad state per word that has a cell, since the compiler knows which cell has which address.

`make layouts` compiles all 18 examples in `examples/symbolic`, compiled by selfie and translated by riscr with a history stack of 1MB, with cells for 2048 words of history, 64 words of heap, and 128 words of stack, on grids of 512 times 1024 cells with between 557 and 1,268 instruction cells in strips of 64 or 128, and 2,289 words in 22 strips of 128 columns. For 17 of them cellfie runs the layout to the exit code of riscr in the number of instructions of riscr, 375 to 2,719, and back to the layout, and bitr's product agrees with rotor's model at every instruction on the pc, the registers, the state of the system calls, and all 2,289 words. The runs take 165,638 to 1,631,492 ticks, 416 to 615 ticks per instruction, where one row of instructions took 630 to 1,210 and one row of words and wire around the torus 1,200 to 1,900. The 18th example accesses memory that is not there, on purpose, and riscr stops it with an exception after 540 instructions; cellfie stops in the 541st with `invalid-address` and riscr's address, the token being at the cell of another word. The compiler tags every instruction cell and every word, so the same happens when the grid is what is too small: with 512 instead of 2048 words of history the most recursive example stops with `invalid-address` at the first word beyond them. Neither run is compared with rotor's model.

The compiler was tested by mutation on one example: arrivals routed by the address instead of the `pc`, routers one bit too high, and a stack without the arguments each fail, the first two in cellfie's run and in the product, the third in the product at the first instruction. An output tape of memory cells and a data segment that is not loaded do not fail on that example, which writes nothing and has one data word that is zero.

## The Hybrid Simulator

A layout of selfie cannot be written down: translated to RISC-R, selfie is 160,220 instructions, but its history stack alone is 3GB, 400 million words, each a cell. `./cellfie -h binary arguments` runs a RISC-R binary on the layout that `-c` would write without laying it out. The instruction cells and the cells of the words are there and act on the token by the procedures of the cell rule, the ones the event-driven simulator calls; the wire is not there, its length is. On a compiled layout the token never turns back on its way through a comb or along a spine, so a transfer takes as many ticks as its wire is long, which the positions of its ends determine. With strips of the path of *n* instructions and *p* rows, of which *S* is the row in which control enters, combs of *h* rows in the strips of words, and *c* and *a* the first strips of the path that transfer control and access memory:

| Transfer | Ticks |
| --- | --- |
| from an instruction to the next on the path | 2, or 2*n* + 4 + *p* if the next is in the next strip |
| from a `beq`, `jal`, or `jalr` in strip *s* and column *x* to the instruction after its come-from in strip *t* and column *y* | 2*S* + *x* + *y* + 4 + (*s* + *t* - 2*c*)*p* |
| from an `ld` or `ecall` in strip *s* and column *x* to the word in column *w* and row *v* and back to its side, one leg | 2*x* + 2*w* + 2*v* + 2*h* - 4 + 2(*s* - 2*a*)*p*, and 2 more after the last leg |

The positions are the compiler's: both simulators take them from the same plan of the path, the regions of words, the strips, and the rows (`plan_path`, `plan_path_combs`, `plan_regions`, `plan_strips`, `place_strips`, `plan_rows`), computed from the regions rather than from each word, with a row per strip in a table. Words are allocated in pages when first accessed, so a region can be the whole heap. The properties are those of the event-driven simulator, with `invalid-address` for a word without a cell and `invalid-pc` for a transfer to an instruction that is no come-from or does not take the token; there the hybrid simulator stops at the instruction and does not follow the token to the cell where the wire would have led it, so its ticks are then those of the last instruction. It runs forward only.

Files are the host's, as in riscr: `openat` opens the file whose name is in memory, which decides whether the token carries the file as open; `read` moves the bytes that are read from the file onto the input tape at the head before the token gets there, and the end of the file is known when fewer bytes are there than asked for; `write` also writes the buffer to the file. Standard input is still the file given with `-i`. `-tapes n` before `-h`, or `-c`, sets the number of file descriptors, a power of two, and gives each of them an output tape and, but for standard output and error, an input tape; without it there are four descriptors and only the standard ones have tapes. `-tapewords n` sets the words per tape. The rule and its model follow the number of descriptors: `./cellfie -tapes 8 -check 50000` passes.

`make hybrid` runs the 18 symbolic examples both ways, on the layouts of `make layouts`: for the 17 that exit, the hybrid simulator stops at the same `pc` with the same exit code after the same number of instructions and the same number of ticks as the event-driven one, natively and for one example with cellfie on mipster. That is the check of the formulas, and of every change to the layout since: one that was 2 ticks short for control transfers failed it.

`make selfie-on-cellfie` is selfie compiling itself on cellfie: `./cellfie -tapes 8 -tapewords 1048576 -heap 0 535000000 -stack 1000000 -h selfie-r.r -c selfie.c -o selfie-c.m`, with a cell for every word of the heap, 8MB of stack, and 8MB per tape. The grid is 524,288 times 262,144 cells, with 160,220 instruction cells in 79 strips of 2,048 instructions and 52 rows each, of which 12,604 transfer control and 71,076 access memory, and 549,633,298 words in 4,195 strips of 131,072 columns and 39 rows each. Selfie exits with exit code 0 after 1,388,403,685 instructions, riscr's number, and the binary it wrote is the binary it writes on riscr and that selfie compiles itself to, byte for byte. That takes five minutes of the host and 94,297,978,686,148 ticks of the grid, 68,000 ticks per instruction.

| Layout | Ticks | per instruction |
| --- | --- | --- |
| one row of words, transfers around the torus | 376,091,754,479,047,372 | 271 million |
| strips of words, no transfer around the torus | 350,763,823,005,762 | 253,000 |
| the stack first and descending | 148,280,941,906,994 | 107,000 |
| the path in strips | 94,297,978,686,148 | 68,000 |

The first step is the dimension, a factor of 1,072. The second is a measurement: of 647 million legs to a word, 39% go to the stack, which was in the far corner, 54% to the heap, most of them pushes onto the history stack, and 6% to the data segment. Control transfers are 45 million and one percent of the ticks. The third takes the way along the path, 90,000 ticks per leg, down to the few thousand of a strip and its rows. What is left is the way to the history stack, which every push finds a word further on, and to the heap behind it.

## Construction

Loading a program onto a grid is writing its cells. With `-c` cellfie writes them. A machine that is to hold more than one program, or to make copies of itself, has to write cells itself, by its own rule, and reversibly. Cellfie's rule can: a program exchanges a register with a part of a cell as it exchanges it with a word of memory.

### Cells Have Addresses

The address 2^61 plus *part* times 2^56 plus *row* times 2^28 plus *column* is the address of a part of the cell in that row and column: part 0 is the eight bits of its kind, orientation, mirror, and tagged flag, part 1 its word, part 2 its tag. `ld rd,imm(rs1)` at such an address exchanges `rd` with that part, the lowest eight bits of `rd` for part 0. Nothing else is new: no instruction, no system call, no kind of cell. A blank cell is all zero, so exchanging a register with the three parts of a blank cell writes a cell and leaves the register zero, and exchanging again takes the cell off the grid and puts it back into the register.

### Flight

No wire leads to a blank cell. A token on its way to a part of a cell *flies*: it has one more word, its *flight*, which is zero on a path and on wire, and no cell acts on a token whose flight is not zero, except the cell it left.

- The instruction cell of the `ld` sets the flight to where it is, 2^63 plus its row times 2^28 plus its column, turns the token south as for any `ld`, and puts the address into the token's address.
- The token flies a rectangle: south to the row of its address, east to the column of its address, north to the row north of the cell it left, west to the column of that cell, and south into it. It turns in the four corners as at a mirror; which cells are corners follows from its position, its address, and its flight, and from nothing on the grid. Rows and columns count around the torus.
- In the corner that is its destination it exchanges its datum with the part of the cell there.
- Back at the cell it left, which is the one cell whose position is its flight, the cell acts as on any token arriving at its side: the datum becomes `rd`, the address is uncomputed, the flight is zero again.

A flight costs twice the columns plus twice the rows to its destination, plus 2 ticks. It is local: only the token and the cell under it change, and only in the one tick at the destination. It is reversible: a mirror and an exchange are their own inverses, so the inverse rule flies the same rectangle the other way round. Bitr proves the rule with flight a bijection on all states, nineteen then and thirty-two with the pocket below, with no constraint, as before; the properties of a token hold only if its flight is zero, since a token in flight is not at the cells it is over.

A token flies over anything, its own program and cells it has just written included, which is what a wire could not do. The price is one word in the token and a rule in which a cell does not always act on the token above it.

### The Constructor

`./cellfie -k binary` compiles the binary into a layout, as `-c` does, and then writes, instead of that layout, a *constructor* for it: a RISC-R program of 18 instructions with a tape in its memory, on a grid that has a blank *window* of the size of the layout south of it. The tape has two words for each part of a cell of the layout that is not zero: the address of the part in the window, and the part. The program is one loop:

```
loop:  ld t0,0(s1)     the address of a part, from the tape
       ld t1,8(s1)     the part, from the tape
       ld t1,0(t0)     exchange it with the part of the cell: a flight
       ld t1,8(s1)     what was there, onto the tape
       ld t0,0(s1)     the address, back onto the tape
       addi s1,zero,16
       ...             count, and branch back while parts are left
       ecall           exit
```

It moves the layout from the tape onto the grid. It keeps no history and leaves no garbage: when it exits, the window holds the layout, the tape holds the addresses and, where the parts were, what the window held before, which is zeros, and the registers hold a counter and a pointer. Backward it takes the layout apart and puts it back onto the tape. Run on a window that is not blank it exchanges all the same, and the tape then holds what was there.

`-window layout` writes the cells of the window as a layout of its size. `make construct` does this for the hand-laid test program and for the running example of `optimizations.md`: the constructor runs to its exit, back to its initial state, and to its exit again; the cells of the window are then the cells of the compiled layout, as files; and with the token of the compiled layout they run the program to its exit code.

| | Test program | `recursive-fibonacci-1-10` |
| --- | --- | --- |
| Instructions of the program | 22 | 704 |
| Layout of the program | 64 x 256 | 512 x 1024 |
| Parts on the tape | 1,216 | 23,477 |
| Grid of the constructor | 512 x 1024 | 4096 x 4096 |
| Instructions the constructor executes | 12,166 | 234,776 |
| Ticks | 4,723,824 | 296,466,548 |
| Ticks per part | 3,885 | 12,628 |

Construction is slow, and for the same reason running was: the constructor is itself a compiled layout, its tape is its memory, twice as many words as the layout has parts, and every part costs four legs to the tape and one flight. The tape is far larger than what it describes: 47,000 words in strips for a layout of 14,521 cells.

What a constructor does not do yet: start the program it built, since the token it has is its own and ends at its exit; build anything but a layout that the compiler computed for it; and build itself.

## The Layout Compiler on Cellfie

Cellfie is a C\* program, so selfie compiles it and riscr translates it, and the result is a RISC-R binary that cellfie can run: the layout compiler on the machine it compiles for. `make cellfie-on-cellfie` has it compile its own binary there.

```
./selfie -c selfie.h tools/btor2.h tools/cellfie.c -o cellfie-u.m
./riscr -l cellfie-u.m -history 12288 -t cellfie-r.r
./cellfie -c cellfie-r.r -o L0.rle
./cellfie -memory 16 -tapes 8 -tapewords 4194304 -heap 0 1800000000 -stack 1000000 -h cellfie-r.r -c cellfie-r.r -o L1.rle
cmp L0.rle L1.rle
```

`L0.rle` is the layout of cellfie's binary as cellfie compiles it on the host. `L1.rle` is the layout of the same binary as that binary compiles it, running on cellfie's hybrid simulator. They are the same file: 355,548 instruction cells among 1,488,779 cells on a grid of 16,384 times 8,192, 14.7MB as text. The run takes 5,586,386,911 RISC-R instructions, 995,720,340,899,180 ticks, 21 minutes of the host, and 9.5GB, most of it the history of 1.5 billion RISC-U instructions.

Four things had to change for this, none of them in the cell rule:

- **The compiler lays cells as a list.** A grid is almost all blank: cellfie's own layout has 1.5 million cells on 134 million. The compiler used to allocate the grid, three words a cell, and to scan it to write it. It now appends each cell it lays to a list, sorts the list by row, and writes rows from it; the grid is allocated only when a token is to run on it (`-f`, `-b`, `-rev`, `-window`, `-k`). The layouts are the same files.
- **The compiler does not use selfie's bit operations where it handles every instruction or every character.** `get_bits`, `left_shift`, and `and` are procedures in C\*, and a procedure call is about 40 RISC-U instructions. Classifying an instruction by decoding it took 7,000 instructions, finding where a comb splits 20,000, and writing a character 520. The compiler now classifies by the fields that matter, splits by comparing keys, remembers the splits of the combs of the path from planning them, and puts the characters of a cell into a buffer together.
- **A layout does not depend on where cellfie runs.** Selfie's boot loader names a binary after the machine that boots it and puts the name on the stack, and the stack is part of a layout. Cellfie boots under one name, so the layout is the same on the host, on mipster, on riscr, and on cellfie.
- **Riscr relays far jumps, and cellfie has more than 4GB of memory.** Translated, cellfie is 1.4MB of code, and `jal` reaches 1MB: see the Bennett translation in `riscr.md`. And a history stack for 1.5 billion instructions is 8GB: `-memory GB` sets the virtual memory of the binaries cellfie boots, with the stack at its end.

The same binary also compiles a small layout on riscr, forward and backward to its initial state, and on mipster, to the file the host writes.

### A Compiler That Constructs What It Compiles

The layout compiler writes a file, as selfie writes a binary, and the constructor of the section before builds a layout from a tape that cellfie wrote on the host. Joined, the compiler builds the layout it computed on the grid it runs on, with no file and no tape in between.

Nothing in the rule is needed for that, and little in the compiler. The parts of a cell have addresses, so in C\* a part of a cell is behind a pointer, and constructing a cell is a store:

```
part = (uint64_t*) (2305843009213693952 + row * 268435456 + column);

*part = kind;
```

Selfie compiles the store to `sd`, and riscr translates `sd` to two exchanges with the word at the address: what is there goes onto the history stack, and the value goes there. Both are `ld` at the address of a part of a cell, so both are flights. A C\* program that stores cells therefore runs on cellfie as it is, forward and backward. The hybrid simulator flies as well: a flight is `2dx + 2dy + 2` ticks, with `dx` columns east and `dy` rows south around the torus, and the parts of cells are in a store of their own.

### The Pocket and Landing

What is constructed needs a token to run, and a grid has one. The token of the program that constructed cannot become the token of what it constructed: its registers, its program break, its descriptors, and the heads of its tapes are what that program computed, and a reversible rule forgets nothing. It can be put away. The token carries a second context, its *pocket*: a pc, registers, address, datum, flight, leg, word, and the state of the system calls, everything a token has but its cell and its heading. No cell acts on the pocket, and two things reach it.

- **An exchange with a field.** `ld rd,imm(rs1)` at the address 2^60 plus *group* times 2^12 plus 8 times *field* exchanges `rd` with a field of the pocket, on the path, in the tick of the instruction: no wire and no flight, the pocket is where the token is. Group 0 is the words, pc 0, address 1, datum 2, flight 3, word 4, program break 5, next descriptor 6, and the leg 7, whose two bits are exchanged with the lowest two of `rd`; group 1 the registers; groups 2 to 5 the heads, the ends, the kinds, and the host opens by descriptor. A token on the side of such an `ld` passes.
- **Landing.** A token that flies to a cell as to its part 3, which no cell has, *lands* there, if the cell is blank and the pocket is at rest, with no flight and no address: it exchanges its context with its pocket and does not turn. It is then a token with what was in the pocket, heading east as it arrived, not in flight, and a tick later one cell east. What it was is in the pocket, with its flight and its address, as it landed.

Landing has to be its own inverse, so there is a second case: a token at rest at a blank cell whose pocket is landing at that cell exchanges as well, which is landing undone. On a path that is never the case; it is what makes the rule a bijection on all states. The three conditions are needed, and bitr says so: without the blank cell, without the pocket at rest, or without the second case, the rule is no bijection and the proof fails; with them bitr proves the rule a bijection on all thirty-two states in two to three seconds per direction, with no constraint. A pocket whose word is overwritten instead of exchanged fails the proof too. An `ld` of the pocket that also acts on the side is another bijection, and fails only the check of the simulator against the model.

So a program gives what it constructed a token by storing the token's context, field by field, in its pocket, and then loading from the cell west of the first instruction, as part 3 of it. In C\* both are a store and a load through a pointer. The load never returns: the token goes on in the constructed program, and the program that constructed is in its pocket, in the middle of that load.

### Room

Where to construct is the last thing a program needs to know, and it cannot know it: a program does not know the layout it runs on. The grid says it. With `-room columns rows` before `-c` or `-h`, the compiler leaves that many columns and rows free south of all cells of the layout and east of its instructions, where a token that leaves an instruction south and turns east gets to, and lays one more cell, a memory cell in the last column and row of the grid, whose word is 2^28 times the first free row plus the first free column. That cell has the same address on every grid, since columns and rows count around the torus: part 1 of the cell in column and row 2^28 - 1. A program that constructs reads it, constructs there, and writes back what is free then, south and east of what it constructed. It is to the grid what the program break is to memory.

- `-room columns rows` gives the grid of a binary room and the cell that says where it is.
- `-onto` after `-c` reads that cell, stores the layout just compiled there, cell by cell, advances the cell by the columns and rows of the layout, stores the pc, the registers, the program break, and the end of the input of the layout's token in the pocket, and lands west of its first instruction (`construct_laid_cells`). On the host there is no grid, and cellfie says so.
- `-window layout` after a run, or before `-h`, writes what was constructed in the room, from where the room began to where it begins now, with the token if it is there, and the pocket.
- A hybrid run ends where the token lands, since what it lands in is not the layout of the binary; the window is written then, and is a layout that the event-driven simulator runs.

`make construct` checks this with two programs. `tests/cellfie-build-test.c` is a short C\* program: it reads where the grid is free, stores a mirror, a router, a memory cell, and three instruction cells that exit with exit code 42, loads the memory cell again, stores the pc of the three in the pocket, and lands. Event-driven it runs to exit code 42 after 2,406,276 ticks and 3,288 instructions, the last two of them in what it constructed, and back to its initial state. The hybrid simulator stops at the landing after 2,406,274 ticks and 3,286 instructions; the window it writes is, byte for byte, the window of the event-driven simulator after that many ticks, token and pocket included; and that window runs 2 ticks and 2 instructions to exit code 42. The second program is cellfie itself, on cellfie:

```
./cellfie -tapes 8 -tapewords 4194304 -heap 0 400000000 -stack 1000000 -room 512 1024 -window W.rle \
  -h cellfie-test.r -heap 0 2048 -heap 1048576 64 -stack 128 -i tests/bitr-input.txt \
  -c examples/symbolic/recursive-fibonacci-1-10.r -onto
```

Cellfie, translated with a history stack of 1GB, compiles the running example of `optimizations.md` on cellfie, constructs its 14,521 cells where the grid says it is free, and lands in it, 33,543,188 instructions and 1.92·10^12 ticks after it began. `W.rle` without the lines of its pocket is the layout that cellfie compiles on the host, byte for byte, and it runs as that layout runs: exit code 1 after 413,768 ticks and 830 instructions.

`make cellfie-on-cellfie` does the same with cellfie's own binary:

```
./cellfie -memory 16 -tapes 8 -tapewords 4194304 -heap 0 1800000000 -stack 1000000 -room 16384 8192 -window L2.rle \
  -h cellfie-r.r -c cellfie-r.r -o L1.rle -onto
```

Cellfie's binary, 376,324 RISC-R instructions with what this section added, compiles itself on cellfie, writes `L1.rle`, stores the 1,575,267 cells of the layout at column 8,226 and row 295,438 of a grid of 1,048,576 times 524,288 cells, right below its own memory, 5,472,590 flights, two for each part that is not zero and a few for the room, and lands. `L1.rle` is `L0.rle`. `L2.rle`, the window, is `L0.rle` once the lines of its pocket are taken out: cells, token, and all. And it runs as `L0.rle` runs, which is not far: a layout compiled with default memory has no cells for its heap, and both stop with `invalid-address 0x188000` after 5,581 ticks and 28 instructions, at the first push onto the history stack.

| | Compile, construct, and land | and write the file |
| --- | --- | --- |
| RISC-R instructions | 2,224,308,137 | 6,378,168,020 |
| Ticks | 3.26·10^14 | 1.19·10^15 |
| Host | 8 minutes | 24 minutes |

Writing the layout as text is two thirds of the work; a compiler that only constructs does not need the file.

What this is and is not. A program computes a layout, builds it by the rule on its own grid, where the grid says there is room, and hands it the only token there is: compiler, constructor, and loader in one, and the copy of the running example runs to its end. It is not self-reproduction yet, for three reasons. The copy of cellfie is cellfie with 64 words of stack and no heap, not the cellfie that made it, which has 14GB of both: a layout that can run the compiler has 1.8 billion memory cells, and constructing those is beyond the simulator. The parent does not go on: it is in the pocket of its child, and nothing but running backward takes it out again. And a store pushes what was in the room onto the history stack, so the layout is built with garbage, a word of history per part, where the constructor of the section before moved it from its tape with none.

## Not There Yet

- Files of the host on a grid: the hybrid simulator has them, the event-driven simulator and the model do not. There input is what the layout holds and output stays on its tape.
- Words without a cell are detected where the cells are tagged, which is in compiled layouts: `invalid-address` when the token is at the wrong word. A `brk` beyond the cells of the heap is not detected before the first access, and the layouts written by hand have no tags. A token that leaves the wire altogether, for want of a mirror, just goes around the torus.
- A parent that goes on after its child is started, and a child that starts a child of its own: there is one token and one pocket. The child would have to put what is in its pocket into its memory first, field by field; nothing does that yet.
- Room is one corner that only advances, south and east. Nothing gives room back, and nothing checks that the room is blank.
- Bitr's simulator does not run a landing: an array that becomes another array is an error there. The proof, which is symbolic, covers it; the products with rotor's model do not land.
- Construction without garbage by a compiler: a store in C\* is an exchange with the history stack. The constructor with a tape leaves none, but its tape comes from the host.
- Flights and landings in the hybrid simulator are formulas tied to the event-driven simulator by one small program; a flight with coinciding corners is `invalid-address` there.
- A flight whose destination is in the column or in the row of the cell it left, or in the row north of it, has corners that coincide. The rule is defined there and a bijection, but the token does not come back; no property says so.
- RISC-U cells, which overwrite `rd` and join paths without a come-from. Their rule is no bijection, and bitr should find two states with the same successor.
- The comparison with RISC-R is 19 programs and one run each, with one input. The cell rule and rotor's model are not compared on all states: an instruction takes one step in one and a number of ticks without bound in the other, so that proof needs the cells of a transfer and the wire between them, not the rule alone. The examples read one byte, so nothing has been compared for other inputs.
- An `ld` at an address that is not word-aligned is not a property: no router looks at the lowest three bits.
- Distance, still. What is left for selfie is memory that is not the stack: 2GB of history that is used once forward, in strips that take 39 rows for one row of words, and the heap behind the third of the history region that is never used. A history stack that is not a region of 3GB, checkpointing, or denser memory would help; placement would not. Which words are hot is a guess from the regions, stack first; a profile, which the hybrid simulator could write, would know. Code is in the order of its addresses, hot or not.
- The hybrid simulator is tied to the event-driven one by 17 runs that agree, not by a proof that wire is monotone, and it does not run backward.
- Files other than the standard ones, and tapes of more than sixteen words, which is also the limit of rotor's model by default.
