# Selfie on the RISC-R branch

This branch extends selfie with RISC-R (a reversible variant of RISC-U), and prepares cellfie (an instruction-level reversible cellular machine that runs RISC-R) and bitr (a BTOR2-only bounded model checker). The full development plan is `projects/reversible.md`; read it before changing anything on this branch. The instruction set is specified in `riscr.md`, next to `riscu.md`. The repo's `PLAN.md` is the course plan and belongs to the `intelligence` branch, not to this work.

## Design rules

Every change must obey these rules from the plan:

1. **C\* only.** Every tool compiles with selfie and with gcc, and runs on mipster, exactly as rotor and babysat do today. Check with `./selfie -c <file>` as well as `make`.
2. **One file per tool**, using `selfie.h` as its library. Shared code becomes one header.
3. **One spec per model of computation.** RISC-R semantics live in rotor's RISC-R machine model (M3); cellfie's cell rule is RISC-R per cell plus token movement. Everything else is checked against these two.
4. **Files are the only interfaces:** ELF binaries, RLE layouts, BTOR2 models. No tool calls into another tool's internals.
5. **Extend, don't fork.** RISC-R reuses RISC-U's 14 opcodes and encodings behind one flag. Existing behaviour, make targets and grader tests stay unchanged.
6. **Every milestone ends in a check a machine runs**, as a make target, not a claim.
7. **Deferred on purpose:** asynchrony, hardware targets, performance.
8. **Reversibility is a switch.** Every tool runs with RISC-U and with RISC-R.
9. **Asynchrony stays below the semantics.** All semantics are synchronous steps.

## Conventions

- Selfie's coding style: C\* subset only (no `&&`, `||`, `!`, `+=`, `for`, structs, bitwise operators; use `not()`, `and()`, `or()`, `bitwise_xor()`, `left_shift()`, `get_bits()`), locals declared before statements, section banners, one blank line between statements, comments that state the semantics.
- RISC-R code in `selfie.c` lives in `do_riscr_*` procedures in the `RISC-R INSTRUCTIONS` section; RISC-U procedures dispatch to them when `RISCR` is set and are otherwise untouched. Backward execution is the `reverse` flag: `instruction_address()` and `continue_at()` hide the direction.
- Testing code lives in `tests/`, never in `tools/` or `selfie.c`. The M1 harness is `tests/riscr-test.c`, built like a tool with `--include selfie.h`, and must itself be C\*.
- Options: `-riscr` selects RISC-R (like `-m32`, before `-c`, `-l`, `-m`); `-rev <MB>` runs forward and then backward (`-r` was taken by the replay engine, so the plan's `-r` became `-riscr`).

## Milestones

| # | Tool | Deliverable | Depends on | Check |
| --- | --- | --- | --- | --- |
| M0 | all | Branch, this file, make targets | — | existing `make` targets and grader tests unchanged and green |
| M1 | selfie | RISC-R in mipster: forward and trace-free backward execution, tested with hand-written RISC-R code | M0 | `make riscr`: for every test, N steps forward then N steps back give the initial state bit for bit |
| M2 | selfie | Bennett-mode compiler behind `-riscr` | M1 | selfie compiled to RISC-R and run on mipster compiles itself to an identical RISC-R binary, then runs back to its initial state |
| M3 | rotor | RISC-R forward and inverse machine models | M1 | inverse after forward is the identity on random states |
| M4–M15 | see `projects/reversible.md` | | | |

Status: M0 and M1 done (October 31, 2026), M1 addendum with system call results, `openat` and `brk` done (November 1, 2026). `make riscr` runs the harness natively and as a RISC-U executable on mipster; `make riscr-rev` demonstrates `-rev`.

## Decisions taken in M1 that refine the plan

- `addi rd,rs1,imm` means `rd += rs1 + imm`, not just `rd += imm`, so register moves into zeroed registers stay one instruction.
- `mul`, `divu`, `remu`, and `sltu` are `rd ^= f(rs1, rs2)` (self-inverse) rather than `rd += f`, because with `+=` no forward program can ever uncompute a comparison or a product, so every loop would leak a register per iteration. `add`, `sub`, `addi`, `lui` stay additive, each invertible by another forward instruction.
- Paired branches: a taken transfer lands *after* its come-from (`target + 4`), so no extra branch register is needed and the step function is a bijection on all states given the static pairing. The come-from of a `beq` may test different registers; its condition must hold at the transfer, checked dynamically.
- Calls: `jal rd` requires `rd == 0` and links `pc + 4`; `jalr rd,0(rd)` is the come-from of a call and also the return, uncomputing `rd`; the come-from of a return is a `jal ra` right after the call site pointing at the callee's return `jalr`. The compiler will need the callee's epilogue address at every call site (M2).
- System calls take arguments in `a1-a3` and add their result into `a0`; backward execution recomputes the result from the tapes and subtracts it. `exit` leaves the state unchanged; `read` exchanges words with a lazily filled input tape that remembers where the file ended; `write` appends to an output tape and still writes the file; `openat` allocates the next descriptor and a tape per file; `brk` requires `a0 == 0`, grows the heap and returns the previous break in `a0`, zero on failure. This is the M1 addendum of November 1, 2026; it changes the system call convention that M2's wrappers must emit.
- RISC-R binaries carry `EF_RISCR` (bit 8 of `e_flags`); mipster refuses mismatches instead of switching modes silently.
- In RISC-R mode mipster does not write the context pointer into `a6` on context switches (hypster is unsupported), so registers are bit for bit reversible.
- An instruction that throws an irreversible instruction exception has no effect; the control-flow inverses were checked by a randomized round trip (200,000 random states, forward then backward and backward then forward, no mismatch) on November 1, 2026, and `riscr.md` records why a branch register, even one hidden in `zero`, would not remove come-froms.

## Open for M2

- `lui` cannot negate the immediate `-2^19`; uncomputing such a constant needs two instructions.
- Bennett mode needs a history stack and, per call site, the callee's epilogue address (a second fixup chain in starc).
- The replay engine (`-r`) is refused in RISC-R mode; comparing trace-based undo with trace-free backward execution is a lesson still to be written.
- `malloc` must learn its initial break from the binary (the heap start is `round_up(data_start + data_size, PAGESIZE)`) since `brk(0)` no longer queries it.
- Tapes are 1MB each (`MAX_TAPE_SIZE`), enough for selfie.c and selfie's binary, with at most 64 open files.
- `riscr.md` ends with a table of how each instruction would look with dedicated opcodes, in case the `^=` and come-from encodings hurt in M2.
