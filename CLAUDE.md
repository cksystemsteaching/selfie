# Selfie on the RISC-R branch

This branch adds RISC-R (a reversible variant of RISC-U) to selfie as the tool riscr (`tools/riscr.c`), and prepares cellfie (an instruction-level reversible cellular machine that runs RISC-R) and bitr (a BTOR2-only bounded model checker). The full development plan is `projects/reversible.md`; read it before changing anything on this branch. The instruction set is specified in `riscr.md`, next to `riscu.md`. The repo's `PLAN.md` is the course plan and belongs to the `intelligence` branch, not to this work.

## Design rules

Every change must obey these rules from the plan:

1. **C\* only.** Every tool compiles with selfie and with gcc, and runs on mipster, exactly as rotor and babysat do today. Check with `./selfie -c <file>` as well as `make`.
2. **One file per tool**, using `selfie.h` as its library. Shared code becomes one header.
3. **One spec per model of computation.** RISC-R semantics live in rotor's RISC-R machine model (M3); cellfie's cell rule is RISC-R per cell plus token movement. Everything else is checked against these two.
4. **Files are the only interfaces:** ELF binaries, RLE layouts, BTOR2 models. No tool calls into another tool's internals.
5. **Extend, don't fork.** RISC-R reuses RISC-U's 14 opcodes and encodings, marks its binaries with one ELF flag, and lives in its own tool, riscr, on top of `selfie.h`. Existing behaviour, make targets and grader tests stay unchanged.
6. **Every milestone ends in a check a machine runs**, as a make target, not a claim.
7. **Deferred on purpose:** asynchrony, hardware targets, performance.
8. **Reversibility is a switch.** Every tool runs with RISC-U and with RISC-R.
9. **Asynchrony stays below the semantics.** All semantics are synchronous steps.

## Conventions

- Selfie's coding style: C\* subset only (no `&&`, `||`, `!`, `+=`, `for`, structs, bitwise operators; use `not()`, `and()`, `or()`, `bitwise_xor()`, `left_shift()`, `get_bits()`), locals declared before statements, section banners, one blank line between statements, comments that state the semantics.
- `selfie.c` stays minimal: it only knows `EF_RISCR`, decodes `e_flags`, and refuses to run RISC-R binaries. All RISC-R code lives in `tools/riscr.c`, which follows `selfie.c`'s layout (library, compiler, interface, architecture, runtime, main) and has its own run loop, as monster does. Instructions are `do_riscr_*` procedures in its `RISC-R INSTRUCTIONS` section. Backward execution is the `reverse` flag: `instruction_address()` and `continue_at()` hide the direction.
- Testing code lives in `tests/`, never in `tools/` or `selfie.c`. The M1 harness is `tests/riscr-test.c`, built like a tool with `--include selfie.h --include riscr.h` (`riscr.h` is generated from `tools/riscr.c` as `selfie.h` is from `selfie.c`), and must itself be C\*.
- Options: `riscr` takes selfie's options plus `-t <binary>` (translate the loaded RISC-U binary into a RISC-R binary, which stays loaded), `-m <MB>` (forward) and `-rev <MB>` (forward and then backward, checking that the initial state is restored) for RISC-R binaries; there is no RISC-R flag in selfie.

## Milestones

| # | Tool | Deliverable | Depends on | Check |
| --- | --- | --- | --- | --- |
| M0 | all | Branch, this file, make targets | — | existing `make` targets and grader tests unchanged and green |
| M1 | riscr | RISC-R emulator: forward and trace-free backward execution, tested with hand-written RISC-R code | M0 | `make rev`: for every test, N steps forward then N steps back give the initial state bit for bit |
| M2 | riscr | Bennett mode: RISC-U to RISC-R, as the translator `riscr -t`, see the decision of November 6, 2026 below | M1 | `make bennett`: selfie translated to RISC-R and run on riscr compiles itself to an identical binary and runs back to its initial state; riscr's translator reaches a fixed point on itself |
| M3 | rotor | RISC-R forward and inverse machine models; evaluator moved into `tools/btor2.h` | M1 | rotor's existing targets unchanged; inverse after forward is the identity on random states |
| M4–M17 | see `projects/reversible.md` | | | |

Status: M0 and M1 done (October 31, 2026), M1 addendum with system call results, `openat` and `brk` done (November 1, 2026). Emulator moved from `selfie.c` to `tools/riscr.c` (November 2, 2026). M2 done (November 6, 2026). `make rev` runs the harness natively and as a RISC-U executable on mipster and checks that mipster refuses RISC-R binaries; `make riscr-rev` demonstrates `riscr -rev` natively and with riscr itself running on mipster; `make bennett` is the M2 check, about 7 minutes and 3GB of memory.

## Decisions that refine the plan

- `addi rd,rs1,imm` means `rd += rs1 + imm`, not just `rd += imm`, so register moves into zeroed registers stay one instruction.
- `mul`, `divu`, `remu`, and `sltu` are `rd ^= f(rs1, rs2)` (self-inverse) rather than `rd += f`, because with `+=` no forward program can ever uncompute a comparison or a product, so every loop would leak a register per iteration. `add`, `sub`, `addi`, `lui` stay additive, each invertible by another forward instruction.
- Paired branches: a taken transfer lands *after* its come-from (`target + 4`), so no extra branch register is needed and the step function is a bijection on all states given the static pairing. The come-from of a `beq` may test different registers; its condition must hold at the transfer, checked dynamically.
- Calls: `jal rd` requires `rd == 0` and links `pc + 4`; `jalr rd,0(rd)` is the come-from of a call and also the return, uncomputing `rd`; the come-from of a return is a `jal ra` right after the call site pointing at the callee's return `jalr`. The compiler will need the callee's epilogue address at every call site (M2).
- System calls take arguments in `a1-a3` and add their result into `a0`; backward execution recomputes the result from the tapes and subtracts it. `exit` leaves the state unchanged; `read` exchanges words with a lazily filled input tape that remembers where the file ended; `write` appends to an output tape and still writes the file; `openat` allocates the next descriptor and a tape per file; `brk` requires `a0 == 0`, grows the heap and returns the previous break in `a0`, zero on failure. This is the M1 addendum of November 1, 2026; it changes the system call convention that M2's wrappers must emit.
- RISC-R binaries carry `EF_RISCR` (bit 8 of `e_flags`); mipster refuses them and riscr refuses binaries without the flag, instead of switching modes silently.
- Riscr does not write the context pointer into `a6` on context switches, so registers are bit for bit reversible; context switching, and with it hypster, stays unsupported until M17, which adds the from-context into a zeroed `a6` instead.
- November 2, 2026: the emulator moved out of `selfie.c` into `tools/riscr.c` to keep `selfie.c` minimal (M1 had added about 1,380 lines; about 10 remain). This refines rule 5: RISC-R is a tool on top of selfie, not a flag inside it. M2 followed the same way, as a translator from RISC-U to RISC-R binaries in `tools/riscr.c` rather than a second code generator in starc, see November 6.
- An instruction that throws an irreversible instruction exception has no effect; the control-flow inverses were checked by a randomized round trip (200,000 random states, forward then backward and backward then forward, no mismatch) on November 1, 2026, and `riscr.md` records why a branch register, even one hidden in `zero`, would not remove come-froms.
- November 6, 2026: M2 is the translator `riscr -t`, in riscr's compiler section, from RISC-U binaries as starc emits them; starc is unchanged. The scheme is the Bennett translation section of `riscr.md`: six reserved registers (`s2` history pointer, `s3` flag, `s4` one, `s5` program break, `s6`/`s7` scratch), one fixed RISC-R sequence per RISC-U instruction, a come-from chain plus one pushed flag per branch target, islands for transfers beyond the reach of `beq`, and a prologue that allocates the history stack (3GB, `HISTORY_GIGABYTES`) at the start of the heap with one `brk`. The translator finds a callee's return as the first `jalr` after its entry, so starc needs no second fixup chain. RISC-U `brk` semantics, including `brk(0)`, are reproduced from the program break register, so `malloc` and the bootstrap stay unchanged. Measured: 3.6 RISC-R instructions per RISC-U instruction statically, 3.5 dynamically; selfie compiling itself pushes 0.65 words per RISC-U instruction, 2GB in total, and reverses in about the time it took forward.
- `-rev` now takes a snapshot of the initial state at boot and checks it after backward execution (`take_initial_snapshot`, `is_initial_state_restored` in `tools/riscr.c`); `tests/riscr-test.c` uses the same procedures through `riscr.h`.
- `MAX_TAPE_SIZE` is 8MB: selfie reads source files one byte per `read`, which costs one tape word per byte. `MAX_CODE_SIZE` and `MAX_BINARY_SIZE` are four times selfie's in riscr, since RISC-R binaries are that much larger.
- `bitwise_xor` masks the bytes it loads from its table; with gcc `char` is signed, which made `mul`, `divu`, `remu`, and `sltu` wrong for bytes of 128 and above (found by M2, November 6, 2026).

## Open after M2

- The most negative immediate cannot be negated in one instruction, so uncomputing such a constant needs two: `-2^19` for `lui`, `-2^11` for `addi`. The translator never negates constants, it pushes.
- Riscr has no replay engine (`-r`); comparing trace-based undo with trace-free backward execution is a lesson still to be written (M15).
- The history stack is a fixed 3GB region; Bennett checkpointing was not needed for selfie and is not implemented. Programs that overflow it fail at the `brk` of the prologue (exit code 20) or run into their own heap.
- The translated bootstrap still executes RISC-U's two `brk` calls, now against the program break register; `malloc` keeps its RISC-U shape. A garbage-free M9 code generator would emit RISC-R system calls directly.
- Transfers beyond the reach of `beq` cost 9 instructions at the origin and 2 per origin plus 4 at the target; selfie has 28 of them.
- `riscr.md` ends with a table of how each instruction would look with dedicated opcodes; M2 confirmed the costs that table predicts: four `^=` instructions need the scratch sequence, and `jal zero` come-froms force islands.
