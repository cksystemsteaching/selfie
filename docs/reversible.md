# selfie · cellfie · bitr — development plan

Oct 30, 2026 · Christoph Kirsch

## Goal and design rules

Build three C\* tools that evolve side by side: selfie extended with RISC-R, cellfie (an instruction-level reversible cellular machine that runs RISC-R), and bitr (a bounded model checker for BTOR2). They are linked only by files, and there is exactly one executable spec per model of computation. The aim is to show that cellfie is possible and that it sharpens how selfie is taught, not to compete on performance.

Rules every change must obey:

1. **C\* only.** Every tool compiles with selfie and with gcc, and runs on mipster, exactly as rotor and babysat do today.
2. **One file per tool**, using `selfie.h` as its library. Shared code becomes one header, the way `selfie.h` is shared now.
3. **One spec per model of computation.** RISC-R semantics live in rotor's RISC-R machine model; cellfie's cell rule is RISC-R per cell plus token movement, checked against that model. Everything else is checked against these two, never the other way round.
4. **Files are the only interfaces:** ELF binaries, RLE layouts, BTOR2 models. No tool calls into another tool's internals.
5. **Extend, don't fork.** RISC-R reuses RISC-U's 14 opcodes and encodings behind one flag. Existing behaviour, make targets and grader tests stay unchanged.
6. **Every milestone ends in a check a machine runs**, as a make target, not a claim.
7. **Deferred on purpose:** asynchrony, hardware targets, performance. Each stays a separate layer that can be added later.
8. **Reversibility is a switch.** Every tool runs with RISC-U and with RISC-R, so each benefit and each cost of reversibility shows up by flipping one flag.
9. **Asynchrony stays below the semantics.** All semantics are synchronous steps. Asynchrony enters only as an implementation layer proven to refine them, and only where several signals are in flight.

## Architecture

Selfie and cellfie produce files, and bitr reads them. The only things the tools share are the two specs: rotor's RISC-R model and cellfie's cell rule.

![Architecture: 3 tools, 5 file kinds, 2 specs](figures/reversible-architecture.png)

No model is generated per program. Programs and layouts enter bitr only as initial state, through its loaders. The abstraction map is the one file that ties cellfie's cells to RISC-R's `pc`, registers and memory.

RISC-R is the narrow waist. Cellfie runs it directly, one instruction per cell. What changes is that instructions and data sit in space, and the token pays for distance.

## Reversibility and symbolic execution: one picture

Reversibility and symbolic execution are two sides of one property. A step that is a bijection can be run backwards, concretely or symbolically, with the same machinery that runs it forwards. Without reversibility, going backwards needs either a recorded trace (concrete) or fresh variables and a solver (symbolic).

![Reversibility and symbolic execution: 2 directions × 2 modes](figures/reversible-duality.png)

**Turning reversibility off.** Reversibility is a switch, not an assumption. Every tool runs with RISC-U (off) and RISC-R (on), and the same programs compile both ways under selfie's `-r`. Flipping the one flag shows exactly where reversibility enters, and what it costs:

| Aspect | RISC-U (off) | RISC-R (on) | Measured as |
| --- | --- | --- | --- |
| Forward execution | baseline | Bennett history stack and extra instructions | instruction count, history size |
| Concrete backward | needs a recorded trace | runs each step's inverse | trace bytes |
| Symbolic backward | fresh variables and constraints per overwritten value | substitution only | variables, solver time |
| cellfie's cell rule | not a bijection; bitr finds two states with the same successor | a bijection, proven by bitr | bitr's check |
| Physical cost | one Landauer erasure per overwritten bit | no erasure in principle | erased bits counted, as a proxy |

Asynchrony stays orthogonal in the same way. All semantics are synchronous steps. In v1 only one cell is active per tick, so synchronous and asynchronous execution coincide, and a clockless implementation needs no synchronizer at all. Asynchrony first matters once several signals are in flight: several tokens, v2's bit-level regions, or level 4 of the story. There it enters as a synchronizer layer below the semantics, proven to refine the synchronous steps.

## Selfie extension: RISC-R

RISC-R keeps RISC-U's 14 opcodes and encodings and changes only what they mean, so starc's emitter, the decoder and the disassembler stay almost untouched. One flag (`-r`) selects RISC-R. Without it, selfie behaves exactly as today.

**The ISA, one rule per instruction class:**

| RISC-U | RISC-R meaning | Why it is reversible |
| --- | --- | --- |
| `add sub mul divu remu sltu` | `rd += op(rs1, rs2)`, with `rd` distinct from `rs1` and `rs2` | `x += f(y, z)` inverts to `x -= f(y, z)` for any f (the Janus trick) |
| `addi lui` | `rd += imm` | inverse is `rd -= imm` |
| `ld`, `sd` | `ld` = exchange `rd` with a memory word; `sd` unused | an exchange is its own inverse |
| `beq` | unchanged forward; every branch target holds a paired come-from `beq` | the pair tells reverse execution which way it came (Pendulum's idea) |
| `jal jalr` | `jal` adds the return address into a zeroed `ra`; the caller subtracts it after return | `ra` is uncomputed with a known constant |
| `ecall` | `read`, `write`, `exit` act on input and output tapes held in machine state | no information leaves the state |

Open point: RISC-R binaries look like RISC-V but do not run on RISC-V hardware. The ELF header gets a flag so nothing confuses the two.

One more ISA rule: the code segment is read-only. Fixing a program's code then keeps the step function a bijection on the remaining state, which is what tier-2 compilation relies on.

**The compiler, in two steps:**

1. **Bennett mode (no language change).** Every destructive assignment `x = e` becomes: compute `e` into zeroed temporaries, exchange `x` with a fresh zero slot on a history stack, add the result into `x`, then run the computation of `e` backwards so every temporary ends at zero again (compute, copy, uncompute). All of C\*, including selfie itself, then compiles to RISC-R unchanged.
2. **Garbage-free mode (small language change).** Add only `x += e` and `x -= e` to C\*, with `x` not occurring in `e`. These compile without touching the history stack. Both remain valid C, so selfie still compiles with gcc. Reversible conditionals and loops (Janus `fi`/`until`) are not C, so they stay out until there is a clear need.

**The emulator.** Mipster's replay engine already undoes instructions from a recorded trace (`execute_undo`, with `undo_ecall` still a TODO). For RISC-R, add a trace-free reverse mode that executes each instruction's inverse directly. Comparing the two is a lesson in its own right: undo with a trace is Bennett in the emulator, undo without a trace is reversibility in the ISA.

**The model.** Rotor already generates machine models without code. Add RISC-R forward and inverse machine models, both program-independent, with the history stack and tapes as named state. That pair becomes the RISC-R spec.

## bitr: a BTOR2-only bounded model checker in C\*

Bitr reads BTOR2 and nothing else, so it never needs to know whether a model came from selfie, cellfie or anywhere else. It is one C\* file, `tools/bitr.c`, built up in layers. Each layer is a mode of the same tool and is checked before the next one starts.

1. **Parser** for the BTOR2 subset rotor emits: bit-vector and array sorts, constants, operators, `state` / `init` / `next`, `input`, `bad`, `constraint`. bitme's `btor2.py` serves as the reference parser for differential tests.
2. **Loaders** that only turn data into `init` fragments, the write chains rotor already produces. One loader takes an ELF binary (RISC-U or RISC-R), the other an RLE layout for the CA grid. No semantics lives here.
3. **Concrete simulator**, the counterpart of btorsim. Rotor's existing evaluator (`eval_line`) moves into a shared header, `tools/btor2.h`, used by both rotor and bitr. That keeps rotor out of bitr as a tool while sharing the code as a library, the way `selfie.h` is shared. The first real check: mipster and the simulator run the same binary and produce the same state at every step.
4. **Bit-blaster** to CNF using Tseitin encoding. Arrays are handled by read-over-write elimination, which works because k is bounded, together with rotor's existing options for bounding memory segments.
5. **SAT core.** Babysat stays as the executable spec (plain enumeration). Next to it goes a minimal CDCL solver in C\*: two watched literals, first-UIP learning, restarts only if needed. Both must give the same SAT/UNSAT answer on `examples/sat` and on every CNF bitr generates.
6. **Forward BMC:** unroll k steps and check `bad`. A satisfying assignment becomes an input trace that mipster replays, which closes the loop.
7. **Backward BMC on the inverse model:** unroll from `bad` backwards to `init`, where each step is plain substitution with no quantifiers. Whether this beats forward BMC on real programs is a research question, not an assumption.
8. **Product machine:** two BTOR2 models plus an abstraction function, also in BTOR2, give an equivalence check. This is how selfie and cellfie are compared, and it is fully generic.
9. **Escape hatch:** export the unrolled formula as DIMACS or SMT-LIB, or hand the BTOR2 file straight to btormc, Pono or bitme, for anything beyond toy size.

**Specialisation, later (`bitr -specialize`).** Needed only for levels 3 and 4 of the story. Given a model and constant code, this mode partially evaluates the model into a smaller one, then applies scalar replacement. Every pass goes from BTOR2 to BTOR2, and the product machine checks it against its input. Optimisation uses cheap solver-backed passes by default: SAT sweeping, and removing logic that k-induction proves dead.

**The BTOR2 profile.** BTOR2 itself stays unextended. A short convention document fixes three things: symbol names for architectural state (`pc`, registers, memory segments, history stack, tapes); file pairs for forward and inverse models; and the abstraction function as a separate file over cellfie's state.

**Realism.** A naive CDCL solver on bit-blasted RISC-R handles programs of a few dozen instructions at small k. That is enough for teaching and for the selfie-versus-cellfie checks on small cases. Research-scale results go through the escape hatch.

## cellfie: an instruction-level cellular machine for RISC-R

Cellfie is one C\* file, `tools/cellfie.c`. Each cell holds one RISC-R instruction, one memory word, or a piece of wire. A single token carries `pc` and the register file from cell to cell. The cell rule is simply RISC-R semantics applied where the token is, so there is no microcode and no interpreter layout. The machine is synchronous and reversible. V1 is deliberately coarse; bit-level cells come later as a checked refinement.

**Cells and token.**

- **Instruction cell:** one RISC-R instruction plus an outgoing direction. When the token enters, the cell applies the instruction to the token's registers and passes the token on.
- **`beq` cell:** two outgoing paths, chosen by the condition. Its paired come-from cell sits where the paths merge, so reverse execution knows which way the token arrived.
- **Wire cells:** move the token one cell per tick, including turns and crossings. `jal` and `jalr` route the token along wires, steered by address bits.
- **Memory cells:** one 64-bit word each. `ld` (exchange) sends the token to the word and back.
- **Tape cells:** input and output for `read` and `write`, following RISC-R's system-call model.

**Rule and reversibility.** The rule is a bijection because every instruction is a bijection on the registers and every wire move is a permutation. Bitr checks this symbolically: rotor's per-instruction inverses give the inverse rule, and inverse after rule must be the identity. Only the token's cell changes per tick, so an event-driven simulator costs path length per instruction.

**Reversibility off.** Cellfie also accepts RISC-U layouts, whose instruction cells overwrite `rd`. That rule is not a bijection, and bitr's check finds two states with the same successor. Running backwards then needs a recorded trace. This is the switch from rule 8, at cell level.

**Formats.** A layout is RLE extended with cell contents (instruction words, memory words). `cellfie -btor2` emits the cell machine as BTOR2 for a given grid size. Layouts enter only as `init`, through bitr's loader.

**Layout compiler.** It turns a RISC-R binary into a layout. Instructions go along a path in program order, branch and jump targets are connected by wire, and memory sits as a region beside the code. Code layout is the performance model: distance is time.

**Equivalence with selfie.** An instruction boundary is the token entering an instruction cell. The abstraction function is direct: `pc` is that cell's address, the registers are the token's payload, memory is the memory cells. Bitr's product check against rotor's RISC-R model holds at every step, and any program can be compared with mipster.

**Running all of selfie.** Event-driven simulation costs tens to thousands of ticks per instruction, mostly memory round trips. Selfie's self-compilation, around 10⁸–10⁹ instructions, should then take hours when run natively. That needs measuring. Hybrid simulation stays as the fallback: abstract RISC-R steps wherever nobody is watching.

**Constructor and tape.** Loading a program means constructing it. A constructor token reads a tape and writes instruction and memory cells into blank space. The tape is kept, so the global map stays injective. The layout compiler is the shortcut that writes the same cells directly. Self-replication, a program that writes a copy of its own cells, follows Avida's precedent.

**The three selfie analogies:**

| Analogy | cellfie version | Target |
| --- | --- | --- |
| Self-compilation | the layout compiler, compiled by selfie to RISC-R, runs on cellfie and reproduces its own layout: L1 = L0 | M11 |
| Self-execution | all of selfie runs on cellfie, cell by cell | M13, pending the speed measurement |
| Self-hosting | the constructor builds guest programs in walled regions; replication = it builds itself plus its tape | after M10 |

**Later layers**, each checked by bitr against the layer above:

1. **Concurrency.** Several tokens act as threads, each carrying its own register file as its thread context. After that comes a dataflow variant in which operand tokens flow between instruction cells, as in WaveScalar; that is the parallel tier 2.
2. **Register liveness.** The layout compiler knows which registers are dead along a path, so the token can drop them and pick them up again later. Register allocation becomes deciding what to carry. Not in v1, because it makes the token's shape vary along the path and complicates the cell rule.
3. **Bit-level refinement (v2).** Each v1 cell kind (instruction, `beq`, come-from, wire, turn, crossing, memory, tape) is refined once into a region of small cells with a tiny alphabet: reversible gates or RLEMs in Morita-style partitioned cells. The token becomes a bit-serial stream of signals rather than one giant state. Bitr proves each refined region equal to the v1 cell it replaces. Layouts can mix refined and abstract cells, so v2 grows one cell kind at a time while v1 keeps working. This is where cellfie becomes a reversible material.

## The story: software becomes hardware, provably

Cellfie's refinement layers form one continuous slide from software into hardware. Bitr proves every step equivalent to mipster, so the semantics stay fixed while the layout moves. This is the repo's proof-versus-truth, syntax-versus-semantics premise made concrete, and it is Gershenfeld's bits-and-atoms thesis made checkable.

v1's cost is travel, not execution: executing an instruction takes one tick, but jumps, memory round trips and the single token all cost distance. Each level removes some of that travel and gives up some generality:

1. **v1, program as data.** Coarse cells hold instructions, and the token travels between them.
2. **v2a, universal bit-level regions.** Small cells read the stored instruction bits and interpret them. This is still software, now made of material.
3. **v2b, specialised regions.** Each region is built for one fixed instruction with fixed operands, so nothing is decoded any more: instructions become structure. This is partial evaluation, carried out by `bitr -specialize`.
4. **v2c, fusion.** On straight-line paths the token dissolves. Register values flow along wires, and statically addressed memory words move next to the cells that use them. What remains is a circuit shaped like the program, and the constructor that builds it is digital fabrication of that program.

How far a program can slide is a property of the program itself. Array kernels can reach level 4. Selfie, with pointers and `malloc`, stays partly interpreted.

**Caveat.** Level 4 needs several signals in flight at once, so the concurrent element set the design otherwise avoids returns here. It is the research endpoint of the story, not a dependency of v1. Levels 1–3 already show most of the blur.

## Self-reference across the system

Selfie's three self-reference properties hold in every tool. At the hardware end of the story, two of them merge and one marks a boundary.

|  | selfie, RISC-R | bitr | cellfie v1 | cellfie, hardware end |
| --- | --- | --- | --- | --- |
| **Self-compilation** | fixed point in Bennett mode (M2) | selfie compiles bitr; bitr bounded-checks its own binary | selfie on cellfie compiles selfie to an identical binary (M13); the layout compiler reproduces its own layout (M11) | compiler plus constructor builds itself: self-reproduction |
| **Self-execution** | mipster on mipster; each level keeps its own history | bitr's simulator runs bitr's binary in the RISC-R model | mipster on cellfie; cellfie's simulator on cellfie | does not survive: a universal interpreter cannot be specialised away |
| **Self-hosting** | hypster, with the context switch as an exchange | — | the constructor builds guests in walled regions | merges with self-reproduction |

What this reveals about cellfie:

1. **Nested self-execution compounds garbage.** A mipster in Bennett mode logs history for its own state, including every update its guest causes, so each level of nesting multiplies the history. That makes M15 an argument for a reversible interpreter, as Yokoyama and Glück built for Janus, not just a cost table.
2. **Hosting becomes spatial.** Hypster divides time; cellfie's host divides space into walled regions, and a context switch is reversible for free because it is an exchange. "The isolator cannot isolate itself" turns geometric: the constructor walls in its guests, but nothing walls in the constructor.
3. **The universal machine is the irreducible software residue.** As programs slide into hardware, self-compilation plus construction becomes von Neumann self-reproduction, and self-hosting folds into it. Self-execution resists. A universal interpreter takes its program as input, so there is nothing static to specialise. Specialising it to a fixed program (the first Futamura projection) produces a compiled program, while the interpreter itself stays software. M14 makes this boundary measurable.

## Milestones

The critical path runs M1 → M3 → M5 → M7 → M8. M7 is the first time cellfie meets selfie. After M8, the work splits into construction (M10, M11) and running all of selfie (M13). M6 and M9 run alongside. Each row ends in a make target that passes or fails.

| # | Tool | Milestone | Needs | Done when |
| --- | --- | --- | --- | --- |
| M0 | all | Branch, `CLAUDE.md` with the design rules, empty make targets | — | existing `make` targets and grader tests unchanged and green |
| M1 | selfie | RISC-R in mipster: forward execution and trace-free reverse execution, tested with hand-written RISC-R code | M0 | for every test, N steps forward then N steps back give the initial state bit for bit |
| M2 | selfie | Bennett-mode compiler behind `-r` | M1 | selfie compiled to RISC-R and run on mipster compiles itself to an identical RISC-R binary, then runs back to its initial state, with Bennett checkpointing if the history stack (possibly gigabytes) does not fit |
| M3 | rotor | RISC-R forward and inverse machine models; evaluator moved into `tools/btor2.h` | M1 | rotor's existing targets unchanged; inverse after forward is the identity on random states |
| M4 | bitr | Parser, loaders, concrete simulator | M3 | bitr's simulator matches mipster `-r` step by step on all RISC-R examples |
| M5 | bitr | Bit-blaster, CDCL next to babysat, forward BMC, witness replay | M4 | finds the known bugs in `examples/symbolic`; witnesses replay in mipster; CDCL and babysat agree on every CNF; proves inverse after forward is the identity symbolically for small k |
| M6 | cellfie | Cell rule (instruction, `beq`, wire, memory and tape cells), event-driven simulator, layout format | M3 | bitr proves inverse after rule is the identity; a forward-then-backward run restores the initial grid |
| M7 | cellfie | A hand-laid program of a few instructions, including a branch and a memory exchange | M5, M6 | bitr's product check against rotor's model passes at every step up to small k; the run matches mipster |
| M8 | cellfie | Layout compiler from RISC-R binaries | M7 | selfie-compiled examples run on cellfie identically to mipster, step by step |
| M9 | selfie | `+=` and `-=` in C\*, compiled without history | M2 | the history stack stays empty for programs that use only these; selfie still compiles with gcc |
| M10 | cellfie | Construction ISA, constructor, tape emission | M8 | constructor plus tape plus blank grid reaches exactly the compiled layout plus tape and idle constructor |
| M11 | cellfie | Self-compilation fixed point: the layout compiler, compiled by selfie to RISC-R, runs on cellfie | M8, M10 | L1 = L0 byte for byte |
| M12 | bitr | Backward BMC on the inverse model, compared with forward BMC | M5 | a written comparison on the examples (research result, not a pass/fail gate) |
| M13 | cellfie | All of selfie on cellfie, event-driven, with hybrid simulation as fallback | M8 | selfie compiles itself on cellfie with output identical to mipster's; running time recorded |
| M14 | cellfie, bitr | Demonstrator: one array kernel at all four levels of the story (v1, v2a, v2b, v2c), next to mipster on cellfie, which should not dissolve | M8, M13 | each level verified against mipster by bitr; one chart of cells used, ticks and active cell-updates per level, with the reprogrammability each level gives up (research result; level 4 needs concurrent elements) |
| M15 | all | Reversibility on/off comparison: the same programs as RISC-U and as RISC-R, through every tool | M2, M5, M8, M12 | a written table per example: instruction count, history size, trace bytes, backward symbolic variables and solver time, erased bits (research result) |

Later, each as a layer checked by bitr: several tokens (threads), the dataflow tier 2, bit-level refinement of instruction cells, replication, clockless execution on DICE.

## Risks, open questions, deferred work

The biggest risk is routing the token across the grid by address, not whether cellfie can be built. Everything else on this list has a known fallback.

**Risks and fallbacks:**

- **Routing.** `jalr` and `ld` need the token steered by address bits to arbitrary cells. Fallback: a fixed routing spine (a tree or bus of wire cells) instead of free placement, at the cost of longer paths.
- **RISC-R control flow.** Paired come-from branches and uncomputing `ra` are the subtlest change to starc. Fallback: prove the scheme in hand-written RISC-R code in M1 before the compiler touches it.
- **Speed.** Memory round trips dominate, so all of selfie on cellfie may take hours or far longer, depending on layout. Fallback: hybrid simulation (abstract RISC-R steps wherever nobody watches), backed by the M7 and M8 equivalence checks.
- **Bitr's own solver** only reaches toy sizes. Fallback: the escape hatch to external solvers.
- **Bounded memory.** Every equivalence holds only up to the memory bound in the models. Say so wherever a result is stated.
- **Drift between selfie and cellfie.** Fallback: rotor's RISC-R model is the single spec, and the M5 and M8 checks run in CI.
- **Is it still a cellular automaton?** Formally yes: finite states, one uniform rule, local neighbourhoods, synchronous update. In spirit no: the alphabet is astronomically large and each cell is a processor, as in Avida. Fallback: say so plainly in v1, and let v2's bit-level refinement earn the stronger claim one cell kind at a time.
- **Bennett history at selfie scale.** Selfie compiling itself in Bennett mode writes history for every destructive store, plausibly gigabytes. Fallback: Bennett checkpointing (recompute between checkpoints, trading time for space), and M9's garbage-free `+=` and `-=` in selfie's hot paths.

**Open questions, with recommendations (tick once agreed):**

- [x] **RISC-U encodings or a separate opcode space for RISC-R?** Recommendation: keep RISC-U's encodings and mark RISC-R binaries with a flag in the ELF header. Mipster, rotor and bitr's loader refuse a binary whose flag doesn't match the selected mode. A separate opcode space would duplicate the encoder, decoder and disassembler in selfie, plus the decode logic in rotor and in cellfie's cell rule, all for a confusion risk that one flag already removes.
- [x] **Start the block rule from Morita, or design it from scratch?** Recommendation: start from Morita's partitioned CAs built on rotary elements (RLEMs). They come with proven reversibility, proven universality and reversible self-reproduction. This now applies only to the later bit-level refinement: instruction-level cells in v1 need no bit-level rule.
- [x] **Which branch and file hold this plan?** Recommendation: a `RISC-R` branch off `main`, kept away from the `intelligence` branch. Export this doc to `docs/reversible.md` there, and add a root `CLAUDE.md` on that branch that points to it and repeats the design rules. The repo's `PLAN.md` stays the course plan.

**Deferred, each as a separate layer:** asynchrony, needed only once several signals are in flight, via a synchronizer proven to refine the synchronous steps (Nakamura and Lee–Peper as starting points); physical reversibility; performance.

**Future work: FPGA.** With instruction-level cells, the natural hardware target is a RISC-R core generated as Verilog from rotor's BTOR2 model. Validate the generator by round trip: Yosys reads the Verilog and writes BTOR2 back, and bitr checks it against the source. Bit-level refined cells could go the same way later.

## How to develop it

Design here, build in Claude Code in the repo. Implementation is an edit–`make`–run loop over a long series of sessions, and that belongs in a native shell with full git.

**Why not here.** This chat can reach the repo, but deleting files there is off by default. Git deletes its own lock files and replaces tracked files by deleting them, so commit, checkout, stash and reset break or leave `.lock` files behind. This chat is also a worse place for long runs of `make` and mipster.

**Setup for Claude Code:**

- [x] Work on a separate branch, not `main` and not the `intelligence` branch.
- [x] Add a `CLAUDE.md` next to the existing `GEMINI.md`, holding the design rules above and the milestone table.
- [x] One milestone per session. A session ends only when its make target passes.

**Which model.** Fable is the stronger model tier. Use it where the design is still open: M1 (RISC-R control flow), M5 (bit-blaster and CDCL correctness), M6–M8 (cell rule, routing and layout compiler). Opus is enough for layers that are already well specified: M0, M3, M4, M9. Nothing measures the difference on this codebase yet, so run M1 with Fable and judge from that.
