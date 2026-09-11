# What is Intelligence? — a plan for three classes and one book

Working document on the `intelligence` branch. It proposes how the three classes
(ICS, CC, SE) and the new edition of the book are structured around the argument of the
[What is Intelligence?](docs/presentations/what-is-intelligence/) talk. Nothing below is
built yet; the point is to agree on the skeleton first. Decisions already taken and the
questions still open are collected at the end.

## 1. The premise

One distinction carries everything: **proof versus truth**, **syntax versus semantics**,
**notation versus meaning**. The story runs along one axis of size:

> small → vast → countable → uncountable

Finite things you can enumerate but not afford to (orders of magnitude, state spaces).
Everything you can *write down* is countable (programs, proofs, grammars, machine code,
models). What you *mean* is not (behaviours, truths, the reals). So almost every truth has
no proof, and any notation rich enough to describe itself — a compiler, a kernel, an axiom
system, a language model — runs into Cantor, Gödel, Turing and Rice. Every one of these is
read twice: **what it forbids** and **what it opens**. The answer to the title:

> Intelligence is developing new formal languages — or at least new properties in existing
> ones — which requires finding and understanding promising *unproven* truth.

The purpose, stated early in every talk and in the book's introduction: a deep understanding
of the basic principles of computer science, deep enough to position generative AI, and
whatever comes next, properly. The principles predate the technology and outlast it.

Selfie stays the specimen. Its three commands are the three theorems you can run:
self-compilation is a fixed point (Gödel's self-reference), self-execution is the universal
machine (Turing's forward move), self-hosting is the bootstrap problem (the second
incompleteness theorem as engineering: the isolator cannot isolate itself). The tools around
it — rotor, bitme, babysat — are where syntax is turned into a formula and meets
NP-completeness. The legacy generators (monster, beator) are not taught; they remain in the
repository's extras.

## 2. The spine — six stations, shared by all three classes and the book

| # | Station | The principle | Selfie manifestation | Forbids / opens |
|---|---|---|---|---|
| I | **Size** (finite) | Orders of magnitude; a bit is one distinction; 34 bytes beat the universe; 4 GiB of RISC-U memory is 2^34,359,738,368 states | `./selfie -c selfie.c` reporting on itself; the machine's state count; a test run visits one state | Testing shows presence, not absence / the vastness is the inventory |
| II | **Notation** (countable) | Everything writable is countable; formal languages; Gödel numbering is just encoding; a binary is a number | C\*, RISC-U, EBNF; `-o` writes a number; `-s` prints it in another notation; the machine and mipster | No notation is lost / all of it can be computed with |
| III | **Meaning** (uncountable) | Cantor's diagonal on subsets and on behaviours; meanings outnumber notations; truths without proof; Gödel I & II; halting; universality; Rice | A compiler defines the meaning of the language it is written in; self-compilation as fixed point; trusting trust; mipster as universal machine; hypster and the bootstrap problem; what starc can and cannot decide | No final language, no self-certificate, no decision procedure for meaning / no ceiling |
| IV | **Cost** (decidable ≠ doable) | P, NP, NP-completeness, Cook–Levin; why SAT is hard and why solvers work anyway; SMT; bounded model checking; Landauer | rotor turns RISC-V code into a BTOR2/SMT-LIB formula; bitme unrolls it k steps and asks a solver; babysat is the executable specification of a SAT solver | Brute force as a strategy / cryptography, and room for cleverness |
| V | **Machines** (AI) | What an LLM mechanically is; hallucination as plausible-and-not-true; world models as a bid for semantics; the loops are closed; generation cheap, verification not | The verification gate: compiler, test, model checker, measurement — every tool of station IV read as the outside check a generator cannot supply | No self-verifying system / value at the two ends: specification and verification |
| VI | **Intelligence** (practice) | The definition; depth as the organ for finding unproven truth; six habits; metrics and Goodhart | Selfie read against the definition: a language and its meaning, a machine, a fixed point and its limit, a workshop of outside checks | — |

Every class visits all six stations. ICS visits them at the level of the talk with selfie
run live. CC dwells in station III from the compiler side and does station IV in full. SE
dwells in station III from the systems side and does station IV applied.

## 3. The book

**Title:** *What is Intelligence?* — subtitle to be chosen (see open questions), e.g.
*From Bits and Bytes to Truth and Proof*.

**What stays:** the tone (first person, slow yourself down, the Lego brick factory, the
astronaut, humour as the only way), the technical chapters almost verbatim (Information,
Language, Machine, Programming, Computing), the Life interludes, the Recommended Readings,
the exercises tied to the autograder, the glossary. Readers of the current book should
recognise every page they liked.

**What goes:** the 51 hand-drawn figures in `book/figures/`. Every figure is redrawn as an
SVG in the visual system of the talks and shared with the class decks (section 7). The book
gains figures it never had — the axis, the diagonal, the three regions of plausible, provable
and true, the gate — and the technical ones (scanner FSM, call frame, page table, the two
operating-system designs) are drawn once for both media.

**What moves:** the end of the current Computing chapter (Turing machines, universality,
halting, diagonalization, recursive and r.e. sets, cardinality, Gödel numbering, Cantor) moves
*forward* to become the heart of a new chapter. The current book "goes back in time to the
1930s and 1870s at the very end"; the new one starts there and keeps returning.

**What is new:** three chapters (Meaning, Cost, Machines), a rewritten Introduction that
states the question and the short answer up front, and a closing chapter that answers it.
The two-column *forbids / opens* reading of each limit becomes a recurring device, as does the
colour code of the talks (ochre for notation, cyan for meaning, rose for contradiction) in
every figure.

### Proposed table of contents

```
Introduction — the question, the short answer, the axis small → vast → countable → uncountable, how to read this book

Part I   FINITE
  1  Selfie          (kept) the specimen, three commands, take a selfie
  2  Size            (Information, reorganised) bits, numbers, negative numbers, overflows, characters,
                     bytes, memory, text, files, images, video, audio, code, apps — plus orders of
                     magnitude, prefixes, kilo vs kibi, state spaces, why testing shows presence only
                     Life 1: enumerating states, evolution as enumeration and selection (kept)

Part II  COUNTABLE
  3  Notation        (Language, extended) C*, RISC-U, EBNF, regular expressions; everything you can write
                     down is countable; a binary is a number (Gödel numbering as encoding); one notation,
                     many meanings
  4  Machine         (kept) model, processor, memory, I/O, instructions, emulation, performance —
                     plus the universal machine: mipster as one page of C per instruction group that
                     runs every program for that machine, itself included
                     Life 2 (kept)

Part III UNCOUNTABLE
  5  Meaning         (new; absorbs the end of Computing) pairing, the diagonal on subsets, on decimals, on
                     behaviours; meanings outnumber notations; truths with no proof; Gödel I and II with
                     trusting trust as their engineering reading; the halting problem; universality as the
                     same move run forwards; Rice; the six-theorem pattern; law's penumbra as the field
                     interlude
  6  Programming     (kept) literals, variables, expressions, statements, assignments, loops, conditionals,
                     procedures, libraries — reframed: a parse is a proof that a string is in the language;
                     code generation constructs semantics; self-compilation as fixed point; what the fixed
                     point proves and what Thompson says it cannot; every optimiser is an approximation
                     Life 3 (kept)
  7  Computing       (kept) virtual machines, virtual memory, time-sharing, self-reference, concurrency,
                     runtime systems — reframed: OS by emulation ≡ OS by virtualization; the bootstrap
                     problem as Gödel II; the timer interrupt as the engineering answer to halting;
                     conservative garbage collection as Rice-forced approximation (reachability for liveness)

Part IV  COST
  8  Cost            (new) decidable is not doable; P, NP, NP-complete, Cook–Levin, Karp; why SAT is hard
                     (2^n, phase transition) and why solvers work (structure); DPLL, CDCL — unit propagation,
                     watched literals, clause learning, restarts — with babysat as the starting point; SMT:
                     bitvectors by bit-blasting (Cook–Levin made concrete), arrays; rotor: machine code in,
                     formula out; bounded model checking with bitme; the bound is the approximation Rice
                     forces; Landauer: every step that forgets costs energy; metrics and Goodhart

Part V   MACHINES
  9  Machines        (new) an LLM as a mechanism: tokens, a distribution over the next one, a sample, the
                     loop; training as compression of notation; a hallucination is a proof-shaped object that
                     is not true; grounding; world models: predict the world, not the text, and inherit every
                     limit anyway; the loops are closed (models judging models); generation got cheap,
                     verification did not

Part VI  INTELLIGENCE
 10  Intelligence    (new; replaces Life 4 as the ending) the definition; not about computers, not
                     finishable; depth; six habits; selfie read against the definition; Goethe
                     Life 4 (rewritten)

Glossary (extended)
```

Chapters 2–4 and 6–7 are edits of existing text, not rewrites: new opening and closing
sections per chapter that place it on the axis, callouts at the places where a station lands
(marked `> Station III: Rice` in the source so they are easy to find and to lift into slides),
and the removed material relocated. Chapters 5, 8, 9, 10 and the Introduction are new prose in
the existing voice, drawing on the talks' speaker notes, which are already written in it.

## 4. The three classes

Geometry: 14 teaching weeks; "2 hours" is 2 × 45 min = one 90-minute session per week (ICS,
SE), "3 hours" is one 135-minute session (CC). Language: English.

### ICS — Introduction to Computer Science (1st semester, 14 × 90 min)

The whole book at the level of the talk, with selfie run live in every session. Week 1 *is*
the intelligence talk (56 min) plus the course; weeks 2–13 earn it; week 14 answers it.

| Wk | Station | Lecture | Live in the terminal |
|---|---|---|---|
| 1 | — | What is Intelligence? The talk, then what this class is | `./selfie` |
| 2 | I | Size: bits, orders of magnitude, state spaces, testing shows presence | `-c selfie.c`, the state count |
| 3 | I | Everything is bits: numbers, two's complement, overflow, ASCII/UTF-8, kilo vs kibi | `examples/` |
| 4 | II | Notation: formal languages, EBNF, regular expressions, C\* and RISC-U side by side | `-s` |
| 5 | II | Countability: a binary is a number; Gödel numbering; self-compilation gets the same number twice | `make self-self-check` |
| 6 | II | The machine: von Neumann, code = data, RISC-U, mipster as the universal machine, self-execution | `make emu`, `-d` |
| 7 | III | Uncountability: pairing, the diagonal twice, meanings outnumber notations, truths without proof | — |
| 8 | III | Self-reference I: a compiler defines its own language; the fixed point; trusting trust; Gödel I & II | `make self` |
| 9 | III | Self-reference II: halting; universality; Rice; what starc decides and what it cannot | `-d` on a loop |
| 10 | III | Systems: OS by emulation ≡ OS by virtualization; self-hosting; the bootstrap problem | `make emu-emu`, `make os-emu` |
| 11 | IV | Cost: P vs NP; SAT; hard to find, easy to check; a SAT solver in 400 lines; Landauer | `make sat` on `rivest.cnf` |
| 12 | IV | Formal methods: machine code in, formula out; rotor and bitme on an example that divides by zero | `make rotor`, `bitme` |
| 13 | V | Machines: what an LLM is; hallucination; world models; the verification gate | a prompt, and a compiler |
| 14 | VI | What is intelligence? The definition, depth, what to study; exam | — |

ICS has no formal assignments. What it has is a recommended exercise list per week: reading in
the book, the terminal commands of the session to rerun at home, paper exercises, and
`print-your-name` as the one thing to try on the autograder. No C\* programming beyond editing
selfie. The list lives in `assignments/introductory-assignments.md`, which is replaced
entirely: the current file is student-written and sketchy, and none of it is reused. The new
file follows the form of the compiler and systems assignment files (the shared-information
header, then one section per week) and is mirrored by the book's per-chapter exercises.

### CC — Compiler Construction (4th semester, 14 × 135 min)

Refines station III from the compiler side and does station IV in full. The claim of the
class: a compiler is a proof system for syntax and a constructor of semantics, and every
semantic question it appears to answer is a chosen approximation.

| Wk | Station | Lecture | Assignment |
|---|---|---|---|
| 1 | spine | What is Selfie? (27 min) then the spine in an hour: the axis, the three theorems, the definition | `print-your-name` |
| 2 | I, II | Regular languages, FSMs, the scanner: a finite machine decides a countable set; literals | `hex-literal` |
| 3 | II | Context-free grammars, EBNF, LL(1), recursive descent: a parse is a proof; Chomsky's hierarchy as sizes of notation | |
| 4 | III | Symbol table, types, casting: type checking is proof checking (decidable); what is semantic is not (Rice) | `bitwise-shift-compilation` |
| 5 | II | Code generation for expressions, register allocation; encoding instructions is Gödel numbering made mechanical; ELF | `bitwise-shift-execution` |
| 6 | III | Statements: assignments, loops, conditionals; while + assignment is universal | `bitwise-and-or-not`, `logical-and-or-not` |
| 7 | III | Procedures, calling convention, stack frames, recursion; where the halting problem lives in a compiler | `for-loop`, `lazy-evaluation` |
| 8 | III | Self-compilation: the fixed point, bootstrapping, trusting trust, diverse double-compiling; what the fixed point proves | `array-access` |
| 9 | III | Optimisation and Rice: constant folding, dead code, register allocation as graph colouring (NP-hard); sound vs complete | `array-allocation` |
| 10 | IV | Semantics as a formula: rotor's bit-precise model of RISC-V; BTOR2; a compiler run backwards into logic | `array-multidimensional` |
| 11 | IV | SAT: NP-completeness, Cook–Levin via circuits, why SAT is hard, DPLL, CDCL on one worked example, babysat as the executable specification | `struct-declaration` |
| 12 | IV | SMT: bitvectors by bit-blasting, arrays; bounded model checking with bitme; a satisfying assignment is a failing input; what a bound buys | `struct-execution`, `rotor-check` |
| 13 | V | What an LLM is; a generated program is notation; the compiler, the test and the model checker as the gate; generation got cheap, verification did not | |
| 14 | VI | What a compiler is; the definition; the field | |

Assignments keep the existing twelve autograded compiler assignments unchanged. One new one
is added for station IV: `rotor-check` — generate a rotor model for a test program that
exercises your language extension (say, the `for` loop or array access) and check it with
bitme against a stated property; the grader runs rotor and bitme on the submitted program and
compares the verdict and the bound. DPLL and CDCL are taught, not implemented: babysat stays
the brute-force reference and the algorithms are shown on one worked example.

### SE — Systems Engineering (5th semester, 14 × 90 min)

Refines station III from the systems side and applies station IV. The claim of the class:
isolation is the semantic problem of systems, virtualization buys performance by introducing
self-reference, and what a kernel cannot decide it bounds.

| Wk | Station | Lecture | Assignment |
|---|---|---|---|
| 1 | spine | What is Selfie? (27 min) then the spine in an hour, weighted to the third command | `print-your-name` |
| 2 | II | The machine again: privilege, exceptions, system calls; the assembler as a regular language | `assembler-parser` |
| 3 | III | Emulation: mipster as universal machine; interpretation and its price (×2,593); self-execution | `self-assembler` |
| 4 | III | Virtual memory: paging, page tables; virtual addresses as notation, physical as meaning; isolation | |
| 5 | IV | Time-sharing: context switching, the timer interrupt as the answer to halting (we do not decide, we bound); scheduling is NP-hard | `processes` |
| 6 | III | Self-hosting: hypster; OS by emulation ≡ OS by virtualization; the bootstrap problem as Gödel II; TCB, microkernels | `fork-wait` |
| 7 | III | Processes: fork, wait, exit; a process is a virtual machine; exit codes as the only semantics that crosses the boundary | `fork-wait-exit` |
| 8 | I | Concurrency: threads, locks, lr/sc; interleavings as state-space explosion; testing shows presence | `lock`, `threads` |
| 9 | III | Runtime systems: malloc, garbage collection; liveness is undecidable, reachability is the approximation; conservative GC | `threadsafe-malloc` |
| 10 | IV | Verifying systems code: rotor models with system calls, memory-safety properties, bounded model checking with bitme; what a bound buys | `treiber-stack`, `rotor-bounds` |
| 11 | IV | Cost: caches, performance, energy; Landauer; measure everything (Goodhart) | |
| 12 | III | Universality for systems: UTM, halting, Rice on schedulers, deadlock detection as approximation | |
| 13 | V | What an LLM is; agents as processes: sandboxing is virtualization; the loops are closed; the verification gate | |
| 14 | VI | What a system is; the definition; the field | |

Assignments keep the existing ten autograded systems assignments. One new one is proposed:
`rotor-bounds` (state a memory-safety property for a small systems routine — the assembler,
or `malloc` — generate its rotor model and find the input that violates it, or the bound up to
which none does). Rotor does not yet model concurrency, so the formal-methods assignment stays
sequential.

### Where each principled idea appears, by class

| Idea | ICS | CC | SE |
|---|---|---|---|
| Orders of magnitude, state spaces | wk 2 | the state space of generated code; testing a compiler | interleavings; caches |
| Countability, Gödel numbering | wk 5 | instruction encoding, ELF, a compiler as a function on numbers | a process image is a number; page tables map numbers to numbers |
| Cantor's diagonal | wk 7 | behaviours outnumber programs, hence semantic analysis approximates | behaviours of a scheduler over all inputs cannot be listed |
| Gödel I & II | wk 8 | the fixed point; trusting trust | the bootstrap problem; TCB |
| Halting, universality | wk 6, 9 | mipster as UTM; recursion; termination of the compiler | emulation as UTM; the timer interrupt |
| Rice | wk 9 | optimiser, type checker: syntax decidable, semantics not | GC liveness; deadlock; safety of a process |
| P vs NP, SAT | wk 11 | register allocation; bit-blasting as Cook–Levin | scheduling, packing |
| How solvers work | babysat, the idea of DPLL | DPLL, CDCL, SMT in full | as a user, with bounds |
| rotor, bounded model checking | wk 12, demo | `rotor-check` on your own extension | `rotor-bounds` on systems code |
| Landauer, metrics | wk 11 | performance of generated code | caches, energy |
| LLMs, world models | wk 13 | generated code and the gate | agents, sandboxing |

## 5. The formal-methods track, at undergraduate level

What "formal methods" means here is exactly what the workshop around selfie already does, and
nothing that needs a proof assistant:

1. **Propositional logic and SAT** — CNF, DIMACS, satisfiability; babysat as the executable
   specification; DPLL as the first real algorithm; CDCL as what modern solvers do, taught on
   one worked example (unit propagation, a conflict, the learned clause, the backjump); why
   structured instances are easy and random ones near the threshold are not.
2. **SMT** — bitvectors as the theory of machine words, arrays as the theory of memory;
   bit-blasting as the reduction to SAT that is also the Cook–Levin construction; the solvers
   bitme drives (bitwuzla, z3) as black boxes with a stated interface.
3. **Models of machines** — rotor's BTOR2 model of RISC-V: state, init, next, bad; how a
   program becomes a formula in linear size; unrolling k steps; a satisfying assignment is a
   failing input; the bound is the approximation.
4. **Bounded model checking** — bitme; safety and finite liveness; what a "no" up to k means
   and does not mean; the connection back to Rice and to testing.

ICS sees 1 and 3 as demos and 2 and 4 as sentences. CC lectures all four, with 1 and 2 in
full, and has students do 3 and 4 in `rotor-check`. SE lectures 3 and 4, recaps 1 and 2, and
has students do 3 and 4 in `rotor-bounds`. Nobody implements a solver; the solvers are the
black boxes with a stated interface, and babysat is there so the box is not opaque.

## 6. The AI track, in limited form

Three slides' worth per class, never a verdict, always an instance of a theorem from the spine:

- **What an LLM is** — the mechanism of the talk's slide 53: tokens in, a distribution over
  the next one, a sample, the loop; training as compression of notation; the parameter count
  as station I (cannot be inspected, only sampled).
- **Hallucination** — plausible, provable, true as three regions; a proof-shaped object that
  is not true; grounding; the verification gate as the engineering answer.
- **World models** — predict the world, not the text; the efficiency argument; and still a
  finite notation inside the world it models, so every limit of the spine applies unchanged.
- **The loops are closed** — models training, judging and writing models; Rice and Gödel II
  say what no such loop can establish about itself.

CC adds generated code as notation that meets the compiler, the test and the model checker.
SE adds agents as processes and sandboxing as virtualization.

## 7. The slides

Decided: the deck engine of the three talks, one HTML file per lecture, so the classes and the
talks are recognisably one course of argument — same colour code, speaker notes on every
slide, the clock, the print layout and the PDF sync. Concretely:

- One HTML file per lecture, under `docs/classes/{ics,cc,se}/NN-<slug>/index.html`, published by
  Pages like the talks; a class index page per directory.
- The engine (CSS, JS, figures, the terminal component) factored out of the talks into a
  shared `docs/classes/deck/` loaded by relative path — still no build step, no network, no
  dependencies, but not one-file-per-deck any more, which at 42 decks is the right trade.
- **Figures as SVG, shared.** Every figure is one SVG file under `docs/figures/`, drawn in the
  talks' visual system, with CSS variables for the light and dark themes. Decks inline them,
  the book references them, and the PDF and KDP builds consume them directly. The 34 canvas
  figures of the three talks are ported to SVG once (the talks themselves stay as they are);
  the book's technical figures are drawn new in the same system rather than taken from
  `book/figures/`, which is retired when the new book lands. `docs/` is the directory Pages
  publishes, which is why the figures live there rather than under `book/`.
- Per-slide minute budgets adding up to the session length, as in the talks, so a lecture can
  be cut live.
- The existing three talks unchanged apart from one sentence on their framing slide stating
  the purpose (see § 1), with their PDFs rebuilt; ICS week 1 and CC/SE week 1 simply play them.

The current classroom Keynote slides on iCloud are superseded; the `/slides/` redirect moves
to the class index.

## 8. Reuse ledger

| Existing | Feeds |
|---|---|
| What is Intelligence? (69 slides, notes) | Book ch. 5, 8, 9, 10, Introduction; ICS week 1 verbatim, weeks 2, 7–9, 11, 13 |
| What is Computer Science? (35) | ICS weeks 2, 5, 8–9; book ch. 5 and 10 (the definition, the specimen) |
| What is Selfie? (29) | CC and SE week 1 verbatim; SE weeks 3, 6; book ch. 7 (emulation ≡ virtualization) |
| Book: Information, Language, Machine, Programming, Computing | Book ch. 2–4, 6–7 with edits; all technical CC and SE lectures |
| Book: Universality of Computing | Book ch. 5 (moved forward) |
| Book: `figures/` | Not reused; every figure is redrawn as shared SVG |
| `introductory-assignments.md` | Not reused; replaced entirely by a generated file in the form of the other two |
| Compiler and systems assignments, grader | CC and SE unchanged, plus `rotor-check` and `rotor-bounds` |
| babysat, rotor, bitme, `examples/sat`, `examples/symbolic` | Station IV in every class |

## 9. Deliberately left out

- monster and beator: named once in the book's extras, not taught.
- Hoare logic, separation logic, proof assistants: beyond undergraduate scope here; bounded
  model checking is the formal method.
- Full complexity theory: P, NP, NP-completeness, reductions and Cook–Levin, nothing beyond.
- Transformer internals beyond the mechanism: attention is named, not derived; no training
  code.
- A solver-implementation assignment (DPLL on babysat), translation validation of starc
  against gcc, and reading emulators and rotor models as world models: considered and left
  out to keep station IV to one hands-on idea per class.
- The video pipeline and the theses: unchanged.

## 10. Decisions taken

- Slides: HTML decks, one per lecture, on the talks' engine factored into a shared directory.
- Book: replaces `book/README.md` in place; the current edition stays on the
  `elementary-computer-science` branch and in its published output.
- Figures: all new, SVG, shared between book and decks; none of `book/figures/` reused.
- Theory: one Meaning chapter before the compiler and systems chapters.
- Hands-on formal methods: `rotor-check` (CC) and `rotor-bounds` (SE) only; solvers are
  taught, not implemented.
- Geometry: 14 weeks; ICS and SE 90 minutes, CC 135 minutes.
- Assignments in scope: the ICS recommended exercise list and the two rotor assignments;
  ICS formally has no assignments; existing CC and SE assignments unchanged.
- ICS hands-on: terminal demos and editing selfie; no C\* programming.

## 11. Still open

- The subtitle. Candidates: *From Bits and Bytes to Truth and Proof*; *Elementary Computer
  Science from Finite Bits to Infinite Meaning*; *Notation, Meaning, and the Gap Between*.
  The book currently carries no subtitle.
- The bitme demonstration in ICS 12, CC 12 and SE 10, and the Cost chapter: verified with
  `--use-bitwuzla` on 2026-09-11 (division by zero at step 76 with input '0', again at step
  89 with '2', the flagged exit(0) at step 106 with byte 12); Z3 and the BVDD engine were
  killed on the division step after minutes. The decks quote these steps and say they move
  with the tool versions; recheck before class.
- The two rotor grader targets run bitme with a 600-second timeout and a solver the grader
  machine has to provide; the bitme check is not mandatory so that the rest of the grade
  computes without one. Whether rotor needs a stable exit code or a property flag beyond
  what `-analyzor` prints remains to be seen after the first semester of submissions.
- The exam for ICS: the question bank follows the new weeks; not part of this effort.
- The `/slides/` redirect now points at the class index; the old Keynote slides are no longer
  linked from anywhere.

## 13. Status

Everything in the build order is done on the `intelligence` branch: framing, engine and
figures, the book's new and edited chapters, the ICS, CC and SE decks with PDFs and index
pages, the class landing page, the three assignment files with `rotor-check` and
`rotor-bounds` and their grader targets, the PDF workflow extended to the class decks, the
README's Support section, and the redirect. What remains is what section 11 lists, and a read
of everything by its author.

## 12. Build order

Proposed sequence, so that every step produces something usable on its own:

0. **Framing.** The purpose sentence on the framing slide of each talk, PDFs rebuilt; this
   plan updated. Done first because everything downstream quotes it.
1. **Engine and figures.** Factor the deck engine out of the talks into `docs/classes/deck/`;
   set up `docs/figures/` and port the talks' figures to SVG; write the figure inventory for
   the book and the decks (one list, both consumers).
2. **The book's new chapters** in the order Meaning, Cost, Machines, Intelligence, then the
   Introduction — the new prose, written first because the decks quote it.
3. **The book's edited chapters**: openings, closings, station callouts, relocations.
4. **ICS decks**, weeks 1–14, since they are the book at talk resolution and test the figure
   set end to end.
5. **CC decks**, then **SE decks**, reusing the ICS decks where the material is identical and
   deepening where it is not.
6. **Assignments**: the ICS exercise list, `rotor-check`, `rotor-bounds`, grader targets.
7. **Publishing**: class index pages, the PDF workflow extended to the class decks, the
   README's Support section, the redirects.
