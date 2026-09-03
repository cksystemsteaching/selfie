# What is Selfie?

A short animated lecture introducing the [selfie](https://github.com/cksystemsteaching/selfie) system
to students deciding whether to take a compiler or an operating systems class. Self-contained: one
HTML file, no build step, no network access, no dependencies. It plans out at just over **27
minutes** — and it is not pinned to that: the clock counts down whatever the per-slide budget adds
up to, so slides can be added or cut without anything else needing to be rebalanced. For a shorter
slot, see the cut list below.

By Christoph Kirsch — University of Salzburg, Austria, and Czech Technical University in Prague,
Czechia. It is the companion to [What is Intelligence?](../what-is-intelligence/), shares its visual
system deliberately, and hands the same distinction — **proof versus truth**, **syntax versus
semantics** — to an audience that is going to go and build the machinery. The third deck of the set,
[Why Computer Science?](../why-computer-science/), is the intelligence argument shortened for students
deciding what to study, with selfie in the middle of it.

**Give or watch the talk:** <https://selfie.cs.uni-salzburg.at/talk/> — or open `index.html` in any
modern browser. Either way, press <kbd>→</kbd> to begin.

**Watch it instead:** <https://youtu.be/aWT2jLb1MVA> — a 13-minute narrated cut of fourteen of
these slides, in the author's voice. It is built *from this deck*, driven through these build steps
in headless Chrome, so it shows what a projector shows; the recipe is in [video/](../../../video/).

**Read it offline:**
[what-is-selfie.pdf](https://selfie.cs.uni-salzburg.at/presentations/what-is-selfie/what-is-selfie.pdf)
— one page per slide, every build step shown, every figure drawn, in the light theme. It is a
rendering of `index.html` and nothing else: `index.html?print` lays the deck out as pages in any
browser, `./make-pdf.sh` drives headless Chrome over that, and a workflow reruns it whenever the
deck changes on `main`, so the two cannot drift. `THEME=dark ./make-pdf.sh` gives the projector
version. The PDF has no speaker notes — those are in the deck, on <kbd>n</kbd>.

Sync is tracked against the source, not the output: each build records the hash of `index.html` in
`what-is-selfie.pdf.sha`, and `./make-pdf.sh --check` compares it. Chrome does not render
deterministically and a Linux runner resolves the font stack differently from a Mac, so comparing
PDF bytes would report a change on every run and commit noise forever. The hash answers the only
question that matters: was this PDF built from the deck as it stands?

This directory lives under `docs/`, which is what GitHub Pages publishes, so the deck is served as a
live page rather than as source. A raw GitHub link will not work: raw files are sent as `text/plain`
and the browser shows the markup.

## The argument

Three commands open the talk and the rest of it is their explanation:

```bash
$ ./selfie -c selfie.c -o selfie1.m -m 2 -c selfie.c -o selfie2.m   # self-compilation
$ ./selfie -c selfie.c -o selfie.m -m 2 -l selfie.m -m 1            # self-execution
$ ./selfie -c selfie.c -o selfie.m -m 3 -l selfie.m -y 2 -l selfie.m -y 1   # self-hosting
```

Understand the first and you understand compilers; the second, machines; the third, operating
systems. The three are genuinely different loops and the talk keeps them apart: self-compilation is
about **meaning**, self-execution about **machines**, self-hosting about **isolation** — and only
the third is hard to implement.

The centre of the talk is Part III, and it is one distinction:

> **An OS by emulation is semantically equivalent to an OS by virtualization.** Virtualization is
> needed only for performance, and it buys that performance by introducing self-reference.

An operating system built by emulation interprets its guest: guest code is data being read, so
isolation is free and there is no self-reference anywhere. An operating system built by
virtualization context-switches its guest onto the same processor the kernel runs on — so the kernel
must be isolated from the things whose isolation it provides, which means running in a virtual
machine, which raises the question of who manages *that* one. That is the bootstrapping problem,
the trusted computing base, and the whole microkernel programme. It is also, in the author's
experience, the single thing whose absence stops students from ever understanding what a kernel is:
they are shown only the virtualized design, with the self-reference tangled into paging and
scheduling and never named.

Selfie can demonstrate the equivalence rather than assert it: `make emu-emu` and `make os-emu` host
the same guest two different ways, and the guest executes exactly the same 86,380 instructions in
both. Selfie even ships `mixter`, which switches a running machine between the two mechanisms
mid-execution.

Part IV connects this to the companion lecture. A compiler is a semantic function you can read and
run, Rice's theorem says every non-trivial question about behaviour is undecidable, and every tool
in the selfie workshop — monster, beator, rotor, bitme, buzzr — is therefore a deliberate
approximation with a stated bound. Part V answers "why learn this when a machine writes the code":
generation got cheap, verification did not, the stack did not disappear, and depth is not
downloadable.

## Structure

| Part | Title | Slides | Plan |
|---|---|---|---|
| 0 | Prologue — three commands, and why the loop is the subject | 1–3 | 3:09 |
| I | The System — one file, C\*, RISC-U, the whole pipeline | 4–8 | 4:09 |
| II | The Three Selves — compiling, executing and hosting yourself | 9–14 | 5:45 |
| III | Operating Systems — emulation, virtualization, and the price | 15–21 | 6:42 |
| IV | Proof and Truth — Rice, and the tools built on selfie | 22–25 | 3:36 |
| V | Yours — the assignments, the AI question, the invitation | 26–29 | 3:54 |

29 slides; the per-slide budget in `data-mins` adds up to **27:15**, and that is what the clock
counts down — it is read off the deck at load, not written into it. Press <kbd>t</kbd> to start the
clock; it turns amber if you are a minute behind the plan and rose if you are three behind.

**Running short?** These four are self-contained and can be dropped without breaking the argument,
buying 4:18: slide 8 (the compiler pipeline), 12 (trusting trust), 25 (the rest of the workshop),
and 27 (the assignments). That lands it at 22:57; also cutting 6 (C\*) and 7 (RISC-U) gets it under
21 minutes for a conference slot. Do not cut 2, 11, 13, 14, 17–21 or 28 — they carry the argument.

**Which slide is the talk?** If you only get five minutes, give 17, 18 and 20: two designs for one
operating system, the evidence that they are equivalent, and the self-reference that is the entire
difference between them.

## Keys

| | |
|---|---|
| <kbd>→</kbd> <kbd>space</kbd> | next build step, then next slide |
| <kbd>←</kbd> | back |
| <kbd>↓</kbd> <kbd>↑</kbd> | next / previous slide, skipping build steps |
| <kbd>home</kbd> <kbd>end</kbd> | first / last slide |
| <kbd>n</kbd> | speaker notes (every slide has them) |
| <kbd>t</kbd> / <kbd>r</kbd> | start-pause / reset the clock |
| <kbd>d</kbd> | light / dark |
| <kbd>?</kbd> | key list |

Clicking the right 78% of the slide advances, the left 22% goes back — usable from a tablet or a
phone with no keyboard.

## The numbers, and where they come from

Every figure quoted on a slide is selfie reporting on selfie, measured on a Mac against the `main`
branch — so it can be defended from the floor, and re-measured in front of the room if somebody
doubts it. Rerun any of these and update the deck if they move.

- **The source.** `./selfie -c selfie.c` — 365,784 characters in 12,394 lines and 1,741 comments;
  491 global variables, 661 procedures, 512 string literals; 188,392 bytes generated with 43,492
  instructions and 14,424 bytes of data. The line count is selfie's own; `wc -l` says 12,393
  because it counts newlines rather than lines.
- **The fixed point.** `make self-self-check` — self-compiles, then runs the result to compile
  again, then `diff`s both the binaries and the assembly. 1,228,259,585 instructions in total.
- **Bare metal.** `make emu` — 85,754 instructions for selfie to print its usage line.
- **OS by emulation.** `make emu-emu` — 222,410,917 instructions on the physical machine, ×2,593.
  The guest itself executes 86,380.
- **OS by virtualization.** `make os-emu` — 17,860,937 instructions, ×208, so ×12.5 cheaper than
  emulation. The guest itself executes **86,380** — the same number, which is the evidence for the
  equivalence claim on slide 18.
- **A VMM underneath as well.** `make os-vmm-emu` — 59,492,501 instructions, ×694.
- **Overhead on real work.** `make self-emu` self-compiles bare metal in 1,228,242,683 instructions;
  `make self-os-emu` does the same on a virtualized OS in 2,112,219,497, of which the guest is
  1,228,262,089 — an overhead of **×1.72**, down from ×208 on the usage-line workload. That collapse
  is the whole economic argument for virtualization, and it is why slide 19 insists the ratio in the
  bar chart understates the real case.
- **The language.** 7 keywords, 22 symbols, LL(1) — from
  [grammar.md](../../../grammar.md).
- **The machine.** 14 instructions, 32 registers, 4GB of byte-addressed memory — from
  [riscu.md](../../../riscu.md).

External sources named on slides: Thompson, *Reflections on Trusting Trust*, Turing Award lecture
1984; Wheeler on diverse double-compiling, 2005; Rice 1953. The tools in Part IV are the ones listed
under **Extras** in the [repository README](../../../README.md), and the assignments in Part V are
the ones the [autograder](../../../grader/README.md) supports.

## Design notes

The visual system is the intelligence deck's, on purpose: the two talks are meant to be recognisably
one course of argument. Deep ink-navy ground with a fine plotter grid, and two accents that carry
the argument rather than decorate it — **ochre for syntax** (text, code, notation, the thing you can
check) and **drafting cyan for semantics** (what the machine actually does, the thing you cannot),
with madder rose reserved for the moment a contradiction lands. An old-style serif for meaning,
monospace for notation. Slide 10 teaches the code explicitly, and from there the colours do the work
wherever the distinction matters.

The one component this deck adds is a **terminal**: prompt in ochre, what you type in ink, what came
back in muted grey. It is there because every claim in this talk is a command the audience can run,
and showing the command is more persuasive than describing it.

Both themes are designed; the viewer's system preference or the <kbd>d</kbd> key selects one.
Everything is sized from a single unit (`--u` = deck width ⁄ 100) so the 16:9 stage scales to any
projector, and all nine figures are drawn on canvas at whatever size they are given. Animation is
suppressed under `prefers-reduced-motion`, where every build step shows at once.

Two guards keep text off text on machines whose font stacks resolve differently from the author's.
At load, `autofit()` measures each slide and, for any whose content would run past its bottom
padding onto the progress bar, scales that slide's unit down until it fits — a pure scale, so
nothing re-wraps. On canvas, every label is drawn with bounds it may not leave: too wide a string is
shrunk and nudged rather than allowed to run off the figure or onto its caption.
