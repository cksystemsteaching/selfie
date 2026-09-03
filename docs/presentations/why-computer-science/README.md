# Why Computer Science?

A short animated lecture for students deciding what to study — and for anyone who has asked, out
loud or not, why they should learn computer science when a machine will write the code. It is the
shorter, computer-science-focused sibling of [What is Intelligence?](../what-is-intelligence/), and it
puts the [selfie](https://github.com/cksystemsteaching/selfie) system in the middle of the argument.
Self-contained: one HTML file, no build step, no network access, no dependencies. It plans out at
just under **28 minutes** — and it is not pinned to that: the clock counts down whatever the
per-slide budget adds up to, so slides can be added or cut without anything else needing to be
rebalanced. For a shorter slot, see the cut list below.

By Christoph Kirsch — University of Salzburg, Austria, and Czech Technical University in Prague,
Czechia. It shares its visual system with the two companion decks deliberately, and hands over the
same distinction — **proof versus truth**, **syntax versus semantics** — to an audience that is about
to decide whether to build the machinery.

**Give or watch the talk:** <https://selfie.cs.uni-salzburg.at/why/> — or open `index.html` in any
modern browser. Either way, press <kbd>→</kbd> to begin.

**Read it offline:**
[why-computer-science.pdf](https://selfie.cs.uni-salzburg.at/presentations/why-computer-science/why-computer-science.pdf)
— one page per slide, every build step shown, every figure drawn, in the light theme. It is a
rendering of `index.html` and nothing else: `index.html?print` lays the deck out as pages in any
browser, `./make-pdf.sh` drives headless Chrome over that, and a workflow reruns it whenever the
deck changes on `main`, so the two cannot drift. `THEME=dark ./make-pdf.sh` gives the projector
version. The PDF has no speaker notes — those are in the deck, on <kbd>n</kbd>.

Sync is tracked against the source, not the output: each build records the hash of `index.html` in
`why-computer-science.pdf.sha`, and `./make-pdf.sh --check` compares it. Chrome does not render
deterministically and a Linux runner resolves the font stack differently from a Mac, so comparing
PDF bytes would report a change on every run and commit noise forever. The hash answers the only
question that matters: was this PDF built from the deck as it stands?

This directory lives under `docs/`, which is what GitHub Pages publishes, so the deck is served as a
live page rather than as source. A raw GitHub link will not work: raw files are sent as `text/plain`
and the browser shows the markup.

## The argument

The talk states its claim on slide 2 and spends the rest of the half hour earning it:

> Only knowing and understanding a nontrivial domain — its languages and their semantics — enables
> efficient and effective use of generative AI, and of whatever follows it. Modern AI does not make
> computer science optional. It motivates studying it **more** than before.

The derivation keeps the spine of the intelligence lecture and drops everything that was there for
other fields. **Size** (Part I): a bit doubles, 34 bytes beat the universe, and selfie — a system a
student can read completely in one semester — runs on a machine with 2<sup>34,359,738,368</sup>
states, so testing shows presence, not absence. **Infinity** (Part II): everything you can write down
is countable, the diagonal argument run once in full on behaviours, and the result everything hangs
on: incomparably more meanings than notations, so almost every truth has no proof. **Self-reference**
(Part III): a compiler defines the meaning of the language it is written in, selfie's three commands
as Gödelisierung you can run, both Gödel theorems on one slide with Thompson's *trusting trust* as
their engineering reading, the halting problem, universality as the same move run forwards with
mipster as a page-per-instruction-group universal machine, Rice, and the six-theorem pattern.
**Cost** (Part IV): decidable is not doable, monster and rotor as the place a student meets
NP-completeness on a laptop, hard-to-find versus easy-to-check, and Landauer. **Machines** (Part V):
what an LLM mechanically is, a hallucination as a proof-shaped object that is not true, and
generation got cheap while verification did not.

Part VI draws the consequence. Slide 30 is the claim, earned, with the deck's one new figure: the
loop everyone already runs — an English prompt, a generator, a plausible answer — and the two things
that can happen to the answer next. Without a domain it is accepted on faith. With one it meets a
semantics you own — a compiler, a test, a proof, a measurement — and is kept or sent back. That gate
is the only part of the loop the machine does not supply, and it is precisely what a discipline
teaches. *Effective* use needs the semantics (Parts II, III, V); *efficient* use needs the domain's
languages and their limits (Part IV); both live in one place. Slide 31 answers why computer science
in particular: every field uses languages, but this is the field whose subject is what languages can
and cannot do — a compiler is a semantics you can read and run, the theorems are the user manual for
every generator that will ever exist, and the stack the generator runs on did not disappear. Slide 32
is what a student actually does with selfie, and its one rule — whatever you change, selfie must
still compile itself — is the talk's argument turned into a grading policy: a machine may draft the
code, the fixed point decides whether the draft was true. Slide 33 states the intelligence lecture's
definition so the room can see the half hour was one instance of it, and the close hands the argument
over: notation is finite, meaning is not, someone has to mean it.

## Structure

| Part | Title | Slides | Plan |
|---|---|---|---|
| 0 | Prologue — disclosure, the question asked honestly, the claim up front | 1–3 | 2:27 |
| I | Size — the map, one bit, selfie on a machine nobody can inspect, testing | 4–8 | 3:48 |
| II | Infinity — countable notation, the diagonal, meaning outnumbers notation | 9–12 | 3:03 |
| III | Self-Reference — compilers, the three commands, Gödel, halting, universality, Rice | 13–20 | 6:54 |
| IV | Cost — 2<sup>100</sup>, NP, Landauer | 21–24 | 2:45 |
| V | Machines — what an LLM is, hallucination, verification did not get cheap | 25–28 | 2:39 |
| VI | Why Computer Science — the claim earned, why this field, selfie, the frontier, the invitation | 29–35 | 6:15 |

35 slides; the per-slide budget in `data-mins` adds up to **27:51**, and that is what the clock
counts down — it is read off the deck at load, not written into it. Press <kbd>t</kbd> to start the
clock; it turns amber if you are a minute behind the plan and rose if you are three behind.

**Running short?** These four are self-contained and can be dropped without breaking the argument,
buying 2:55: slide 20 (the six-theorem pattern), 24 (Landauer), 26 (the LLM mechanism, if the room
already knows it), and 34 (the close with the two outcomes). Do not cut 2, 11, 12, 15, 16, 23, 30 or
31 — they carry the claim.

**Which slide is the talk?** If you only get five minutes, give 23, 30 and 31: hard to find and easy
to check, the gate that only a domain supplies, and why this domain.

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

Every figure quoted on a slide, so it can be defended from the floor:

- **266 bits > the observable universe.** 2²⁶⁶ ≈ 1.19 × 10⁸⁰; ordinary-matter atom count ≈ 10⁸⁰.
- **Selfie's source.** `./selfie -c selfie.c` — 365,784 characters in 12,394 lines and 1,741
  comments; 491 global variables, 661 procedures, 512 string literals; 188,392 bytes generated with
  43,492 instructions. Selfie reporting on selfie, measured against `main`; rerun it and update the
  deck if the numbers move.
- **Selfie's machine.** RISC-U has 4 GB of byte-addressed memory, and memory is base two: 4 GiB =
  2³⁵ = 34,359,738,368 bits, so 2^34,359,738,368 states — a decimal number with 10,343,311,892
  digits (× log₁₀2). At 3,000 digits a page that is 3.45 M pages, ~6,900 books of 500 pages.
- **Testing coverage.** 10⁹ states/second × 13.8 Gyr ≈ 4.4 × 10²⁶ ≈ 2⁸⁸ states examined.
- **SAT.** 2¹⁰⁰ ≈ 1.3 × 10³⁰; at 10⁹ checks/second, ~4 × 10¹³ years.
- **Landauer limit.** kT ln 2 ≈ 2.87 × 10⁻²¹ J at 300 K. Brute-forcing 2²⁶⁶ erasures ≈ 3.4 × 10⁵⁹ J;
  the Sun's whole-lifetime output ≈ 1.2 × 10⁴⁴ J, hence the ~10¹⁵ multiplier. Human brain ≈ 20 W.
- **The machine.** 14 instructions, 32 registers, 4GB of byte-addressed memory — from
  [riscu.md](../../../riscu.md).

Sources cited on the slides: Cantor 1891, Russell 1901, Gödel 1931, Tarski 1936, Turing 1936, Rice
1953, Landauer 1961, Cook 1971, Karp 1972, Levin 1973; Dijkstra 1969; Thompson, *Reflections on
Trusting Trust*, Turing Award lecture 1984; Wheeler on diverse double-compiling, 2005. The tools
named in Parts IV and VI are the ones listed under **Extras** in the
[repository README](../../../README.md), and the assignments in Part VI are the ones the
[autograder](../../../grader/README.md) supports.

## Design notes

The visual system is the intelligence deck's, on purpose: the three talks are meant to be
recognisably one course of argument. Deep ink-navy ground with a fine plotter grid, and two accents
that carry the argument rather than decorate it — **ochre for syntax** (finite, countable, notation,
proof) and **drafting cyan for semantics** (infinite, uncountable, meaning, truth), with madder rose
reserved for the moment a contradiction lands, or an answer is accepted on faith. An old-style serif
for meaning, monospace for notation. Slide 1 teaches the code in the two colours themselves, slide 14
restates it in the room's own terms, and from there the colours do the work wherever the distinction
matters.

Sixteen of the seventeen figures are the companion decks' figures, reused unchanged so that a
student who has seen either of the other talks recognises the argument. The one figure this deck adds
is the **gate** on slide 30: prompt, generator, answer, and then either faith or a semantics, drawn so
that the part the machine does not supply is the part in cyan. The **terminal** component is the
selfie deck's: prompt in ochre, what you type in ink, what came back in muted grey, because every
selfie claim in this talk is a command the audience can run.

Both themes are designed; the viewer's system preference or the <kbd>d</kbd> key selects one.
Everything is sized from a single unit (`--u` = deck width ⁄ 100) so the 16:9 stage scales to any
projector, and all figures are drawn on canvas at whatever size they are given. Animation is
suppressed under `prefers-reduced-motion`, where every build step shows at once.

Two guards keep text off text on machines whose font stacks resolve differently from the author's.
At load, `autofit()` measures each slide and, for any whose content would run past its bottom
padding onto the progress bar, scales that slide's unit down until it fits — a pure scale, so
nothing re-wraps. On canvas, every label is drawn with bounds it may not leave: too wide a string is
shrunk and nudged rather than allowed to run off the figure or onto its caption.
