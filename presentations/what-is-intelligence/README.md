# What is Intelligence?

A 45-minute animated lecture for undergraduate and graduate students **in any field**, built from
basic principles of computer science. Self-contained: one HTML file, no build step, no network access,
no dependencies.

Open `index.html` in any modern browser and press <kbd>→</kbd>.

## The argument

The talk turns on one distinction — **proof versus truth**, **syntax versus semantics**, **notation
versus meaning** — and on the self-reference that shows up whenever a language becomes expressive
enough to describe itself.

It answers its own title like this:

> Intelligence is developing new formal languages — or at least new properties in existing ones —
> which requires finding and understanding promising **unproven** truth. New languages and properties
> let us ask new questions about that truth, and then answer them in proofs. Forever.

Which splits into the two halves of a university education: *developing the skills to answer*
questions (undergraduate) and *learning to choose the questions* (graduate). And it is why studying a
field in depth remains the point, regardless of how good AI gets: depth is the organ you find
promising unproven truth with, and no theorem, tool, or model hands you that step.

Every apparently negative result in the deck is turned over and shown as a positive one — a limit
that opens unbounded room for innovation rather than closing it. Each of the five gets the same
two-column treatment: **what it forbids** / **what it opens**.

## Structure

| Part | Title | Slides | Plan |
|---|---|---|---|
| 0 | Prologue — disclosure, acknowledgement, the question, the short answer up front | 1–5 | 3:51 |
| I | Vastness — bits, exponential state spaces, why bugs are geometry | 6–12 | 5:15 |
| II | Infinity — countability, diagonalization, meaning outnumbers notation | 13–19 | 5:21 |
| III | Self-Reference — syntax/semantics, Gödelisierung, incompleteness, halting, Rice | 20–29 | 8:42 |
| IV | Cost — decidable ≠ doable, NP-completeness, Landauer's energy floor | 30–35 | 4:36 |
| V | Everywhere — biology, mind, and the notations that made every field | 36–39 | 3:03 |
| VI | Machines — what today's AI is, where world models take it, what neither escapes | 40–45 | 3:57 |
| VII | Practice — six habits, the definition, depth, humour, Goethe | 46–57 | 10:15 |

57 slides; the per-slide budget in `data-mins` sums to exactly **45:00**. Press <kbd>t</kbd> to start
the clock — it turns amber if you are a minute behind the plan and rose if you are three behind.

**Running long?** These four are self-contained and can be dropped without breaking the argument,
buying 3:06: slide 12 (Borges), 14 (pairing ℕ ↔ evens), 17 (Cantor's theorem in general form),
49 (bridges and aviation). Do not cut 16, 18, 24, 26, 50–52 — they carry the thesis.

## Keys

| | |
|---|---|
| <kbd>→</kbd> <kbd>space</kbd> | next build step, then next slide |
| <kbd>←</kbd> | back |
| <kbd>↓</kbd> <kbd>↑</kbd> | next / previous slide, skipping build steps |
| <kbd>home</kbd> <kbd>end</kbd> | first / last slide |
| <kbd>n</kbd> | speaker notes (every slide has them) |
| <kbd>t</kbd> / <kbd>r</kbd> | start-pause / reset the 45-minute clock |
| <kbd>d</kbd> | light / dark |
| <kbd>?</kbd> | key list |

Clicking the right 78% of the slide advances, the left 22% goes back — usable from a tablet or a
phone with no keyboard.

## The numbers, and where they come from

Every figure quoted on a slide, so it can be defended from the floor:

- **266 bits > the observable universe.** 2²⁶⁶ ≈ 1.19 × 10⁸⁰; ordinary-matter atom count ≈ 10⁸⁰.
  296 bits (37 bytes) passes the ~10⁸⁹ photon count.
- **8 GB of RAM.** 8 GiB = 68,719,476,736 bits, so 2^68,719,476,736 states — a decimal number with
  20,686,623,784 digits (× log₁₀2). At 3,000 digits a page that is 6.9 M pages, ~13,800 books of 500
  pages, ~400 m of shelf.
- **Testing coverage.** 10⁹ states/second × 13.8 Gyr ≈ 4.4 × 10²⁶ ≈ 2⁸⁸ states examined.
- **SAT.** 2¹⁰⁰ ≈ 1.3 × 10³⁰; at 10⁹ checks/second, ~4 × 10¹³ years.
- **Landauer limit.** kT ln 2 ≈ 2.87 × 10⁻²¹ J at 300 K. Brute-forcing 2²⁶⁶ erasures ≈ 3.4 × 10⁵⁹ J;
  the Sun's whole-lifetime output ≈ 1.2 × 10⁴⁴ J, hence the ~10¹⁵ multiplier. Human brain ≈ 20 W.
- **Biology.** Human genome ≈ 3.2 × 10⁹ base pairs × 2 bits ≈ 800 MB; 64 codons → 20 amino acids +
  stop; Levinthal's paradox ≈ 10³⁰⁰ conformations folding in milliseconds.
- **Games.** Chess ≈ 10⁴⁴ legal positions, Go ≈ 10¹⁷⁰.

Sources cited on the slides: Cantor 1891, Russell 1901, Gödel 1931, Tarski 1936, Turing 1936, Rice
1953, Cook 1971, Karp 1972, Levin 1973; Shannon 1948, Landauer 1961, Bremermann 1962, von Neumann
1948/1966; Frege 1892, Wittgenstein 1921/1953, Korzybski 1931, Miller 1956, Chomsky 1957, Wigner
1960, Levinthal 1969, Goodhart 1975, Harnad 1990, Kahneman 2011, Jumper et al. 2021; Borges 1941,
Hofstadter 1979, Dijkstra 1969/1984, Knuth 1977; Pacioli 1494, Guido d'Arezzo c. 1025, Mendeleev 1869.

## For the computer scientists only

Two slides carry a marked aside for the small CS subset of the audience — selfie as Gödelisierung you
can run in a terminal (a compiler that compiles itself, an emulator that executes itself), and
monster/rotor as the syntax→semantics bridge that runs straight into NP-completeness on a laptop.
They are visually flagged as asides so the rest of the room knows they were not the intended target.

## Design notes

The visual system is a drafting table: deep ink-navy ground with a fine plotter grid, and two accents
that carry the argument rather than decorate it — **ochre for syntax** (finite, countable, notation)
and **drafting cyan for semantics** (infinite, uncountable, meaning), with madder rose reserved for
the moment a contradiction lands. The typography makes the same distinction: an old-style serif for
meaning, monospace for notation.

Both themes are designed; the viewer's system preference or the <kbd>d</kbd> key selects one.
Everything is sized from a single unit (`--u` = deck width ⁄ 100) so the 16:9 stage scales to any
projector, and all twelve figures are drawn on canvas at whatever size they are given. Animation is
suppressed under `prefers-reduced-motion`, where every build step shows at once.

Two guards keep text off text on machines whose font stacks resolve differently from the author's.
At load, `autofit()` measures each slide and, for any whose content would run past its bottom padding
onto the progress bar, scales that slide's unit down until it fits — a pure scale, so nothing
re-wraps. On canvas, every label is drawn with bounds it may not leave: too wide a string is shrunk
and nudged rather than allowed to run off the figure or onto its caption.
