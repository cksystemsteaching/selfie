# What is Intelligence?

An animated lecture for undergraduate and graduate students **in any field**, built from basic
principles of computer science. Self-contained: one HTML file, no build step, no network access,
no dependencies. It runs a little under fifty minutes as planned — and it is not pinned to that: the
clock counts down whatever the per-slide budget adds up to, so slides can be added or cut without
anything else needing to be rebalanced.

By Christoph Kirsch — University of Salzburg, Austria, and Czech Technical University in Prague,
Czechia. The talk is a collaborative effort with **Leoni Brand**, **Eva Jonas**, **Julius Möller** and
**Stefan Reiß** of the Department of Psychology at the University of Salzburg, who inspired and
encouraged its framing: address everyone affected by AI, and do it by academic grounding rather than
by repeating the booming and the dooming. Slide 2 says the same to the room.

**Give or watch the talk:** <https://selfie.cs.uni-salzburg.at/intelligence/> — or open `index.html`
in any modern browser. Either way, press <kbd>→</kbd> to begin.

This directory lives under `docs/`, which is what GitHub Pages publishes, so the deck is served as a
live page rather than as source. A raw GitHub link will not work: raw files are sent as `text/plain`
and the browser shows the markup.

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
| I | Vastness — orders of magnitude, units, bits, state spaces, why bugs are geometry | 6–16 | 8:51 |
| II | Infinity — countability, the diagonal twice over, meaning outnumbers notation | 17–27 | 9:06 |
| III | Self-Reference — syntax/semantics, Gödelisierung, incompleteness, halting, Rice | 28–37 | 8:42 |
| IV | Cost — decidable ≠ doable, NP-completeness, Landauer's energy floor | 38–43 | 4:36 |
| V | Everywhere — biology, the self-copying machine, mind, and the notations that made every field | 44–48 | 4:06 |
| VI | Machines — what today's AI is, where world models take it, what neither escapes | 49–54 | 3:57 |
| VII | Practice — six habits, the definition, depth, humour, Goethe | 55–66 | 10:15 |

66 slides; the per-slide budget in `data-mins` adds up to **53:24**, and that is what the clock counts
down — it is read off the deck at load, not written into it. Press <kbd>t</kbd> to start the clock;
it turns amber if you are a minute behind the plan and rose if you are three behind.

Part I opens with four slides on **size** before any computing happens: a map of the whole axis the
talk lives on (small → vast → countable → uncountable), a million/billion/trillion seconds as anchors,
the prefixes for bytes and hertz, and the two meanings of "kilo". They are there because every later
number — 10<sup>80</sup>, 2<sup>266</sup>, a 20-billion-digit state count — is unreadable to anyone
who has not first practised turning an exponent into a picture. The last of them also lands the
thesis in miniature: "GB" is one notation with two meanings, and the notation does not say which.

Part II states the claim once (slide 20) and then earns it slowly. Slide 21 makes the objects
concrete — a subset of ℕ *is* an infinite answer sheet, and the figure shows the empty set, its
opposite, the evens, the primes, `{3}` and one with no name at all. Slides 22 and 23 then run
Cantor's argument twice, in full, on two different kinds of object: once on subsets, building
`D = { n : n is not in Sn }` column by column, and once on decimal expansions, including the
trailing-nines patch that most popular accounts leave out. Slide 24 hands over the density picture —
between any two reals there is another, so there is no *next* one — together with the reason not to
trust it: the fractions are dense too, and they can be listed. Only the diagonal separates the cases.

Part VI shows rather than states. Slide 50 runs an LLM as a mechanism — context chips, a reserved
slot for the next token, the weights, a bar chart of candidates, one sample taken, and a feedback
path carrying the answer back round as the next question. Slide 52 draws the two routes to the same
world: the long way through a transcript of it, the short way straight at it — which is the
efficiency argument as a picture — and then a dashed border around the whole figure, because every
box in it is inside the thing being modelled. Both slides used to carry that content as prose.

Part V ends its biology stretch on the machine that builds itself (slide 46). The figure runs von
Neumann's architecture as a cell runs it: one strand, a **DNA polymerase** head that duplicates it
letter by letter without ever reading it, and a **ribosome** head that obeys the same letters three
at a time and builds proteins — among them the polymerase and the ribosome. Both heads keep cycling
so the process is visibly running rather than sitting finished. The point to make out loud is why
the architecture needs *two* tools: interpret the description only and the offspring inherits
machinery but no description, so it could never reproduce in turn; copy it only and there is a text
with nothing to run it. Reproduction needs one string used both ways — as instructions and as inert
data — which is this lecture's distinction, four billion years old.

**Running long?** These four are self-contained and can be dropped without breaking the argument,
buying 3:06: slide 16 (Borges), 18 (pairing ℕ ↔ evens), 25 (Cantor's theorem in general form),
58 (bridges and aviation). Do not cut 20, 22, 23, 26, 32, 34, 46, 59–61 — they carry the thesis.

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

- **A million, a billion, a trillion seconds.** 10⁶ s = 11.6 days; 10⁹ s = 31.7 years; 10¹² s =
  31,688 years. The Chauvet cave paintings are radiocarbon-dated to roughly 32,000 years — so a
  trillion seconds ago is, near enough, someone at work on that wall.
- **The map.** Grains of sand on Earth ≈ 7.5 × 10¹⁸ (Gwynne's beach-sand estimate); atoms in the
  Earth ≈ 1.3 × 10⁵⁰; atoms in the observable universe ≈ 10⁸⁰. People alive today ≈ 8.2 × 10⁹,
  which is the 10¹⁰ mark on the Part I ruler.
- **Prefixes.** kilo/mega/giga/tera = 10³/10⁶/10⁹/10¹². One byte holds one character, so 1 MB is a
  500-page book of plain text — hence a novel, a thousand novels, a million novels. Hearing tops out
  near 20 kHz; the IBM PC (1981) ran at 4.77 MHz; laptop clocks and Wi-Fi sit in the low gigahertz;
  infrared light is terahertz.
- **The nanosecond.** At 1 GHz one cycle is 10⁻⁹ s, in which light covers 29.98 cm — the length of
  wire Grace Hopper handed out in lectures so an audience could hold one.
- **Base 2 against base 10.** KiB/MiB/GiB/TiB = 2¹⁰/2²⁰/2³⁰/2⁴⁰ (IEC 60027-2, 1998). The drift over
  the base-ten prefix compounds: +2.4%, +4.9%, +7.4%, +10.0%, and +12.6% at peta. A "1 TB" disk is
  10¹² bytes = 931 GiB. Memory is sold in powers of two, which is why the 8 GB phone on slide 13 is
  8 GiB exactly.
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
projector, and all twenty figures are drawn on canvas at whatever size they are given. Animation is
suppressed under `prefers-reduced-motion`, where every build step shows at once.

Two guards keep text off text on machines whose font stacks resolve differently from the author's.
At load, `autofit()` measures each slide and, for any whose content would run past its bottom padding
onto the progress bar, scales that slide's unit down until it fits — a pure scale, so nothing
re-wraps. On canvas, every label is drawn with bounds it may not leave: too wide a string is shrunk
and nudged rather than allowed to run off the figure or onto its caption.
