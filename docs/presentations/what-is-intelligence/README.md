# What is Intelligence?

An animated lecture for undergraduate and graduate students **in any field**, built from basic
principles of computer science. Self-contained: one HTML file, no build step, no network access,
no dependencies. It plans out at just under **an hour** — and it is not pinned to that: the
clock counts down whatever the per-slide budget adds up to, so slides can be added or cut without
anything else needing to be rebalanced. For a shorter slot, see the cut list below.

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
| III | Self-Reference — syntax/semantics, Gödelisierung, incompleteness, halting, universality, Rice, law | 28–39 | 10:42 |
| IV | Cost — decidable ≠ doable, NP-completeness, Landauer's energy floor | 40–45 | 4:36 |
| V | Everywhere — biology, the self-copying machine, geometry, mind, and the notations that made every field | 46–51 | 5:06 |
| VI | Machines — what today's AI is, where world models take it, what neither escapes | 52–57 | 3:57 |
| VII | Practice — six habits, the definition, depth, humour, Goethe | 58–69 | 10:15 |

69 slides; the per-slide budget in `data-mins` adds up to **56:24**, and that is what the clock counts
down — it is read off the deck at load, not written into it. Press <kbd>t</kbd> to start the clock;
it turns amber if you are a minute behind the plan and rose if you are three behind.

**Every field in the room.** The audience is undergraduates and graduates from anywhere, so no
discipline is left as a name-check. Biology gets a worked mechanism (48). Law gets the penumbra and
Gödel's constitutional loophole (37). Mathematics and physics get the parallel postulate, and
chemistry rides along on the same slide, since Mendeleev's gaps and Dirac's positron are the same
move as Riemann's geometry (49). Psychology opens the talk — operational definitions are why "is it
intelligent?" is badly posed (3) — and gets its own slide later (50). Medicine's surrogate-endpoint
disaster is on the metrics slide (45), art's linear perspective on the pattern table (51). The rule
each of them follows is the one the DNA slide set: the example has to be a mechanism or a puzzle a
non-specialist can follow in fifteen seconds, whose general lesson is the thesis of the talk. The
specialist gets recognition; nobody else gets lost.

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

Part III does not end on the bad news. Slide 35 turns the halting proof over: the move that produced
the contradiction — a machine handed a description of a machine — is the identical move that produces
the computer, and Turing published both in 1936. The figure sets three machines that each *are* their
job against one machine that becomes any of them, because the job now arrives on the tape as data;
on the last step the tape holds `<U>`, and the machine is handed its own description. **Universality**
is stated in the room's own terms: nobody here owns a calculator, a typewriter, a map and a record
player, because they own one object that becomes any of those when handed a description. Self-
reference is the positive force here, not the destructive one, and the two readings are the same
sentence. The slide also sets up Rice on the next page — a machine that can be any machine can have
any behaviour, so there is nothing general left to decide.

Part V closes its biology stretch on the machine that builds itself (slide 48). The figure runs von
Neumann's architecture as a cell runs it: one strand, a **DNA polymerase** head that duplicates it
letter by letter without ever interpreting it, and a **ribosome** head that *executes* the same
letters three at a time. Interpreter is meant in its strong sense here, the sense in which a 3D
printer is one — description in, object out, not a reading of the description — and among the
objects it prints are the polymerase and the ribosome. Both heads keep cycling so the process is
visibly running rather than sitting finished. Two things to say out loud. Why the architecture needs
*two* tools: interpret the description only and the offspring inherits machinery but no description,
so it could never reproduce in turn; copy it only and there is a text with nothing to run it —
reproduction needs one string used both ways, as instructions and as inert data, which is this
lecture's distinction, four billion years old. And what the ribosome *is*: one machine that prints
any protein because which protein is data on the strand, which makes it slide 35's `U` built out of
chemistry. Turing did not invent universality. He noticed it.

Slide 49 does the same job for mathematics, physics and chemistry at once. Euclid's fifth postulate
resisted proof for two thousand years because it was *independent* — a choice, not a fact — and
Bolyai and Lobachevsky got out by changing it rather than proving it. The figure asks one question
in three panels: through a point beside a line, how many parallels? One, none, or many, and the only
thing to see is whether the candidates touch the given line. Then the payoff, which is the reason
this slide is not a digression: Riemann built the curved-space machinery in 1854 for nothing in
particular and Einstein could not have written relativity without it; Mendeleev left holes in his
table and named elements nobody had seen; Dirac's equation had a solution nobody wanted and the
positron turned up in 1932. Three times, a notation described something before anyone had seen it.

Part VI shows rather than states. Slide 53 runs an LLM as a mechanism — context chips, a reserved
slot for the next token, the weights, a bar chart of candidates, one sample taken, and a feedback
path carrying the answer back round as the next question. Slide 54 draws plausible, provable and
true as three regions: provable strictly inside true (the Gödel gap, labelled), plausible
overlapping true and sticking out of it, and that crescent — plausible and not true — is what a
hallucination is. Slide 55 draws the two routes to the same world: the long way through a transcript
of it, the short way straight at it, which is the efficiency argument as a picture — and then a
dashed border around the whole figure, because every box in it is inside the thing being modelled.
All three used to carry that content as prose.

**Running long?** These four are self-contained and can be dropped without breaking the argument,
buying 3:06: slide 16 (Borges), 18 (pairing ℕ ↔ evens), 25 (Cantor's theorem in general form),
61 (bridges and aviation). If you need another two minutes, the two field interludes — 37 (law) and
49 (geometry) — are written to be liftable: the argument does not depend on either, and which one
you keep should depend on who is in the room. Do not cut 20, 22, 23, 26, 32, 34, 35, 48, 62–64 —
they carry the thesis.

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
Hofstadter 1979, Dijkstra 1969/1984, Knuth 1977, Chaitin on randomness; Pacioli 1494, Guido d'Arezzo
c. 1025, Mendeleev 1869, Grace Hopper's nanosecond.

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

The code is taught rather than assumed. Slide 1 names it in the two colours themselves — *proof,
notation, syntax* in ochre, *truth, meaning, semantics* in cyan — and from there the words **proof**
and **truth** carry their colour wherever the distinction is doing work: the short answer (4), the
result everything hangs on (26), both Gödel slides (32, 33), the definition (63). Note that rose is
*not* the truth colour and must not become one: the whole talk is about telling proof, truth and
contradiction apart, so contradiction needs an ink of its own.

Both themes are designed; the viewer's system preference or the <kbd>d</kbd> key selects one.
Everything is sized from a single unit (`--u` = deck width ⁄ 100) so the 16:9 stage scales to any
projector, and all twenty-four figures are drawn on canvas at whatever size they are given. Animation is
suppressed under `prefers-reduced-motion`, where every build step shows at once.

Two guards keep text off text on machines whose font stacks resolve differently from the author's.
At load, `autofit()` measures each slide and, for any whose content would run past its bottom padding
onto the progress bar, scales that slide's unit down until it fits — a pure scale, so nothing
re-wraps. On canvas, every label is drawn with bounds it may not leave: too wide a string is shrunk
and nudged rather than allowed to run off the figure or onto its caption.
