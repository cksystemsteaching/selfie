# Figures

Every figure of the book *What is Intelligence?* and of the class decks, as one SVG each,
drawn in the visual system of the three talks: ochre for notation (finite, countable,
proof), drafting cyan for meaning (infinite, uncountable, truth), madder rose for
contradiction; mono for notation, serif for meaning. This directory is the single source
for both media. It lives under `docs/` because that is what GitHub Pages publishes, and
the decks fetch the files at load.

**Standalone**, a figure carries its own small stylesheet: a light palette, and the dark
palette under `prefers-color-scheme: dark`. That is what the book (`![…](../docs/figures/x.svg)`)
and any `<img>` show.

**In a deck**, `deck.js` strips that stylesheet and inlines the SVG, so the deck's tokens
apply and the figure follows the theme and the <kbd>d</kbd> key. Groups marked
`<g class="f" data-step="n">` then build with the slide's other fragments — the figure is
complete on paper and builds on the projector.

Conventions: `viewBox` in a 16:9 or wider frame, all lengths in user units, colours only
through `var(--ink)`, `var(--ink-2)`, `var(--muted)`, `var(--line)`, `var(--syn)`,
`var(--sem)`, `var(--bad)`, `var(--panel)`, `var(--ground)`; text in mono unless
`class="serif"`; every label inside the frame with room to spare, because the fallback
fonts differ per machine. No external resources, no scripts.

## Inventory

Ported from the talks (the talks themselves keep their canvas originals):

| Figure | From | Shows | Used by |
|---|---|---|---|
| `scale` | intelligence 7, cs 5 | the axis: eighty decades, the wall, two sizes of endless | book intro, ch. 2; ICS 2 |
| `bits` | intelligence 11 | sixteen bits, 2ⁿ states, the doubling curve | book ch. 2; ICS 2 |
| `ruler` | intelligence 12, cs 6 | log scale to 10⁸⁰ with anchors, 266 bits | book ch. 2; ICS 2 |
| `needle` | intelligence 14, cs 8 | a state space, the states a test visits, one bad state untested | book ch. 2; ICS 2; CC 2; SE 8 |
| `pairing` | intelligence 18 | ℕ paired with the evens | book ch. 5; ICS 7 |
| `enum` | intelligence 19, cs 10 | every finite text, listed | book ch. 3; ICS 5 |
| `diagonal` | intelligence 20 | Cantor's diagonal on bit sequences | book ch. 5; ICS 7 |
| `powerset` | intelligence 21 | subsets as answer sheets, one with no name | book ch. 5; ICS 7 |
| `diagset` | intelligence 22, cs 11 | the diagonal on subsets, D built column by column | book ch. 5; ICS 7 |
| `diagreal` | intelligence 23 | the diagonal on decimal expansions | book ch. 5; ICS 7 |
| `dense` | intelligence 24 | between any two, another; and again | book ch. 5; ICS 7 |
| `gap` | intelligence 26, cs 12 | notations countable, meanings not, the gap | book ch. 5; ICS 7 |
| `godel` | intelligence 31 | give every text a number | book ch. 3, 5; ICS 5 |
| `halt` | intelligence 34, cs 17 | the halting construction | book ch. 5; ICS 9; CC 7; SE 12 |
| `universal` | intelligence 35, cs 18 | three machines that are their job, one that becomes any of them | book ch. 4, 5; ICS 6; SE 3 |
| `penumbra` | intelligence 37 | a text and its application | book ch. 5 |
| `tree` | intelligence 41, cs 22 | 2ⁿ branches, one satisfying leaf | book ch. 8; ICS 11; CC 11; SE 5 |
| `energy` | intelligence 43, cs 24 | joules on a log scale, Landauer to the Sun | book ch. 8; ICS 11; CC 14; SE 11 |
| `vonneumann` | intelligence 48 | the self-copying machine: polymerase and ribosome | book ch. 10 |
| `parallels` | intelligence 49 | one, none, many parallels | book ch. 10 |
| `tokens` | intelligence 53, cs 26 | an LLM as a mechanism | book ch. 9; ICS 13; CC 13; SE 13 |
| `venn` | intelligence 54, cs 27 | plausible, provable, true | book ch. 9; ICS 13; CC 13; SE 13 |
| `worldmodel` | intelligence 55 | two routes to the same world | book ch. 9; ICS 13 |
| `loop` | intelligence 56, cs 28 | the loops are closed | book ch. 9; ICS 13; SE 13 |
| `meaning` | cs 14, selfie 10 | a compiler defines the meaning of the language it is written in | book ch. 1, 6; ICS 8; CC 1 |
| `galaxy` | cs 32, selfie 25 | the workshop of tools around one file | book ch. 1, 10; CC 1; SE 1 |
| `gate` | cs 30 | a generator supplies notation; the gate supplies the semantics | book ch. 9, 10; ICS 13; CC 13; SE 13 |
| `pipeline` | selfie 8 | the whole pipeline, nothing in the middle left out | book ch. 1, 6; CC 1 |
| `bootstrap` | selfie 11 | self-compilation: the same answer twice | book ch. 6; ICS 5; CC 8 |
| `interp` | selfie 13 | self-execution: an emulator running its own code | book ch. 4, 7; ICS 6; SE 3 |
| `ladder` | selfie 14 | self-hosting: hypervisor on hypervisor on emulator | book ch. 7; ICS 10; SE 6 |
| `emuvirt` | selfie 17 | two ways to build one operating system | book ch. 7; ICS 10; SE 6 |
| `cost` | selfie 19 | what emulation and virtualization cost | book ch. 7; SE 3, 6 |
| `selfref` | selfie 20 | virtualization is emulation plus self-reference | book ch. 7; ICS 10; SE 6 |

Drawn new for the book's technical chapters and the CC and SE decks, replacing the 51 hand-drawn
figures of the first edition:

| Figure | Shows | Used by |
|---|---|---|
| `half-adder`, `full-adder`, `7-bit-adder` | adders, from gates to a 7-bit chain | book ch. 2 |
| `tens-complement` | two digits read as encoding, unsigned, signed | book ch. 2 |
| `byte`, `memory`, `pointers`, `contiguous` | bytes, addresses, pointers, blocks | book ch. 2; ICS 3 |
| `text`, `string`, `directory`, `file-tree` | text, strings, directories, paths in memory | book ch. 2 |
| `image`, `video`, `audio`, `code` | media and code as bytes | book ch. 2; ICS 3 |
| `von-neumann`, `risc-u-machine`, `layout` | the architecture, the RISC-U machine, a program's memory layout | book ch. 4, 6; ICS 6; CC 5; SE 2, 4 |
| `performance`, `complexity`, `constants` | measured performance, asymptotic complexity, small inputs | book ch. 4, 8; SE 11 |
| `integer-literal-fsm`, `correct-integer-literal-fsm` | the integer-literal FSMs | book ch. 6; CC 2 |
| `scanning-integer-literals`, `atoi`, `scanning-character-literals`, `scanning-string-literals`, `scanning-identifiers`, `scanner` | the scanner: FSM, code sketch, compiler memory | book ch. 6; CC 2 |
| `parsing-literals`, `emitting-literals`, `global-variable-declaration`, `variable-use`, `symbol-table` | parsing and emitting, the symbol table | book ch. 6; CC 3, 4, 5 |
| `elementary-expressions`, `emitting-terms`, `emitting-arithmetic`, `emitting-expressions`, `emitting-assignments`, `emitting-while-loops`, `emitting-if-statements` | code generation, one construct at a time | book ch. 6; CC 5, 6 |
| `call-frame` | a call frame on the stack | book ch. 6; CC 7 |
| `page-table`, `paging-page-tables` | paging, array- and tree-based page tables | book ch. 7; SE 4 |
| `traffic-light-model` | process states | book ch. 7; SE 5 |
| `emu-emu`, `os-emu`, `os-vmm-emu` | an OS by emulation, by virtualization, under a VMM | book ch. 7; SE 6 |
| `live-versus-dead`, `roots-into-heap` | garbage collection | book ch. 7; SE 9 |
| `btor2` | a BTOR2 model: state, init, next, bad, unrolled k steps | book ch. 8; ICS 12; CC 10; SE 10 |
| `station` | the six stations on the axis | book, part openings; week-1 decks |

Still to draw when a deck needs them: `sat` (DPLL and CDCL on Rivest's formula) and `bitblast` (a
word operation as a circuit as a formula), both for CC 11 and 12.
