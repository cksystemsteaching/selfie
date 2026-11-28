# bitr on entropy — development plan

November 27, 2026, restructured November 28 around one loop and two knobs. This plan is next to `projects/reversible.md` and takes over its bitr part (what is open of M12, M15's bitr columns, and the research notes on free bits), starting from M12's first result of November 26 and the bit-length loop of November 27. Cellfie is factored out: its checks keep running on today's `tools/bitr.c`, unchanged, and nothing here touches `-grid` or `-product`. The design rules of `CLAUDE.md` hold: C\* only, one file per tool, BTOR2 as the only input, every milestone a make target.

Target: CAV 2027, submission January 20, 2027 (conferences.i-cav.org/2027/cfp; confirm the time zone). The section on the paper says what that allows.

## Status

E1 done, E0 done but for external tools, E2 done but for `watch` (November 28, 2026). `tools/entr.c` has the arithmetic of counts, the reference, and the loop on formulas with its first two switches; `make count` (4 minutes), `make baselines`, and `make ledger` (36 seconds) are its checks, see the milestones. `make count` and `make ledger` are part of `make reversible`.

**E2, what is there.** `entr -cnf formula` runs the loop of the story on a formula in DIMACS format: the weakest bracket (a clause without a true or an open literal makes a region empty, all clauses with a true literal make it full) and the weakest estimate (the first open variable, true first), and two switches of the bracket, `propagate` and `pure`. With all switches off and the question whether, the first world it finds is babysat's, on every formula. The ledger is exact without big numbers: per rule the number of regions of each size, and two regions of a size are one of the next, from the smallest up, until one region of all worlds is left. The trace is the run as a file, and `tests/entr-trace.c` replays it against the formula alone: 23 formulas, every setting of the switches, counts equal to the reference's up to 20 variables, and a trace with one wrong clause is refused.

- **The measure shows the technique.** The pigeonhole formula, 12 variables: 98 regions undecided with all switches off, 8 with `propagate`, 5 with `pure` as well; the ledger says where the 4,096 worlds went, 4,096 to violated clauses against 9 to violated clauses and 4,087 to propagation.
- **Open bits are not entropy, on the first formulas.** The formulas that model checking generates have up to 96 variables and at most 8 bits of entropy: a count of 255 of 2^90 worlds, 7.99 of 90 bits, with 7 regions undecided, in milliseconds. The other 82 bits are determined, and propagation is the bracket that sees it. This is U minus H closed by the first switch, and why the plan wanted the unoptimized design seen first.
- **`pure` is where the two kinds of soundness part.** It is on only when the question is whether; its halves are in the ledger as not looked at, the trace marks them, and the checker reports a count replayed from such a trace as a lower bound.
- **`learn`, and what it is in this frame** (November 28, 2026). A region found empty gives a clause, by resolution back to the first unique implication point, and the clause is remembered: a bracket that keeps the count, since the clause only says what the formula says. The checker of traces does not take that on trust; it makes the literals of every learned clause false and propagates to a conflict. Counting the pigeonhole formulas, regions undecided without and with `learn`: 51 and 33 for 5 pigeons, 374 and 128 for 6, 3,245 and 424 for 7, and the ledger says how many worlds the learned clauses disposed of. The loop still goes back one region at a time. What CDCL does besides, jumping back over regions that are still open, is not in the bracket and is not there: it gives regions up, which only an estimate may do, and `restart` is the one switch that does, all of them at once, with the ledger cleared so that the last run accounts for all worlds.
- **`branch`, `phase`, `restart`, `reduce`** are there and checked, and the measure says what they do on the one family measured so far, which is not what they are known for: on the pigeonhole formula with 8 pigeons, asking whether, 393 regions undecided with `learn` and `pure` in babysat's order, 17,012 with all four more switches on, and 9.7 seconds against 0.02. Today's bitr, a CDCL solver with the same heuristics, watched literals, and jumps, takes 4,373 decisions and 0.07 seconds. So the order of a formula written by hand beats activity here, restarts without jumps cost what they give up, and with the heuristics on entr pays for looking at every clause in every bracket: 425 million clauses visited. One family, built to be hard for resolution; the formulas of model checking are next, in E3 and E4, and decide the defaults.
- **Left of E2: `watch`.** Two watched literals are `propagate` at a lower cost per bracket, and nothing else: the regions stay the same, the clauses visited drop. They are not simple in a loop that goes back one region at a time, where a learned clause can become unit without any literal having been made false since, and a full region is not something watches see. Deferred until the measure says that the bracket's cost per clause is what limits a run that matters; on the formulas of model checking so far a run is milliseconds. `components`, `cache`, `eliminate` are E6.

**The families, grown, and a bug in the specification.** A fifth family, `factor`: two numbers of n bytes that multiply to a product of two primes, 2 of 256^(2n) inputs. Growing the families found that rotor's RISC-R model let a read of one byte take a whole word from the tape, of which riscr fills one byte: a program that reads six bytes one at a time had a bad state with tape words that no file provides, and bitr "factored" a product of two 24-bit primes as RISC-R in a second. The constraint `input-zero-beyond-end` now also says zero beyond the size of the read; `make riscr-model`, `identity`, `sim`, `bmc`, `backward`, and `bit-length` pass with it. No earlier check read more than once. Two things follow for bitr as it is: the file `-w` writes for a RISC-R witness is the tape, a word per read, and does not replay in riscr when a program reads less than a word at a time more than once (the bytes in the order they are read do); and the conflicts of RISC-R rows in the first table of baselines, for families of more than one byte, were of the wrong question.

- **A correction that the fix forces: translated code does not cost conflicts.** The table of baselines redone with the fixed model has, on the 18 symbolic examples, a median of 2 conflicts as RISC-R against 2.5 as RISC-U, and 556 against 590 in total; before the fix it was 55 against 2.5, and 5,591. So the conflicts that this plan and `projects/reversible.md` put down to compute and uncompute were the solver working through seven bytes per read that should have been zero. What is left of the difference is time without conflicts: the slowest example takes 37 seconds as RISC-R with 35 conflicts and 2 seconds as RISC-U with 49, for 3.4 times the instructions. That time is in building and evaluating the paths, not in the solver, and is the baseline for `cancel` and `fold` forward. The hypothesis that cost follows U minus H stands on the backward tables of M12 only until they are measured again; the forward half of its evidence is withdrawn. The bit-length numbers of November 27 (58 against 43,486 conflicts) were measured with the old constraint, on a program that reads once, a byte, and need measuring again before they are quoted.
- **The table redone** (`baselines.txt`, 82 rows, a bound of 200,000 instructions, 60 seconds per run of bitr, about 50 minutes in two parts, since `baselines-list` and `baselines-table` let a part be measured). The rows that have no answer are where entr has to be better: `branch` at 12 bytes as RISC-R and `factor` at 3 bytes either way for the first bad state; every `branch` from 2 bytes on for all inputs, and `sum` at 16 bytes, 816 inputs in 50 seconds against 0.08 for the first. Depth costs RISC-R about eight times what it costs RISC-U: `loop` at 64 rounds is 2.3 against 19.5 seconds, at 256 rounds 16.6 seconds against none in 60. The recursive examples have exact counts at this bound, the same as RISC-U and as RISC-R.
- **What separates solvers, measured before the table is redone:** paths, not arithmetic. `branch` at 8, 10, and 12 bytes takes bitr 1.1, 4.4, and 17.6 seconds as RISC-U (255, 1,023, 4,095 forks, no conflict at all) and 5.9, 26, and over 60 as RISC-R. `sum` and `password` stay under a tenth of a second at 16 bytes. `factor` at 2 bytes is 24,004 conflicts and 1.4 seconds as RISC-U, 31,661 and 3.2 seconds as RISC-R, and at 3 bytes no answer in 60 seconds either way. With the two largest primes below 256^n instead, `factor` at 3 bytes took 105 conflicts: their bits are nearly all ones, which is where the solver's phases start. The primes are now taken from the middle of the range.

- **The reference counts what bitr enumerates.** On the 13 symbolic examples that end within 5,000 instructions on every input, the bad worlds of the reference are the inputs `bitr -bmc -all` lists, the same number as RISC-U and as RISC-R: 3 of 256 for the division example, 1.58 of 8 bits, after bitr's and riscr's numbers of instructions (77, 90, 107 and 322, 369, 431).
- **The interval shows.** The five recursive and looping examples do not end within the bound on every input, and the reference says so: a count of 1 to 98 of 256 as RISC-U and of 1 to 219 as RISC-R for the factorial, since the translated program takes three and a half times the instructions under the same bound.
- **Projection is not optional, measured.** On the RISC-R model of the division example `bitr -bmc -all` does not end: the file size is 64 open bits that the run does not read beyond its first byte, and bitr enumerates their values, 1,413 witnesses for the one input `0` before it ran out of memory after 47 seconds. Entr refuses that model until every open state is declared, and with one byte on the tape counts 3. In the table of baselines, bitr on all inputs of a RISC-R model is "no projection".
- **A world may be in two bad states.** An access outside the address space is `store-invalid-address` and `store-seg-fault` in the same step; bitr lists both and the reference the first. The check compares the inputs, not the properties.
- **The families have the counts they are built to have**: `sum` 1 and 4, `password` 1, `loop` 1 at 16 and at 64 rounds, `branch` 128 and 16,384 (7 of 8 and 14 of 16 bits), at one byte as RISC-U and as RISC-R and at two bytes as RISC-U.
- **Cost of the reference:** a millisecond per world natively with the models of `make bmc`, most of it restoring 2MB of heap, so 256 worlds in 0.2 seconds as RISC-U, a second as RISC-R, and 65,536 worlds in 20 seconds with small segments. On mipster a world of the division example is 30 million instructions, a second and a half, so the check there counts over 2 bits, the inputs 48 to 51.
- **The table of baselines** (`baselines.txt`, 14 minutes, a bound of 20,000 instructions, 60 seconds per run of bitr) says three things. Finding the first bad state is not hard for today's bitr on anything here: under half a second for every family up to four input bytes, as RISC-U and as RISC-R, and over 2.2 seconds only for one example, 36 seconds as RISC-R. So the families at these sizes do not separate solvers on reachability, which is the first risk of this plan confirmed: they have to grow, in bytes and in depth, before E4's decision means anything. Enumerating is where bitr stops: `branch` at two bytes has 16,384 bad inputs and `bitr -all` has no answer in 60 seconds, at three and four bytes neither, while the first of them takes a tenth of a second; that is the gap a count by regions is for. (The first table also had RISC-R at ten times the conflicts of RISC-U; that was the bug in the model, see the correction below.)
- **Not done in E0:** no external model checker or counter is installed where this was built, so the table has the reference and today's bitr only. `tools/bitme.py` with Bitwuzla, the one external solver at hand, did not get past its first step on the division example in 100 seconds with default options, against bitr's 0.1 seconds; that is an observation, not a baseline, until someone who knows bitme's options has tried. btormc, Pono, AVR, rIC3, and Ganak are still to be measured, by hand, into the same table.
- **Decided while building:** entr is built on `bitr.h`, bitr's source with its main renamed, for parser, loaders, and the lines of a model, instead of a copy of 2,000 lines; when entr takes bitr's name, that front end is what is kept of today's bitr. The reference makes the input buffer of a RISC-U model a state as any other, where the evaluator of `tools/btor2.h` returns rotor's current input for every read of it, so that models with several input bytes count.

## The story

**Worlds, count, entropy.** A model with n unknown bits has 2^n worlds. A question marks some of them, the bad ones. Their number is the **count**, a natural number, and its logarithm in bits is the **entropy** of the question: how much there is to find. The two are one quantity on two scales, as in Boltzmann's S = log W. The engine computes counts, because they are integers, an empty set is 0 and not minus infinity, and the count of a whole is the sum of the counts of its halves; the story and every report are in entropy, because bits are the unit a reader knows and because the laws are about it: a reversible step keeps it, erasure lowers it, and solving is the work of lowering it on purpose.

**Regions.** A region is a set of worlds given by what is fixed: these bits have these values, the others are open. A region has two numbers that must not be confused: its **open bits**, U, how much is not known, and its **entropy**, H, the logarithm of the number of bad worlds in it, how much is there. H is at most U.

**The machine that does not exist.** Imagine a machine that reports the count of a region in one step. With it, solving takes n steps and no search: fix the first bit to 0 and ask; if the count is zero fix it to 1, otherwise keep it; go on to the next bit. It never enters an empty region, so it never comes back. The count of the whole is the answer to "how many", zero is the proof, and the bits fixed are the witness. The physics such a machine would need is known: it is a machine whose run can be set at its end as well as at its beginning, see the three machines below.

**The machine that exists.** A real solver runs the same loop with a weaker instrument. Instead of the count of a region it gets a **bracket**: two counts, lo and hi, with the count between them. Then:

| Bracket | Meaning | The loop |
| --- | --- | --- |
| hi = 0 | empty | leaves the region |
| lo = hi | counted | adds it |
| lo > 0 | something is here | stops, if the question was whether |
| lo = 0 < hi | undecided | splits the region on an open bit and brackets the halves |

Only the last row costs. **Search is the price of an undecided bracket**, and the time of a solver is the number of regions it leaves undecided times the cost of one bracket. That is the one measure for every technique in this plan.

**Two knobs, and no third.**

1. **The bracket**, which is sound: the count is always inside it. Everything a solver concludes is here, whether it sees it now (unit propagation, constant folding, a cancelled bijection, concrete execution) or saw it before (a learned clause, a cached count, an invariant).
2. **The estimate**, which need not be sound: which open bit to split on and which half to take first. It changes the cost and never the answer. Activity, phases, restarts, forking on the pc, the direction of the search, and messages passed between clauses are all here.

The question is not a knob but a parameter of the problem: whether, how many, at least how many, and over which bits.

```
count(region)
  (lo, hi) = bracket(region)
  if lo == hi, or the question is answered
    return (lo, hi)
  bit = estimate(region)
  return count(region, bit = 0) + count(region, bit = 1)
```

**The known techniques are settings.**

| Technique | Question | Bracket sees | Bracket remembers | Estimate splits first on |
| --- | --- | --- | --- | --- |
| Truth table (babysat) | any | a region with nothing open | nothing | the next bit |
| DPLL | whether | unit propagation | nothing | a bit |
| CDCL | whether | unit propagation | empty regions, generalized by resolution | the most active bit |
| Model counting (#SAT) | how many | unit propagation, independent parts | counts of parts | a bit that separates parts |
| Concrete simulation | whether | everything: nothing is open | nothing | never splits |
| Abstract interpretation | whether | a domain per word | nothing | never splits, and may stay undecided |
| BMC by unrolling | whether | unit propagation over all steps at once | empty regions | the most active bit, at any step |
| Symbolic execution | whether | execution where the pc is known, propagation for the rest | nothing across paths | the bits the pc depends on |
| Explicit-state model checking | whether | everything | the states visited | the bits of the state, all of them |
| IC3, interpolation | whether | propagation over one step | empty sets of states, per depth | a state that reaches bad |

Read by rows, the table is the lesson: CDCL and model counting differ in the question and in what is remembered, and in nothing else. Symbolic execution and BMC differ only in the estimate. IC3 remembers what CDCL remembers, about states instead of bits. Simulation and abstract interpretation are a bracket without a split, exact and inexact. The refinements below are settings too: projection is part of the question, the trace is the record of the loop, and width is a lower bound on what must be remembered.

**What the story claims and what it does not.**

- It is not new theory. It is the self-reducibility of satisfiability, the equivalence of counting and sampling (Jerrum, Valiant, Vazirani, 1986), and counting as search with memory (Bacchus, Dalmao, Pitassi, 2003). What is ours is the executable form: one loop, one interface, and the known solvers as settings of it that a machine checks.
- It has content only if the interface is narrow. A region is a partial assignment, extended in time to partial states at steps. A bracket is two counts. A technique is judged by undecided regions per unit of bracket cost. A setting of the switches that names a row of the table must behave as that row's algorithm: the same answers, and the same decisions where a reference exists (babysat, today's CDCL with its order).
- It says what a technique is and how it relates to the others, not why it is fast. Everything under the estimate is classified, not explained: why first UIP and not another cut, why restarts help.
- The row of IC3 is an argument, not a switch, until after the submission.

## The three machines

| Machine | Holds | Reads out | A witness costs |
| --- | --- | --- | --- |
| Classical | one world | that world | up to 2^n / N runs, fewer with a better bracket |
| Quantum | all worlds | one, at random | about the square root of 2^n / N runs forward and backward |
| With the end set (postselection) | all worlds | those that end bad | n steps of the loop |

- **Setting the end.** Postselection is the imaginary ability to condition a run on its outcome, however unlikely: run from a uniform mix of inputs, decree that the run ended bad, and what remains is a uniformly random bad input. It is Bayes' rule as physics, with the count as the normalizing constant. Nature lets a run be set at its beginning only; done honestly, conditioning costs 2^n / N repetitions. A solver is a simulation of setting the end, and its search is what nature's refusal costs.
- **What it is worth.** A quantum computer with postselection decides exactly the questions "do more than half of the worlds satisfy this", which is counting in the form of a decision (Aaronson, 2005: PostBQP = PP). A classical randomized machine with postselection finds witnesses and counts approximately. So the machine of the story needs only the classical kind for whether, and the quantum kind, with a search over thresholds, for how many exactly.
- **Executing is not solving.** A quantum computer that runs the model on all inputs at once and is then measured has run it on one random input: random testing. Grover's iteration buys the conditioning at the square root of its price, and it is a run forward, a sign flipped on the bad states, and a run backward: `riscr -rev` with one step in between. This is the precise sense in which a reversible model runs right away: its inverse exists, and what Bennett's translation pushes is uncomputed by the run backward instead of left to spoil the interference. For the model to be a unitary, `exit` needs a step counter: stopping in place is not a bijection, and the plan's round trips exclude it for that reason.
- **Memory is what a quantum machine lacks.** In superposition a split is free and the run is the bracket, but keeping a fact and dropping how it was found is erasure. The nearest known result is a square root on the size of a backtracking tree (Montanaro, 2015); nothing comparable is known for clause learning.
- **One sum, three arithmetics.** A RISC-R step is a permutation matrix, a unitary with entries 0 and 1. The count is a sum over paths of products of entries: in the natural numbers for us, in the complex numbers for a quantum simulator, in the Booleans for satisfiability. Contracting a tensor network, eliminating variables, and counting by parts are one algorithm (Markov and Shi, 2008). From the naturals to the Booleans there is a homomorphism, n to n > 0, and from the complex numbers there is none, since amplitudes cancel: that is why an empty region stays empty and learning is sound, and why whether is easier than how many, and how many easier than simulating a quantum computer.
- **Heat.** Going from any of 2^n inputs to one of N lowers the entropy by n minus log N bits, and by Landauer that much heat must leave, which is next to nothing. A solution is cheap in energy and expensive in time. The bits a solver disposes of are the heat a relaxing machine would dump, and the bracket is what shortens the way.

None of this is implemented. bitr may print the count and the square root that it implies.

## The discussion this plan started from

The discussion that started this plan argues by analogy with statistical physics. Three of its claims hold and carry the design; the rest are analogies without theorems, and a solver built on them would have no specification.

| Claim | Verdict | What the plan does |
| --- | --- | --- |
| Entropy can be done in integers | True, and simpler than claimed: the entropy of a constraint is the logarithm of its number of solutions, and a number of solutions is an integer. No fixed-point messages are needed. | The engine computes counts, the story is in entropy |
| CDCL is a special case of entropy reasoning | True, but not as "zero-temperature belief propagation". Only unit propagation is a limit of message passing (warning propagation). Clause learning is caching: a learned clause records that a cube has no solutions. DPLL with caching is model counting, and CDCL is what remains of it when only zero or not zero matters (Bacchus, Dalmao, Pitassi, 2003; Sang et al., 2004). | One loop; CDCL is a setting of it |
| Reversible models help backward reasoning | True for the step: the inverse model is a function, so a predecessor is computed, not solved for. False for the search, and measured: M12's first result has backward lose to forward by orders of magnitude on Bennett-translated code, from the most favourable start. Nothing meets at k/2. | Backward is a consumer of the word-level rules, see below, and a check; not the headline |
| Survey and belief propagation as the engine | No evidence on structured instances; exact on trees only; "learned clauses cut the loops so messages converge" is unsupported. | An estimate, never a bracket: one late experiment with a kill criterion (E7) |
| LBD is mutual information, VSIDS is an entropy gradient | Analogies. | Measured instead: undecided regions per clause kept, per split |
| Soft penalties, soft conflicts, soft temporal lifting | Anything soft may order the search and may never prune it. | Estimates only, behind switches |
| A conflict clause records destructive interference; BMC simulates a quantum search | Wrong. A reversible classical step is a permutation, all of its amplitudes are 0 or 1, and nothing cancels. | See the three machines for what is true |

## Counting, precisely

Everything bitr answers is a statement about a count:

| Question | As a count |
| --- | --- |
| Satisfiable? | N > 0 |
| A bad state reachable in k steps? | N(init, k steps, bad) > 0 |
| A witness | one element |
| All bad inputs (`-bmc -all` today) | all elements |
| How many inputs are bad? (new) | N |
| Inverse undoes forward on all states (`-identity`) | N(step, inverse step, state changed) = 0 |
| The step is a bijection | N is the same before and after the step, for every set of states |
| Concrete simulation | N = 1 at every step: entropy zero |

**Integer arithmetic.** A count is m times 2^e with m and e unsigned 64-bit integers: open bits only add to e. If m overflows, the count is marked a lower bound; the tool never reports an inexact count as exact. Nothing in the tool is floating point, and nothing is a probability. Entropy, the logarithm, is for reports only.

**The rules of a bracket.** Empty: a region in which the constraint is violated has lo = hi = 0. Full: a region in which it is satisfied, with f bits open, has lo = hi = 2^f. Independent: the bracket of parts that share no bits is the product of their brackets. Bijection: a region and its image under a reversible step have the same bracket. Otherwise lo = 0 and hi = 2^f. The loop adds: the bracket of a region is the sum of the brackets of its halves. A bracket rule is sound if the count is inside the bracket (it preserves the count) or, weaker, if it is right about zero (it preserves whether), and which of the two a technique is, is the interesting part: the second kind is off when the question is how many.

**The interval of a run.** While it runs, the loop holds two counts: *found*, the sum of lo over the regions it has left, and *open*, the sum of hi minus lo over the regions not yet decided. The count of the question is between found and found plus open: [0, 2^n] at the start, the exact count when nothing is open. It is the state of an unfinished exact count, never an estimate. Whether stops when found is not zero or found plus open is zero, how many when nothing is open, a threshold when the interval is on one side of it.

**The ledger.** Without restarts the loop is a tree whose leaves partition the 2^n worlds into regions that are empty or full. The engine keeps a ledger of how many worlds each bracket rule disposed of (propagation, a learned clause, a part, a cached count, a cancelled bijection). The ledger must sum to exactly 2^n: a conservation law that is a machine check of the whole solver, the instrument that shows who did the work, and the ablation table of the paper, next to the one measure, undecided regions times bracket cost. With restarts there is no partition; the ledger is then a report, not a check.

## What is counted: four refinements

The count of a region is the simplest notion. Four more are needed, the first for correctness, the others because they are what the story is about. Each comes with a picture.

**1. Over which bits: projected counting.** *Picture: counting people, not people with their shadows.* "How many inputs reach the bug" counts assignments to the input bits. A formula also has state bits, auxiliary bits, and backward the words of history. As long as every other bit is determined by the bits counted over, each solution has exactly one shadow and counting all bits gives the same number; such a set of bits is an independent support. Forward on a deterministic model the inputs are one. As soon as a bit is free that is not counted over (a history word backward, a don't-care, a merged path), one input has many shadows and the plain count is too large, silently. So every count in this plan is a count *over* a named set of bits, and for the others the engine must show that they are determined, or count each projection once. Projected counting is harder than counting in general (a satisfiability question inside a count); the plan stays where the projection is onto an independent support and says so when it is not. Rule: the bracket of a full region is 2^f over the open bits counted over; an open bit that is not counted over and not determined is an error at `-O0`, not a factor.

**2. Images instead of preimages: how much a step forgets.** *Picture: letters into pigeonholes.* Count the letters, the states before a step, and the pigeonholes in use after it, the distinct states after. If every letter has its own hole nothing is forgotten; where two share a hole one bit is. The loss of a step on a set of states is log2 of the states before minus log2 of the distinct states after: zero for every RISC-R step, by the bijection, and what RISC-U erases otherwise. This is the measure of quantitative information flow (the leakage of a program is the logarithm of the number of outputs an observer can tell apart), applied to the machine's own state, and it is the second law of this plan as a number per instruction: a deterministic step never increases the count of distinct states, a reversible one keeps it, and what Bennett's translation pushes is an upper bound on what was lost. Counting distinct states is a count projected onto the state bits, so it is refinement 1 with the roles of input and state exchanged.

**3. Width: how much of the past the future needs.** *Picture: a relay race, and the baton is the state.* Cut the run at a time t. Everything the future needs to know about the past crosses the cut as the state at t, and the number of distinct states that can cross, over all inputs, is the width of the cut. Counting costs time exponential in width, not in size: a counter that works its way through time meets each distinct state at a cut once, if it recognizes it (`cache`, `merge`), and as often as there are paths to it if it does not. That is the gap M12 measured from another side, paths against bits, and it is `projects/reversible.md`'s merging lower bound. A reversible step cannot lower the width, since the states of a cut are in one-to-one correspondence with the states of the cut before plus the input read in between; an irreversible step can, and that is what erasure buys a checker, and what history gives back. The quantum counterpart is literal: cutting a tensor network gives a bond, and its dimension, the logarithm of which is an entanglement entropy, is the width of the cut and the cost of simulating across it.

**4. The trace is a circuit: counting once, asking often.** *Picture: the accountant's ledger, kept.* A run of the loop is a tree of sums (a split) and products (independent parts) over empty and full leaves, with shared subtrees where the bracket remembered. Written out, that is a circuit for the constraint in which every sum is over disjoint cases and every product over disjoint bits (a d-DNNF; a decision diagram is the special case of one fixed order of bits). On such a circuit the count is one pass from the leaves, and so is the count under any assumption, any element, the next element, and the count over any weights. So the search is a compilation, and the ledger is its summary: who disposed of how much is the size of the leaves by rule. This gives the plan three things: a certificate of a count that a small checker replays, which a wrong cache does not survive; `-all` and witnesses as walks over the trace instead of repeated solving; and the connection to the decision diagrams already in this repository (`tools/bvdd.py`, `tools/cflobvdd.py`).

What these change below: the reference counts over a declared set of bits (E1); the loop can write its trace and a checker in `tests/` replays it (E2); `-entropy` reports per step the loss of refinement 2 and per cut the width of refinement 3 on the examples whose inputs can be enumerated (E5); `merge` and `cache` are judged by how close the states visited per cut come to the width (E6).

## Design, unoptimized

One C\* file (working name `tools/entr.c`, see open decisions), on `selfie.h` and `tools/btor2.h`, laid out as count, reference, loop, bracket, estimate, words, checker, main.

1. **Count.** The arithmetic above: add, multiply, shift, compare, print as m·2^e and as bits.
2. **Reference.** The specification of every count, and the only component that is trusted: enumerate the bits counted over, run the concrete evaluator of `tools/btor2.h` on each world, and count the runs that hit the question. For DIMACS files, enumerate assignments as babysat does, counting. Exponential in the open bits, which is fine for one or two input bytes and 30 variables.
3. **Loop.** The seven lines above, over regions as partial assignments, with the interval, the ledger, and the trace.
4. **Bracket, the weakest.** Empty if a clause is falsified, full if all are satisfied, undecided otherwise. No propagation, no memory.
5. **Estimate, the weakest.** The next open bit, 0 first.
6. **Words.** Bit vectors and arrays of BTOR2 as gates, one operator at a time, no folding, no hashing; arrays by a choice per cell; Tseitin encoding, which preserves counts because every auxiliary bit is determined by the others.
7. **Checker.** The model unrolled k times into one formula, the question added, the loop asked. A region is then a partial state at each step.

With 4 and 5 as they are, this is babysat with counts, and hopeless beyond toys: it splits on bits that are determined. That is intended. The first switch, propagation, is what makes a circuit feasible at all, and the plan wants that seen in undecided regions.

## The switches, by knob

Each row is one switch (`-O name` on, `-no name` off; the default is all on, `-O0` is the design above). P = the bracket contains the count, Z = it is only right about zero, so the switch is off when the question is how many. The last column is the sentence the documentation proves and the measure shows. The grouping is the point: the same knob at the level of bits, of words, and of steps.

**The bracket sees**

| Switch | Technique | Level | | Says |
| --- | --- | --- | --- | --- |
| `propagate` | unit propagation | bits | P | one half of a split is empty and no split is needed to see it; concrete simulation is propagation with nothing open |
| `watch` | two watched literals | bits | P | `propagate`, lazily: a clause with two open literals has nothing to say |
| `components` | disconnected parts of the residual formula | bits | P | entropies of independent parts add |
| `eliminate` | bounded variable elimination | bits | P for determined bits | summing a bit out; bucket elimination and tensor contraction are this one move |
| `pure` | pure literals, Plaisted-Greenbaum | bits | Z | a rule that is only right about zero |
| `fold` | constant folding | words | P | a word with no open bit is a constant |
| `hash` | structural hashing | words | P | a word has no entropy given an equal word |
| `cancel` | normal forms `(x + v) - v`, `(x ^ v) ^ v`, exchange twice | words | P | a bijection changes no count, so it is never turned into gates; this is how M5 proved the identity without multiplying |
| `bounds` | known bits and intervals per word | words | P | an abstract domain is a bracket on a word: hi is 2^(unknown bits), or the length of the interval |
| `row` | read over write, index equalities decided lazily | words | P | a read at an index with h open bits is a choice among 2^h cells; pay for it only where it matters |
| `cone` | cone of influence | words | P | a bit outside the cone doubles the count and is never looked at |
| `emulate` | propagation by emulation, forward and with the inverse model | steps | P | on a bijection what is known at one step is known at the next and at the one before |

**The bracket remembers**

| Switch | Technique | Level | | Says |
| --- | --- | --- | --- | --- |
| `learn` | conflict analysis, first UIP, backjumping | bits | P | a learned clause is an empty region remembered, generalized by resolution from one region to many |
| `reduce` | clause deletion by LBD | bits | P | forgetting: the bracket gets weaker, never wrong |
| `cache` | component caching | bits | P | `learn` for every count, not only zero |
| `incremental` | learned clauses kept from depth k to k + 1 | steps | P | empty stays empty |
| `merge` | paths that reach the same state joined | steps | P | a state seen before; explicit-state model checking remembers nothing else |
| `invariants` | history invariants of `riscr -t` as constraints | steps | P on reachable states | memory that is given, not found: without it backward counts states with no ancestor |

**The estimate**

| Switch | Technique | Level | Says |
| --- | --- | --- | --- |
| `branch` | variable order by activity | bits | split where brackets have been undecided |
| `phase` | phase saving | bits | take first the half that was not empty last time |
| `restart` | restarts | bits | start over with what is remembered; gives up the partition, so the ledger is a report |
| `blast` off | word-level splits before bit-level ones | words | split on a word's value, not its bits: the entropy of a word is the sum over its bits, each given the lower ones |
| `fork` (a threshold in bits) | split first on states with at most that many open bits | steps | threshold 0 is BMC by unrolling; forking on the pc is symbolic execution, bitr's decision of November 14; no threshold is explicit-state model checking |
| `backward`, `direction` | split first on bits of the end, or of the end with fewer open bits | steps | on a bijection the bracket of a full state is exact from either end |
| `messages` (E7) | integer min-sum on the residual formula | bits | an estimate of the ratio of the halves' counts; may order, may never decide |

**The question**

| Option | Question | Says |
| --- | --- | --- |
| `-first` | whether | stop at lo > 0; all Z switches allowed |
| `-count` | how many, over a declared set of bits | stop when nothing is open |
| `-atleast N`, `-atmost N` | a threshold | stop when the interval is on one side |
| `-all` | which | walk the trace |

Not implemented before the submission, but in the documentation as rows of the table of techniques: k-induction, interpolation, and IC3, which remember empty sets of states that are closed under the step; on a bijection a full state has exactly one predecessor. Approximate counting by XOR hashing (ApproxMC) is integer-only and is a bracket that holds with a probability; it is the first thing to add if exact counts do not scale.

## What reversibility buys

1. **Conservation.** A deterministic step maps a set of states to a set that is no larger, and to one of the same size exactly when it is injective on the set. RISC-R's step is a bijection on all states (proven, `make identity`), so the number of states at depth k is the number of initial states, tapes included: entropy enters only where input is read and leaves nowhere. RISC-U's step erases, and `riscr -t` moves what it erases to the history stack. `-entropy` reports per step the bits that enter and the bits that are erased; for a translated binary the erased bits are zero and the history grows by at most what RISC-U erased. This is M15's table, produced by the checker.
2. **Two directions, one number.** Forward from init and backward from the query count the same set. `make directions` checks that the two counts are equal on every example. This is the strongest check in the plan: two searches that share only the count.
3. **Open bits are not entropy, and the gap is the cost.** M12's first result refutes "direction by free bits" as the plan had it: free bits predict neither paths nor time. Paths count the control decisions that depend on free bits; the time goes into the solver finding out that 64 fresh bits of a history word are determined by the rest of the state, and into reads at free addresses, blasted as multiplexers over a segment. In the story's terms: U, the open bits, was 320 to 1,024, and H, the entropy of the history given the state, was zero, since every run reached the initial state on exactly one path. A solver pays for U minus H, in regions whose bracket is undecided although nothing in them is open in fact. Forward the same gap seemed to show, a median of 2.5 conflicts as RISC-U against 55 as RISC-R on the examples; that was a bug in rotor's model and is gone with it, see the status above: 2.5 against 2. So the hypothesis to test is: **cost follows U minus H after the word-level rules, not U.** `cancel` (a pop of what was pushed, an uncompute of what was computed), `row` (a read at a free address as a fresh value with consistency constraints), and `invariants` are the bracket's ways to close the gap without a split; the measurements above are their baselines, and each must move them or is not kept.

Rule 8 holds: every experiment runs on the RISC-U and on the RISC-R model of the same program.

## Setting the end: hindsight as the baseline

The machine of the story has its end set. A solved problem makes that machine real for an experiment: its end is known, and a run can be given it.

**A partial state at a time.** One more input, next to the model: at step t, these bits of these states have these values, as a state file (name, index, value per line, as `-dump` writes it) with a time and with what is left out being free. It generalizes today's `-state` and `-free`, which set the end and free a range of it. A partial state at a time is a region of the search, extended in time; with everything known at one time it is a region with nothing open, and its bracket is exact, 0 or 1, by execution, forward with the model and backward with the inverse model.

**Deriving the end.** A witness, replayed concretely, gives the full state at every step, the end included (`-dump`). A count of N gives N ends.

**Three floors, from one mechanism.**

| Revealed | Run | Cost | Holds for |
| --- | --- | --- | --- |
| the full end | backward, concretely, to the initial state | k steps | RISC-R only: its end still holds the input, a RISC-U end does not determine its past |
| the full start, the witness's input | forward, concretely, to the bad state | k steps | RISC-U and RISC-R |
| the full state at a time t | backward to the start and forward to the end | k steps | the best any strategy that meets in the middle can do |

No run that finds a bug does less than replay it, so k steps is a floor for every experiment with a witness, and a configuration of the solver is reported as its ratio to it.

**The ladder.** The floor alone is loose. The instrument is what lies between everything revealed and nothing: reveal a part of a state at a time, and measure the cost against what was revealed. M12's first result is such a ladder, with the top of the history as the hidden part, 0.1 seconds with up to 4 words hidden, minutes with 5 to 12, no result with 16; and it showed that which bits are hidden matters more than how many, a frame pointer against a value. The ladder measures what a bit is worth to the solver, which is the experimental handle on U minus H: a hidden bit that is determined by the rest should cost nothing, and a rule (`cancel`, `row`, `invariants`) is judged by the rungs on which it makes that true. `-reveal` takes the state file of a solved problem and a description of what to hide, so that a ladder is a loop in a make target.

**Limits.**

- A proof has no end to set: if no bad state is reachable there is nothing to reveal. The analogue is the solver's own proof in hindsight: the run again, given only the learned facts that the answer used, which is what trimming a proof computes. That bounds the strategy, not the problem; the shortest proof cannot be computed, see information as proof size in `projects/reversible.md`.
- The floor is for one witness. N backward runs bound enumeration and not counting, which need not visit every bad state.
- The end comes from our own solution. The ladder measures how far a strategy is from its own hindsight, not from the best solver there could be. That is what an ablation needs, and no more.

## Milestones

| # | Deliverable | Done when |
| --- | --- | --- |
| E0 | Benchmarks and baselines. Scalable families of C\* programs (input bytes, depth, known number of bad inputs) next to the 18 symbolic examples, as RISC-U and RISC-R. btormc, Pono, AVR, rIC3 on rotor's BTOR2 for reachability; unrolling plus an exact counter (Ganak) for counts. Measurement only, no external tool in any check. | `make baselines` writes the table; today's bitr is in it |
| E1 | Count and reference, every count over a declared set of bits | `make count`: a model with a free bit that is neither counted over nor determined is refused; the reference counts 3 of 256 on the division example and agrees with `bitr -bmc -all` on all examples, as RISC-U and RISC-R, natively and on mipster |
| E2 | The loop with the weakest bracket and estimate, the interval, the ledger, the trace (`-trace file`), then the switches at the level of bits; a trace checker in `tests/` | `make ledger`: at `-O0` the loop makes babysat's decisions; with the switches of the row of CDCL it gives today's CDCL's answers; every run reports undecided regions and bracket cost; the checker replays every trace to the count reported; for every single switch and for all on, the count equals the reference's, zero or not zero equals babysat's and today's CDCL, and the ledger sums to 2^n where there is a partition |
| E3 | Words, unoptimized, then the bracket at the level of words: `fold`, `hash`, `cancel`, `row`, `cone` | `make words`: counts on single BTOR2 operators and on one step of the machine models equal the reference's, switch by switch |
| E4 | Checker: unrolling, then `fork`, `incremental`; the rows of BMC and of symbolic execution as settings | `make entropy`: `make bmc`'s checks (same bugs, same instruction counts, witnesses replay) plus the counts, for fork thresholds 0 and pc. **Go or no-go for the paper's claim, see below.** |
| E5 | `backward`, `direction`, `invariants`, `-entropy`, partial states at a time and `-reveal`. Continues M12 from its first result (`make backward`, `make bit-length`), whose tables are the baseline. | `make directions`: forward and backward counts equal where backward finishes; with the full end, start, or middle revealed every example is replayed in its number of instructions without a decision; `make ladder` writes cost against what is hidden for the end of every example, per switch; `-entropy` reports loss per step (zero on every RISC-R step, the bits erased on RISC-U) and width per cut, both against enumeration by the reference; M12's tables and the bit-length table again, with U, H, and conflicts per switch: `cancel` and `row` must bring the time of RISC-R forward to the time of RISC-U per instruction (the conflicts are there already, since the model was fixed), and the 8-bit garbage-free loop to an end backward, or the paper says backward does not pay and why |
| E6 | `components`, `cache`, `eliminate`, `bounds`, `emulate`, `merge` | each: its check in E2 to E4 extended, and a line in the ablation table; for `cache` and `merge`, states visited per cut against the width |
| E7 | `messages`: integer min-sum on the residual formula as an estimate | kept only if it reduces undecided regions and time on the families; otherwise a paragraph in the paper on why not |
| E8 | Experiments frozen: families, baselines, ablation (every switch off alone, `-O0` where it terminates), artifact | `make paper-tables` regenerates every number in the paper |
| E9 | `entropy.md`, the specification and the lesson, next to `riscr.md`: the story, the table of techniques with each row as a setting that runs, each switch with its sentence proven, one running example with ledgers before and after (the division example: 3 of 256, 1.58 of 8 bits) | written with each milestone, as `optimizations.md` is |

After the submission: the identity proof as a count in the new engine, the unbounded methods, `-grid` and `-product` (cellfie returns, with the stutter test), and then today's `tools/bitr.c` retires and the new file takes its name.

## Rules of development

- The design comes first and complete (E1 to E4 at `-O0` plus `propagate`), then one switch per commit. A switch lands with its check: on and off agree with the reference on every instance.
- There are two knobs. A switch that is neither a bracket nor an estimate does not land; a switch that is a bracket lands with a statement of P or Z, and an estimate with a check that it changes no answer.
- `-O0` and every single-switch configuration stay runnable forever. They are the correctness oracle and the performance baseline; the ablation table is a by-product.
- Today's bitr is the differential oracle for zero or not zero and for witnesses, and the source of procedures that are known to work (watched literals, first UIP, the normal forms). Rebuilt in the new order, not copied wholesale.
- M5's lesson is a rule here: a cache holds only facts that are true on all paths. For counts this is sharper than for zeros, since a wrong count is silent. The reference and the two directions are the guard.
- The compiler's cost model applies (40 instructions per call on mipster): mipster runs are for checks, native runs for numbers.

## The paper, and what the time to January 20 allows

**Do not claim general SAT or HWMCC performance.** A C\* solver without bit operations does not get within an order of magnitude of Kissat or rIC3, and reviewers will check. Competitive has to mean something bitr can win:

1. **Reachability on machine-code models** (rotor's BTOR2, RISC-U and RISC-R, the scalable families): bitr against BTOR2 model checkers. The lever is the estimate at the level of steps (`fork`) and the bracket at the level of words (`cancel`), not the level of bits. Unknown today: E0 measures it before anything is built.
2. **Counting on the same models** (how many inputs reach the bug): bitr against unrolling plus an exact counter. No BTOR2 checker answers this; this is the likely win.
3. **The executable unification:** one loop, two knobs, and the known solvers as settings of some 25 switches that a machine checks, measured by one number, in one self-compiling file. This is the contribution that does not depend on speed.
4. **Reversibility:** cost follows U minus H; compute and uncompute, and history, cost nothing once the word-level rules cancel them. Forward the conflicts are equal since rotor's model was fixed, and what is left is time per path. Backward it is open, and a negative result with a measured reason is still a result.

Go or no-go at E4, December 18: if bitr is not within a factor of 10 of the best baseline on reachability for at least one family as RISC-U and as RISC-R, the paper is written on 2 to 4, and the title does not say fast. If counting (2) does not beat the unrolling pipeline either, CAV 2027 is the wrong deadline and the work goes to a later one with unbounded methods in it.

| By | Milestones |
| --- | --- |
| December 4 | E0, E1 |
| December 11 | E2 |
| December 18 | E3, E4, go or no-go |
| January 1 | E5, E6 |
| January 8 | E7 decided, E8 frozen |
| January 20 | E9, paper, artifact |

Risks, largest first: (1) the benchmarks are toys, 18 programs with one input byte, and a paper needs families that scale and at least one program nobody wrote for the purpose; (2) exact counts overflow or do not scale past a few input bytes, then approximate counting moves from later to E6; (3) backward stays out of reach even with `cancel` and `row`: garbage-free code (M9, in riscr since November 26) makes the paths independent of the iterations and leaves the arithmetic, which is what E3's rules are for; if they do not close it, backward is a section on limits, and the paper stands on 2 and 3; (4) writing a new tool and a paper in the same eight weeks, where the paper loses.

## Open decisions

1. **Name and file.** Recommended: a new file under a working name until it passes E5, so that every existing make target stays green; then it becomes `tools/bitr.c`.
2. **The claim.** Recommended: 2 and 3 as the core, 1 and 4 as measured, decided at E4. After M12's first result, a paper whose headline is backward or bidirectional checking is not recommended.
3. **Exact or approximate counts** when m overflows. Recommended: exact or marked as a bound until E6, no approximation before it is needed.
4. **E7.** Recommended: timeboxed to three days. It is the part of the discussion with the least evidence behind it.

## References

- Bacchus, Dalmao, Pitassi: Algorithms and complexity results for #SAT and Bayesian inference, FOCS 2003; Solving #SAT and Bayesian inference with backtracking search, JAIR 2009.
- Sang, Bacchus, Beame, Kautz, Pitassi: Combining component caching and clause learning for effective model counting, SAT 2004.
- Kimmig, Van den Broeck, De Raedt: Algebraic model counting, Journal of Applied Logic 2017.
- Dechter: Bucket elimination, a unifying framework for reasoning, Artificial Intelligence 1999.
- Huang, Darwiche: DPLL with a trace, from SAT to knowledge compilation, IJCAI 2005.
- Darwiche, Marquis: A knowledge compilation map, JAIR 2002.
- Ivrii, Malik, Meel, Vardi: On computing minimal independent support and its applications to sampling and counting, Constraints 2016.
- Aziz, Chu, Muise, Stuckey: #∃SAT, projected model counting, SAT 2015.
- Smith: On the foundations of quantitative information flow, FoSSaCS 2009.
- Samer, Szeider: Algorithms for propositional model counting, Journal of Discrete Algorithms 2010 (counting and treewidth).
- Chakraborty, Meel, Vardi: A scalable approximate model counter, CP 2013.
- Braunstein, Mézard, Zecchina: Survey propagation, an algorithm for satisfiability, Random Structures and Algorithms 2005.
- Niemetz, Preiner, Reynolds, Barrett, Tinelli: Solving quantified bit-vectors using invertibility conditions, CAV 2018.
- Kuznetsov, Kinder, Bucur, Candea: Efficient state merging in symbolic execution, PLDI 2012.
- Markov, Shi: Simulating quantum computation by contracting tensor networks, SIAM Journal on Computing 2008.
- Brassard, Høyer, Mosca, Tapp: Quantum amplitude amplification and estimation, 2002.
- Aaronson: Quantum computing, postselection, and probabilistic polynomial-time, Proceedings of the Royal Society A, 2005.
- Jerrum, Valiant, Vazirani: Random generation of combinatorial structures from a uniform distribution, Theoretical Computer Science 1986.
- Montanaro: Quantum walk speedup of backtracking algorithms, 2015.
