# bitr: model checking as counting

Bitr is a bounded model checker for BTOR2 models, written in C\* as one file, `tools/bitr.c`, on `selfie.h` and `tools/btor2.h`. It reads BTOR2 and nothing else; rotor writes the models, of RISC-U and of RISC-R binaries (`riscr.md`). Entr, `tools/entr.c`, is the part of bitr that is being rebuilt on one principle, and becomes bitr's only engine when it can do what bitr's solver does today, see the last section.

The principle is that every question a model checker answers is a count, and that every technique for answering it is one of two things: a way to conclude something about a set of cases without splitting it, or a way to choose the split. The goal is a checker that is as simple as that sentence, in which every optimization is a switch that can be turned off, so that the unoptimized checker stays there as specification and as baseline.

## Worlds, counts, entropy

A model with n open bits has 2^n **worlds**, one per value of these bits. A question marks some of them, here the worlds in which a bad state is reached within k steps. Their number is the **count** of the question, and its binary logarithm the **entropy**: how much there is to find. A bug exists if the count is not zero, a proof is the count zero, a witness is one marked world, and "how many inputs reach the bug" is the count itself.

A **region** is a set of worlds given by fixing some bits; the others are its open bits. A region with f open bits has 2^f worlds, of which some number between 0 and 2^f are marked. Two quantities must not be confused: the open bits of a region, how much is not known, and its entropy, how much is there. A word of history that a translated program pushes is 64 open bits and no entropy at all, since the rest of the state determines it.

Counts are integers; the tool has no floating point and no probabilities. Every count is over a declared set of bits: an open bit that is neither counted over nor fixed is refused, since it would double the count without being asked to.

## The loop

A **bracket** of a region is two numbers, lo and hi, with the count of the region between them. It is *decided* if lo = hi. An **estimate** picks an open bit of an undecided region, and which half to take first.

```
count(region)
  (lo, hi) = bracket(region)
  if lo == hi
    return lo
  bit = estimate(region)
  return count(region, bit = 0) + count(region, bit = 1)
```

That is all of the checker. Search is the price of an undecided bracket.

## The theorem

Let F be a set of worlds over n bits and N(R) the number of worlds of F in a region R. A bracket is *sound* if lo ≤ N(R) ≤ hi for every region R it is asked about, and *complete at the bottom* if it is decided on every region with no open bit.

**Theorem 1 (the loop counts).** For every sound bracket that is complete at the bottom, and every estimate, the loop terminates on the region of all worlds after at most 2^n - 1 splits and returns N, the count of F. The bracket may depend on what the loop did before; the estimate may be anything.

*Proof.* By induction on the open bits of a region R. If the bracket is decided, lo = N(R) by soundness. Otherwise R has an open bit, by completeness at the bottom, and the two halves of R by that bit are disjoint, cover R, and have one open bit less, so N(R) = N(R0) + N(R1), and the loop returns the sum by induction. ∎

**Corollary (the ledger).** The regions in which the loop stops are a partition of all 2^n worlds. So the sizes of these regions sum to 2^n, whatever the bracket and the estimate: a conservation law that a machine checks on every run. A rule that makes a region smaller, as unit propagation does, is a split of which one half is decided empty, and enters that half.

**Corollary (whether).** If the question is only whether N > 0, the loop may stop at the first region with lo > 0, and its bracket may be weaker: it need only be right about zero, that is, never say hi = 0 for a region with a marked world, and say lo > 0 only for a region that has one. Rules of that kind, such as pure literals, are sound for whether and not for how many.

**Theorem 2 (what search costs).** The number of bracket calls of a run is 2u + 1, where u is the number of undecided regions it meets, and its time is the sum of the costs of these calls. For a bracket that is a function of the region, and an estimate that is a function of the region: if a bracket B' is decided wherever a bracket B is, then the undecided regions of the run with B' are a subset of those of the run with B. With the exact bracket u = 0. With a bracket that is exact only about zero, a witness is found in at most n splits, each into a half that is known not to be empty.

*Proof.* A run is a binary tree whose inner nodes are the undecided regions: u inner nodes, u + 1 leaves, one call each. If both bracket and estimate are functions of the region, the tree of B' is the tree of B cut off at the regions on which B' is decided and B is not. The last claim is the self-reduction of satisfiability: ask which half is not empty, and go there. ∎

The theorem is honest about its condition. A stronger bracket never costs regions as long as the estimate stays the same function. Learned clauses make the bracket depend on the past, and activity makes the estimate depend on it; then Theorem 1 still holds and Theorem 2 does not, and measurements below show runs getting longer with more switches on.

**Theorem 3 (reversible models conserve counts).** Let T be the step of a model on a finite set of states S, with the input a part of the state, I a set of initial states, and B a set of bad states. If T is a bijection, then for every k

- |T^k(I)| = |I|: the number of states that can be reached after k steps is the number of initial states, and
- |{ s in I : T^k(s) in B }| = |{ b in B : T^-k(b) in I }|: counting forward from the initial states and backward from the bad states gives the same number.

If T is only a function, |T^(k+1)(I)| ≤ |T^k(I)| ≤ |I|: the entropy of the set of reachable states never grows, and the difference log |I| - log |T^k(I)| is what k steps have erased.

*Proof.* A bijection maps a finite set onto a set of the same size, and s is in I with T^k(s) in B exactly if b = T^k(s) is in B with T^-k(b) in I. A function maps a set onto a set that is no larger. ∎

RISC-R's step is a bijection on the states that satisfy the constraints of rotor's model, proven by bitr for all states (`make identity`), but for `exit`, which stops in place. RISC-U's step erases, and riscr's translation moves what it erases onto a history stack, which is what makes the translated step a bijection: the history is the erased entropy, kept.

None of this is new. Theorem 1 and 2 are the self-reducibility of satisfiability and counting as search (Davis, Logemann, Loveland; Bacchus, Dalmao, Pitassi 2003; Jerrum, Valiant, Vazirani 1986), Theorem 3 is that a permutation preserves cardinality. What bitr adds is that the statements are executable: one loop, the known solvers as settings of it, and a ledger and a checker of traces that hold every run to Theorem 1.

## Known techniques as settings

| Technique | Question | Bracket sees | Bracket remembers | Estimate splits first on |
| --- | --- | --- | --- | --- |
| Truth table (babysat) | any | a region with nothing open | nothing | the next bit |
| DPLL | whether | unit propagation | nothing | a bit |
| CDCL | whether | unit propagation | empty regions, generalized by resolution | the most active bit; gives up regions when it jumps back or restarts |
| Model counting | how many | unit propagation, independent parts | counts of parts | a bit that separates parts |
| Concrete simulation | whether | everything: nothing is open | nothing | never splits |
| Abstract interpretation | whether | a domain per word | nothing | never splits, and may stay undecided |
| BMC by unrolling | whether | unit propagation over all steps | empty regions | the most active bit, at any step |
| Symbolic execution | whether | execution where the pc is known | nothing across paths | the bits the pc depends on |
| Explicit-state model checking | whether | everything | the states visited | all bits of the state |

Two machines that do not exist frame the picture. A machine whose run can be set at its end as well as at its beginning (postselection) would have the exact bracket: n splits. A quantum computer holds all worlds and reads out one at random; Grover's search finds one of N marked worlds among 2^n in about the square root of 2^n / N runs forward and backward, which a reversible model allows as it is. Counting with postselection is exactly as hard as counting (Aaronson 2005). A solver simulates setting the end, and its search is what that costs on a machine that cannot.

## What is there

**Bitr** (`tools/bitr.c`): a parser for the BTOR2 that rotor emits; loaders that put a binary and an input file into the initial state; a concrete simulator on the evaluator of `tools/btor2.h`; a bit-blaster into an and-inverter graph; a CDCL solver; a bounded model checker that follows a model path by path, forking where the next program counter is a choice between constants, and asks the solver whether a fork is feasible and a bad state reachable; and a proof that one model undoes another on all states.

```
bitr model.btor2 [ -l binary ] [ -i file ] [ -k steps ] [ -p ]
bitr model.btor2 [ -l binary ] -bmc steps [ -all ] [ -w file ] [ -dimacs prefix limit ] [ -v ]
bitr model.btor2 -identity inverse.btor2
bitr -sat formula.cnf
```

**Entr** (`tools/entr.c`, built on `bitr.h`, bitr's source with its main renamed): the arithmetic of counts; the *reference*, which enumerates the declared bits of a model and runs the simulator on each world, the specification of every count; and the loop, on formulas in DIMACS format, with a ledger, a trace, and switches.

```
entr model.btor2 [ -l binary ] [ -k steps ] { -over state index bits | -fix state index value | -zero state } [ -v ]
entr -cnf formula { -first | -count | -reference | -O0 | -O switch | -no switch | -trace file }
```

| Switch | Knob | Keeps | What it is |
| --- | --- | --- | --- |
| `propagate` | bracket | the count | a clause with one open literal and no true one makes a half empty |
| `pure` | bracket | zero or not | a literal whose negation occurs in no open clause; off when counting |
| `learn` | bracket | the count | a clause from every region found empty, by resolution to the first unique implication point |
| `reduce` | bracket | the count | learned clauses of more than average glue are forgotten |
| `branch` | estimate | the answer | split on the open variable that learned clauses name most |
| `phase` | estimate | the answer | first the half with the value the variable had last |
| `restart` | estimate | the answer | give up all open regions and begin again with what was learned; off when counting |

With all switches off (`-O0`) the loop is babysat with counts, and finds babysat's first world. The loop goes back one region at a time and never jumps over open regions, which keeps the ledger a check; a restart clears the ledger, so that the last run accounts for all worlds. The trace is the run as a file, and `tests/entr-trace.c` replays it trusting only the formula: an empty region must violate the clause named, a full one satisfy all clauses, and a learned clause must follow, by making its literals false and propagating to a conflict.

## Checks

| Target | Checks |
| --- | --- |
| `make sim` | bitr's simulator stops in rotor's model of every symbolic example, as RISC-U and as RISC-R, with the emulator's exit code after the emulator's number of instructions |
| `make bmc` | bitr finds the bug in every symbolic example, as RISC-U and as RISC-R, and the witness replays in mipster or riscr |
| `make cdcl` | bitr's CDCL solver and babysat agree on `examples/sat` and on the formulas of model checking with at most 100 variables |
| `make identity` | the inverse RISC-R machine model undoes the forward model and the forward model the inverse, on all states |
| `make count` | the reference refuses an undeclared open state, counts the inputs that `bitr -bmc -all` enumerates, the same number as RISC-U and as RISC-R, and the counts that the families of `examples/entropy` are built to have |
| `make ledger` | on 23 formulas and every setting of the switches the ledger accounts for all worlds, the trace replays to the count, the counts are the reference's and the answers bitr's and babysat's; wrong traces are refused |
| `make baselines` | not a check: a table of the reference and bitr on the examples and the families |

All but the last are part of `make reversible`, and all tools also run on mipster.

## What was measured

- **A count needs its bits declared.** On the RISC-R model of an example `bitr -bmc -all` does not end: the file size is 64 open bits that the run never reads, and bitr enumerates their values. The reference refuses the model until every open state is declared, and then counts 3 of 256, the same as for RISC-U.
- **Open bits are not entropy.** The formulas that model checking the examples generates have up to 96 variables and at most 8 bits of entropy, a count of 255 of 2^90 worlds; propagation alone decides all but 7 regions.
- **Translated code costs time, not conflicts.** With rotor's model of `read` corrected, see `riscr.md`, bitr has a median of 2 conflicts on the examples as RISC-R and 2.5 as RISC-U. The slowest example still takes 37 seconds as RISC-R against 2 as RISC-U, for 3.4 times the instructions: the time is in building and evaluating paths.
- **What is hard for bitr today** (`examples/entropy`, each family with a size and a known count): paths, `branch` with 12 input bytes is 4,095 forks and 18 seconds; arithmetic, `factor` with two 24-bit primes has no answer in a minute; depth, `loop` costs RISC-R eight times what it costs RISC-U; and enumeration, `branch` with 2 bytes has 16,384 bad inputs that `-all` does not list in a minute, while the first takes a tenth of a second. The last is what counting by regions is for.
- **Learning helps counting; the heuristics do not help on pigeons.** Counting the pigeonhole formula with 7 pigeons takes 3,245 undecided regions without `learn` and 424 with it. Asking whether for 8 pigeons: 393 regions with `propagate`, `pure`, and `learn` in the order of the formula, 17,012 with `branch`, `phase`, `restart`, and `reduce` on as well, and 4,373 decisions for bitr's CDCL.
- **The loop is not yet a solver for model checking.** The 431 formulas that bitr generates for three examples, up to 161,000 variables, take bitr's CDCL 25 seconds together. Entr's loop looks at every clause in every bracket and does not finish them in two minutes.

## Next

In this order, each as a switch, each checked by `make ledger` before the next:

1. `watch`: two watched literals, so that a bracket looks only at the clauses a new value touches.
2. `jump`: going back over regions that a learned clause has made pointless. It gives regions up, as a restart does, so it is a switch of the estimate, and the ledger is a report while it is on.
3. The loop as bitr's solver: the model checker's questions go to the loop instead of the CDCL solver, `make bmc` and `make identity` pass with it, and the CDCL solver and entr as a separate tool go. One file, one engine.
4. Words: the bracket at the level of BTOR2 operators, constant folding, structural hashing, and the cancellation of what an instruction and its inverse do, as switches.
5. Counting in the checker: the count of the bad inputs of a model, by regions, checked against the reference.

Deliberately not there: backward checking and cellfie. Bitr checked backward from a bad state with the inverse model, and lost to forward checking by orders of magnitude; that code, cellfie (a reversible cellular machine that runs RISC-R, with its layout compiler), bitr's product of two models, and the plans and measurements of both are in this repository at commit `62593875eecf` of the branch `RISC-R`.

## References

- Davis, Logemann, Loveland: A machine program for theorem-proving, 1962.
- Bacchus, Dalmao, Pitassi: Algorithms and complexity results for #SAT and Bayesian inference, FOCS 2003.
- Sang, Bacchus, Beame, Kautz, Pitassi: Combining component caching and clause learning for effective model counting, SAT 2004.
- Jerrum, Valiant, Vazirani: Random generation of combinatorial structures from a uniform distribution, 1986.
- Huang, Darwiche: DPLL with a trace, from SAT to knowledge compilation, IJCAI 2005.
- Aaronson: Quantum computing, postselection, and probabilistic polynomial-time, 2005.
- Bennett: Logical reversibility of computation, 1973.

The references are from memory and are to be checked before they are cited elsewhere.
