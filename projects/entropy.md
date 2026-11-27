# bitr on entropy — development plan

November 27, 2026. This plan is next to `projects/reversible.md` and takes over its bitr part (what is open of M12, M15's bitr columns, and the research notes on free bits), starting from M12's first result of November 26 and the bit-length loop of November 27. Cellfie is factored out: its checks keep running on today's `tools/bitr.c`, unchanged, and nothing here touches `-grid` or `-product`. The design rules of `CLAUDE.md` hold: C\* only, one file per tool, BTOR2 as the only input, every milestone a make target.

Target: CAV 2027, submission January 20, 2027 (conferences.i-cav.org/2027/cfp; confirm the time zone). That is 54 days. The last section says what that allows.

## What the discussion gets right, and what this plan does not build on

The discussion that started this plan argues by analogy with statistical physics. Three of its claims hold and carry the design; the rest are analogies without theorems, and a solver built on them would have no specification.

| Claim | Verdict | What the plan does |
| --- | --- | --- |
| Entropy can be done in integers | True, and simpler than claimed: the entropy of a constraint is the logarithm of its number of solutions, and a number of solutions is an integer. No fixed-point messages are needed. | Counts are the semantics, see below |
| CDCL is a special case of entropy reasoning | True, but not as "zero-temperature belief propagation". Only unit propagation is a limit of message passing (warning propagation). Clause learning is caching: a learned clause records that a cube has no solutions. DPLL with caching is model counting, and CDCL is what remains of it when only zero or not zero matters (Bacchus, Dalmao, Pitassi, 2003; Sang et al., 2004). | The solver is a counter; SAT is its image |
| Reversible models help backward reasoning | True for the step: the inverse model is a function, so a predecessor is computed, not solved for. False for the search, and measured: M12's first result has backward lose to forward by orders of magnitude on Bennett-translated code, from the most favourable start. Nothing meets at k/2. | Backward is a consumer of the word-level rules, see below, and a check; not the headline |
| Survey and belief propagation as the engine | No evidence on structured instances; exact on trees only; "learned clauses cut the loops so messages converge" is unsupported. | One late experiment with a kill criterion (E7) |
| LBD is mutual information, VSIDS is an entropy gradient | Analogies. | Measured instead: bits removed per clause, per decision |
| Soft penalties, soft conflicts, soft temporal lifting | Anything soft may order the search and may never prune it. | Heuristics only, behind switches |
| A conflict clause records destructive interference; BMC simulates a quantum search | Wrong. A reversible classical step is a permutation, all of its amplitudes are 0 or 1, and nothing cancels. | See the quantum section for what is true |

## The principle: every question is a count

A query is a set of assignments to n bits, given by a constraint F. Its **count** N(F) is the number of assignments in it, a natural number, and its **entropy** H(F) = log2 N(F), between minus infinity and n. Everything bitr answers is a statement about a count:

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

**Integer arithmetic.** A count is m times 2^e with m and e unsigned 64-bit integers: free bits only add to e. If m overflows, the count is marked a lower bound; the tool never reports an inexact count as exact. Entropy is used in whole bits, as bounds: the engine holds an interval L ≤ H ≤ U for the query, where U starts at the number of free bits and L at minus infinity. Nothing in the tool is floating point, and nothing is a probability.

**One rule for every component:** a technique is a rule that tightens L or U and is sound if it never loses a solution (it preserves N) or, weaker, never turns a count from zero to nonzero or back (it preserves N > 0). The questions differ only in when to stop: SAT stops at L ≥ 0, UNSAT at U = minus infinity, counting at L = U. This is the claim the tool makes executable: the established techniques of SAT, SMT, and BMC are such rules, each either count-preserving or zero-preserving, and which of the two is the interesting part.

**The ledger.** Without restarts the search is a tree whose leaves partition the 2^n assignments into cubes, each either refuted or full of solutions. The engine keeps a ledger of how many assignments each rule disposed of (propagation, conflict, learned clause, component, cache hit, cancelled bijection). The ledger must sum to exactly 2^n: a conservation law that is a machine check of the whole solver, the instrument that shows the special cases (the table of who removed how many bits is the lesson), and the ablation table of the paper. With restarts there is no partition; the ledger is then a report, not a check.

## Design, unoptimized

One C\* file (working name `tools/entr.c`, see open decisions), on `selfie.h` and `tools/btor2.h`, laid out as count, reference, counter, words, checker, main.

1. **Count.** The arithmetic above: add, multiply, shift, compare, print as m·2^e and as bits.
2. **Reference.** The specification of every count, and the only component that is trusted: enumerate the free bits of a model (uninitialized states and inputs, bounded), run the concrete evaluator of `tools/btor2.h` on each, and count the runs that hit the query. For DIMACS files, enumerate assignments as babysat does, counting. Exponential in the free bits, which is fine for one or two input bytes and 30 variables.
3. **Counter** (the SAT unit). DPLL on CNF in a fixed variable order: a falsified clause counts 0, all clauses satisfied with f free variables counts 2^f, a decision counts the sum of both sides. No propagation, no learning. This is the reference with a formula in place of the evaluator.
4. **Words** (the SMT unit). Bit vectors and arrays of BTOR2 blasted to gates one operator at a time, no folding, no hashing; arrays by a choice per cell; Tseitin encoding, which preserves counts because every auxiliary variable is defined by the others (a defined bit has entropy zero given its inputs).
5. **Checker** (the BMC unit). The model unrolled k times into one formula, the query added, the counter asked. Nothing is enumerated, nothing forked, forward only.

Unoptimized, 3 to 5 are hopeless beyond toys: the counter branches on defined bits. That is intended. The first optimization, propagation, is what makes a circuit feasible at all, and the plan wants that seen.

## Established techniques as special cases

Each row is one switch (`-O name` on, `-no name` off; the default is all on, `-O0` is the design above). P = preserves the count, Z = preserves only zero or not zero, so the rule is off when counting. The "says" column is the sentence the documentation proves and the ledger shows.

**SAT**

| Switch | Technique | | Says |
| --- | --- | --- | --- |
| `propagate` | unit propagation | P | one side of a decision has count 0 and no search is needed to see it; concrete simulation is propagation with no free bits |
| `first` | stop at the first model | Z | the question was N > 0 |
| `learn` | conflict analysis, first UIP, backjumping | P | a learned clause is a cached zero, generalized by resolution from one cube to many |
| `watch` | two watched literals | P | `propagate`, lazily: a clause with two unassigned literals has nothing to say |
| `branch` | variable order by activity | P | decide where the bound moves most; activity is a proxy, and the ledger says how good |
| `phase`, `restart`, `reduce` | phase saving, restarts, clause deletion by LBD | Z | heuristics of the zero image; restarts give up the partition |
| `components` | disconnected parts of the residual formula | P | entropies of independent parts add |
| `cache` | component caching | P | learning generalized from zeros to all counts |
| `eliminate` | bounded variable elimination | P for defined variables | marginalization; variable elimination, bucket elimination, and tensor contraction are this one move |
| `pure` | pure literals, Plaisted-Greenbaum | Z | a rule that exists only in the zero image |

**SMT (bit vectors and arrays)**

| Switch | Technique | | Says |
| --- | --- | --- | --- |
| `fold` | constant folding | P | a term of entropy zero is a constant |
| `hash` | structural hashing | P | a term has entropy zero given an equal term |
| `cancel` | normal forms `(x + v) - v`, `(x ^ v) ^ v`, exchange twice | P | a bijection changes no count, so it is never blasted; this is how M5 proved the identity without multiplying |
| `bounds` | known bits and intervals per term | P | abstract domains are upper bounds on entropy: 2^(unknown bits), hi - lo + 1 |
| `blast` off | word-level decisions before bit-level ones | P | bit blasting is the chain rule: the entropy of a word is the sum over its bits, each given the lower ones |
| `row` | read over write, index equalities decided lazily | P | a read at an index of h bits is a choice among 2^h cells; lemmas on demand pay for it only when it matters |
| `cone` | cone of influence | P | a bit outside the cone doubles the count and is never looked at: it adds 1 to e |
| `emulate` | propagation by emulation, forward and with the inverse model | P | invertibility conditions are trivially true for a bijection: outputs propagate to inputs |

**BMC**

| Switch | Technique | | Says |
| --- | --- | --- | --- |
| `fork` (a threshold in bits) | enumerate a state whose entropy is at most the threshold, keep the rest symbolic | P | threshold 0 is BMC by unrolling; forking on the pc is symbolic execution, bitr's decision of November 14; an unbounded threshold is explicit-state model checking; one knob |
| `merge` | join paths that reach the same pc | P | state merging: the count of a join is the sum |
| `incremental` | keep learned clauses from depth k to k + 1 | P | a zero stays a zero |
| `backward` | search from the query with the inverse model | P | on a bijection preimages are computed; the count is the same from both ends |
| `direction` | search from the end with fewer free bits, meet where they balance | P | input bits read forward against history bits undetermined backward |
| `invariants` | history invariants of `riscr -t` as constraints | P on reachable states | without them backward counts states with no ancestor |

Not implemented before the submission, but in the documentation as the same picture: k-induction, interpolation, and IC3 compute sets R with init inside and bad outside, an upper bound on reachable entropy that is closed under the step; on a bijection a full state has exactly one predecessor. Approximate counting by XOR hashing (ApproxMC) is integer-only and fits; it is the first thing to add if exact counts do not scale.

## What reversibility buys, in counts

1. **Conservation.** A deterministic step maps a set of states to a set that is no larger, and to one of the same size exactly when it is injective on the set. RISC-R's step is a bijection on all states (proven, `make identity`), so the number of states at depth k is the number of initial states, tapes included: entropy enters only where input is read and leaves nowhere. RISC-U's step erases, and `riscr -t` moves what it erases to the history stack. `-entropy` reports per step the bits that enter and the bits that are erased; for a translated binary the erased bits are zero and the history grows by at most what RISC-U erased. This is M15's table, produced by the checker.
2. **Two directions, one number.** Forward from init and backward from the query count the same set. `make directions` checks that the two counts are equal on every example. This is the strongest check in the plan: two searches that share only the count.
3. **Free bits are the bound, not the entropy, and the gap is the cost.** M12's first result refutes "direction by free bits" as the plan had it: free bits predict neither paths nor time. Paths count the control decisions that depend on free bits; the time goes into the solver finding out that 64 fresh bits of a history word are determined by the rest of the state, and into reads at free addresses, blasted as multiplexers over a segment. In this plan's terms: U, the free bits, was 320 to 1,024, and H, the entropy of the history given the state, was zero, since every run reached the initial state on exactly one path. A solver pays for U minus H. The same gap shows forward: a median of 2.5 conflicts as RISC-U against 55 as RISC-R on the examples, and 58 against 43,486 on the bit-length loop with history and garbage-free, because translated code computes and uncomputes and the bit-level solver has to see that. So the hypothesis to test is: **cost follows U minus H after the word-level rules, not U.** `cancel` (a pop of what was pushed, an uncompute of what was computed), `row` (a read at a free address as a fresh value with consistency constraints), and `invariants` are the rules that close the gap without search; the measurements above are their baselines, and each must move them or is not kept.

Rule 8 holds: every experiment runs on the RISC-U and on the RISC-R model of the same program.

## The quantum connection, in the documentation only

- A RISC-R step is a permutation matrix, a unitary with entries 0 and 1. The count N(init, k, bad) is a sum over paths of products of matrix entries: the quantity a quantum circuit simulator computes as an amplitude, in the semiring of natural numbers instead of complex numbers. SAT is the same sum in the Boolean semiring. Variable elimination, component decomposition, and tensor network contraction are one algorithm (Markov and Shi, 2008).
- There is a homomorphism from the naturals to the Booleans, n to n > 0, and none from the complex numbers: amplitudes cancel. That is why a classical zero is a zero forever and learning is sound, and why SAT is easier than counting, and counting easier than simulating a quantum computer.
- The model runs on a quantum computer as an oracle without ancillas for uncomputation, because it is reversible already. Grover finds one of N bad inputs among 2^n with about the square root of 2^n / N oracle calls, and quantum counting estimates N. The number bitr computes is the number that sets the quantum cost. bitr may print that estimate; nothing else is implemented.

## Milestones

| # | Deliverable | Done when |
| --- | --- | --- |
| E0 | Benchmarks and baselines. Scalable families of C\* programs (input bytes, depth, known number of bad inputs) next to the 18 symbolic examples, as RISC-U and RISC-R. btormc, Pono, AVR, rIC3 on rotor's BTOR2 for reachability; unrolling plus an exact counter (Ganak) for counts. Measurement only, no external tool in any check. | `make baselines` writes the table; today's bitr is in it |
| E1 | Count and reference | `make count`: the reference counts 3 of 256 on the division example and agrees with `bitr -bmc -all` on all examples, as RISC-U and RISC-R, natively and on mipster |
| E2 | Counter with the ledger and the SAT switches up to `reduce` | `make ledger`: for every single switch and for all on, the count equals the reference's, zero or not zero equals babysat's and today's CDCL, and the ledger sums to 2^n where there is a partition |
| E3 | Words, unoptimized, then `fold`, `hash`, `cancel`, `row`, `cone` | `make words`: counts on single BTOR2 operators and on one step of the machine models equal the reference's, switch by switch |
| E4 | Checker: unrolling, then `fork`, `incremental` | `make entropy`: `make bmc`'s checks (same bugs, same instruction counts, witnesses replay) plus the counts, for fork thresholds 0 and pc. **Go or no-go for the paper's claim, see below.** |
| E5 | `backward`, `direction`, `invariants`, `-entropy`. Continues M12 from its first result (`make backward`, `make bit-length`), whose tables are the baseline. | `make directions`: forward and backward counts equal where backward finishes; M12's tables and the bit-length table again, with U, H, and conflicts per switch: `cancel` and `row` must bring the RISC-R conflicts to the RISC-U ones forward, and the 8-bit garbage-free loop to an end backward, or the paper says backward does not pay and why |
| E6 | `components`, `cache`, `eliminate`, `bounds`, `emulate`, `merge` | each: its check in E2 to E4 extended, and a line in the ablation table |
| E7 | Message passing as a branching and phase heuristic: integer min-sum on the residual formula at a decision | kept only if it reduces decisions and time on the families; otherwise a paragraph in the paper on why not |
| E8 | Experiments frozen: families, baselines, ablation (every switch off alone, `-O0` where it terminates), artifact | `make paper-tables` regenerates every number in the paper |
| E9 | `entropy.md`, the specification and the lesson, next to `riscr.md`: the principle, each switch with its sentence proven, one running example with ledgers before and after (the division example: 3 of 256, 1.58 of 8 bits) | written with each milestone, as `optimizations.md` is |

After the submission: the identity proof as a count in the new engine, the unbounded methods, `-grid` and `-product` (cellfie returns, with the stutter test), and then today's `tools/bitr.c` retires and the new file takes its name.

## Rules of development

- The design comes first and complete (E1 to E4 at `-O0` plus `propagate`), then one switch per commit. A switch lands with its check: on and off agree with the reference on every instance.
- `-O0` and every single-switch configuration stay runnable forever. They are the correctness oracle and the performance baseline; the ablation table is a by-product.
- Today's bitr is the differential oracle for zero or not zero and for witnesses, and the source of procedures that are known to work (watched literals, first UIP, the normal forms). Rebuilt in the new order, not copied wholesale.
- M5's lesson is a rule here: a cache holds only facts that are true on all paths. For counts this is sharper than for zeros, since a wrong count is silent. The reference and the two directions are the guard.
- The compiler's cost model applies (40 instructions per call on mipster): mipster runs are for checks, native runs for numbers.

## The paper, and what 54 days allow

**Do not claim general SAT or HWMCC performance.** A C\* solver without bit operations does not get within an order of magnitude of Kissat or rIC3, and reviewers will check. Competitive has to mean something bitr can win:

1. **Reachability on machine-code models** (rotor's BTOR2, RISC-U and RISC-R, the scalable families): bitr against BTOR2 model checkers. The lever is the fork threshold and cancellation, not the SAT core. Unknown today: E0 measures it before anything is built.
2. **Counting on the same models** (how many inputs reach the bug): bitr against unrolling plus an exact counter. No BTOR2 checker answers this; this is the likely win.
3. **The executable unification:** some 25 techniques as switches, each count- or zero-preserving, checked by a conservation law, in one self-compiling file. This is the contribution that does not depend on speed.
4. **Reversibility:** cost follows U minus H; compute and uncompute, and history, cost nothing once the word-level rules cancel them. Forward this is a fix that is needed anyway (RISC-R must not cost more conflicts than RISC-U). Backward it is open, and a negative result with a measured reason is still a result.

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
- Chakraborty, Meel, Vardi: A scalable approximate model counter, CP 2013.
- Braunstein, Mézard, Zecchina: Survey propagation, an algorithm for satisfiability, Random Structures and Algorithms 2005.
- Niemetz, Preiner, Reynolds, Barrett, Tinelli: Solving quantified bit-vectors using invertibility conditions, CAV 2018.
- Kuznetsov, Kinder, Bucur, Candea: Efficient state merging in symbolic execution, PLDI 2012.
- Markov, Shi: Simulating quantum computation by contracting tensor networks, SIAM Journal on Computing 2008.
- Brassard, Høyer, Mosca, Tapp: Quantum amplitude amplification and estimation, 2002.
