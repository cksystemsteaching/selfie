# Introductory Exercises

## The following information is shared via the course's slack channel.

- Lectures and tutorials
- Recordings
- Class schedule
- The exam

## Important:

The introductory class has no graded assignments. What it has is one set of recommended exercises per week, listed below, and an exam at the end of the semester that draws on these exercises and on nothing else. Every exam question has the shape of one of them: place a number on the axis, build a diagonal, say what a self-check proves, sort text from behaviour, name the outside check. Doing the exercises every week is the preparation; there is no other.

The exercises follow the fourteen lectures, whose slides are at [docs/classes/ics](../docs/classes/ics/), and the book [*What is Intelligence?*](../book/README.md), one chapter section at a time. Where an exercise says *run*, it means run selfie yourself, in a terminal, and read what it prints. Where it says *write*, it means on paper, in a language with a semantics, so that someone else could check it.

Students who want more can do the first assignments of the [compiler](compiler-assignments.md) and [systems](systems-assignments.md) classes, starting with `print-your-name`; the [autograder](../grader/README.md) grades them for you. They are not part of this class.

## Essential for every week

Have selfie installed and built; see the [README](../README.md). Every week's exercises use it.

> Read the section first, then do the exercises, then read it again.

## Week 1: What is Intelligence?

The talk, and the purpose of the class: a deep understanding of basic computer science principles, deep enough to position generative AI, and whatever comes next, properly.

1. Get a terminal. Every laptop has one; if you only have a browser, the repository's README shows the cloud option.
2. Download selfie from `github.com/cksystemsteaching/selfie` and type `make` in its directory. You need a C compiler; the README says which.
3. Type `./selfie`. It answers with its synopsis, one line, in a formal language. Bring that line to week 2.
4. Read the introduction of the book, and the Selfie chapter, and type the two commands in it.

## Week 2: Size

Small, vast, then two sizes of endless: the axis the whole class walks along.

1. Read the Size chapter up to *Numbers*, and Borges's *Library of Babel*.
2. Rerun `./selfie -c selfie.c`. Where on the map do 365,784 characters sit? And 43,492 instructions? And the machine's state count?
3. How many bits do you need for a thousand states? A million? Every person alive? Every atom in the Earth (about 10^50)?
4. A "512 GB" phone: how many GiB does it report, and why?
5. Find three anchors of your own for a million, a billion, and a trillion, of anything.

## Week 3: Everything is Bits

Numbers, negative numbers, overflow, characters, text, files, code: the same 85 in five notations.

1. Read the Size chapter from *Numbers* to *Code*.
2. Write 42, 255, and 1000 in binary and hexadecimal. Add 85 and 42 in binary with carries.
3. What is 1010101 as a signed 7-bit number? What is 11111111 as an unsigned and as a signed byte?
4. Write your first name in ASCII, in binary, and count the bits. Then in UTF-8 if it has an umlaut.
5. Run `examples/overflows.c` and explain each line of output.
6. In the pointers figure of the book, what happens if the byte at address 0 held 7 instead of 85?

## Week 4: Notation

Formal languages: EBNF, and the two languages selfie is made of, C\* with seven keywords and RISC-U with fourteen instructions.

1. Read the Notation chapter: C\*, RISC-U, EBNF.
2. Write the EBNF rule for a C\* character literal, and for a string literal. Check against `grammar.md`.
3. Derive `c = c + 1;` from the grammar, rule by rule, starting at `statement`.
4. Type `tiny.c` from the book, compile it with `-S`, and find the nine instructions of the loop. Change 7 to 700 and see which bits change.
5. Write a regular expression for the dates of this course, and an EBNF grammar for nested parentheses. Which of the two needs the stack?

## Week 5: Countability

Everything you can write down can be listed, so every program has a number, and a binary is one number, 188,392 bytes long.

1. Read the Meaning chapter up to *Give every text a number*, and the Selfie chapter's three commands.
2. Write down the first sixteen strings over {0, 1} in the order of the enumeration. Where is 1011? What is at position 100?
3. Gödel-number the string `c = 7;` by writing its ASCII codes one after the other. Then decode 99611032611032555559.
4. Run `make self-self-check` and time it. Roughly how many instructions did the emulator execute? The output tells you.
5. Pair the natural numbers with the integers, negative ones included. Then with the fractions, if you dare.

## Week 6: The Machine

RISC-U, code and data in one memory, and the emulator that runs every program written for it, including itself.

1. Read the Machine chapter: Model, Processor, Memory, Instructions, Emulation.
2. Trace `tiny.c` with `-d 1` and find the nine loop instructions executing seven times. How many lines does the loop take in total?
3. For each of the fourteen instructions, write one sentence saying what it does, without looking.
4. Where in memory does `c` live? Find its address in the trace, and find the store that writes 7 into it.
5. Run self-execution and time it against running selfie directly. Estimate the factor.

## Week 7: Uncountability

The diagonal, twice. Programs are countable; what programs do is not.

1. Read the Meaning chapter from *What we want to talk about is not* to *Syntax and semantics*.
2. Make up six subsets of {1, …, 6} as answer sheets and build the diagonal D by hand. Check that it differs from every row.
3. Run the decimal version on a list of six decimals of your own. Then explain, in one sentence, why the fractions escape the argument.
4. How many programs of at most 1,000 characters are there over an alphabet of 100 symbols? How many behaviours on inputs 1 to 1,000 are there? Which number is bigger, and by how much?
5. Find one new notation from your own life, a recipe format, chess notation, a knitting pattern, and say what it made sayable.

## Week 8: Self-Reference I

A compiler defines the meaning of the language it is written in; the fixed point, what Ken Thompson says it cannot prove, and Gödel's two theorems with the same diagonal.

1. Read the Meaning chapter from *Syntax and Semantics* to *Trusting Trust*, and the two station callouts in the Programming chapter.
2. Read Thompson's lecture. It is three pages. Write down, in one sentence, what an outside check for it looks like.
3. Run `make self-self-check` once more. Then state, in one sentence each, what the identical binaries prove and what they do not.
4. Write three C\* programs: one with a syntax error, one with a type warning, one that divides by zero at runtime. Say for each whether the compiler could have known.
5. In your own words: why is a dictionary written in the language it defines a problem in English and not in C\*?

## Week 9: Self-Reference II

Will this program ever stop? No program can always tell. Then the same move run forwards, one machine that can be any machine, and Rice's theorem.

1. Read the Meaning chapter from *The Machine, and What It Cannot Decide* to the end.
2. Write, in C\*, the wrapper D for a hypothetical H. Then explain in one paragraph why no change to mipster could make it print "this program never halts" for all such programs.
3. Sort into text and behaviour: uses the keyword `while`; ever executes the `while` loop; contains the character `/`; ever divides by zero; is longer than 100 lines; prints the same as another program. Which can starc decide?
4. Name one approximation for each of: is it free of infinite loops; is it safe; is it correct. Say what each gives up.
5. Find the penumbra in a rule you live under: a house rule, a traffic rule, a grading rule.

## Week 10: Systems

Two ways to build an operating system, why they are the same, why virtualization is used anyway, and the loop at its centre.

1. Read the Computing chapter's opening, *Emulation*, *Virtualization*, and *Self-Reference*.
2. Run `make emu`, `make emu-emu`, `make os-emu`. Write down the guest's instruction count and the host's for each, and compute the factors.
3. Run `make self-emu` and `make self-os-emu` if your machine has the time, and compute the overhead on real work.
4. Say in one paragraph why an operating system by emulation has no self-reference and one by virtualization does.
5. Name the outside check in each of: Thompson's compiler, Gödel's second theorem, the trusted computing base.

## Week 11: Cost

A question with a guaranteed answer you will never receive; hard to find, easy to check; a SAT solver in 400 lines; and every step that forgets costs energy.

1. Read the Cost chapter up to *Models of Machines*.
2. Check by hand that −1 −2 3 4 satisfies every clause of `rivest.cnf`. Add the eighth clause `1 2 -3 0` back and show that nothing satisfies all eight.
3. Write a CNF file of your own with five variables and run `babysat` on it. Then one with twenty-five, and time it.
4. How many years to try 2^60 assignments at a billion per second? At a trillion?
5. Compute the minimum energy to erase 8 GB once, by Landauer, and compare it with a phone battery, about 4 × 10^4 joules.

## Week 12: Formal Methods

Machine code in, formula out, solver next. Rotor turns a program into a formula, and bitme finds the input that makes it divide by zero, within a bound.

1. Read the Cost chapter from *Models of Machines* to the end.
2. Generate the rotor model of `examples/symbolic/simple-if-else-1-35.c` and count its state, init, next and bad lines.
3. Run bitme on it with a bound of 100 and report which bad states are reachable and with what input.
4. Change the bound to 20 and explain what a report of no bad state now means and does not mean.
5. Write a C\* program of your own with a bug that only one input triggers, and let the solver find the input.

## Week 13: Machines

What a large language model mechanically is, why a hallucination is a proof-shaped object that is not true, and the gate that the machine cannot supply.

1. Read the Machines chapter.
2. Ask a chat bot for a C\* program that reads a number and prints its factorial. Compile it. If it does not compile, note why; if it does, run it on three inputs.
3. Ask the same bot whether its program can divide by zero. Then run rotor and bitme on it with a bound of 500. Say which answer is a certificate.
4. Find a hallucination: an exact page number for a claim in a book you own. Place it in the three regions of the book's figure.
5. Write the four appearances of the one theorem behind the gate, and for each name what came from outside.

## Week 14: So, What is Intelligence?

The definition, its two halves, why depth still matters, and what computer science is. Then the exam.

1. Read the Intelligence chapter.
2. Write the six habits of the last lecture in your own words, one sentence each, with one example from your own life for each.
3. Go back through weeks 2 to 13 and, for each week, write the one exercise you would put on the exam, and its answer.
4. State the book's definition of intelligence from memory. Then say, in one paragraph, what it makes of a machine that produces notation without a semantics.
