# Introductory Exercises

## The following information is shared via the course's slack channel.

- Lectures and tutorials
- Recordings
- Class schedule
- The exam

## Important:

The introductory class has no graded assignments. What it has is one set of recommended exercises per week, listed below, and an exam at the end of the semester that draws on these exercises and on nothing else. Every exam question has the shape of one of them: place a number on the axis, build a diagonal, say what a self-check proves, sort text from behaviour, name the outside check. Doing the exercises every week is the preparation; there is no other. Each week also ends with a piece of music to listen to after studying the material, a symphony from Beethoven, Brahms, Mahler, Bruckner, Mozart or Dvořák, once Kraftwerk, and Bach's Goldberg Variations where they fit, and two things to read, a book for everyone and a paper for the ones who want the source. Neither is on the exam.

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

Listen, after this week: [Beethoven · Symphony No. 3 “Eroica”](https://www.youtube.com/watch?v=RkP33esCi5g), Bernstein, Vienna Philharmonic. A symphony that invented a new language for the form — twice the length of anything before it, and every later symphony is written in the language it made. The definition, in E flat.

Read, after this week: [Gödel, Escher, Bach](https://en.wikipedia.org/wiki/G%C3%B6del,_Escher,_Bach), Hofstadter, 1979: Gödel, Bach and Escher as three renderings of one loop, the book this class’s spine grew out of. And, more technical, [On the cruelty of really teaching computing science](https://www.cs.utexas.edu/~EWD/transcriptions/EWD10xx/EWD1036.html), Dijkstra, 1988: why the small steps are not optional.

## Week 2: Size

Small, vast, then two sizes of endless: the axis the whole class walks along.

1. Read the Size chapter up to *Numbers*, and Borges's *Library of Babel*.
2. Rerun `./selfie -c selfie.c`. Where on the map do 365,784 characters sit? And 43,492 instructions? And the machine's state count?
3. How many bits do you need for a thousand states? A million? Every person alive? Every atom in the Earth (about 10^50)?
4. A "512 GB" phone: how many GiB does it report, and why?
5. Find three anchors of your own for a million, a billion, and a trillion, of anything.

Listen, after this week: [Beethoven · Symphony No. 5](https://www.youtube.com/watch?v=PNpyRBVTavQ), Carlos Kleiber, Vienna Philharmonic, 1974. Four notes, and the whole first movement — the whole symphony — is built from them. Small to vast in one line. Then watch Leonard Bernstein explain the first movement [on YouTube](https://www.youtube.com/watch?v=mu2HJerMp8A) on the 1954 Omnibus broadcast: how Beethoven found the notation he needed, one rejected sketch at a time.

Read, after this week: [One Two Three… Infinity](https://en.wikipedia.org/wiki/One_Two_Three..._Infinity), Gamow, 1947: from counting to the sizes of endless, by a physicist who could draw. And, more technical, [Mathematics and Computer Science: Coping with Finiteness](https://doi.org/10.1126/science.194.4271.1235), Knuth, 1976: numbers so large that finite stops meaning small.

## Week 3: Everything is Bits

Numbers, negative numbers, overflow, characters, text, files, code: the same 85 in five notations.

1. Read the Size chapter from *Numbers* to *Code*.
2. Write 42, 255, and 1000 in binary and hexadecimal. Add 85 and 42 in binary with carries.
3. What is 1010101 as a signed 7-bit number? What is 11111111 as an unsigned and as a signed byte?
4. Write your first name in ASCII, in binary, and count the bits. Then in UTF-8 if it has an umlaut.
5. Run `examples/overflows.c` and explain each line of output.
6. In the pointers figure of the book, what happens if the byte at address 0 held 7 instead of 85?

Listen, after this week: [Mozart · Symphony No. 40 in G minor](https://www.youtube.com/watch?v=z_4jMxbwmVc), Harnoncourt, Concentus Musicus. One two-note sigh, the smallest unit, and the whole first movement is that figure at different positions. Everything is bits, in G minor.

Read, after this week: [Code: The Hidden Language of Computer Hardware and Software](https://en.wikipedia.org/wiki/Code:_The_Hidden_Language_of_Computer_Hardware_and_Software), Petzold, second edition 2022: from flashlights and Morse code to a working computer, one bit at a time. And, more technical, [A Mathematical Theory of Communication](https://doi.org/10.1002/j.1538-7305.1948.tb01338.x), Shannon, 1948: where the bit got its name.

## Week 4: Notation

Formal languages: EBNF, and the two languages selfie is made of, C\* with seven keywords and RISC-U with fourteen instructions.

1. Read the Notation chapter: C\*, RISC-U, EBNF.
2. Write the EBNF rule for a C\* character literal, and for a string literal. Check against `grammar.md`.
3. Derive `c = c + 1;` from the grammar, rule by rule, starting at `statement`.
4. Type `tiny.c` from the book, compile it with `-S`, and find the nine instructions of the loop. Change 7 to 700 and see which bits change.
5. Write a regular expression for the dates of this course, and an EBNF grammar for nested parentheses. Which of the two needs the stack?

Listen, after this week: [Mozart · Symphony No. 41 “Jupiter”](https://www.youtube.com/watch?v=qB7g_Y3LvbU), Böhm, Vienna Philharmonic, 1979. The finale: a four-note motif and four other themes, combined by the rules of counterpoint in every way the rules allow. A grammar, derived to the end.

Read, after this week: [Introduction to the Theory of Computation](https://en.wikipedia.org/wiki/Introduction_to_the_Theory_of_Computation), Sipser: regular and context-free languages done properly, chapters 1 and 2. And, more technical, [What can we do about the unnecessary diversity of notation for syntactic definitions?](https://doi.org/10.1145/359863.359883), Wirth, 1977: the one page that gave us EBNF.

## Week 5: Countability

Everything you can write down can be listed, so every program has a number, and a binary is one number, 188,392 bytes long.

1. Read the Meaning chapter up to *Give every text a number*, and the Selfie chapter's three commands.
2. Write down the first sixteen strings over {0, 1} in the order of the enumeration. Where is 1011? What is at position 100?
3. Gödel-number the string `c = 7;` by writing its ASCII codes one after the other. Then decode 99611032611032555559.
4. Run `make self-self-check` and time it. Roughly how many instructions did the emulator execute? The output tells you.
5. Pair the natural numbers with the integers, negative ones included. Then with the fractions, if you dare.

Listen, after this week: [Bach · Goldberg Variations](https://www.youtube.com/watch?v=p4yAB37wG5s), Glenn Gould, 1981. Thirty variations on one bass line, enumerated: every third one is a canon, at the unison, then the second, then the third, up to the ninth. Then the aria again, the same text at the end of the list. Countability you can hear.

Read, after this week: [Infinity and the Mind](https://en.wikipedia.org/wiki/Infinity_and_the_Mind), Rucker, 1982: Cantor’s paradise for the general reader, with Gödel in person. And, more technical, [On Formally Undecidable Propositions](https://en.wikipedia.org/wiki/On_Formally_Undecidable_Propositions_of_Principia_Mathematica_and_Related_Systems), Gödel, 1931, in the Dover translation: the numbering of every text is on its first pages.

## Week 6: The Machine

RISC-U, code and data in one memory, and the emulator that runs every program written for it, including itself.

1. Read the Machine chapter: Model, Processor, Memory, Instructions, Emulation.
2. Trace `tiny.c` with `-d 1` and find the nine loop instructions executing seven times. How many lines does the loop take in total?
3. For each of the fourteen instructions, write one sentence saying what it does, without looking.
4. Where in memory does `c` live? Find its address in the trace, and find the store that writes 7 into it.
5. Run self-execution and time it against running selfie directly. Estimate the factor.

Listen, after this week: [Kraftwerk · First Techno](https://www.youtube.com/watch?v=hWUiLJnEYJI&t=34s), Hütter and Schneider, live on West German television, 1970, before the word existed. Two men, oscillators, a rhythm machine and a flute: the machine as an instrument that plays itself, and everything with a four-on-the-floor beat since, from Detroit to Berlin, descends from this room. Then *Die Mensch-Maschine*, 1978, and *Computerwelt*, 1981, when the machine got a face and a voice. The machine week has its own music.

Read, after this week: [The RISC-V Instruction Set Manual](https://riscv.org/technical/specifications/), volume I: the fourteen instructions, and the other hundred or so, from the source. And, more technical, [First Draft of a Report on the EDVAC](https://en.wikipedia.org/wiki/First_Draft_of_a_Report_on_the_EDVAC), von Neumann, 1945: code and data in one memory, proposed.

## Week 7: Uncountability

The diagonal, twice. Programs are countable; what programs do is not.

1. Read the Meaning chapter from *What we want to talk about is not* to *Syntax and semantics*.
2. Make up six subsets of {1, …, 6} as answer sheets and build the diagonal D by hand. Check that it differs from every row.
3. Run the decimal version on a list of six decimals of your own. Then explain, in one sentence, why the fractions escape the argument.
4. How many programs of at most 1,000 characters are there over an alphabet of 100 symbols? How many behaviours on inputs 1 to 1,000 are there? Which number is bigger, and by how much?
5. Find one new notation from your own life, a recipe format, chess notation, a knitting pattern, and say what it made sayable.

Listen, after this week: [Bruckner · Symphony No. 7](https://www.youtube.com/watch?v=PvCUHLQx2uM), Karajan, Vienna Philharmonic, 1989. The Adagio, written as Wagner lay dying: endlessness that comes in sizes. Bruckner’s time does not tick, it expands, and the climax arrives the way the diagonal does — from outside every row.

Read, after this week: [Everything and More: A Compact History of ∞](https://en.wikipedia.org/wiki/Everything_and_More_(book)), Wallace, 2003: the infinite by a novelist who did the mathematics. And, more technical, [Cantor’s diagonal argument](https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument), 1891, four pages; the article has the construction and the reference to the original.

## Week 8: Self-Reference I

A compiler defines the meaning of the language it is written in; the fixed point, what Ken Thompson says it cannot prove, and Gödel's two theorems with the same diagonal.

1. Read the Meaning chapter from *Syntax and Semantics* to *Trusting Trust*, and the two station callouts in the Programming chapter.
2. Read Thompson's lecture. It is three pages. Write down, in one sentence, what an outside check for it looks like.
3. Run `make self-self-check` once more. Then state, in one sentence each, what the identical binaries prove and what they do not.
4. Write three C\* programs: one with a syntax error, one with a type warning, one that divides by zero at runtime. Say for each whether the compiler could have known.
5. In your own words: why is a dictionary written in the language it defines a problem in English and not in C\*?

Listen, after this week: [Mahler · Symphony No. 5](https://www.youtube.com/watch?v=9KSESLJ0LWA), Bernstein, Vienna Philharmonic. The finale takes the Adagietto’s own theme as its input and runs it as a fugue subject: a symphony compiling itself. Whether what comes out is the same piece is this week’s question.

Read, after this week: [Gödel’s Proof](https://nyupress.org/9780814758373/godels-proof/), Nagel and Newman, 1958: the incompleteness theorems in a hundred pages, still the clearest short account. And, more technical, [Reflections on Trusting Trust](https://doi.org/10.1145/358198.358210), Thompson, 1984: three pages, read them twice.

## Week 9: Self-Reference II

Will this program ever stop? No program can always tell. Then the same move run forwards, one machine that can be any machine, and Rice's theorem.

1. Read the Meaning chapter from *The Machine, and What It Cannot Decide* to the end.
2. Write, in C\*, the wrapper D for a hypothetical H. Then explain in one paragraph why no change to mipster could make it print "this program never halts" for all such programs.
3. Sort into text and behaviour: uses the keyword `while`; ever executes the `while` loop; contains the character `/`; ever divides by zero; is longer than 100 lines; prints the same as another program. Which can starc decide?
4. Name one approximation for each of: is it free of infinite loops; is it safe; is it correct. Say what each gives up.
5. Find the penumbra in a rule you live under: a house rule, a traffic rule, a grading rule.

Listen, after this week: [Beethoven · Symphony No. 9](https://www.youtube.com/watch?v=Hn0IS-vlwCI), Bernstein, Berlin, Christmas 1989. The finale replays each earlier movement and rejects it — “O Freunde, nicht diese Töne!” — a symphony that asks about itself before it answers. Then the universal machine: everybody sings. Bernstein conducted it in Berlin six weeks after the Wall fell, with Freiheit for Freude.

Read, after this week: [Die Verwandlung](https://www.gutenberg.org/ebooks/22367), Kafka, Prague, 1915: Gregor Samsa wakes up as something else, and everyone around him reads the text and misses the meaning. The week’s lesson, told twenty years before Turing proved it. And, more technical, [On Computable Numbers, with an Application to the Entscheidungsproblem](https://doi.org/10.1112/plms/s2-42.1.230), Turing, 1936: the machine, the universal machine and the halting problem in thirty-six pages; [The Annotated Turing](https://en.wikipedia.org/wiki/The_Annotated_Turing) by Petzold explains every paragraph.

## Week 10: Systems

Two ways to build an operating system, why they are the same, why virtualization is used anyway, and the loop at its centre.

1. Read the Computing chapter's opening, *Emulation*, *Virtualization*, and *Self-Reference*.
2. Run `make emu`, `make emu-emu`, `make os-emu`. Write down the guest's instruction count and the host's for each, and compute the factors.
3. Run `make self-emu` and `make self-os-emu` if your machine has the time, and compute the overhead on real work.
4. Say in one paragraph why an operating system by emulation has no self-reference and one by virtualization does.
5. Name the outside check in each of: Thompson's compiler, Gödel's second theorem, the trusted computing base.

Listen, after this week: [Dvořák · Symphony No. 9 “From the New World”](https://www.youtube.com/watch?v=scGXNcAjeXc), Karel Ančerl, Czech Philharmonic. Written in New York by a Bohemian: American spirituals and the songs of the plains, hosted on a Bohemian machine, and the guest cannot tell which orchestra it is running on. Emulation and virtualization, in E minor, and the Largo went home and became a folk song.

Read, after this week: [Operating Systems: Principles and Practice](https://ospp.cs.washington.edu/), Anderson and Dahlin: the kernel as this class sees it, from processes to virtual machines. And, more technical, [Formal Requirements for Virtualizable Third Generation Architectures](https://doi.org/10.1145/361011.361073), Popek and Goldberg, 1974: the theorem that says which machines can be virtualized.

## Week 11: Cost

A question with a guaranteed answer you will never receive; hard to find, easy to check; a SAT solver in 400 lines; and every step that forgets costs energy.

1. Read the Cost chapter up to *Models of Machines*.
2. Check by hand that −1 −2 3 4 satisfies every clause of `rivest.cnf`. Add the eighth clause `1 2 -3 0` back and show that nothing satisfies all eight.
3. Write a CNF file of your own with five variables and run `babysat` on it. Then one with twenty-five, and time it.
4. How many years to try 2^60 assignments at a billion per second? At a trillion?
5. Compute the minimum energy to erase 8 GB once, by Landauer, and compare it with a phone battery, about 4 × 10^4 joules.

Listen, after this week: [Mahler · Symphony No. 6 “Tragic”](https://www.youtube.com/watch?v=BSY7qYLG4Y0), Bernstein, Vienna Philharmonic. Eighty minutes of a budget being spent. The hammer blows of the finale are the bound, and the last one is not struck. Every step that forgets costs something.

Read, after this week: [The Golden Ticket: P, NP, and the Search for the Impossible](https://en.wikipedia.org/wiki/The_Golden_Ticket), Fortnow, 2013: what would follow if P were NP, for anyone. And, more technical, [The complexity of theorem-proving procedures](https://doi.org/10.1145/800157.805047), Cook, 1971: the paper that made SAT the first hard problem.

## Week 12: Formal Methods

Machine code in, formula out, solver next. Rotor turns a program into a formula, and bitme finds the input that makes it divide by zero, within a bound.

1. Read the Cost chapter from *Models of Machines* to the end.
2. Generate the rotor model of `examples/symbolic/simple-if-else-1-35.c` and count its state, init, next and bad lines.
3. Run bitme on it with a bound of 100 and report which bad states are reachable and with what input.
4. Change the bound to 20 and explain what a report of no bad state now means and does not mean.
5. Write a C\* program of your own with a bug that only one input triggers, and let the solver find the input.

Listen, after this week: [Brahms · Symphony No. 4](https://www.youtube.com/watch?v=l9dGLYJE05Y), Carlos Kleiber, Bavarian State Orchestra, 1996. The finale is a passacaglia: an eight-bar formula stated once, then thirty variations checked against it, every one within the bound, none escaping. Bounded model checking in E minor.

Read, after this week: [Model Checking](https://mitpress.mit.edu/9780262038836/model-checking/), Clarke, Grumberg, Kroening, Peled and Veith, second edition 2018: the textbook, from temporal logic to SAT-based methods. And, more technical, [Symbolic Model Checking without BDDs](https://doi.org/10.1007/3-540-49059-0_14), Biere, Cimatti, Clarke and Zhu, 1999: the paper that invented bounded model checking, the k that bitme runs.

## Week 13: Machines

What a large language model mechanically is, why a hallucination is a proof-shaped object that is not true, and the gate that the machine cannot supply.

1. Read the Machines chapter.
2. Ask a chat bot for a C\* program that reads a number and prints its factorial. Compile it. If it does not compile, note why; if it does, run it on three inputs.
3. Ask the same bot whether its program can divide by zero. Then run rotor and bitme on it with a bound of 500. Say which answer is a certificate.
4. Find a hallucination: an exact page number for a claim in a book you own. Place it in the three regions of the book's figure.
5. Write the four appearances of the one theorem behind the gate, and for each name what came from outside.

Listen, after this week: [Bruckner · Symphony No. 9](https://www.youtube.com/watch?v=ugHoycD1Nd8), Bernstein, Vienna Philharmonic. Unfinished: three movements, and sketches for a fourth. Every completion of the finale since is a proof-shaped object, plausible notation with no way to check it against a meaning Bruckner did not leave. Listen to what is there, and notice where it stops.

Read, after this week: [Artificial Intelligence: A Guide for Thinking Humans](https://en.wikipedia.org/wiki/Artificial_Intelligence:_A_Guide_for_Thinking_Humans), Mitchell, 2019: what the machines do and do not do, without hype. And, more technical, [Attention Is All You Need](https://arxiv.org/abs/1706.03762), Vaswani et al., 2017: the architecture, fifteen pages.

## Week 14: So, What is Intelligence?

The definition, its two halves, why depth still matters, and what computer science is. Then the exam.

1. Read the Intelligence chapter.
2. Write the six habits of the last lecture in your own words, one sentence each, with one example from your own life for each.
3. Go back through weeks 2 to 13 and, for each week, write the one exercise you would put on the exam, and its answer.
4. State the book's definition of intelligence from memory. Then say, in one paragraph, what it makes of a machine that produces notation without a semantics.

Listen, after this week: [Mahler · Symphony No. 9](https://www.youtube.com/watch?v=D4o2SBWUH0s), Bernstein, Vienna Philharmonic, 1971. The last movement ends ersterbend, dying away: the notation thins until the page is nearly empty and the meaning is not. Geist, not Technik. And for the road, Bach’s Goldberg Variations once more [on YouTube](https://www.youtube.com/watch?v=p4yAB37wG5s) — the aria returns unchanged, and you are not.

Read, after this week: [How to Solve It](https://en.wikipedia.org/wiki/How_to_Solve_It), Pólya, 1945: heuristics for finding truth before you can prove it, which is the definition in practice. And, more technical, [Computing Machinery and Intelligence](https://doi.org/10.1093/mind/LIX.236.433), Turing, 1950: the question, asked first, and better than most since.
