# Compiler Assignments

## The following information is shared via the course's slack channel.

- Lectures and tutorials
- Recordings
- Submitting homework
- Class schedule

## Important:

Always submit something for each assignment by the due date and time, even if you have not done anything. In that case, your self-grade is 5. If you fail to submit anything on time you will be failed (unless you provide proof of a medical or family emergency in a DM to me, no email please!).

## Essential for every assignment

Use the autograder to determine your grade. See the autograder's [README.md](../grader/README.md) for instructions.

> No compiler warnings, please!

## Assignment `print-your-name`:

Modify **selfie.c** such that selfie prints your name right after initialization.
Part of the assignment is to figure out how to do that.

- Do not modify any files other than **selfie.c**.
- Use the `print-your-name` target in the grader to determine your grade.

**Hint**: see [output_processing.py](../grader/lib/output_processing.py)

Your message has to be prefixed like every other "status message" of selfie.
So instead of printing:

`This is <firstname> <lastname>'s Selfie!`, you have to print `<selfiename>: This is <firstname> <lastname>'s Selfie!`



## Assignment `hex-literal`:

Implement support of hexadecimal integer literals.

- Before coding, extend the C\* grammar with hexadecimal integer literals.
- Do not modify any files other than **grammar.md** and **selfie.c**.
- Use the `hex-literal` target in the grader to determine your grade.



## Assignment `bitwise-shift-compilation`:

Implement support of bitwise shift operators `<<` and `>>` in C\*.

- Before coding, extend the C\* grammar such that both operators have proper precedence as in C.
- Do not modify any files other than **grammar.md** and **selfie.c**.
- Use the `bitwise-shift-compilation` target in the grader to determine your grade.



## Assignment `bitwise-shift-execution`:

Implement code generation for bitwise shift operators `<<` and `>>` in C\* and support of bitwise shift instructions `sll` and `srl` in RISC-U using `<<` and `>>`, respectively.

- Before coding, extend the RISC-U ISA in **riscu.md** with `sll` and `srl` assembly and semantics.
- Do not modify any files other than **riscu.md** and **selfie.c**.
- Use the `bitwise-shift-execution` target in the grader to determine your grade.



## Assignment `bitwise-and-or-not`:

Implement code generation for bitwise logical operators `&`, `|`, and `~` in C\* and support of bitwise logical instructions `and`, `or`, and `xori` in RISC-U using `&`, `|`, and `~`.

- Before coding, extend the grammar in **grammar.md** with `&`, `|`, and `~` and the RISC-U ISA in **riscu.md** with `and`, `or`, and `xori` assembly and semantics.
- Do not modify any files other than **grammar.md**, **riscu.md**, and **selfie.c**.
- Use the `bitwise-and-or-not` target in the grader to determine your grade.



## Assignment `logical-and-or-not`:

Implement code generation for Boolean operators `&&`, `||`, and `!` in C\*.

- Before coding, extend the grammar in **grammar.md** accordingly.
- Do not modify any files other than **grammar.md** and **selfie.c**.
- Use the `logical-and-or-not` target in the grader to determine your grade.



## Assignment `for-loop`:

Implement support of and code generation for `for` loops in C\*.

- Before coding, extend the grammar in **grammar.md** accordingly.
- Do not modify any files other than **grammar.md** and **selfie.c**.
- Use the `for-loop` target in the grader to determine your grade.



## Assignment `lazy-evaluation`:

Change the Boolean operators `&&`, `||`, and `!` such that lazy evaluation is used.

- Before coding, extend the grammar in **grammar.md** accordingly.
- Do not modify any files other than **grammar.md** and **selfie.c**.
- Use the `lazy-evaluation` target in the grader to determine your grade.



## Assignment `array-access`:

Implement support of and code generation for array access on heap-allocated arrays through pointers in C\* with the symbols `[` and `]`.

- Before coding, extend the grammar in **grammar.md** to include `[` and `]` for access.
- Do not modify any files other than **grammar.md** and **selfie.c**.
- Use the `array-access` target in the grader to determine your grade.



## Assignment `array-allocation`:

Implement support for allocation of one-dimensional arrays in the data segment (as global variables) and on the stack (as local variables) in C\* with the symbols `[` and `]`.

- Before coding, extend the grammar in **grammar.md** to include `[` and `]` for declaration.
- Do not modify any files other than **grammar.md** and **selfie.c**.
- Use the `array-allocation` target in the grader to determine your grade.


## Assignment `array-multidimensional`:

Implement support of and code generation for multi-dimensional arrays in C\* with the symbols `[` and `]`.

- Before coding, extend the grammar in **grammar.md** to include `[` and `]`.
- Do not modify any files other than **grammar.md** and **selfie.c**.
- Use the `array-multidimensional` target in the grader to determine your grade.



## Assignment `struct-declaration`:

Implement support of and code generation for `struct` declarations in C\* including internal representation of structs in the symbol table.

- Before coding, extend the grammar in **grammar.md** accordingly.
- Do not modify any files other than **grammar.md** and **selfie.c**.
- Use the `struct-declaration` target in the grader to determine your grade.



## Assignment `struct-execution`:

Implement support of and code generation for `struct` access in C\*.

- Before coding, extend the grammar in **grammar.md** accordingly.
- Do not modify any files other than **grammar.md** and **selfie.c**.
- Use the `struct-execution` target in the grader to determine your grade.


## Assignment `rotor-check`:

Turn a model checker on your own language extension. Rotor generates a BTOR2 model of a RISC-U binary; bitme checks, for every input and every path up to a bound, whether a bad state is reachable, and if so reports the input that reaches it.

- Write a C\* program **assignments/rotor-check/program.c** that exercises one of your extensions (a `for` loop, array access, a struct) and reads at least one byte of input with `read`. Keep it small: a few dozen instructions per iteration, so that the solver finishes.
- Write **assignments/rotor-check/property.txt** with exactly these four lines, in this order:

```
bad: <name of a bad state in the model, for example core-0-division-by-zero>
bound: <number of steps, for example 80>
verdict: <reachable or unreachable>
input: <the input bitme found, or none>
```

- Generate the model with `./rotor -c assignments/rotor-check/program.c - 0` and run `tools/bitme.py -kmax <bound> assignments/rotor-check/program-rotorized.btor2`. Do not commit the model; the grader regenerates it under your compiler.
- Do not modify any files other than **selfie.c**, **grammar.md**, and the two files above.
- Use the `rotor-check` target in the grader to determine your grade. It compiles and runs your program, regenerates the model, checks that the named bad state exists in it, and runs bitme with your bound: a *reachable* verdict must be confirmed by a satisfying assignment within the bound, an *unreachable* one by bitme reaching the bound without one. bitme needs a solver; see the [grader README](../grader/README.md).

**Hint**: `./rotor` prints the names of all bad states it generates. Start with the program from the lecture, `examples/symbolic/division-by-zero-3-35.c`, and change one thing at a time.
