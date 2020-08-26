# Compiler Assignments

## This information is shared via the course's slack channel.

- Lectures and tutorials
- Recordings
- Submitting homework
- Class schedule

## Important:

Always submit something for any assignment by the due date and time, even if you have not done anything.
In that case, your self-grade is 5. If you fail to submit anything on time you will be failed (unless you provide proof of a medical or family emergency in a DM to me, no email please!).

## Essential for every assignment.

Use the autograder to determine your grade. See the grader [README.md](https://github.com/cksystemsteaching/selfie/blob/master/grader/README.md) file for instructions.

## Assignment #0:

Modify **selfie.c** such that selfie prints your name right after initialization.
Part of the assignment is to figure out how to do that.

- Do not modify any files other than **selfie.c**.

The assignment is called `print-your-name`.

## Assignment #1:

Implement support of hexadecimal integer literals.

- Do not modify any files other than **selfie.c**.

The assignment is called `hex-literal`.

## Assignment #2:

Implement support of bitwise shift operators `<<` and `>>` in C\*.

- Before coding, extend the C\* grammar such that both operators have proper precedence as in C.
- Do not modify any files other than **grammar.md** and **selfie.c**.

The assignment is called `bitwise-shift-compilation`.

## Assignment #3:

Implement code generation for bitwise shift operators `<<` and `>>` in C\* and support of bitwise shift instructions `sll` and `srl` in RISC-U using `<<` and `>>`, respectively.

- Before coding, extend the RISC-U ISA in **riscu.md** with `sll` and `srl` assembly and semantics.
- Do not modify any files other than **riscu.md** and **selfie.c**.

The assignment is called `bitwise-shift-execution`.

## Assignment #4:

Implement code generation for bitwise logical operators `&`, `|`, and `~` in C\* and support of bitwise logical instructions `and`, `or`, and `xori` in RISC-U using `&`, `|`, and `~`.

- Before coding, extend the grammar in **grammar.md** with `&`, `|`, and `~` and the RISC-U ISA in **riscu.md** with `and`, `or`, and `xori` assembly and semantics.
- Do not modify any files other than **grammar.md**, **riscu.md**, and **selfie.c**.

The assignment is called `bitwise-and-or-not`.

## Assignment #5:

Implement support of and code generation for one-dimensional arrays in C\* with the symbols `[` and `]`.

- Before coding, extend the grammar in **grammar.md** to include `[` and `]`.
- Do not modify any files other than **grammar.md** and **selfie.c**.

The assignment is called `array`.

## Assignment #6:

Implement support of and code generation for multi-dimensional arrays in C\* with the symbols `[` and `]`.

- Before coding, extend the grammar in **grammar.md** to include `[` and `]`.
- Do not modify any files other than **grammar.md** and **selfie.c**.

The assignment is called `array-multidimensional`.

## Assignment #7:

Implement support of and code generation for struct declarations in C\*.

- Before coding, extend the grammar in **grammar.md** accordingly.
- Do not modify any files other than **grammar.md** and **selfie.c**.

The assignment is called `struct-declaration`.

## Assignment #8:

Implement support of and code generation for struct access in C\*.

- Before coding, extend the grammar in **grammar.md** accordingly.
- Do not modify any files other than **grammar.md** and **selfie.c**.

The assignment is called `struct-execution`.

## Assignment #9:

Implement support of and code generation for for loops in C\*.

- Before coding, extend the grammar in **grammar.md** accordingly.
- Do not modify any files other than **grammar.md** and **selfie.c**.

The assignment is `called for-loop`.
