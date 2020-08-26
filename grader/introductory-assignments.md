# Introduction to Operating Systems - Tutorial

## Description

Creation of simple exercises for first semester students based on the Selfie System.


## Tasks

- [ ] Description of simple exercises
- [ ] Development of simple code examples
- [ ] Development of assistance
- [ ] Development of an evaluation scheme


## Resources

- [rust-lang.org](https://www.rust-lang.org/learn)
- [rust-lang.org - Book](https://doc.rust-lang.org/book/title-page.html)
- [Rust by Example - interactive Tutorial](https://doc.rust-lang.org/stable/rust-by-example/index.html)

---

# Ideas - work in progress

## 0) Preface

- Introduce the exercises for IOS
- How to use git (clone, pull, private repo, branch, like the readme for CC), selfie, grader
- Step by step explanation

## 1) Introduction

### Exercise 1:

TODO: detailed description of the exercise

**Description of the exercise:**

A C\* code file that prints the value of 4GB into MB, KB.

TODO: insert code example

```c
// code template with the print statements for MB and KB
// the code template is available in the repo
// you can extend the code template and grade it with your solution
```

TODO: detailed description of the task

**Task:**

Extend the code template to also print byte and bit values of 4GB.

**Goal:**

Show the states of the machine.

## 2) Architecture

### Exercise 1:

- binary arithmetics, calculate by hand and put the result into the exercise file, see output and grade, unsigned, only positive values? decimal to binary by hand and solution into file

### Exercise 2:

- convert binary, octa, hexadecimal, decimal


## 3) Architecture 2

### Exercise 1:

- search [cpubitwidth](../selfie.c#L209), [numberofregisters](../selfie.c#L703), [registersize](../selfie.c#L1074), [virtualmemorysize](../selfie.c#L1068), [wordsize](../selfie.c#L1070-L1071) etc in the selfie.c file. Then enter them in the C\* assignment file or describe it.


## 4) Tools

- Take the print-my-name.c file and change the output from "Hello World!" to "This is \<firstname\> \<lastname\>’s Selfie", and grade it with self.py

## 5) RISC-V & ISA

- Change the assembly code template to ???, write simple things yourself ???

## 6) Programming Languages

- Create meaning (Semantics) of the PL
- fill in hello-world.c template file
- Compile hello-world.c and output a binary file and an assembly file, inspect the assembly file

## 7) Semantics & Syntax

- Search atoi code in selfie.c file, insert it into new file and do something with it.
- Search itoa code in selfie.c file, insert it into new file and do something with it.
- write the string "Hello World!    " as hexadecimal or binary via ASCII table. [ASCII-Table](https://en.wikipedia.org/wiki/ASCII)
- Resource: grammar.md (EBNF)
- declaration, definition of a global variable
- procedure

## 8) Finite state machine (FSM) - Scanner

- `get_character()`, `find_next_character()` fill in the blanks via selfie.c file
- syntactically valid symbols? (sequence of characters), `get_symbol()`
- EBNF, regular expressions

## 9) Pushdown automata (PDA) - Parser

- Debug C\* file for missing `(,),{,}, etc.` (syntax)
- context free grammar
- Write a syntactically valid program that counts from 10 to 0
- compile C\* file and execute it on emulator

## 10) Virtual Memory

- stack, heap, program break, data segment, code segment, program counter, stack pointer, frame pointer
- pages, page table size?

## 11) Virtualization

- create virtual version of hardware
- hypervisor

