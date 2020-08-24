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

## Ideas - work in progress

1) Introduction
- convert binary, octa, hexadecimal, decimal

2) Architecture
- search [cpubitwidth](../selfie.c#L209), [numberofregisters](../selfie.c#L703), [registersize](../selfie.c#L1074), [virtualmemorysize](../selfie.c#L1068), [wordsize](../selfie.c#L1070-L1071) etc in the selfie.c file. Then enter them in the C\* assignment file or describe it.

3) RISC-V & ISA
- blueprint for assembly code, write simple things yourself

4) Programming Languages
- fill in hello-world.c blueprint file

5) Semantics & Syntax
- atoi, itoa, ascii
- write the string "Hello World!    " as hexadecimal or binary via ASCII table. [ASCII-Table](https://en.wikipedia.org/wiki/ASCII)
- compiler, emulator
- reading machine code (assembly)

6) Finite state machine (FSM) - Scanner
- get_character(), find_next_character() fill in the blanks via selfie.c file

7) Pushdown automata (PDA) - Parser
- write EBNF grammar

8) Virtual Memory
- stack, heap, program break, data segment, code segment, program counter, stack pointer, frame pointer

9) Virtualization
- hypervisor
