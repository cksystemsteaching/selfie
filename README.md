# Selfie

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

[Selfie](http://selfie.cs.uni-salzburg.at)

The Selfie Project provides an educational platform for teaching
undergraduate and graduate students the design and implementation
of programming languages and runtime systems. The focus is on the
construction of compilers, libraries, operating systems, and even
virtual machine monitors. The common theme is to identify and
resolve self-reference in systems code which is seen as the key
challenge when teaching systems engineering, hence the name.

Selfie is a fully self-referential 4k-line C implementation of:

1. a self-compiling compiler called cstarc that compiles
   a tiny but powerful subset of C called C Star (C*) to
   a tiny but powerful subset of MIPS32 called MIPSter,
2. a self-executing emulator called mipster that executes
   MIPSter code including itself when compiled with cstarc, and
3. a tiny C* library called libcstar utilized by cstarc and mipster.
 
Selfie is kept minimal for simplicity and implemented in a single file.
There is no linker, assembler, or debugger. However, there is minimal
operating system support in the form of MIPS32 o32 system calls built
into the emulator. Selfie is meant to be extended in numerous ways.

C* is a tiny Turing-complete subset of C that includes dereferencing
(the * operator) but excludes data structures, Boolean expressions, and
many other features. There are only signed 32-bit integers and pointers,
and character constants for constructing word-aligned strings manually.
This choice turns out to be helpful for students to understand the
true role of composite data structures such as arrays and records.
Bitwise operations are implemented in libcstar using signed integer
arithmetics helping students gain true understanding of two's complement.
C* is supposed to be close to the minimum necessary for implementing
a self-compiling, single-pass, recursive-descent compiler. C* can be
taught in around two weeks of classes depending on student background.

The compiler can readily be extended to compile features missing in C*
and to improve performance of the generated code. The compiler generates
MIPSter executables that can directly be executed by the emulator or
written to a file in a simple, custom-defined format. Support of standard
MIPS32 ELF binaries should be easy but remains future work.

MIPSter is a tiny Turing-complete subset of the MIPS32 instruction set.
It only features arithmetic, memory, and control-flow instructions but
neither bitwise nor byte-level instructions. MIPSter can be properly
explained in a single week of classes.

The emulator implements minimal operating system support that is meant
to be extended by students, first as part of the emulator, and then
ported to run on top of it, similar to an actual operating system or
virtual machine monitor. The fact that the emulator can execute itself
helps exposing the self-referential nature of that challenge.

Selfie is the result of many years of teaching systems engineering
inspired by the work of Professor Niklaus Wirth from ETH Zurich.