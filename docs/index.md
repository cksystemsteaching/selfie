Selfie is a project of the [Computational Systems Group](http://www.cs.uni-salzburg.at/~ck) at the Department of Computer Sciences of the University of Salzburg in Austria.

The Selfie Project provides an educational platform for teaching undergraduate and graduate students the design and implementation of programming languages and runtime systems. The focus is on the construction of compilers, libraries, operating systems, and even virtual machine monitors. The common theme is to identify and resolve self-reference in systems code which is seen as the key challenge when teaching systems engineering, hence the name.

Slides providing an overview of selfie and an introduction to its design and implementation are made available incrementally [here](http://selfie.cs.uni-salzburg.at/slides). There is a free book in early draft form called [Selfie: Computer Science for Everyone](http://leanpub.com/selfie) using selfie even more ambitiously reaching out to everyone with an interest in learning about computer science.

Selfie is a self-contained 64-bit, 10-KLOC C implementation of:

1. a self-compiling compiler called starc that compiles
   a tiny but still fast subset of C called C Star (C*) to
   a tiny and easy-to-teach subset of RISC-V called RISC-U,
2. a self-executing emulator called mipster that executes
   RISC-U code including itself when compiled with starc,
3. a self-hosting hypervisor called hypster that provides
   RISC-U virtual machines that can host all of selfie,
   that is, starc, mipster, and hypster itself,
4. a prototypical symbolic execution engine called monster
   that executes RISC-U code symbolically,
5. a simple SAT solver that reads CNF DIMACS files, and
6. a tiny C* library called libcstar utilized by selfie.

Selfie is implemented in a single (!) file and kept minimal for simplicity. There is also a simple in-memory linker, a RISC-U disassembler, a profiler, and a debugger with replay as well as minimal operating system support in the form of RISC-V system calls built into the emulator.

C* is a tiny Turing-complete subset of C that includes dereferencing (the * operator) but excludes composite data types, bitwise and Boolean operators, and many other features. There are only unsigned 64-bit integers and 64-bit pointers as well as character and string literals. This choice turns out to be helpful for students to understand the true role of composite data types such as arrays and records. Bitwise operations are implemented in libcstar using unsigned integer arithmetics helping students better understand arithmetic operators. C* is supposed to be close to the minimum necessary for implementing a self-compiling, single-pass, recursive-descent compiler. C* can be taught in one to two weeks of classes depending on student background.

The compiler can readily be extended to compile features missing in C* and to improve performance of the generated code. The compiler generates RISC-U executables in ELF format that are compatible with the official RISC-V toolchain. The mipster emulator can execute RISC-U executables loaded from file but also from memory immediately after code generation without going through the file system.

RISC-U is a tiny Turing-complete subset of the RISC-V instruction set. It only features unsigned 64-bit integer arithmetic, double-word memory, and simple control-flow instructions but neither bitwise nor byte- and word-level instructions. RISC-U can be taught in one week of classes.

The emulator implements minimal operating system support that is meant to be extended by students, first as part of the emulator, and then ported to run on top of it, similar to an actual operating system or virtual machine monitor. The fact that the emulator can execute itself helps exposing the self-referential nature of that challenge. In fact, selfie goes one step further by implementing microkernel functionality as part of the emulator and a hypervisor that can run as part of the emulator as well as on top of it, all with the same code.

Selfie is the result of many years of teaching systems engineering. The design of the compiler is inspired by the Oberon compiler of Professor Niklaus Wirth from ETH Zurich. RISC-U is inspired by the RISC-V community around Professor David Patterson from UC Berkeley. The design of the hypervisor is inspired by microkernels of Professor Jochen Liedtke from University of Karlsruhe.