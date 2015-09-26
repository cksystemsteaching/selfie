# Selfie

Selfie is a project of the [Computational Systems Group](http://www.cs.uni-salzburg.at/~ck) at the Department of Computer Sciences of the University of Salzburg in Austria.

The Selfie Project provides an educational platform for teaching undergraduate and graduate students the design and implementation of programming languages and runtime systems. The focus is on the construction of compilers, libraries, operating systems, and even virtual machine monitors. The common theme is to identify and resolve self-reference in systems code which is seen as the key challenge when teaching systems engineering, hence the name.

There is a free [book](http://leanpub.com/selfie) in early draft form using selfie even more ambitiously reaching out to everyone with an interest in learning about computer science.

Selfie is a fully self-referential 4k-line C implementation of:

1. a self-compiling compiler called cstarc that compiles a tiny but powerful subset of C called C Star (C\*) to a tiny but powerful subset of MIPS32 called MIPSter,
2. a self-executing emulator called mipster that executes MIPSter code including itself when compiled with cstarc, and
3. a tiny C\* library called libcstar utilized by cstarc and mipster.

Selfie is kept minimal for simplicity and implemented in a single file. There is no linker, assembler, or debugger. However, there is minimal operating system support in the form of MIPS32 o32 system calls built into the emulator. Selfie is meant to be extended in numerous ways.

C\* is a tiny Turing-complete subset of C that includes dereferencing (the \* operator) but excludes data structures, Boolean expressions, and many other features. There are only signed 32-bit integers and pointers, and character constants for constructing word-aligned strings manually. This choice turns out to be helpful for students to understand the true role of composite data structures such as arrays and records. Bitwise operations are implemented in libcstar using signed integer arithmetics helping students gain true understanding of two's complement. C\* is supposed to be close to the minimum necessary for implementing a self-compiling, single-pass, recursive-descent compiler. C\* can be taught in around two weeks of classes depending on student background.

The compiler can readily be extended to compile features missing in C\* and to improve performance of the generated code. The compiler generates MIPSter executables that can directly be executed by the emulator or written to a file in a simple, custom-defined format. Support of standard MIPS32 ELF binaries should be easy but remains future work.

MIPSter is a tiny Turing-complete subset of the MIPS32 instruction set. It only features arithmetic, memory, and control-flow instructions but neither bitwise nor byte-level instructions. MIPSter can be properly explained in a single week of classes.

The emulator implements minimal operating system support that is meant to be extended by students, first as part of the emulator, and then ported to run on top of it, similar to an actual operating system or virtual machine monitor. The fact that the emulator can execute itself helps exposing the self-referential nature of that challenge.

Selfie is the result of many years of teaching systems engineering. The design of the compiler is inspired by the Oberon compiler of Professor Niklaus Wirth from ETH Zurich.

## Build Instructions

### On 32-bit Linux

The first step is to produce a binary that runs on your computer. To do that, use `gcc` in a terminal to compile `selfie.c`:

```bash
$ gcc -o selfie selfie.c
```

This produces an executable called `selfie` which contains both the C\* compiler as well as the MIPSter emulator. Selfie may be invoked as follows:

```bash
./selfie [ -c | -m <memory size in MB> <binary> ]
```

When using `selfie` with the -c option or without any arguments the compiler is invoked. With the -m option the emulator is invoked and configured to create a machine instance with \<memory size in MB\> that loads and executes \<binary\>.

To compile `selfie.c` for MIPSter, use the following commands. Be aware that the compiler requires an empty file called `out` in the current execution directory to write its output to it.

```bash
$ gcc -o selfie selfie.c
$ touch out
$ ./selfie < selfie.c
$ mv out selfie.mips
```

### Self-compilation

Here is an example of how to test self-compilation of `selfie.c`:

```bash
$ gcc -o selfie selfie.c
$ touch out
$ ./selfie -c < selfie.c
$ mv out selfie.mips1
$ touch out
$ ./selfie -m 32 selfie.mips1 < selfie.c
$ mv out selfie.mips2
$ diff -s selfie.mips1 selfie.mips2
Files selfie.mips1 and selfie.mips2 are identical
```

### Self-execution

The following example shows how to test self-execution of `selfie.c`. In this case we invoke the emulator to invoke itself which then invokes the compiler to compile itself:

```bash
$ gcc -o selfie selfie.c
$ touch out
$ ./selfie < selfie.c
$ mv out selfie.mips1
$ touch out
$ ./selfie -m 64 selfie.mips1 -m 32 selfie.mips1 < selfie.c
$ mv out selfie.mips2
$ diff -s selfie.mips1 selfie.mips2
Files selfie.mips1 and selfie.mips2 are identical
```

### Work Flow

To compile any C\* source you may use `selfie` directly or `selfie.mips` on top of the emulator. Both generate identical MIPSter binaries:

```bash
$ gcc -o selfie selfie.c
$ touch out
$ ./selfie < selfie.c
$ mv out selfie.mips
$ touch out
$ ./selfie < any-cstar-file.c
$ mv out any-cstar-file.mips1
$ touch out
$ ./selfie -m 32 selfie.mips < any-cstar-file.c
$ mv out any-cstar-file.mips2
$ diff -s any-cstar-file.mips1 any-cstar-file.mips2
Files any-cstar-file.mips1 and any-cstar-file.mips2 are identical
```

#### Debugging

By default, the boot prompt shows the amount of memory used by the emulator instance and how execution of the binary file terminated (exit code).

You can enable verbose debugging with variables set in `selfie.c`:

 - debug_diassemble: Print disassemble output on the screen
 - debug_registers: Print register content
 - debug_syscalls: Print debugging information on every syscall
 - debug_load: Print hex code of what the emulator loaded

### On Mac OS X / 64-bit Linux

On Mac OS X and 64-bit Linux, you may use the following command to compile `selfie.c`:

```bash
clang -w -m32 -D'main(a, b)=main(int argc, char **argv)' -o selfie selfie.c
```

After that, you can proceed with the same commands as for 32-bit Linux.

The -w option suppresses warnings that can be ignored for now. The -m32 option makes the compiler generate a 32-bit executable. Selfie only supports 32-bit architectures right now. The -D option is needed to bootstrap the main function declaration since the char data type is not supported by selfie. The -o option directs the compiler to call the executable selfie.