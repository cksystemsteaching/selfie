# Selfie [![selfie](https://github.com/cksystemsteaching/selfie/actions/workflows/selfie.yml/badge.svg)](https://github.com/cksystemsteaching/selfie/actions) [![Run on Repl.it](https://replit.com/badge/github/cksystemsteaching/selfie)](https://replit.com/new/github/cksystemsteaching/selfie)

Selfie is a project of the [Computational Systems Group](https://cs.uni-salzburg.at/~ck) at the Department of Computer Sciences of the University of Salzburg in Austria.

The Selfie Project provides an educational platform for teaching undergraduate and graduate students the design and implementation of programming languages and runtime systems. The focus is on the construction of compilers, libraries, operating systems, and virtual machine monitors. The common theme is to identify and resolve self-reference in systems code which is seen as the key challenge when teaching systems engineering, hence the name.

Selfie is a self-contained 64-bit, 12KLOC C implementation of:

1. a self-compiling compiler called starc that compiles a tiny but still fast [subset of C](https://github.com/cksystemsteaching/selfie/blob/main/semantics.md) called C Star ([C\*](https://github.com/cksystemsteaching/selfie/blob/main/grammar.md)) to a tiny and easy-to-teach subset of RISC-V called [RISC-U](https://github.com/cksystemsteaching/selfie/blob/main/riscu.md),
2. a self-executing emulator called mipster that executes RISC-U code including itself when compiled with starc,
3. a self-hosting hypervisor called hypster that provides RISC-U virtual machines that can host all of selfie, that is, starc, mipster, and hypster itself, and
4. a tiny C\* library called libcstar utilized by selfie.

Selfie is implemented in a single (!) file and kept minimal for simplicity. There is also a simple in-memory linker, a RISC-U disassembler, a garbage collector, L1 instruction and data caches, a profiler, and a debugger with replay as well as minimal operating system support in the form of RISC-V system calls built into the emulator and hypervisor. The garbage collector is conservative and even self-collecting. It may operate as library in the same address space as the mutator and/or as part of the emulator in the address space of the kernel.

Selfie generates ELF binaries that run on real [RISC-V hardware](https://www.sifive.com/boards) as well as on [QEMU](https://www.qemu.org) and are compatible with the official [RISC-V](https://riscv.org) toolchain, in particular the [spike emulator](https://github.com/riscv/riscv-isa-sim) and the [pk kernel](https://github.com/riscv/riscv-pk).

Selfie is designed as 64-bit system and requires as such a 64-bit system to run (LP64 data model). However, selfie also compiles on systems that support compiling and executing 32-bit binaries (ILP32 data model). In that case, selfie becomes a 32-bit system that generates and executes 32-bit binaries out-of-the-box. This is possible because the implementation of selfie carefully avoids 32-bit overflows throughout the system.

## Support

1. Slack: Join the conversation in the #selfie channel at [cksystemsteaching.slack.com](https://join.slack.com/t/cksystemsteaching/shared_invite/zt-cp3kb9uq-ACUnAuI8DBdmULQXIjW15A)
2. Slides: There are classroom [slides](https://selfie.cs.uni-salzburg.at/slides) that provide a comprehensive introduction to the design and implementation of selfie.
3. Autograder: There is an [autograder](https://github.com/cksystemsteaching/selfie/blob/main/grader/README.md) with compiler and operating systems assignments.
4. Paper: There is an [Onward! 2017 paper](https://dl.acm.org/doi/10.1145/3133850.3133857) featuring selfie.
5. Book: There is a free book in early draft form based on selfie called [Elementary Computer Science: From Bits and Bytes to the Universality of Computing](https://github.com/ckirsch/book) reaching out to everyone with an interest in learning about computer science.
6. Code: The selfie code is open source and available at [github.com/cksystemsteaching/selfie](https://github.com/cksystemsteaching/selfie)
7. X: Follow us at [x.com/christophkirsch](https://twitter.com/christophkirsch)
8. Web: The selfie homepage is at [selfie.cs.uni-salzburg.at](https://selfie.cs.uni-salzburg.at)

## Extras

1. Garbage collection: In addition to the conservative but O(n^2) garbage collector in selfie, there is an implementation of an O(n) [Boehm](https://github.com/cksystemsteaching/selfie/blob/main/tools/boehm-gc.c) garbage collector for small memory blocks with fall-back to the garbage collector in selfie for large memory blocks.
2. Fuzzing: There is a simple but self-fuzzing fuzzer called [buzzr](https://github.com/cksystemsteaching/selfie/blob/main/tools/buzzr.c) based on selfie that fuzzes RISC-U code including all of selfie and itself.
3. Symbolic execution: There is a self-executing symbolic execution engine called [monster](https://github.com/cksystemsteaching/selfie/blob/main/tools/monster.c) based on selfie that translates RISC-U code including all of selfie and itself to SMT-LIB formulae that are satisfiable if and only if there is input to the code such that the code exits with non-zero exit codes or performs division by zero within a given number of machine instructions.
4. Bounded model checking: There is a self-translating modeling engine called [beator](https://github.com/cksystemsteaching/selfie/blob/main/tools/beator.c) based on selfie that translates RISC-U code including all of selfie and itself to BTOR2 formulae that are satisfiable if and only if there is input to the code such that the code exits with non-zero exit codes, performs division by zero, or accesses memory outside of allocated memory blocks.
5. Bit-precise code analysis and synthesis: There is a self-translating modeling engine called [rotor](https://github.com/cksystemsteaching/selfie/blob/main/tools/rotor.c) based on selfie that translates full RISC-V code including all of selfie and itself to BTOR2 and SMT-LIB formulae that are satisfiable if and only if there is input to the code such that the code exits with non-zero exit codes, performs division by zero, or accesses memory outside of memory segments. Rotor also generates models that enable RISC-V code synthesis.
6. BTOR2 visualization: There is a visualization tool called [beatle](https://github.com/cksystemsgroup/beator-visualizer) that displays BTOR2 formulae generated from RISC-U binaries as directed acyclic graphs.
7. SAT solving: There is a bruteforce SAT solver called [babysat](https://github.com/cksystemsteaching/selfie/blob/main/tools/babysat.c) based on selfie that computes satisfiability of SAT formulae in DIMACS CNF.
8. Binary translation: There is a self-translating [binary translator](https://github.com/cksystemsteaching/selfie/blob/riscv-2-x86-unsupported/tools/riscv-2-x86.c) based on selfie that translates RISC-U code including all of selfie and itself to x86 binary code.

## Installing Selfie

Selfie runs natively on Linux, macOS, and Windows machines and possibly other systems that have a terminal and a C compiler installed. However, even without a C compiler installed on your machine, or if you only have access to a web browser you can run selfie. There are at least three ways to install and run selfie:

1. Natively on your machine (recommended): download and unzip [selfie](https://github.com/cksystemsteaching/selfie/archive/main.zip). Then, open a terminal to run selfie, see further below. For this to work, you need to have a C compiler installed on your machine. We recommend using [clang](https://clang.llvm.org) or [gcc](https://gcc.gnu.org) (with [cygwin](https://www.cygwin.com) on Windows).

2. In docker on your machine (advanced): download and install [docker](https://docker.com). Then, open a terminal and type `docker run -it cksystemsteaching/selfie`. The advantage of using docker is that you can run selfie out of the box on your machine without installing any tools such as a C compiler. All necessary and even optional tools are pre-installed in the [selfie docker image](https://hub.docker.com/r/cksystemsteaching/selfie). However, you need to know how to use docker.

1. In the cloud (easy but requires Internet connectivity): if you only have access to a web browser, just click [here](https://replit.com/new/github/cksystemsteaching/selfie). Alternatively, create a [github](https://github.com) account, unless you already have one, and fork [selfie](https://github.com/cksystemsteaching/selfie) into your github account. Then, create a [cloud9](https://c9.io) student account, connect it to your github account, verify your email address and set a password (important!), and finally clone your fork of selfie into a new cloud9 workspace.

At this point we assume that you have a system that supports running selfie. Below we use the `make` command assuming it is installed on your system which is usually the case. However, we also show the command invoked by `make` so that you can always invoke that command manually if your system does not have `make` installed.

The next step is to produce a selfie binary. To do that `cd` to the selfie folder in your terminal and then type `make`. With docker, the system will respond `make: 'selfie' is up to date` since there is already a selfie binary pre-installed. Without docker, `make` will invoke the C compiler on your machine or in the cloud9 workspace:

```bash
cc -Wall -Wextra -O3 -D'uint64_t=unsigned long' selfie.c -o selfie
```

and then compile `selfie.c` into an executable called `selfie` as directed by the `-o` option. The executable contains the C\* compiler, the mipster emulator, and the hypster hypervisor. The `-Wall` and `-Wextra` options enable all compiler warnings which is useful during further development of selfie. The `-O3` option instructs the compiler to generate optimized code. The `-D'uint64_t=unsigned long'` option is needed to bootstrap the code. It defines the data type `uint64_t` which would otherwise be undefined since C\* does not include the necessary definitions. If your system supports compiling and executing 32-bit binaries you may also try `make selfie-32` which will produce a 32-bit system that in turn generates and executes 32-bit binaries.

## Running Selfie

Once you have successfully compiled `selfie.c` you may invoke `selfie` without any arguments as follows:

```bash
$ ./selfie
./selfie { -c { source } | -o binary | [ -s | -S ] assembly | -l binary } [ ( -m | -d | -r | -y ) 0-4096 ... ]
```

In this case, `selfie` responds with its usage pattern.

The order in which the options are provided matters for taking full advantage of self-referentiality.

The `-c` option invokes the C\* compiler on the given list of `source` files compiling and linking them into RISC-U code that is stored internally. For example, `selfie` may be used to compile its own source code `selfie.c` as follows:

```bash
$ ./selfie -c selfie.c
```

The `-o` option writes RISC-U code produced by the most recent compiler invocation to the given `binary` file. For example, `selfie` may be instructed to compile itself and then output the generated RISC-U code into a RISC-U binary file called `selfie.m`:

```bash
$ ./selfie -c selfie.c -o selfie.m
```

The `-s` option writes RISC-U assembly of the RISC-U code produced by the most recent compiler invocation to the given `assembly` file while the `-S` option additionally includes approximate line numbers and the binary representation of the instructions. Similarly as before, `selfie` may be instructed to compile itself and then output the generated RISC-U code into a RISC-U assembly file called `selfie.s`:

```bash
$ ./selfie -c selfie.c -s selfie.s
```

The `-l` option loads RISC-U code from the given `binary` file. The `-o` and `-s` options can also be used after the `-l` option. However, in this case the `-s` option does not generate approximate source line numbers. For example, the previously generated RISC-U binary file `selfie.m` may be loaded as follows:

```bash
$ ./selfie -l selfie.m
```

The `-m` option invokes the mipster emulator to execute RISC-U code most recently loaded or produced by a compiler invocation. The emulator creates a machine instance with `0-4096` MB of memory. The `source` or `binary` name of the RISC-U code and any remaining `...` arguments are passed to the main function of the code. For example, the following invocation executes `selfie.m` using mipster:

```bash
$ ./selfie -l selfie.m -m 1
```

This is in fact semantically equivalent to executing `selfie` without any arguments:

```bash
$ ./selfie
```

The `-d` option is similar to the `-m` option except that mipster outputs each executed instruction, its approximate source line number, if available, and the relevant machine state. Alternatively, the `-r` option limits the amount of output created with the `-d` option by having mipster merely replay code execution when runtime errors such as division by zero occur. In this case, mipster outputs only the instructions that were executed right before the error occurred.

If you are using docker you can also execute `selfie.m` directly on spike and pk as follows:

```bash
$ spike pk selfie.m
```

which is again semantically equivalent to executing `selfie` without any arguments.

The `-y` option invokes the hypster hypervisor to execute RISC-U code similar to the mipster emulator. The difference to mipster is that hypster creates RISC-U virtual machines rather than a RISC-U emulator to execute the code. See below for an example.

### Self-compilation

Here is an example of how to perform self-compilation of `selfie.c` and then check if the RISC-U code `selfie1.m` generated for `selfie.c` by executing the `./selfie` binary is equivalent to the code `selfie2.m` generated by executing the just generated `selfie1.m` binary:

```bash
$ ./selfie -c selfie.c -o selfie1.m -m 2 -c selfie.c -o selfie2.m
$ diff -s selfie1.m selfie2.m
Files selfie1.m and selfie2.m are identical
```

Note that at least 2MB of memory is required for this to work.

### Self-execution

The following example shows how to perform self-execution of the mipster emulator. In this case we invoke mipster to invoke itself to execute `selfie`:

```bash
$ ./selfie -c selfie.c -o selfie.m -m 2 -l selfie.m -m 1
```

which is again semantically equivalent to executing `selfie` without any arguments but this time with `selfie` printing its usage pattern much slower since there is a mipster running on top of another mipster.

### Self-hosting

The previous example can also be done by running hypster on mipster. This is significantly faster and requires less memory since hypster does not create a second emulator instance on top of the first emulator instance. Instead, hypster creates a virtual machine to execute selfie that runs concurrently to hypster on the first emulator instance:

```bash
$ ./selfie -c selfie.c -o selfie.m -m 1 -l selfie.m -y 1
```

We may even run hypster on hypster on mipster which is still reasonably fast since there is still only one emulator instance involved and hypster itself does not add much overhead:

```bash
$ ./selfie -c selfie.c -o selfie.m -m 2 -l selfie.m -y 1 -l selfie.m -y 1
```

### Workflow

To compile any C\* source code and execute it right away in a single invocation of `selfie` without generating a RISC-U binary use:

```bash
$ ./selfie -c any-cstar-file.c -m 1 "arguments for any-cstar-file.c"
```

Equivalently, you may also use a selfie-compiled version of `selfie` and have the mipster emulator execute selfie to compile any C\* source code and then execute it right away with hypster on the same emulator instance:

```bash
$ ./selfie -c selfie.c -m 1 -c any-cstar-file.c -y 1 "arguments for any-cstar-file.c"
```

You may also generate RISC-U binaries both ways which will then be identical:

```bash
$ ./selfie -c any-cstar-file.c -o any-cstar-file1.m
$ ./selfie -c selfie.c -m 1 -c any-cstar-file.c -o any-cstar-file2.m
$ diff -s any-cstar-file1.m any-cstar-file2.m
Files any-cstar-file1.m and any-cstar-file2.m are identical
```

This can also be done in a single invocation of `selfie`:

```bash
$ ./selfie -c any-cstar-file.c -o any-cstar-file1.m -c selfie.c -m 1 -c any-cstar-file.c -o any-cstar-file2.m
$ diff -s any-cstar-file1.m any-cstar-file2.m
Files any-cstar-file1.m and any-cstar-file2.m are identical
```

The generated RISC-U binaries can then be loaded and executed as follows:

```bash
$ ./selfie -l any-cstar-file1.m -m 1 "arguments for any-cstar-file1.m"
```

#### Linking

To compile and link any C\* source code from multiple source files use:

```bash
$ ./selfie -c any-cstar-file1.c any-cstar-file2.c ... -m 1
```

For example, to make the source code of `selfie.c` available as library code in any C\* source code use:

```bash
$ ./selfie -c any-cstar-file.c selfie.c -m 1
```

Note that multiple definitions of symbols are ignored by the compiler with a warning.

#### Debugging

Selfie's console messages always begin with the name of the source or binary file currently running. The mipster emulator also shows the amount of memory allocated for its machine instance and how execution terminated (exit code).

As discussed before, RISC-U assembly for `selfie` and any other C\* file is generated as follows:

```bash
$ ./selfie -c selfie.c -s selfie.s
```

If the assembly code is generated from a binary generated by the compiler (and not loaded from a file) approximate source line numbers are included in the assembly file.

Verbose debugging information is printed with the `-d` option, for example:

```bash
$ ./selfie -c selfie.c -d 1
```

Similarly, if the executed binary is generated by the compiler (and not loaded from a file) approximate source line numbers are included in the debug information.