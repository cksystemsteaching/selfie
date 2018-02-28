# Selfie [![Build Status](https://travis-ci.org/cksystemsteaching/selfie.svg?branch=master)](https://travis-ci.org/cksystemsteaching/selfie)

Selfie is a project of the [Computational Systems Group](http://www.cs.uni-salzburg.at/~ck) at the Department of Computer Sciences of the University of Salzburg in Austria.

The Selfie Project provides an educational platform for teaching undergraduate and graduate students the design and implementation of programming languages and runtime systems. The focus is on the construction of compilers, libraries, operating systems, and even virtual machine monitors. The common theme is to identify and resolve self-reference in systems code which is seen as the key challenge when teaching systems engineering, hence the name.

There is a free book in early draft form called [Selfie: Computer Science for Everyone](http://leanpub.com/selfie) using selfie even more ambitiously reaching out to everyone with an interest in learning about computer science.

Selfie is a self-contained 8k-line, 64-bit C implementation of:

1. a self-compiling compiler called starc that compiles
   a tiny but still fast subset of C called C Star (C*) to
   a tiny and easy-to-teach subset of RISC-V called RISC-U,
2. a self-executing emulator called mipster that executes
   RISC-U code including itself when compiled with starc,
3. a self-hosting hypervisor called hypster that provides
   RISC-U virtual machines that can host all of selfie,
   that is, starc, mipster, and hypster itself, and
4. a tiny C* library called libcstar utilized by selfie.

Selfie is implemented in a single (!) file and kept minimal for simplicity.
There is also a simple in-memory linker, a RISC-U disassembler, a profiler,
and a debugger as well as minimal operating system support in the form of
RISC-V system calls built into the emulator. As part of an ongoing effort,
there is also a simple SAT solver implemented in selfie that may eventually
be used in some form of self-verification.

For further information and support please refer to [http://selfie.cs.uni-salzburg.at](http://selfie.cs.uni-salzburg.at)

## Supported Platforms

Selfie runs on Mac, Linux, Windows and possibly other systems that have a terminal and a C compiler installed. Even if you only have access to a web browser you can still run selfie through a cloud-based development environment. Selfie generates ELF binaries. Making them compatible with the official [RISC-V](https://riscv.org) toolchain, in particular the [spike emulator](https://github.com/riscv/riscv-isa-sim) and the [pk kernel](https://github.com/riscv/riscv-pk), is ongoing work.

## Installing Selfie

If you have access to a computer with a terminal application and a C compiler installed, just download and unzip [selfie](https://github.com/cksystemsteaching/selfie/archive/master.zip) on that machine. If you only have access to a web browser, get a [github](https://github.com) account, unless you already have one, and fork [selfie]( https://github.com/cksystemsteaching/selfie) into your github account. Then, get a [cloud9](https://c9.io) student account, connect it to your github account, verify your email address and set a password (important!), and finally clone your fork of selfie into a new cloud9 workspace.

At this point we assume that you have a system that supports running selfie. Below we use the `make` command assuming it is installed on your system which is usually the case. However, we also show the command invoked by `make` so that you can always invoke that command manually if your system does not have `make` installed.

The next step is to produce a selfie binary that runs on your system. To do that type `make` in your terminal. This will invoke the C compiler:

```bash
cc -w -O3 -m64 -D'main(a,b)=main(int argc, char** argv)' -Duint64_t='unsigned long long' selfie.c -o selfie
```

and compile `selfie.c` into an executable called `selfie` as directed by the `-o` option. The executable contains the C\* compiler, the mipster emulator, and the hypster hypervisor. The `-w` option suppresses warnings that can be ignored here. The `-O3` option instructs the compiler to generate optimized code. The `-m64` option makes the compiler generate a 64-bit executable. The `-D'main(a,b)=main(int argc, char** argv)'` and `-Duint64_t='unsigned long long'` options are needed to bootstrap the code. The `char` data type is not available in C\* but may be required by the compiler. The `uint64_t` data type is undefined since C\* does not support including the necessary declarations.

## Running Selfie

Once you have successfully compiled selfie you may invoke it in your terminal according to the following pattern:

```bash
./selfie { -c { source } | -o binary | -s assembly | -l binary | -sat dimacs } [ (-m | -d | -y | -min | -mob ) size ... ]
```

The order in which the options are provided matters for taking full advantage of self-referentiality.

The `-c` option invokes the C\* compiler on the given list of `source` files compiling and linking them into RISC-U code that is stored internally.

The `-o` option writes RISC-U code produced by the most recent compiler invocation to the given `binary` file.

The `-s` option writes RISC-U assembly of the RISC-U code produced by the most recent compiler invocation including approximate source line numbers to the given `assembly` file.

The `-l` option loads RISC-U code from the given `binary` file. The `-o` and `-s` options can also be used after the `-l` option. However, in this case the `-s` option does not generate approximate source line numbers.

The `-sat` option invokes the SAT solver on the SAT instance loaded from the `dimacs` file. The current implementation is naive and only works on small instances.

The `-m` option invokes the mipster emulator to execute RISC-U code most recently loaded or produced by a compiler invocation. The emulator creates a machine instance with `size` MB of memory. The `source` or `binary` name of the RISC-U code and any remaining `...` arguments are passed to the main function of the code. The `-d` option is similar to the `-m` option except that mipster outputs each executed instruction, its approximate source line number, if available, and the relevant machine state.

The `-y` option invokes the hypster hypervisor to execute RISC-U code similar to the mipster emulator. The difference to mipster is that hypster creates RISC-U virtual machines rather than a RISC-U emulator to execute the code.

The `-min` and `-mob` options invoke special versions of the mipster emulator used for teaching.

To compile `selfie.c` for mipster and hypster use the following command:

```bash
$ ./selfie -c selfie.c -o selfie.m
```

This produces a RISC-U binary file called `selfie.m` that implements selfie.

To execute `selfie.m` by mipster use the following command:

```bash
$ ./selfie -l selfie.m -m 1
```

This is semantically equivalent to executing `selfie` without any arguments:

```bash
$ ./selfie
```

To execute `selfie.m` by hypster use the following command:

```bash
$ ./selfie -l selfie.m -y 1
```

This is semantically equivalent to executing `selfie.m` by mipster and thus `selfie` without any arguments. There is a difference in output though since mipster reports code execution profiles whereas hypster does not.

### Self-compilation

Here is an example of how to perform self-compilation of `selfie.c`:

```bash
$ ./selfie -c selfie.c -o selfie1.m -m 2 -c selfie.c -o selfie2.m
$ diff -s selfie1.m selfie2.m
Files selfie1.m and selfie2.m are identical
```

Note that at least 2MB of memory is required.

### Self-execution

The following example shows how to perform self-execution of `selfie.c`. In this case we invoke the mipster emulator to invoke itself which then invokes the compiler to compile itself:

```bash
$ ./selfie -c selfie.c -o selfie1.m -m 4 -l selfie1.m -m 2 -c selfie.c -o selfie2.m
$ diff -s selfie1.m selfie2.m
Files selfie1.m and selfie2.m are identical
```

Note that the example may take several hours to complete. Also, an emulator instance A running an emulator instance B needs more memory than B, say, 4MB rather than 2MB in the example here.

### Self-hosting

The previous example can also be done by running hypster on mipster. This is significantly faster since hypster does not create a second emulator instance on top of the first emulator instance. Instead, hypster creates a virtual machine to execute selfie that runs concurrently to hypster on the first emulator instance:

```bash
$ ./selfie -c selfie.c -o selfie1.m -m 4 -l selfie1.m -y 2 -c selfie.c -o selfie2.m
$ diff -s selfie1.m selfie2.m
Files selfie1.m and selfie2.m are identical
```

We may even run hypster on hypster on mipster which is still reasonably fast since there is still only one emulator instance involved and hypster itself does not add much overhead:

```bash
$ ./selfie -c selfie.c -o selfie1.m -m 8 -l selfie1.m -y 4 -l selfie1.m -y 2 -c selfie.c -o selfie2.m
$ diff -s selfie1.m selfie2.m
Files selfie1.m and selfie2.m are identical
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

RISC-U assembly for `selfie` and any other C\* file is generated as follows:

```bash
$ ./selfie -c selfie.c -s selfie.s
```

If the assembly code is generated from a binary generated by the compiler (and not loaded from a file) approximate source line numbers are included in the assembly file.

Verbose debugging information is printed with the `-d` option, for example:

```bash
$ ./selfie -c selfie.c -d 1
```

Similarly, if the executed binary is generated by the compiler (and not loaded from a file) approximate source line numbers are included in the debug information.
