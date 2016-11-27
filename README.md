# Selfie [![Build Status](https://travis-ci.org/cksystemsteaching/selfie.svg?branch=master)](https://travis-ci.org/cksystemsteaching/selfie)

Selfie is a project of the [Computational Systems Group](http://www.cs.uni-salzburg.at/~ck) at the Department of Computer Sciences of the University of Salzburg in Austria.

For further information and support please refer to http://selfie.cs.uni-salzburg.at

## Build Instructions

Selfie runs on Mac, Linux, Windows and possibly other systems. The only requirement is a terminal application and a C compiler that supports generating 32-bit binaries. We assume that the compiler is invoked as `cc` in the terminal. We also use `make` which is strictly speaking not necessary but anyway convenient to have. The commands invoked by `make` are listed below and can also be invoked manually.

The first step is to produce a selfie binary that runs on your computer. To do that type `make` in a terminal. This will invoke the C compiler:

```bash
cc -w -m32 -D'main(a,b)=main(a,char**argv)' selfie.c -o selfie
```

and compile `selfie.c` into an executable called `selfie` as directed by the `-o` option. The executable contains the C\* compiler, the mipster emulator, and the hypster hypervisor. The `-w` option suppresses warnings that can be ignored here. The `-m32` option makes the compiler generate a 32-bit executable (which may require installing gcc-multiarch or gcc-multilib, depending on your system). Selfie only supports 32-bit architectures. The `-D` option is needed to bootstrap the main function declaration. The `char` data type is not available in C\* but may be required by the compiler.

## Running Selfie

Once you have successfully compiled selfie you may invoke it in a terminal as follows:

```bash
./selfie { -c { source } | -o binary | -s assembly | -l binary } [ -m size ... | -d size ... | -y size ... ]
```

The order in which the options are provided matters for taking full advantage of self-referentiality.

The `-c` option invokes the C\* compiler on the given list of `source` files compiling and linking them into MIPSter code that is stored internally.

The `-o` option writes MIPSter code produced by the most recent compiler invocation to the given `binary` file.

The `-s` option writes MIPSter assembly of the MIPSter code produced by the most recent compiler invocation including approximate source line numbers to the given `assembly` file.

The `-l` option loads MIPSter code from the given `binary` file. The `-o` and `-s` options can also be used after the `-l` option. However, in this case the `-s` option does not generate approximate source line numbers.

The `-m` option invokes the mipster emulator to execute MIPSter code most recently loaded or produced by a compiler invocation. The emulator creates a machine instance with `size` MB of memory. The `source` or `binary` name of the MIPSter code and any remaining `...` arguments are passed to the main function of the code. The `-d` option is similar to the `-m` option except that mipster outputs each executed instruction, its approximate source line number, if available, and the relevant machine state.

The `-y` option invokes the hypster hypervisor to execute MIPSter code similar to the mipster emulator. The difference to mipster is that hypster creates MIPSter virtual machines rather than a MIPSter emulator to execute the code.

To compile `selfie.c` for mipster and hypster use the following command:

```bash
$ ./selfie -c selfie.c -o selfie.m
```

This produces a MIPSter binary file called `selfie.m` that implements selfie.

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

To compile any C\* source code and execute it right away in a single invocation of `selfie` without generating a MIPSter binary use:

```bash
$ ./selfie -c any-cstar-file.c -m 1 "arguments for any-cstar-file.c"
```

Equivalently, you may also use a selfie-compiled version of `selfie` and have the mipster emulator execute selfie to compile any C\* source code and then execute it right away with hypster on the same emulator instance:

```bash
$ ./selfie -c selfie.c -m 1 -c any-cstar-file.c -y 1 "arguments for any-cstar-file.c"
```

You may also generate MIPSter binaries both ways which will then be identical:

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

The generated MIPSter binaries can then be loaded and executed as follows:

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

MIPSter assembly for `selfie` and any other C\* file is generated as follows:

```bash
$ ./selfie -c selfie.c -s selfie.s
```

If the assembly code is generated from a binary generated by the compiler (and not loaded from a file) approximate source line numbers are included in the assembly file.

Verbose debugging information is printed with the `-d` option, for example:

```bash
$ ./selfie -c selfie.c -d 1
```

Similarly, if the executed binary is generated by the compiler (and not loaded from a file) approximate source line numbers are included in the debug information.

### Running Selfie on Spike/PK
#### Build instructions
These instructions describe how to build the RISC-V emulator spike and the proxy kernel necessary to run selfie in a native RISC-V environment.
Running selfie on spike with pk has only been tested on Ubuntu 14.04 and 16.04 so far.

1. Clone or download the RISC-V tools from [here](https://github.com/riscv/riscv-tools/tree/4635ab67966c763a84f7217bc2c20b65dcabc7ec).
2. Follow the instructions described in the RISC-V tools Readme, section "Quickstart". Note: do not skip any of the steps below, even if only the 32-bit version is needed.
  1. Execute the first four commands exactly as listed. Note: only Ubuntu packages that are missing have to be installed. This installs all tools in the 64-bit version.
  2. If the build finished without errors, execute `$ ./build.sh --with-xlen=32`. This installs all tools in the 32-bit version.
3. Apply the sbrk patch for the proxy kernel:
  1. Change to the directory `riscv-tools/riscv-pk/pk` in the RISC-V source folder.
  2. Execute `patch < path/to/sbrk.patch` (sbrk.patch should be in the selfie source folder).
  3. Repeat step 2ii. This builds the proxy kernel with the new patch.
  
#### Execution of selfie binaries on top of Spike/PK
To make use of the RISC-V execution environment, you either need a selfie generated binary (using starc) or make use of the RISC-V crosscompiler (`riscv32-unknown-elf-gcc`). To do this, follow one of the steps below.
* Compile `selfie.c` using `make`, which yields a binary called `selfie`. Then, self-compile `selfie.c` using `selfie` by executing `./selfie -c selfie.c -o selfie.r`. `selfie.r`now contains a binary ready to run on spike with pk. You can execute (almost) any command described in the other sections now by using spike/pk and `selfie.r`, for example: 
  ```
    $RISCV/bin/spike --isa=RV32IMAFDC $RISCV/riscv32-unknown-elf/bin/pk selfie.pk -c test.c -o test.r
  ```
  This yields a binary `test.r` compiled from a C*-file `test.c` which can in turn be executed by selfie, either on top of spike/pk or on Linux, for example.

* The other option would be to use the RISC-V crosscompiler to generate a binary of selfie:
  ```
    $RISCV/bin/riscv32-unknown-elf-gcc selfie.c -o selfie.r
  ```
  This generates the binary `selfie.r` which can be used as described above.
