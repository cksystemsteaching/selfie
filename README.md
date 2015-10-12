# Selfie

Selfie is a project of the [Computational Systems Group](http://www.cs.uni-salzburg.at/~ck) at the Department of Computer Sciences of the University of Salzburg in Austria.

For further information and support please refer to http://selfie.cs.uni-salzburg.at

## Build Instructions

### On 32-bit Linux

The first step is to produce a binary that runs on your computer. To do that, use `gcc` in a terminal to compile `selfie.c`:

```bash
$ gcc -o selfie selfie.c
```

This produces an executable called `selfie` as directed by the `-o` option. The executable contains both the C\* compiler as well as the MIPSter emulator.

Selfie may be invoked as follows:

```bash
./selfie [ -c | -m <memory size in MB> <binary> ]
```

When using `selfie` with the `-c` option or without any arguments the compiler is invoked. With the `-m` option the emulator is invoked and configured to create a machine instance with \<memory size in MB\> that loads and executes \<binary\>.

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
 - debug_syscalls: Print debugging information on every system call
 - debug_load: Print hex code of what the emulator loaded

### On Mac OS X / 64-bit Linux

On Mac OS X as well as on 64-bit Linux (requires gcc-multiarch. On Ubuntu, install gcc-multilib), you may use the following command to compile `selfie.c`:

```bash
clang -w -m32 -D'main(a, b)=main(int argc, char **argv)' -o selfie selfie.c
```

After that, you can proceed with the same commands as for 32-bit Linux.

The `-w` option suppresses warnings that can be ignored for now. The `-m32` option makes the compiler generate a 32-bit executable. Selfie only supports 32-bit architectures right now. The `-D` option is needed to bootstrap the main function declaration. The `char` data type is not available in C\* but required by `clang`.
