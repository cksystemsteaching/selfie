# Selfie [![Build Status](https://travis-ci.org/cksystemsteaching/selfie.svg?branch=master)](https://travis-ci.org/cksystemsteaching/selfie)

Selfie is a project of the [Computational Systems Group](http://www.cs.uni-salzburg.at/~ck) at the Department of Computer Sciences of the University of Salzburg in Austria.

The Selfie Project provides an educational platform for teaching undergraduate and graduate students the design and implementation of programming languages and runtime systems. The focus is on the construction of compilers, libraries, operating systems, and even virtual machine monitors. The common theme is to identify and resolve self-reference in systems code which is seen as the key challenge when teaching systems engineering, hence the name.

Slides providing an overview of selfie and an introduction to its design and implementation are made available incrementally [here](http://selfie.cs.uni-salzburg.at/slides). There is also a free book in early draft form called [Selfie: Computer Science for Everyone](http://leanpub.com/selfie) using selfie even more ambitiously reaching out to everyone with an interest in learning about computer science.

Selfie is a self-contained 64-bit, 10-KLOC C implementation of:

1. a self-compiling compiler called starc that compiles
   a tiny but still fast [subset of C](https://github.com/cksystemsteaching/selfie/blob/master/semantics.md) called C Star ([C*](https://github.com/cksystemsteaching/selfie/blob/master/grammar.md)) to
   a tiny and easy-to-teach subset of RISC-V called [RISC-U](https://github.com/cksystemsteaching/selfie/blob/master/riscu.md),
2. a self-executing emulator called mipster that executes
   RISC-U code including itself when compiled with starc,
3. a self-hosting hypervisor called hypster that provides
   RISC-U virtual machines that can host all of selfie,
   that is, starc, mipster, and hypster itself,
4. a prototypical symbolic execution engine called monster
   that executes RISC-U code symbolically,
5. a simple SAT solver that reads CNF DIMACS files, and
6. a tiny C* library called libcstar utilized by selfie.

Selfie is implemented in a single (!) file and kept minimal for simplicity. There is also a simple in-memory linker, a RISC-U disassembler, a profiler, and a debugger with replay as well as minimal operating system support built into the emulator. Selfie generates ELF binaries that are compatible with the official [RISC-V](https://riscv.org) toolchain, in particular the [spike emulator](https://github.com/riscv/riscv-isa-sim) and the [pk kernel](https://github.com/riscv/riscv-pk).

For further information and support please refer to [http://selfie.cs.uni-salzburg.at](http://selfie.cs.uni-salzburg.at)

## Supported Platforms

Selfie runs on Mac, Linux, and Windows machines and possibly other systems that have a terminal and a C compiler installed. However, even if there is no C compiler installed on your machine or you only have access to a web browser you can still run selfie.

## Installing Selfie

There are at least three ways to install and run selfie, from real simple to a bit more difficult:

1. If you have access to a Mac, Linux, or Windows machine download and install [docker](https://docker.com). Then, open a terminal window and type `docker run -it cksystemsteaching/selfie`. Besides simplicity, the key advantage of using docker is that you can run selfie out of the box natively on your machine but also on spike and pk which are both pre-installed in the [selfie docker image](https://hub.docker.com/r/cksystemsteaching/selfie).

2. Instead of using docker, you may also just download and unzip [selfie](https://github.com/cksystemsteaching/selfie/archive/master.zip), and then open a terminal window to run selfie on your machine. However, for this to work you need to have a C compiler installed on your machine. We recommend using [clang](https://clang.llvm.org) or [gcc](https://gcc.gnu.org).

3. If you only have access to a web browser, create a [github](https://github.com) account, unless you already have one, and fork [selfie](https://github.com/cksystemsteaching/selfie) into your github account. Then, create a [cloud9](https://c9.io) student account, connect it to your github account, verify your email address and set a password (important!), and finally clone your fork of selfie into a new cloud9 workspace.

At this point we assume that you have a system that supports running selfie. Below we use the `make` command assuming it is installed on your system which is usually the case. However, we also show the command invoked by `make` so that you can always invoke that command manually if your system does not have `make` installed.

The next step is to produce a selfie binary. To do that type `make` in your terminal. With docker, the system will respond `make: 'selfie' is up to date` since there is already a selfie binary pre-installed. Without docker, `make` will invoke the C compiler on your machine or in the cloud9 workspace:

```bash
cc -Wall -Wextra -O3 -m64 -Duint64_t='unsigned long long' selfie.c -o selfie
```

and then compile `selfie.c` into an executable called `selfie` as directed by the `-o` option. The executable contains the C\* compiler, the mipster emulator, and the hypster hypervisor. The `-Wall` and `-Wextra` options enable all compiler warnings which is useful during further development of selfie. The `-O3` option instructs the compiler to generate optimized code. The `-m64` option makes the compiler generate a 64-bit executable. The `-Duint64_t='unsigned long long'` option is needed to bootstrap the code. It defines the data type `uint64_t` which would otherwise be undefined since C\* does not support including the necessary definitions.

## Running Selfie

Once you have successfully compiled `selfie.c` you may invoke `selfie` without any arguments as follows:

```bash
$ ./selfie
./selfie { -c { source } | -o binary | [ -s | -S ] assembly | -l binary | -sat dimacs }  [ -v 0-4 ] [ ( -m | -d | -r | -n | -y | -min | -mob ) 0-64 ... ]
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

The `-m` option invokes the mipster emulator to execute RISC-U code most recently loaded or produced by a compiler invocation. The emulator creates a machine instance with `0-64` MB of memory. The `source` or `binary` name of the RISC-U code and any remaining `...` arguments are passed to the main function of the code. For example, the following invocation executes `selfie.m` using mipster:

```bash
$ ./selfie -l selfie.m -m 1
```

This is in fact semantically equivalent to executing `selfie` without any arguments:

```bash
$ ./selfie
```

The `-d` option is similar to the `-m` option except that mipster outputs each executed instruction, its approximate source line number, if available, and the relevant machine state. Alternatively, the `-r` option limits the amount of output created with the `-d` option by having mipster merely replay code execution when runtime errors such as division by zero occur. In this case, mipster outputs only the instructions that were executed right before the error occurred. The `-min` and `-mob` options invoke special versions of the mipster emulator used for teaching.

If you are using docker you can also execute `selfie.m` directly on spike and pk as follows:

```bash
$ spike pk selfie.m
```

which is again semantically equivalent to executing `selfie` without any arguments.

The `-y` option invokes the hypster hypervisor to execute RISC-U code similar to the mipster emulator. The difference to mipster is that hypster creates RISC-U virtual machines rather than a RISC-U emulator to execute the code. See below for an example.

The `-n` option invokes the symbolic execution engine which interprets the `0-64` value as fuzzing parameter. Value `0` means that code is executed symbolically but without any fuzzing of its input. In other words, code execution uses the symbolic execution engine but is effectively concrete. The `64` value, on the other hand, means that all input read from files is fuzzed to the extent that any machine word read from files may represent any 64-bit value. Note that the current implementation is incomplete and buggy.

The `-sat` option invokes the SAT solver on the SAT instance loaded from the `dimacs` file. The current implementation is naive and only works on small instances.

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

# Littlemonster [![Build Status](https://travis-ci.org/cksystemsteaching/selfie.svg?branch=littlemonster)](https://travis-ci.org/cksystemsteaching/selfie/branches)

The -n option invokes the symbolic execution engine which interprets the 0-64 value as fuzzing parameter. Value 0 means that code is executed symbolically but without any fuzzing of its input. In other words, code execution uses the symbolic execution engine but is effectively concrete. The 64 value, on the other hand, means that all input read from files is fuzzed to the extent that any machine word read from files may represent any 64-bit value. Note that the current implementation is incomplete and buggy.

## Testing Selfie
Littlemonster provides a symbolic emulator by executing risc-u binary for a set of input values. Examples of test files can be found in the folder `test`. Use the option `-n` instead of `-m` in order to execute a risc-u file symbolically.
```bash
$ ./selfie -c test/read_test.c -n 2
[...]
./selfie: test/read_test.c reaching end point at: 0x00000294(~35) with exit code <49,52,1>
./selfie: backtracking 1
```
By default only the line number, the exit code and the number of backtracks are printed. In monster, different `symbolic` values abstract the program executions. Here the triple `<49, 52, 1>`, called msiid, specifies that the set of possible exit code values are `{49, 50, 51, 52}` (the values fuzzed by the system call `read` in read_test.c).

A msiid value is three integers, a start, an end and a step. It specifies the set of values from the beggining and each step more until reaching the end. It models overflow and `<-3, 1, 2>` corresponds to the values in the set `{-3, -1, 1}`.

The combination `read/fuzz` is a possible way to `initialize` symbolic values in the execution. A second possibility exists with the system call `input`. This function allows the user to debug more precisely its own code by explicitely setting the `msiid value` into a specific variable.

*Notice that we handle for the moment exclusive uses of input and read system calls into one file.*

```bash
$ ./selfie -c test/input_test.c -v 1 -n 2
[...]
./selfie: test/input_test.c reaching end point at: 0x000001BC(~6) with exit code <0,10,1>
./selfie: trace of length 15.
./selfie: 65 instructions executed for the path, total instructions 65.
Symbolic values witness:
<0,10,1> for variable: 0xFFFFFFA8 at index [15]
./selfie: backtracking 1
```
The verbose option `-v` requires a digit and will print more details about a symbolic execution. The level `1` prints a sum-up with the length of the `trace` (the symbolic memory), the number of instructions executed for this path, the total number of executed instructions, and the witness specifying the input values to reproduce this path. The other verbose values enable the unreachable branch warnings only with symbolic value (level `2`) or any unreachable branches (level `3`). The last level enables the symbolic debbuger which is similar to `-d` but with symbolic values.

### Bounded Execution
```c
// symbolic BOUNDS
uint64_t MAX_TRACE_LENGTH
uint64_t MAX_PATH_LENGTH
uint64_t MAX_READ
```
Litlemonster provides three parameters to limit your symbolic execution and prevent from infinite runs. `MAX_TRACE_LENGTH` will limit the number of values stored into the symbolic memory. Littlemonster executes a path until `MAX_PATH_LENGTH` instructions and will not analyze it further. Finally, `MAX_READ` is the number of reads the analysis will consider (along one path), next reads will return `EOF`.

# Test file
Littlemonster also provides `test-script.pl` automatically testing a set of files by symbolically executing them and checking their correct actual outputs. A `test` file is a `C*` file with a header specifying the command and the expecting results.
```c
// [-c test/input_test.c -v 3 -n 2;<6,0,10,1>;<8,false>]
uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t x;
  x = input(0, 10, 1);
  if( x < 15)
    return x;
  else
    return x;
}
```
In this example we expect this code with verbose `3` to be executed, resulting in the exit code `<0,10,1>` at line `6` and in the unreachable false branch at line `8` (the beggining of else statement).
```bash
./test-script.pl test/input_test.c
Log file in log_118.11.17.2.9.txt
run ./selfie -c test/input_test.c -v 3 -n 2
```
Each run of `test-script.pl` will create a log where the tests and their results are listed (a folder can be passed to the script). *Be aware the path is checked against the first compiled .c file  and the current tested file.* The test commands are also printed as here with `./selfie -c test/input_test.c -v 3 -n 2`.

```bash
cat log_118.11.17.2.9.txt
~~~--~~~------~~~---~~~ test/input_test.c:
At line 8 is false == <8,false>?
. . . ok!
At line 6 is <0, 10, 1> == <6,0,10,1>?
. . . ok!
PASS
- - - - - - -
1 test(s) executed
```
Congrats, you passed your first Littlemonster test!

# Expected value format
The expected format to specify test headers is the following:
```bash
"// [" command_line ';' {output ';'}* ']'
with output :=        '<'line ',' start ',' end ',' step '>'
                    | '< 'line ',' "false" '>'
                    | '<' line ',' "true" '>'
```
