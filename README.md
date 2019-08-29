# Littlemonster [![Build Status](https://travis-ci.org/cksystemsteaching/selfie.svg?branch=littlemonster)](https://travis-ci.org/cksystemsteaching/selfie/branches)

*Monster* is a symbolic engine based on *selfie*.
Read [selfie.md](https://github.com/cksystemsteaching/selfie/blob/littlemonster/selfie.md) to know more about the *selfie* version.

The symbolic engine is invoked by the option `-n` and interprets the 0-64 value as fuzzing parameter. Value 0 means that code is executed symbolically but without any fuzzing of its input. In other words, code execution uses the symbolic execution engine but is effectively concrete. The 64 value, on the other hand, means that all input read from files is fuzzed to the extent that any machine word read from files may represent any 64-bit value.

## Bugs Hunting
*Monster* tests your binary for several possible executions. For instance, the following command compiles the file [**read_test**](https://github.com/cksystemsteaching/selfie/blob/littlemonster/test/read_test.c) (`-c`) and symbolically executes it fuzzing any *reads* with `+-2^2`.
```bash
$ ./selfie -c test/read_test.c selfie.c -n 2
[...]
./selfie: selfie executing test/read_test.c with 2MB physical memory on monster
./selfie: backtracking 1
./selfie: selfie terminating test/read_test.c with exit code 0
```
By default the engine only prints the number of backtracks, that is to say the number of distinct paths executed.
The verbose option `-v`
prints more about the symbolic state.
```bash
$ ./selfie -c test/read_test.c selfie.c -v 1 -n 2
[...]
./selfie: selfie executing test/read_test.c with 2MB physical memory on monster
./selfie: test/read_test.c reaching end point at: 0x00000294(~35) with exit code <49,52,1>
./selfie: backtracking 1
./selfie: selfie terminating test/read_test.c with exit code 0
```
Contrary to usual symbolic execution engines,
*monster* uses [abstract domains](https://en.wikipedia.org/wiki/Abstract_interpretation#Examples_of_abstract_domains) and executes a program with sets of concrete values.
Here, the triple `<49,52,1>` specifies that the set of possible exit code values is `{49, 50, 51, 52}` which are the fuzzed values read with the option `-n 2`.

### Specify your values
The system call `input` allows to insert a symbolic value into a variable.
For instance,
the file [**input_test**](https://github.com/cksystemsteaching/selfie/blob/littlemonster/test/input_test.c) is executed
for a value of `x` from `0` to `10` with verbose `2`.
```bash
$ ./selfie -c test/input_test.c -v 2 -n 2
[...]
./selfie: selfie executing test/input_test.c with 2MB physical memory on monster
./selfie: test/input_test.c reaching end point at: 0x000001BC(~6) with exit code <0,10,1>
./selfie: instructions:           - total 65 : path 65(53.27% of 122 instructions).
./selfie:                symbolic - total 11(16.92%).
./selfie: trace:   length 18
./selfie: state:   2 symbolic variable(s) and 2 assignment(s), 0 symbolic call(s), and 0 correction(s).
./selfie: memory:  1184(0.05%)
./selfie: end with 1 symbolic input value(s):
./selfie:  -  symbolic 1 from @16{0xFFFFFFA8=(0,10,1)} at 0x101A0(~4) -> @17{0xFFFFFFA8=(0,10,1)} (100.00%)
./selfie: backtracking 1
```
At each end point,
the verbose `2` outputs
the set of possible exit code values,
the number of instructions executed,
the number of symbolic memory entries,
the whole symbolic states with its memory consumption, and
for each symbolic variable
the set of values and the line
of its initialization and ending points
(the possible values to reproduce that path) with its input coverage.

In our case,
there is only one possible path with `11` symbolic instructions (among `65`).
The engine executed `53.27%` of the program instructions.
There are `18` trace entries
and two symbolic variables
using `1184`Bytes.
Finally, the set of input values created at line `4`
is completely covered,
meaning that the same path is taken
for `x` between `0` and `10`.

#### Verbose values
The option values `-v 3` and `-v 4` print the unreachable branches *during a path execution*,
and `-v 5` enables the symbolic debugger which is similar to `-d` but with symbolic values.

### Bounded Execution
```c
// symbolic BOUNDS
uint64_t MAX_TRACE_LENGTH
uint64_t MAX_PATH_LENGTH
uint64_t MAX_SYMBOLIC
uint64_t MAX_CORRECTION
uint64_t MAX_ALIAS
uint64_t MAX_NODE
uint64_t MAX_ASSIGN
uint64_t MAX_PREDECESSOR
uint64_t MAX_CALL
```

*Monster* has constants to limit
a symbolic execution.
Whenever the execution reaches one of that constant, the current path is aborted and the engine backtracks.
- `MAX_TRACE_LENGTH` limits the number of values stored into the symbolic memory.
- *Monster* executes a path until `MAX_PATH_LENGTH` instructions and will not analyze further.
- `MAX_SYMBOLIC` is the maximum number of symbolic inputs the analysis will consider (along one path), a next read will return `EOF`.
- `MAX_CORRECTION` is the number of relational domains stored into memory.
- `MAX_ALIAS` is the alias depth for which it is allowed to load a variable.
- `MAX_NODE` and `MAX_ASSIGN` are the number of symbolic variables and total assignments of a path
- `MAX_PREDECESSOR` the number of aliased assignments a symbolic variable can have.
- `MAX_CALL` the number of recursive symbolic calls a path can do.

# Test file
The script `test-script.pl` symbolically executes a folder of test files and checks their actual outputs. A `test` file is a **C*** file with a header specifying the command and the expected results.
```c
// [-c test/input_test.c -v 4 -n 2;<6,0,10,1>;<8,false>;]
uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t x;
  x = input(0, 10, 1);
  if( x < 15)
    return x;
  else
    return x;
}
```
In this test file, the program will be compiled and symbolically executed with verbose `4`. It is expected a symbolic exit code `<0,10,1>` at line `6` and an unreachable false branch at line `8` (the beginning of the else statement).
```bash
$ ./test-script.pl test/input_test.c
Log file in log_119.0.19.5.56.txt
run ./selfie -c test/input_test.c -v 4 -n 2
Log file in log_119.0.19.5.56.txt
```
Each run of `test-script.pl` will create a log file in which the tests and their results are listed (a folder can be passed to the script).

*Be aware that the path is checked against the first compiled .c file  and the current tested file.*

The following output depicts the result of feeding `input_test.c` to the script.
```bash
$ cat log_119.0.19.5.56.txt
~~~--~~~------~~~---~~~ test/input_test.c:
At line 8 is false == <8,false>?
. . . ok!
At line 6 is <0, 10, 1> == <6,0,10,1>?
. . . ok!
PASS
- - - - - - -
1 test(s) executed
```

# Expected value format
The expected format to specify test headers is the following:
```bash
"// [" command_line ';' (output ';')* ']'
with output :=        '<'line ',' start ',' end ',' step '>'
                    | '< 'line ',' "false" '>'
                    | '<' line ',' "true" '>'
```

The file `test.zip` contains the last regression tests for the `msuiid` (01/03/2019). To test your `monster` version, unzip it and run `make test`.
