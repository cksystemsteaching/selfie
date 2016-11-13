# 4. State {#state}

Computation is the evolution of state. At any given time, a computer stores a very large but still finite amount of bits in registers and memory. The values of all these bits together is what we call the state of the machine. Then the processor executes one instruction which directs it to change the values of a very small number of bits creating a new state. That process of change from one state to the next continues until the machine is turned off.

[State](https://en.wikipedia.org/wiki/State_(computer_science))
: The state of a digital logic circuit or computer program is a technical term for all the stored information, at a given instant in time, to which the circuit or program has access. The output of a digital circuit or computer program at any time is completely determined by its current inputs and its state.

Software on source and machine code level specifies for each state what the next state is. There are the data bits that are being changed and the code bits that determine that change. Input is typically modeled by data bits that are changed by something other than the processor such as a keyboard, for example.

In this chapter, we explain how on machine level registers and memory represent state and how machine code describes change of that state. We also show how source code provides a high-level view of program state and how that translates down to machine code level. Seeing both levels and how they connect is an important step towards learning how to code.

## Memory

A machine that can store n bits in registers and memory can distinguish 2^n^ states.

X> The mipster emulator implements a machine with 32 general purpose 32-bit registers and 3 special purpose 32-bit registers, explained below, and 64MB of memory.
X>
X> Therefore, a mipster machine can store 32\*32+3\*32+2^26^\*8 bits which is equal to 536872032 bits. Thus the machine can be in [2^536872032^](http://www.wolframalpha.com/input/?source=nav&i=2%5E536872032) different states, a number with 161,614,586 decimal digits. Imagine what a machine with gigabytes or even terabytes of memory can do.

Interestingly, we can always, at least in principle, partition that enormously large state space into a set of good states and a set of bad states. Software without bugs would always keep the machine in good states, or conversely, prevent the machine from ever going to a bad state. However, what is a good state?

The answer to that question depends on what we would like the machine to do, it depends on the application. But most applications have nothing to do with individual bits. We therefore need formalisms that allow us to formalize what we want the machine to do on the level of the applications we are interested in. This is the reason why high-level programming languages were invented.

Since there are new applications or at least application characteristics appearing all the time new programming languages are also invented all the time. The key to being able to follow that trend is to understand the principles of programming languages and how they translate to machine level.

The programming language C of which we use a tiny subset here was originally designed for programming systems software such as operating systems and compilers. However, C has become very popular in many other application domains as well. Programming in C is called *imperative programming* which closely matches the imperative nature of most computers. It is therefore relatively straightforward to compile C code to machine code and manipulate machine states in C code even at the level of individual bits.

[Imperative Programming](https://en.wikipedia.org/wiki/Imperative_programming)
: A programming paradigm that uses statements that change program's state. In much the same way that the imperative mood in natural languages expresses commands, an imperative program consists of commands for the computer to perform. Imperative programming focuses on describing how a program operates.

Imperative programming is supported by many programming languages but it is not the only programming paradigm. *Declarative programming* is an important alternative that is also supported by many programming languages but handles program state differently.

[Declarative Programming](https://en.wikipedia.org/wiki/Declarative_programming)
: A programming paradigm — a style of building the structure and elements of computer programs — that expresses the logic of a computation without describing its control flow.

Intuitively, rather than saying imperatively how to change state, declarative programming focuses on declaring what needs to change. While spelling out how to change state can become tedious with imperative programming spelling out what to change can become burdensome with declarative programming. Yet both paradigms have their important use cases and a port of selfie to a declarative programming language would be very nice to have but remains future work for now.

Before explaining how C\* code operates, we introduce C\* language elements that allow us to describe program state as a high-level abstraction of machine state. Code written in C\* then operates on that program state. Let us have a look at the following C\* program which we call the countdown program or just countdown:

{line-numbers=on, lang=c}
<<[The Countdown Program](code/countdown.c)

The program takes the decimal value 10 (Line 3) and decrements it (Line 13) until it reaches the decimal value 0 (Line 11) which is then returned (Line 19) as so-called *exit code*. To see for yourself run the [code](http://github.com/cksystemsteaching/selfie/blob/2b97bcfc85897ed2a3c421bb601cd8255ad3a3f3/manuscript/code/countdown.c) as follows:

```
> ./selfie -c manuscript/code/countdown.c -o countdown.m -s countdown.s -m 1
./selfie: this is selfie's starc compiling manuscript/code/countdown.c
./selfie: 625 characters read in 19 lines and 9 comments
./selfie: with 55(8.80%) characters in 28 actual symbols
./selfie: 1 global variables, 1 procedures, 0 string literals
./selfie: 0 calls, 1 assignments, 1 while, 0 if, 1 return
./selfie: 496 bytes generated with 122 instructions and 8 bytes of data
./selfie: 496 bytes with 122 instructions and 8 bytes of data written into countdown.m
./selfie: 4301 characters of assembly with 122 instructions written into countdown.s
./selfie: this is selfie's mipster executing countdown.m with 1MB of physical memory
countdown.m: exiting with exit code 0 and 0.00MB of mallocated memory
./selfie: this is selfie's mipster terminating countdown.m with exit code 0 and 0.00MB of mapped memory
./selfie: profile: total,max(ratio%)@addr(line#),2max(ratio%)@addr(line#),3max(ratio%)@addr(line#)
./selfie: calls: 1,1(100.00%)@0x17C(~11),0(0.00%),0(0.00%)
./selfie: loops: 10,10(100.00%)@0x190(~11),0(0.00%),0(0.00%)
./selfie: loads: 26,11(42.37%)@0x190(~11),10(38.46%)@0x1A4(~13),1(3.84%)@0x24(~1)
./selfie: stores: 13,10(76.92%)@0x1B0(~13),1(7.69%)@0x4C(~1),0(0.00%)
```

### Global Variables

For the countdown program to be able to operate on a number there needs to be memory to store that number. For this purpose, Line 3 in the source code *declares* a so-called *global variable* called `bar`. The starc compiler even reports that it found exactly that one global variable, see Line 5 in the above output.

[Global Variable](https://en.wikipedia.org/wiki/Global_variable)
: A variable with global scope, meaning that it is visible (hence accessible) throughout the program, unless shadowed. The set of all global variables is known as the global environment or global state.

So global really just means here that `bar` can be used throughout the program. Line 3 is thus a *declaration* that specifies that the identifier `bar` refers to the same variable in the whole program.

[Declaration](https://en.wikipedia.org/wiki/Declaration_(computer_programming) "Declaration")
: Specifies properties of an identifier: it declares what an identifier means. Declarations are most commonly used for functions, variables, constants, and classes. Beyond the name (the identifier itself) and the kind of entity (function, variable, etc.), declarations typically specify the data type (for variables and constants), or the type signature (for functions). The term "declaration" is frequently contrasted with the term "definition", but meaning and usage varies significantly between languages.

Line 3 not only declares `bar` but also *defines* the initial value of `bar` as the decimal value 10 represented by the integer literal `10`. The initial value of a global variable is nevertheless optional. Line 3 could be rewritten to `int bar;` in which case the value of `bar` would be initially undefined meaning it could initially be any value. Undefined values are a common source of errors, if programs depend on them. Modern compilers usually warn programmers about that (not starc though since we need to keep things simple). A simple way to avoid depending on undefined values is to either provide an initial value for a variable or to assign a value to a variable before using the variable in any computation, see below for more about how to do that. A program that does not depend on undefined values has a single initial state from which it begins all computations. This is what we want!

Note that the equality sign `=` in Line 3 is merely [syntactic sugar](https://en.wikipedia.org/wiki/Syntactic_sugar) making the code more readable while the [semicolon](https://en.wikipedia.org/wiki/Semicolon) `;` is a so-called *terminator* which indicates the end of a statement. After the semicolon we could insert more global variable declarations as long as they all were to introduce unique identifiers and were properly terminated with semicolons. Programming languages newer than C often make such terminators optional or omit them altogether since they are, similar to syntactic sugar, not necessary for the compiler to work and, unlike syntactic sugar, sometimes considered a burden.

Line 3 also specifies that the *data type* of `bar` is `int` which, according to the C standard, means that `bar` represents a signed 32-bit integer, that is, 32 bits encoding a positive or negative number in two's complement. It also means that arithmetic operations involving `bar` will be done with 32-bit wrap-around semantics.

[Data Type](https://en.wikipedia.org/wiki/Data_type)
: A classification of data which tells the compiler or interpreter how the programmer intends to use the data. Most programming languages support various types of data, for example: real, integer, or Boolean. A data type provides a set of values from which an expression (i.e. variable, function ...) may take its values. The type defines the operations that can be done on the data, the meaning of the data, and the way values of that type can be stored.

So, this is important! A data type tells us and the compiler what the intended meaning of the bits are that encode the data. Remember, bits can encode anything and have no meaning unless when changed by some operation. Data types therefore help with identifying meaning even without performing any operations.

A global variable of type `int` such as `bar` provides storage for 32 bits which happens to match the size of a word on a mipster machine. In fact, the value of `bar` will be stored in exactly one word somewhere in memory. First of all, this means that `bar` provides storage that is identified by the identifier `bar` and not by some memory address. But it also means that the program as is cannot access any other bits in memory than the 32 bits identified by `bar` which obviously reduces the size of the state space dramatically! So the program state space is much smaller than the machine state space and therefore much easier to reason about. However, there is also code in countdown that operates on `bar`. Let us have a closer look at how that is introduced in C\*.

### Procedures

The source code of the countdown program declares a so-called *procedure* called `main` in Line 6. The broader term for procedures is *subroutines* defined as follows.

[Subroutine](https://en.wikipedia.org/wiki/Subroutine)
: A sequence of program instructions that perform a specific task, packaged as a unit. This unit can then be used in programs wherever that particular task should be performed. Subprograms may be defined within programs, or separately in libraries that can be used by multiple programs. In different programming languages, a subroutine may be called a procedure, a function, a routine, a method, or a subprogram.

In C subroutines are called procedures. Line 6 specifies that `main` refers to a procedure rather than a global variable simply by using `()` after the identifier. In fact, it would be perfectly fine to just say `int main();`. The code enclosed in `{}`, however, also *defines* the implementation of the procedure. We get to that below. The `int` keyword before `main` specifies that the so-called [return type](https://en.wikipedia.org/wiki/Return_type) of the procedure is a signed 32-bit integer. This means that the procedure returns a signed 32-bit integer value when done.

Global variable and procedure declarations, as in Lines 3 and 6, may use any identifier not used anywhere else in the program. In other words, identifiers used in declarations must be unique. The `main` procedure name, however, is even more special because the `main` procedure is the one that is invoked when a C program starts executing. Thus a valid C program needs to contain exactly one declaration and definition of a procedure called `main`. Otherwise, the system would not "know" what to execute. See for yourself by renaming `main` in `countdown.c` to something else. When `main` returns the program stops executing and the system outputs the value returned by `main`, which is 0, as the previously mentioned exit code, see Line 10 in the above output.

There can be any number of global variable and procedure declarations in a C program. The starc compiler reports in Line 5 in the above output that there is exactly one procedure declared in `countdown.c` which is in fact the `main` procedure.

Line 7 in the above output mentions that starc generated exactly 496 bytes for `countdown.c` representing 122 instructions (remember each instruction takes 4 bytes) and 8 bytes of data (496=122\*4+8). The 122 instructions represent the machine code generated by starc for implementing the `main` procedure, that is, the C\* code in Lines 11-19 in `countdown.c`. Out of the 8 bytes of data, 4 bytes represent the initial value of `bar` which is 10. The other 4 bytes encode the amount of bytes needed to represent the instructions, that is, the value 488 which is equal to 122\*4. This information is necessary to determine which bytes are code and which are data.

Selfie can write the generated bytes into a [binary file](https://en.wikipedia.org/wiki/Binary_file) (using the `-o` option) that can later be loaded again (using the `-l` option) and executed (using the `-m` option, for example). In our example, selfie is instructed to write the generated bytes, also called *executable code* or just [executable](https://en.wikipedia.org/wiki/Executable), into a binary file called `countdown.m`, as reported in Line 8 in the above output. The format of that file is very simple. It begins with the 4 bytes encoding the number of bytes of code (representing 488 here), followed by the 488 bytes of code, followed by the 4 bytes of data (representing 10 here). That's it.

We also instructed selfie to generate an assembly file `countdown.s` for the countdown program (using the `-s` option) that represents a human-readable version of the binary file `countdown.m`. Selfie reports on that in Line 9 in the above output. Note that `countdown.s` only contains code but not any data such as the initial value of `bar`.

### Program Break

[Program Break](https://en.wikipedia.org/wiki/Sbrk)

## Code

[Control Flow](https://en.wikipedia.org/wiki/Control_flow "Control Flow")
: The order in which individual statements, instructions or function calls of an imperative program are executed or evaluated. The emphasis on explicit control flow distinguishes an imperative programming language from a declarative programming language.

### Program Counter

[Program Counter (PC)](https://en.wikipedia.org/wiki/Program_counter "Program Counter (PC)")
: A processor register that indicates where a computer is in its program sequence. In most processors, the PC is incremented after fetching an instruction, and holds the memory address of ("points to") the next instruction that would be executed. Instructions are usually fetched sequentially from memory, but control transfer instructions change the sequence by placing a new value in the PC. These include branches (sometimes called jumps), subroutine calls, and returns. A transfer that is conditional on the truth of some assertion lets the computer follow a different sequence under different conditions. A branch provides that the next instruction is fetched from somewhere else in memory. A subroutine call not only branches but saves the preceding contents of the PC somewhere. A return retrieves the saved contents of the PC and places it back in the PC, resuming sequential execution with the instruction following the subroutine call.

### Statements