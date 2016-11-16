# 4. State {#state}

Computation is the evolution of state. At any given time, a computer stores a very large but still finite amount of bits in memory and registers. The values of all these bits together is what we call the state of the machine. Then the processor executes one instruction which directs it to change the values of a very small number of bits creating a new state. That process of change from one state to the next continues until the machine is turned off.

[State](https://en.wikipedia.org/wiki/State_(computer_science))
: The state of a digital logic circuit or computer program is a technical term for all the stored information, at a given instant in time, to which the circuit or program has access. The output of a digital circuit or computer program at any time is completely determined by its current inputs and its state.

Software on source and machine code level specifies for each state what the next state is. There are the data bits that are being changed and the code bits that determine that change. Input is typically modeled by data bits that are changed by something other than the processor such as a keyboard, for example.

In this chapter, we explain how on machine level memory and registers represent state and how machine code describes change of that state. We also show how source code provides a high-level view of program state and how that translates down to machine code level. Seeing both levels and how they connect is an important step towards learning how to code.

## Machine

Most general-purpose computers today are based on what is known as the *von Neumann model* or *von Neumann architecture*.

[Von Neumann Architecture](https://en.wikipedia.org/wiki/Von_Neumann_architecture)
: A computer architecture, described in 1945 by the mathematician and physicist John von Neumann and others, for an electronic digital computer with parts consisting of a processing unit containing an arithmetic logic unit and processor registers; a control unit containing an instruction register and program counter; a memory to store both data and instructions; external mass storage; and input and output mechanisms.

![Von Neumann Architecture](images/von-neumann-architecture.png "Von Neumann Architecture")

The CPU and main memory in a typical computer correspond to the processing unit and memory of a von Neumann architecture, respectively. The mipster emulator is no exception. It emulates a *von Neumann machine*.

The key idea is very simple. A von Neumann machine is a [stored-program computer](https://en.wikipedia.org/wiki/Stored-program_computer) which stores both code and data in the same memory. In fact, in memory there is really no distinction between code and data. A von Neumann machine fetches code from memory and executes it. The code will in turn instruct the machine to load data from memory into registers, perform some computation on registers, and finally store the results back in memory. We explain the details of how this works below. For now it is only important to understand that bits fetched from memory and executed happen to represent code in that moment while bits loaded from memory into registers, then modified, and finally stored back in memory represent data in that moment. At all other times, they are just bits.

## Memory

A von Neumann machine that can store n bits in memory and registers can distinguish 2^n^ states.

X> The mipster emulator implements a von Neumann machine with 64MB of memory, and 32 general-purpose 32-bit registers and 3 special-purpose 32-bit registers, explained below.
X>
X> Therefore, a mipster machine can store 2^26^\*8+32\*32+3\*32 bits which is equal to 536872032 bits. Thus the machine can be in [2^536872032^](http://www.wolframalpha.com/input/?source=nav&i=2%5E536872032) different states, a number with 161,614,586 decimal digits. Imagine what a machine with gigabytes or even terabytes of memory can do.

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

Before explaining how C\* code works, we introduce C\* language elements that allow us to describe program state as a high-level abstraction of machine state. Code written in C\* then operates on that program state. Let us have a look at the following C\* program which we call the countdown program or just countdown:

{line-numbers=on, lang=c}
<<[The Countdown Program](code/countdown.c)

The program takes the decimal value 10 (Line 3) and decrements it (Line 13) until it reaches the decimal value 0 (Line 11) which is then returned (Line 19) as so-called *exit code*. To see for yourself run the [code](http://github.com/cksystemsteaching/selfie/blob/2b97bcfc85897ed2a3c421bb601cd8255ad3a3f3/manuscript/code/countdown.c) as follows:

{line-numbers=on}
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

So, this is important! A data type tells us and the compiler what the intended meaning of the bits are that encode the data. Remember, bits can encode anything and have no meaning unless they are involved in an operation. Data types therefore help with identifying meaning even without performing any operations.

A global variable of type `int` such as `bar` provides storage for 32 bits which happens to match the size of a word on a mipster machine. In fact, the value of `bar` will be stored in exactly one word somewhere in memory. First of all, this means that `bar` provides storage that is identified by the identifier `bar` and not by some memory address. But it also means that the program as is cannot access any other bits in memory than the 32 bits identified by `bar` which obviously reduces the size of the state space dramatically! So the program state space is much smaller than the machine state space and therefore much easier to reason about. However, there is also code in countdown that operates on `bar`. Let us have a closer look at how that is introduced in C\*.

### Procedures

The source code of the countdown program declares a so-called *procedure* called `main` in Line 6. The broader term for procedures is *subroutines* defined as follows.

[Subroutine](https://en.wikipedia.org/wiki/Subroutine)
: A sequence of program instructions that perform a specific task, packaged as a unit. This unit can then be used in programs wherever that particular task should be performed. Subprograms may be defined within programs, or separately in libraries that can be used by multiple programs. In different programming languages, a subroutine may be called a procedure, a function, a routine, a method, or a subprogram.

In C subroutines are called procedures. Line 6 specifies that `main` refers to a procedure rather than a global variable simply by using `()` after the identifier. In fact, it would be perfectly fine to just say `int main();`. The code enclosed in `{}`, however, also *defines* the implementation of the procedure. We get to that below. The `int` keyword before `main` specifies that the so-called [return type](https://en.wikipedia.org/wiki/Return_type) of the procedure is a signed 32-bit integer. This means that the procedure returns a signed 32-bit integer value when done.

Global variable and procedure declarations, as in Lines 3 and 6, may use any identifier not used anywhere else in the program. In other words, identifiers used in declarations must be unique. The `main` procedure name, however, is even more special because the `main` procedure is the one that is invoked when a C program starts executing. Thus a valid C program needs to contain exactly one declaration and definition of a procedure called `main`. Otherwise, the system would not "know" what to execute. See for yourself by renaming `main` in `countdown.c` to something else. When `main` returns the program stops executing and the system outputs the value returned by `main`, which is 0, as the previously mentioned exit code, see Line 10 in the above output.

There can be any number of global variable and procedure declarations in a C program. The starc compiler reports in Line 5 in the above output that there is exactly one procedure declared in `countdown.c` which is in fact the `main` procedure.

Line 7 in the above output mentions that starc generated exactly 496 bytes for `countdown.c` representing 122 instructions (remember each instruction takes 4 bytes) and 8 bytes of data (496=122\*4+8). The 122 instructions represent the machine code generated by starc for implementing the `main` procedure, that is, the C\* code in Lines 11-19 in `countdown.c`. Out of the 8 bytes of data, 4 bytes represent the initial value of `bar` which is 10. The other 4 bytes encode the amount of bytes needed to represent the instructions, that is, the value 488 which is equal to 122\*4. This information is necessary to determine which bytes are code and which are data.

Selfie can [write](http://github.com/cksystemsteaching/selfie/blob/1d595e36388e2621f4dd24d541f04856547c7a5d/selfie.c#L4448-L4497) the generated bytes into a *binary file* or just *binary* (using the `-o` option) that can later be [loaded](http://github.com/cksystemsteaching/selfie/blob/1d595e36388e2621f4dd24d541f04856547c7a5d/selfie.c#L4531-L4601) again (using the `-l` option) and [executed](http://github.com/cksystemsteaching/selfie/blob/1d595e36388e2621f4dd24d541f04856547c7a5d/selfie.c#L6934-L6984) (using the `-m` option, for example).

[Binary File](https://en.wikipedia.org/wiki/Binary_file)
: A computer file that is not a text file. The term "binary file" is often used as a term meaning "non-text file". Binary files are usually thought of as being a sequence of bytes, which means the binary digits (bits) are grouped in eights. Binary files typically contain bytes that are intended to be interpreted as something other than text characters. Compiled computer programs are typical examples; indeed, compiled applications are sometimes referred to, particularly by programmers, as binaries.

In our example, selfie is instructed to write the generated bytes into a binary file called `countdown.m`, as reported in Line 8 in the above output. The `countdown.m` binary is what is known as an *executable*.

[Executable](https://en.wikipedia.org/wiki/Executable)
: Causes a computer "to perform indicated tasks according to encoded instructions," as opposed to a data file that must be parsed by a program to be meaningful. These instructions are traditionally machine code instructions for a physical CPU.

We may use the terms binary and executable interchangeably even though, strictly speaking, there are binary files such as image files, for example, that are obviously not executable. However, executables are usually binaries.

The format of the `countdown.m` executable is very simple. It begins with [the 4 bytes encoding the number of bytes of code](http://github.com/cksystemsteaching/selfie/blob/1d595e36388e2621f4dd24d541f04856547c7a5d/selfie.c#L4480) (representing 488 here) followed by [the 488 bytes of code followed by the 4 bytes of data](http://github.com/cksystemsteaching/selfie/blob/1d595e36388e2621f4dd24d541f04856547c7a5d/selfie.c#L4485) (representing 10 here). That's it.

When invoking selfie on the countdown program, we also instructed selfie to [produce](http://github.com/cksystemsteaching/selfie/blob/1d595e36388e2621f4dd24d541f04856547c7a5d/selfie.c#L6366-L6423) an assembly file `countdown.s` for the countdown program (using the `-s` option) that represents a human-readable version of the binary file `countdown.m`. Selfie reports on that in Line 9 in the above output. Note that `countdown.s` only contains code but not any data such as the initial value of `bar`.

Ok, but what happens now when selfie is instructed by the final `-m 1` option to execute the generated code? Doing that involves solving a problem that appears to have no solution. How does a computer load an executable into memory without an executable in memory that instructs the processor how to do this? The process that solves that problem is called *bootstrapping*.

[Bootstrapping](https://en.wikipedia.org/wiki/Bootstrapping)
: A self-starting process that is supposed to proceed without external input. In computer technology the term (usually shortened to [booting](https://en.wikipedia.org/wiki/Booting)) usually refers to the process of loading the basic software into the memory of a computer after power-on or general reset, especially the operating system which will then take care of loading other software as needed.

A computer typically bootstraps itself by having the processor initially fetch, decode, and execute machine code from some non-volatile memory rather than volatile main memory. That machine code implements a so-called *boot loader* which instructs the processor to load the code that the processor is actually supposed to execute from some external source and store it in main memory. When done, the boot loader instructs the processor to start fetching, decoding, and executing the code stored in main memory.

### Layout

Before launching the mipster emulator, selfie [bootstraps](http://github.com/cksystemsteaching/selfie/blob/90815070126adc8d8fc6b525d307debe075d7d0c/selfie.c#L6876-L6932) mipster exactly like a computer bootstraps itself. First of all, the emulated memory and registers are all *zeroed*, that is, set to `0x0`. The machine code and data generated by starc (or loaded from a binary file) is then [copied](http://github.com/cksystemsteaching/selfie/blob/90815070126adc8d8fc6b525d307debe075d7d0c/selfie.c#L6604-L6615) into the emulated memory starting at the lowest address `0x0`. The portions of memory where code and data are located are also called the *code segment* and the *data segment*, respectively. The result is the following memory layout.

![Memory Layout](images/memory-layout.png "Memory Layout")

With code and data copied to memory the machine is essentially ready to go. The rest of the memory layout will be explained in later chapters. For now we only need to know that the border between code and data and the rest of memory is the [program break](https://en.wikipedia.org/wiki/Sbrk) which divides memory into *statically* and *dynamically* allocated storage. The addresses of the code and data stored in memory below the program break will not change while the storage above the program break may be used for different purposes during execution. Keep in mind though that the memory layout we describe here is only one choice out of many possible choices. However, that layout is probably the most widely adopted choice today.

Going back to C\* in general and the countdown program in particular, global variable and procedure declarations specify exactly what is below the program break, what is code and data, and what the code does with the data, as we see next. Most important here is to understand that the state of memory is fully determined after copying the code for procedures and the data for global variables into memory. While countdown is a simple program think of the code and data for selfie. There are hundreds of global variable and procedure declarations in `selfie.c` but it is still the same thing. The fact that C\* allows us to talk about variables and procedures without worrying about memory layout is a key ingredient for managing the enormously large state space. The only missing piece now for a complete picture is the state of the registers. Let us take a look at that next!

## Registers

How does a computer "know" what to execute? After all the bits in memory could mean anything. They could be code, they could be data, anything. But the answer to that question can anyway not be any simpler.

### Program Counter

Processors based on the von Neumann model feature a special-purpose register as part of their control unit called the *program counter* (PC). The PC of the machine emulated by mipster is, unsurprisingly, yet another 32-bit register.

[Program Counter (PC)](https://en.wikipedia.org/wiki/Program_counter "Program Counter (PC)")
: A processor register that indicates where a computer is in its program sequence. In most processors, the PC is incremented after fetching an instruction, and holds the memory address of ("points to") the next instruction that would be executed. Instructions are usually fetched sequentially from memory, but control transfer instructions change the sequence by placing a new value in the PC. These include branches (sometimes called jumps), subroutine calls, and returns. A transfer that is conditional on the truth of some assertion lets the computer follow a different sequence under different conditions. A branch provides that the next instruction is fetched from somewhere else in memory. A subroutine call not only branches but saves the preceding contents of the PC somewhere. A return retrieves the saved contents of the PC and places it back in the PC, resuming sequential execution with the instruction following the subroutine call.

At boot time, when selfie is done zeroing all emulated memory and registers, in particular the PC, and copying code and data into memory, mipster is ready to start code execution, well, at the lowest memory address `0x0` because that is where the PC points to. From then on mipster [fetches the word in memory where the PC points to, decodes that word, and executes the resulting instruction](http://github.com/cksystemsteaching/selfie/blob/322ab8249e5cbd921735f5239ef6965b416489cc/selfie.c#L6289-L6291). Each instruction not only instructs the processor to perform some computation but also determines the next value of the PC so that the processor "knows" where in memory the next instruction is stored. That sequence of PC values is called *control flow*.

[Control Flow](https://en.wikipedia.org/wiki/Control_flow "Control Flow")
: The order in which individual statements, instructions or function calls of an imperative program are executed or evaluated. The emphasis on explicit control flow distinguishes an imperative programming language from a declarative programming language.

Let us take a look at how the first few instructions for the countdown program execute. You will need to scroll back to the beginning after the following command though since selfie will output the whole sequence of executed instructions:

{line-numbers=off}
```
> ./selfie -c manuscript/code/countdown.c -d 1
./selfie: this is selfie's starc compiling manuscript/code/countdown.c
./selfie: 625 characters read in 19 lines and 9 comments
./selfie: with 55(8.80%) characters in 28 actual symbols
./selfie: 1 global variables, 1 procedures, 0 string literals
./selfie: 0 calls, 1 assignments, 1 while, 0 if, 1 return
./selfie: 496 bytes generated with 122 instructions and 8 bytes of data
./selfie: this is selfie's mipster executing manuscript/code/countdown.c with 1MB of physical memory
manuscript/code/countdown.c: $pc=0x0(~1): 0x240801EC: addiu $t0,$zero,492: $t0=0,$zero=0 -> $t0=492
manuscript/code/countdown.c: $pc=0x4(~1): 0x251C0000: addiu $gp,$t0,0: $gp=0,$t0=492 -> $gp=492
manuscript/code/countdown.c: $pc=0x8(~1): 0x24080FFF: addiu $t0,$zero,4095: $t0=492,$zero=0 -> $t0=4095
manuscript/code/countdown.c: $pc=0xC(~1): 0x24094000: addiu $t1,$zero,16384: $t1=0,$zero=0 -> $t1=16384
manuscript/code/countdown.c: $pc=0x10(~1): 0x01090019: multu $t0,$t1: $t0=4095,$t1=16384,$lo=0 -> $lo=67092480
manuscript/code/countdown.c: $pc=0x14(~1): 0x00004012: mflo $t0: $t0=4095,$lo=67092480 -> $t0=67092480
manuscript/code/countdown.c: $pc=0x18(~1): 0x00000000: nop
manuscript/code/countdown.c: $pc=0x1C(~1): 0x00000000: nop
manuscript/code/countdown.c: $pc=0x20(~1): 0x25083FFC: addiu $t0,$t0,16380: $t0=67092480,$t0=67092480 -> $t0=67108860
manuscript/code/countdown.c: $pc=0x24(~1): 0x8D1D0000: lw $sp,0($t0): $sp=0,$t0=0x3FFFFFC -> $sp=67108816=memory[0x3FFFFFC]
...
```

Line 9 shows the first instruction executed by mipster and reads as follows. The PC denoted by `$pc` points to memory address `0x0`. The instruction at this address has been generated by starc for source code at approximately line number `~1` in `countdown.c`. Even though there is a comment at that line number this does make sense because the instruction is actually part of code for initializing the machine further and is always generated by starc for any source code. The instruction itself is encoded in the word `0x240801EC` which stands for `addiu $t0,$zero,492`.

Now, here is the interesting part. The remaining output `$t0=0,$zero=0 -> $t0=492` tell us which part of the state space (memory, registers) the instruction depends on and what the affected state actually is right before executing the instruction (`$t0=0,$zero=0` to the left of the arrow `->`) and which part of the state space changed and how after executing the instruction (`$t0=492` to the right of `->`). In other words, the instruction depends on the values in the two registers `$t0` and `$zero` that both contain 0 and the instruction changes the value in register `$t0` to 492. This is because `addiu $t0,$zero,492` instructs the processor to add the value 492 to the value in register `$zero` which always is 0 and store the result in register `$t0`.

Also, very important and not to forget, `addiu $t0,$zero,492` makes the processor increment the `$pc` register from `0x0` to `0x4` so that the next instruction executed by the processor is the instruction at memory address `0x4` that immediately follows the current instruction in memory. Incrementing the PC like that creates so-called *sequential* control flow. Most instructions actually do that, not just `addiu`. There are, however, also instructions that can alter the control flow by setting the `$pc` register depending on the values in registers other than `$pc`. We explain that below.

This takes us to the next instruction at memory address `0x4`. Its effect on the machine state is that the value in the `$gp` register is set to 492 because it instructs the processor to add 0 to the value in register `$t0` which is currently 492 and store the result in `$gp`. Also, the value of the `$pc` register is incremented to `0x8`.

What is the purpose of the first two instructions? Simple. They are meant to [initialize](http://github.com/cksystemsteaching/selfie/blob/d5e3134063256d509752fe381a9fdcb76bb65ff2/selfie.c#L3941-L3944) the `$gp` register which stands for *global pointer*. Why do we use two instructions instead of one? Good question. Just using `addiu $gp,$zero,492` would do the trick as well. The reason why we are not doing this is because it makes the compiler simpler, and better performance through using fewer instructions and fewer registers is not our focus here. It is, however, of major concern in state-of-the-art compilers.

More important here is the question as to why `$gp` is initialized to 492? Because 492, 0x1EC in hexadecimal, is the address of the first word after the code and data segments in memory which occupies exactly, well, 492 bytes but starting from address `0x0`. But wait, 492 is in this case the program break, right? Yes and no. It is but we anyway use as program break in selfie a higher, more conservative [address independent of code and data size](http://github.com/cksystemsteaching/selfie/blob/8848bdcf88f20087e7b602cf0ac7f6517ad0cbe7/selfie.c#L1098) because it is simpler to implement.

The purpose of the `$gp` register is to provide a fixed point of reference for referring to the memory words that store global variables. We only need to know the offset of how far below `$gp` the word of a global variable is located in the data segment. So, what is the offset of the memory word relative to the `$gp` register that stores the value of the global variable `bar`? Think about it! This is clarified and explained in more detail below.

Before continuing take a look at the next eight instructions in the above output. Their purpose is to [load the word at the highest address in the 64MB memory](http://github.com/cksystemsteaching/selfie/blob/d5e3134063256d509752fe381a9fdcb76bb65ff2/selfie.c#L3952-L3956) emulated by mipster into the `$sp` register which stands for *stack pointer*. The reason for that becomes clear in later chapters. Interesting here is to see how the highest address which is 2^26^-4=67108860=0x3FFFFFC is loaded into register `$t0`. Remember that 64MB is 2^26^ bytes. The highest address is thus 2^26^ bytes subtracted by 4 bytes because memory addresses start at `0x0` and need to be word-aligned.

Now, the issue is that 0x3FFFFFC requires 26 bits but the signed integer argument of `addiu` is only 16 bits. The solution is to break that large number into smaller numbers using left and logical right shift and then arithmetics to recompute the original number. Here, we exploit that with signed 32-bit integer arithmetics 2^26^-4=(2^26^-4)/2^14^\*2^14^+(2^26^-4)-(2^26^-4)/2^14^\*2^14^=67092480+67108860-67092480=67092480-16380=4095\*16384+16380 where all three numbers fit into 16-bit signed integers and can therefore be loaded into registers through immediate addressing with `addiu`.

The multiplication is then performed by the instruction `multu $t0,$t1` which multiplies the value in `$t0` with the value in `$t1` and stores the 32 LSBs of the 64-bit result in a special-purpose 32-bit register called `$lo`. An actual MIPS processor would also store the 32 MSBs in another special-purpose 32-bit register called `$hi` which we nevertheless ignore here. We simply assume that multiplication results requiring more than 32 bits wrap around. However, `$hi` is used for integer division in mipster just like on a MIPS32 processor. The `$lo` and `$hi` registers are together with the `$pc` register the 3 special-purpose registers of a mipster machine that we mentioned above. At boot time, `$lo` and `$hi` are also zeroed just like all other registers. This is in fact now the complete machine state, no more surprises.

In order to access the result in `$lo` we use the instruction `mflo $t0` which copies the value in `$lo` to `$t0`. The following two `nop` instructions do not do anything other than advancing the PC to the next instruction. They are there for historical reasons that we can safely ignore here. After adding 16380 to the value in `$t0` we have the desired value 0x3FFFFFC in `$t0`. The following `lw $sp,0($t0)` instruction loads the word (`lw`) stored at the memory address stored in `$t0` plus 0 into the `$sp` register. This is called *register-relative addressing*. We hear more about that below and never mind here why we are loading that word.

Imagine, it took us ten instructions to get the integer value 492 into `$gp` and the value at memory address 0x3FFFFFC into `$sp`. We definitely need a higher-level programming language to raise the level of abstraction. However, as tedious as the machine level might be, it is completely deterministic and rather easy to understand.

For now, the important take-away message here is that we can reconstruct the full state of the machine at any instruction in the above output just by following the arrows `->` line by line until that instruction. If you still cannot believe that a computer really is so simple and does work in these tiny steps and does so completely deterministically it is time to reflect about that here again. The machine starts in some given state and proceeds from there by changing very few bits in each step instructed by other bits that are identified by the program counter. That's it. The only reason why computers appear to be so powerful is because they are so fast and can store enormous amounts of bits. This even applies to computers appearing to do many things at the same time. They don't. When looking close enough things happen step by step.

### Statements

Mention string handling using the "Hello World!" program.

## Summary

| High-Level Programming Construct | Low-Level Machine Artifact |
| -------------------------------- | -------------------------- |
| Global Variable Declaration      | Data Location in Memory |
| Global Variable Definition       | Initial Value in Memory |
| Data Type                        | Intended Meaning of Bits |
| Procedure Declaration            | Code Location in Memory |
| Procedure Definition             | Actual Code in Memory |
| Statement                        | Machine Instructions |
| Current Statement                | Program Counter |

| High-Level Programming Construct | Low-Level Machine Artifact |
| -------------------------------- | -------------------------- |
| Character Literal in Definition  | Data: Character in Memory Word |
| Character Literal in Expression  | Code: Character in Instruction Argument |
| String Literal in Expression     | Data: Characters in Memory Words |
|                                  | Code: Address in Instruction Argument |
| Integer Literal in Definition    | Data: Value in Memory Word |
| Integer Literal in Expression    | Code: Value in Instruction Argument |
| Variable in Expression           | Code: Load Memory Word into Register |
| Arithmetic/Comparison Operator   | Code: Compute with Registers |
| Assignment                       | Code: Store Register into Memory Word |
| While Statement                  | Code: Forward and Backward Branching |