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

The answer to that question depends on what we would like the machine to do, it depends on the application. But most applications have nothing to do with individual bits. We need formalisms that allow us to formalize what we want the machine to do on the level of the applications we are interested in. This is the reason why high-level programming languages were invented.

Since there are new applications or at least application characteristics appearing all the time new programming languages are also invented all the time. The key to being able to follow that trend is to understand the principles of programming languages and how they translate to machine level.

The programming language C of which we use a tiny subset here was originally designed for programming systems software such as operating systems and compilers. However, C has become very popular in many other application domains as well. Programming in C is called *imperative programming* which closely matches the imperative nature of most computers. It is therefore relatively straightforward to compile C code to machine code and manipulate machine states in C code even at the level of individual bits.

[Imperative Programming](https://en.wikipedia.org/wiki/Imperative_programming)
: A programming paradigm that uses statements that change program's state. In much the same way that the imperative mood in natural languages expresses commands, an imperative program consists of commands for the computer to perform. Imperative programming focuses on describing how a program operates.

Before explaining how C\* statements work, we introduce C\* language elements that allow us to describe program state as a high-level abstraction of machine state. Statements in C\* then operate on that program state.

Note that imperative programming is not the only programming paradigm. *Declarative programming*, for example, is an important alternative paradigm that models program state differently.



### Declarations

[Declaration](https://en.wikipedia.org/wiki/Declaration_(computer_programming) "Declaration")
: Specifies properties of an identifier: it declares what a word (identifier) means. Declarations are most commonly used for functions, variables, constants, and classes. Beyond the name (the identifier itself) and the kind of entity (function, variable, etc.), declarations typically specify the data type (for variables and constants), or the type signature (for functions). The term "declaration" is frequently contrasted with the term "definition", but meaning and usage varies significantly between languages.

### Definitions

## Control Flow

[Control Flow](https://en.wikipedia.org/wiki/Control_flow "Control Flow")
: The order in which individual statements, instructions or function calls of an imperative program are executed or evaluated. The emphasis on explicit control flow distinguishes an imperative programming language from a declarative programming language.

## Program Counter

[Program Counter (PC)](https://en.wikipedia.org/wiki/Program_counter "Program Counter (PC)")
: A processor register that indicates where a computer is in its program sequence. In most processors, the PC is incremented after fetching an instruction, and holds the memory address of ("points to") the next instruction that would be executed. Instructions are usually fetched sequentially from memory, but control transfer instructions change the sequence by placing a new value in the PC. These include branches (sometimes called jumps), subroutine calls, and returns. A transfer that is conditional on the truth of some assertion lets the computer follow a different sequence under different conditions. A branch provides that the next instruction is fetched from somewhere else in memory. A subroutine call not only branches but saves the preceding contents of the PC somewhere. A return retrieves the saved contents of the PC and places it back in the PC, resuming sequential execution with the instruction following the subroutine call.

## Statements

## Procedures

### Recursion