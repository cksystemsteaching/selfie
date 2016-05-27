# 4. Architecture and Language

{#architecture}

The idea of this chapter is to explain how computers work in principle and how to program them using a set of simple examples. The focus is on understanding the relationship of computer (architecture) and programming (language) as early as possible. This is in contrast to the traditional approach of teaching both topics in separate classes, or even just teaching programming without ever explaining how the machine works. We believe that knowing how computers work in principle is important for programming. Gladly, it is not that hard to figure out how they work. The principles of *computer architecture* still remain relatively simple since the physics of a digital computer can be completely hidden by Boolean logic. To us the machine is just handling bits, true and false, nothing else. I still remember the computer architecture class that I took as freshman. I liked it a lot because everything was clean and simple.

[Computer Architecture](https://en.wikipedia.org/wiki/Computer_architecture "Computer Architecture")
: A set of rules and methods that describe the functionality, organization, and implementation of computer systems.

Programming, on the other hand, is more difficult and can get very messy since software can grow arbitrarily complex. We believe the key to becoming a good programmer is to develop a deep sense for semantics. What is the true meaning of a piece of code? Have I really understood what happens when the machine executes that code? There is of course also the right choice of programming languages and the professional use of software development tools but it all begins with truly understanding the meaning of code.

Imagine you are taking a class to learn a foreign language. One particularly interesting type of class is when the language is taught by speaking in that language without using any other language. This means that as soon as the class starts the teacher exclusively speaks in the language that everyone would like to learn but does not understand. This approach anyway works because the teacher may use means of communication other than spoken language such as gestures, facial expressions, and even body language. Questions may be asked in a language that everyone understands but answers are always given in the foreign language. Students are anyway encouraged to use the foreign language as soon as possible and eventually even ask questions in that language.

We do something similar here. We explain how a computer works using examples written in the language that the computer *speaks* but we do not yet understand. That language is called machine code. However, we use Boolean logic and elementary algebra that everyone is familiar with as *body language* to clarify the meaning of machine code. Hard to believe but machine code is so simple that Boolean logic and elementary algebra is enough. The only problem is that machine code is not really a language that anyone but a few computer engineers enjoy. Most code these days is actually written in higher-level programming languages. We therefore introduce in a number of examples a simple high-level programming language called C\*, pronounced *see star*. The meaning of C\* is explained using machine code as another type of body language. Interestingly, our understanding of machine code and how a computer works will also improve as a result.

Before we continue note that all these analogies are helpful and entertaining but in the end the term *programming language* is anyway an unfortunate misnomer. Its origin goes back to a time when scientists believed that the structure of natural languages can be formalized mathematically. The outcome of that belief was not that but something unforeseen, namely, the notion of formal languages and their structural properties. That research became part of the foundation for describing programming languages and machine code which are formal languages or rather formalisms for describing computation. They are not really languages in the sense of natural languages. This is a beautiful example of scientific exploration not producing the desired result but something completely different yet incredibly important.

Q> What is the difference between natural languages and programming languages?
Q>
Q> Programming languages are formalisms, not languages!

[Programming Language](https://en.wikipedia.org/wiki/Programming_language "Programming Language")
: A formal constructed language designed to communicate instructions to a machine, particularly a computer.

## Von Neumann Architecture

![Von Neumann Architecture](images/von-neumann-architecture.png "Von Neumann Architecture")

Most computers including smart phones and tablets are at their core based on a computer architecture that has not changed in a long time. It is known as the *von Neumann architecture*.

[Von Neumann Architecture](https://en.wikipedia.org/wiki/Von_Neumann_architecture "Von Neumann Architecture")
: A computer architecture introduced in 1945 by the mathematician and physicist John von Neumann and others.

The idea is very simple. There is a *central processing unit* (CPU), also called a *processor*, that executes instructions of a computer program stored as machine code in so-called *main memory* or *memory* for short. The purpose of the program is to direct the CPU to compute something and use main memory not occupied by code for storing data. In particular, the CPU fetches instructions from memory and executes them. During code execution the CPU is directed by the instructions to read data from memory, compute something, write data to memory, and even communicate with the outside world.

[Central Processing Unit (CPU)](https://en.wikipedia.org/wiki/Central_processing_unit "Central Processing Unit (CPU)")
: A digital electronic circuit within a computer that carries out the instructions of a computer program by performing the basic arithmetic, logical, control and input/output (I/O) operations specified by the instructions.

The key innovation of the von Neumann architecture is that code and data are both stored in main memory. In fact, since code and data are just bits there is no difference in representation either.

[Memory](https://en.wikipedia.org/wiki/Computer_memory "Memory")
: Hardware device that stores information for immediate use in a computer; it is synonymous with the term "primary storage".

Since code can be seen as data and vice versa, code is really just pure information known as *software* clearly distinct from physical hardware. The von Neumann architecture is thus a machine model for executing software.

[Software](https://en.wikipedia.org/wiki/Software "Software")
: That part of a computer system that consists of encoded information or computer instructions, in contrast to the physical hardware from which the system is built.

Now, how does code and data get into a computer, and out? This is done through so-called *input/output* (I/O) devices such as keyboards and screens but also network and storage adapters, for example. Storage adapters are usually connected to "secondary storage" which is non-volatile storage containing code and data. In contrast, main memory is typically volatile meaning it loses its content when power is cut. However, volatility of memory is a property not relevant in the von Neumann architecture. We can thus ignore it.

[Input/Output (I/O)](https://en.wikipedia.org/wiki/Input/output "Input/Output (I/O)")
: The communication between an information processing system, such as a computer, and the outside world, possibly a human or another information processing system.

But how does a computer with empty memory load code into memory to execute it? In other words, how does the CPU know what to do if there are no instructions on what to do? Keep in mind that when turning on a computer the only thing the CPU can do is to follow the instructions of a computer program. This is a typical paradox in computer science called *bootstrapping* derived from the phrase "to pull oneself up by one's bootstraps". Even more amusingly, there is also the related story of the Baron Munchausen who pulled himself (and his horse) out of a swamp by his pigtail.

Well, in most computers there is a special program called a *bootloader* stored in special non-volatile memory from which the CPU fetches instructions and executes them if main memory is empty (initially or after a loss of memory). The bootloader contains instructions that direct the CPU to load code into main memory from some I/O device such as the network or storage adapter. Once this is done control is turned over to main memory and the CPU from then on fetches and executes the instructions loaded into main memory.

[Booting](https://en.wikipedia.org/wiki/Booting "Booting")
: The initialization of a computerized system.

The arguably most important piece of information a CPU needs to remember is which instruction it is currently executing and where it finds the next instruction to execute. For this purpose a CPU maintains an *instruction register* (IR) which contains the currently executed instruction and a so-called *program counter* (PC) which identifies the location of the next instruction the CPU is supposed to execute. Both IR and PC are part of the *control unit* of a CPU.

[Control Unit](https://en.wikipedia.org/wiki/Control_unit "Control Unit")
: A component of a computer's central processing unit (CPU) that directs operation of the processor.

When a CPU is done executing an instruction it fetches the next instruction from the location identified by the PC and stores that instruction in the IR. Then the CPU decodes the instruction to find out what it is supposed to do. Lastly, the CPU executes the instruction accordingly which includes changing the PC to the location of the instruction the current instruction wants the CPU to execute next. Once the CPU is done with executing the current instruction and in particular changing the PC it fetches the next instruction identified by the PC and so on ad infinitum or until power is turned off.

[Instruction Register (IR)](https://en.wikipedia.org/wiki/Instruction_register "Instruction Register (IR)")
: The part of a control unit that stores the instruction currently being executed or decoded.

Here it is important to understand that in principle a CPU really just executes one instruction after another, nothing else, but does that incredibly fast.

[Program Counter (PC)](https://en.wikipedia.org/wiki/Program_counter "Program Counter (PC)")
: A register that indicates where a computer is in its program sequence.

Each individual instruction represents a tiny step in any computation so in the end it is only the speed of execution that enables computers to do interesting work in reasonable amounts of time. This implies that understanding how a computer works only requires knowing what these instructions do.

To facilitate fast execution a CPU typically features a number of *registers* that can be accessed much faster than main memory.

[Register](https://en.wikipedia.org/wiki/Processor_register "Processor Register")
: A quickly accessible memory location available to a computer's central processing unit (CPU).

In fact, the IR and PC are such registers but there are also others. Registers are the fastest memory of a computer, much faster than main memory. However, because of technical and economical limitations a CPU usually features only a small amount of registers compared to main memory. An important problem is therefore to write programs that make efficient use of registers and main memory by keeping frequently needed data in registers and the rest in memory.

In addition to the control unit with the IR and the PC, a CPU also features an *arithmetic logic unit* (ALU) with its own set of registers for performing actual computation. For example, an ALU may add the values stored in two registers and save the result in a third register for further computation.

[Arithmetic Logic Unit (ALU)](https://en.wikipedia.org/wiki/Arithmetic_logic_unit "Arithmetic Logic Unit (ALU)")
: A digital electronic circuit that performs arithmetic and logical operations on integer binary numbers.

To summarize, the von Neumann architecture is a machine model consisting of a CPU connected to main memory for storing code and data and to I/O devices for communication. A CPU consists of a control unit for executing instructions and an arithmetic logic unit for actual computation. The typical workflow of a computer is to bootstrap first by loading code from secondary storage into main memory and then execute the loaded code. Typically, that code directs the CPU to retrieve data from the outside world through some I/O communication, perform some computation, and eventually send data back to the outside world. Data needed for computation is kept in main memory and copied into registers for actual computation.

A fundamental performance limitation of the von Neumann architecture is the connection of the CPU and memory also known as the *von Neumann bottleneck*. To perform computation the involved data as well as the involved code need to pass through that connection. However, for now we can safely ignore that limitation and rather focus on a widely used example of the von Neumann architecture.

## Low-Level Programming

In order to understand how a computer works we need to know how to program it in the language that the machine *understands*. This may sound very ambitious and difficult to do but is in fact not all that hard. The language of a computer, also called machine language, is defined by the *instruction set architecture* (ISA) of the machine's processor. There are many different processors with different ISAs but luckily they are all based on similar principles.

[Instruction Set Architecture (ISA)](https://en.wikipedia.org/wiki/Instruction_set "Instruction Set Architecture (ISA)")
: The part of the computer architecture related to programming, including the native data types, instructions, registers, addressing modes, memory architecture, interrupt and exception handling, and input/output (I/O).

Programming a computer in machine language is considered low-level programming in the sense of a *low level of abstraction* close to the machine rather than any of its applications. Honestly, machine language is not at all meant to be used as formalism in which software is developed. It is rather designed to be efficiently executable and otherwise a target of software development tools that automatically translate software written on higher levels of abstraction more appropriate for humans. However, there are very simple and beautiful ISAs that are not only widely used in real processors but also for teaching computer architecture. One such ISA is *MIPS*.

[Microprocessor without Interlocked Pipeline Stages (MIPS)](https://en.wikipedia.org/wiki/MIPS_instruction_set "Microprocessor without Interlocked Pipeline Stages (MIPS)")
: An instruction set architecture (ISA) developed by MIPS Technologies (formerly MIPS Computer Systems, Inc.).

MIPS is so simple it is actually fun to learn it, never mind the interlocked pipeline stages. To make things even simpler we decided to focus on the 32-bit version of MIPS called *MIPS32* where everything happens at the granularity of 32 bits. There are newer versions of MIPS with support of more bits for better performance. We can safely ignore them. Also, out of the 43 available MIPS32 instructions we only use a subset of 17 instructions that we call *MIPSter*. Most importantly, MIPSter is a proper subset of MIPS32, that is, all MIPSter code runs on MIPS32 machines but not vice versa.

Before going through the list of MIPSter instructions, we need to know the registers and memory architecture of our MIPSter processor. Similar to the instructions, the registers are also just a subset of the registers of a real MIPS32 processor.

T> All MIPSter registers including the IR and the PC are 32-bit each. This means that each register contains exactly 32 bits.
T>
T> In addition to the 32-bit IR and the 32-bit PC there are, yes, 32 general-purpose 32-bit registers in the ALU plus two more special-purpose 32-bit registers called the *hi* and the *lo* register.
T>
T> This gives us a total of 36 32-bit registers in the CPU.

In a real MIPS processor there are a few more registers but we can again safely ignore them. Now, the only missing piece is memory.

T> Our MIPSter machine features 64MB of main memory, that is, 2^26^ bytes or 8 times 2^26^ equal to 2^29^ bits.

The size of memory could be less or more but is ultimately determined by the capabilities of the processor. We have chosen 64MB because memory of that size can directly be accessed by all MIPSter instructions.

MIPSter memory like most main memory today is *byte-addressed*. This means that each byte in memory has its own address with the first byte being at address 0, the next at address 1, and so on. However, MIPSter memory, again like most main memory, is also *word-aligned*. Unsurprisingly, the word size in MIPSter is four bytes, that is, well, 32 bits. This means we can only access memory in chunks of four bytes or 32 bits and we can only do so at word boundaries.

Consider the following example.

X> If we would like to read the first byte in memory at address 0 we would have to read the whole first word in memory at address 0 containing not just the first byte but also the bytes at addresses 1, 2, and 3.
X>
X> Moreover, if we would like to read, say, the sixth byte in memory at address 5 we would have to read the second word in memory at address 4 containing the bytes at addresses 4, 5, 6, and 7. In other words, memory access can only be done at addresses that are multiples of four.

Why is it done like that? Simple. Accessing memory in larger chunks is faster and can easily be done through parallelization. To access 32 rather than 8 bits in one step we only need 32 rather than 8 wires in parallel between CPU and memory. There is of course also a price to pay which is space for the wires and energy for using them but that is a story for another day.

Now, to get a better idea of how much memory we have in our machine let us do a quick calculation.

T> With 36 registers times 32 bits a MIPSter CPU can store 1,152 bits in total. Each bit can either be zero or one. As a result, a MIPSter CPU can be in 2^1152^ different *states* of zeroes and ones which is a number with [347 decimal digits](http://www.wolframalpha.com/input/?i=2%5E1152), and this does not even include main memory yet.
T>
T> MIPSter memory can store 2^29^ equal to 536,870,912 bits and thus be in 2^536870912^ (!) different states which is a number with [161,614,249 decimal digits](http://www.wolframalpha.com/input/?i=2%5E536870912), seriously.

In case you are wondering how to compute such large numbers check out [Wolfram Alpha](http://www.wolframalpha.com "Wolfram Alpha").

[State](https://en.wikipedia.org/wiki/State_(computer_science) "State")
: A technical term for all the stored information, at a given instant in time, to which a digital circuit or computer program has access. The output of a circuit or program at any time is completely determined by its current inputs and its state.

We mention the notion of state here because it is important to realize that a computer is really just a machine that can distinguish a very large but still finite number of different states. If we had a way to store the state somewhere we could stop the machine and then reload the state ten years later to have the machine continue exactly where it left off. Well, closing the lid of a laptop putting it to sleep and then opening the lid again waking the machine up is exactly that, except maybe for the ten years. This can in principle be done with any digital circuit.

Turning a computer off and then on again in hope of getting the machine to work again is also related to state. It is essentially a way to set the machine to the state with all bits zero, also called the initial state. That state is assumed to be *safe* in the sense that the machine should be able to go from there to other *safe* states that are useful. How does the machine go there? Well, it goes there by loading and executing a program. The only problem is that the program may also direct the machine to go to undesirable or *unsafe* states. This happens when the program contains bugs which then make us power cycle the machine again and so on.

In order to avoid that routine we could distinguish good from bad behavior by  partitioning the set of all machine states into *safe* and *unsafe* states and then check before running a program if the program will ever take the machine to an unsafe state. Computer scientists and increasingly also programmers are actually doing that with the help of advanced software development tools. However, the ongoing challenge is to handle the enormous amounts of machine states. So far only relatively small programs can be sanitized this way. Buggy software will therefore be with us in the foreseeable future.

Now, let us write our first MIPSter program.

{line-numbers=off}
```
0x00000000: 0x2408002A: addiu $t0,$zero,42
```

Seriously? I am afraid, yes. But you will get used to it.

First of all this program contains only one instruction which directs the CPU to load the decimal number [42](https://en.wikipedia.org/wiki/Phrases_from_The_Hitchhiker%27s_Guide_to_the_Galaxy "42") into the ALU's general-purpose register called `$t0`. That's it. To see how this works let's walk through the example step by step.

The leftmost hexadecimal number `0x00000000` is the address in main memory where the instruction is supposed to be stored. The hexadecimal number `0x2408002A` next to the address is in fact the instruction in *machine code*. That number really is the whole program. The rest is just there to make us feel better, I mean make it more readable for us.

[Machine Code](https://en.wikipedia.org/wiki/Machine_code "Machine Code")
: A sequence of instructions executed directly by a computer's central processing unit (CPU).

So, what is `addiu $t0,$zero,42`? It is *assembly* which is meant to provide a human-readable version of machine code, in this case of `0x2408002A`. Despite their different appearance they are in fact semantically equivalent.

[Assembly](https://en.wikipedia.org/wiki/Assembly_language "Assembly Language")
: A low-level programming language for a computer, or other programmable device, in which there is a very strong (generally one-to-one) correspondence between the language and the architecture's machine code instructions.

However, even `0x2408002A` is already a more compact representation of what is physically stored in memory which is the following 32-bit binary number:

{line-numbers=off}
```
00100100000010000000000000101010
```

That number is equal to `0x2408002A` in binary. Both `0x2408002A` and `addiu $t0,$zero,42` are just different representations of that number.

T> Imagine we programmed computers in their native machine languages using binary code. There were times when people actually did that. Going from binary code to hexadecimal code and then assembly is therefore already a significant advancement over the lowest level of programming. People still program in assembly to this day.
T>
T> However, programming in assembly already requires *assembling* the binary code for each instruction either manually, like I did for a [Z80](https://en.wikipedia.org/wiki/Zilog_Z80 "Z80") machine when I was fourteen, or using a software tool called an *assembler*. Unfortunately, Selfie does not feature an assembler but it does include a *disassembler* which produces the assembly representation of MIPSter binary code.

Assembly uses *mnemonic* to help us remember what machine code means.

[Mnemonic](https://en.wikipedia.org/wiki/Mnemonic "Mnemonic")
: Any learning technique that aids information retention in the human memory.

In our example, the `addiu` string stands for "add immediate unsigned" and represents the so-called *opcode* of the instruction.

[Opcode](https://en.wikipedia.org/wiki/Opcode "Opcode")
: The portion of a machine language instruction that specifies the operation to be performed.

The opcode of a MIPSter instruction is encoded in the six most significant bits of the 32-bit machine code. In other words, `addiu` represents `001001` in binary. We repeat the above 32-bit binary number here with the one-to-one correspondence to the assembly representation:

{line-numbers=off}
```
addiu  $zero   $t0               42
001001 00000 01000 0000000000101010
```

The remaining 26 bits encode the, in this case, three *operands* of the instruction which are `$t0`, `$zero`, and `42`. The second operand `$zero` refers to the first general-purpose register of the CPU and is encoded in the five bits `00000` next to the opcode. The first operand `$t0` refers to the eighth general-purpose register of the CPU and is encoded in the five bits `01000` next to the bits representing the second operand. Note that `01000` is binary for eight. Lastly, the third operand `42` is an integer encoded by the remaining sixteen bits `0000000000101010` which is binary for forty-two.

This all seems to make sense but what is now the semantics of this instruction? How does it work? This is after all what really matters. The `addiu` instruction makes the CPU take the sixteen least significant bits and add them as integer value to the value of the register identified by the five bits next to the opcode bits, that is, in our example the value of the register `$zero`. The result of that binary addition is stored in the register identified by the five bits next to the five bits identifying `$zero`, that is, in our example the register `$t0`. However, there is still two problems with our example and also one important assumption made here. The assumption first:

T> Register `$zero` is assumed to contain zero at all times which means that the value in register `$t0` will be `42` after executing the instruction. In other words, using `addiu` on `$zero` is not meant to perform binary addition. It is rather meant to load an integer value into a register. This is so typical for anything computer-related. What it says on the box and what it is intended to do can be very different things. I apologize on behalf of all computer scientists.
T>
T> But there is also this problem of adding a 16-bit number to a 32-bit register. How does that work? The CPU actually takes the 16-bit number and *sign-extends* it to 32 bits before performing the addition. This means that the CPU treats the 16 bits as signed integer representation in two's complement and preserves the sign in the extension to 32 bits. We may therefore use signed integers from -2^15^ to 2^15^-1 as third operand of `addiu`.
T>
T> But what happens if there is an overflow, that is, the result of the addition does not fit into 32 bits? This could be a serious problem. Well, in that case the CPU wraps the result around to stay within the 32 bits. This is fine but does not correspond to regular arithmetic so be aware of that!

The fact that the CPU performs wrap-arounds upon overflows when executing `addiu` is emphasized by the `u` in `addiu` which stands for `unsigned`, obviously another unfortunate misnomer, my apologies. The behavior of the CPU treating an operand as value is called *immediate addressing* which explains the `i` in `addiu`. In general, CPUs support different *addressing modes* of which immediate addressing is only one example (even though there is no real addressing going on here).

[Addressing Mode](https://en.wikipedia.org/wiki/Addressing_mode "Addressing Mode")
: Specifies how to calculate the effective memory address of an operand by using information held in registers and/or constants contained within a machine instruction or elsewhere.

The addressing mode of the two other operands of `addiu` is called *register addressing* since the operands identify registers. Note that the five bits of these operands can distinguish 2^5^, that is, 32 registers which non-coincidentally happens to be the number of general-purpose registers of our processor. Nice!

There are more addressing modes with other instructions which we discuss as we encounter them. However, instead of introducing the remaining 16 MIPSter instructions one by one here we do something different. Since low-level programming is obviously a tedious endeavor we move on and present a high-level form of programming next. This hopefully keeps us sufficiently motivated before eventually returning to machine code and how it relates to high-level programs.

You may nevertheless already ask yourself how you can run MIPSter code and see what happens. Fortunately, we do not need a real MIPS processor to run MIPSter code. Computers have this fascinating ability to imitate each other and many other things. A computer or software running on a computer that imitates another computer (or even the same computer) is called an *emulator* which is exactly what we suggest to use here.

[Emulator](https://en.wikipedia.org/wiki/Emulator "Emulator")
: Hardware or software that enables one computer system (called the host) to behave like another computer system (called the guest).

If you are interested in the exact specification of MIPSter or would even like to run MIPSter code there is a MIPSter emulator called mipster implemented in Selfie. The mipster emulator is able to execute MIPSter code and even output the code it executes as well as the involved machine state. The code execution output presented in the example below is obtained with mipster.

## High-Level Programming

Most software is not written in machine code or assembly but in programming languages that are designed to describe computation on levels of abstraction much higher than CPU registers and main memory.

[High-level Programming Language](https://en.wikipedia.org/wiki/High-level_programming_language "High-Level Programming Language")
: A programming language with strong abstraction from the details of the computer. In comparison to low-level programming languages, it may use natural language elements, be easier to use, or may automate (or even hide entirely) significant areas of computing systems (e.g. memory management), making the process of developing a program simpler and more understandable relative to a lower-level language. The amount of abstraction provided defines how "high-level" a programming language is.

But which language should we learn and then use? There are so many already and then there are new ones being developed all the time. The solution to this problem, in our opinion, is to develop a strong sense for principles and semantics, and awareness of your own understanding. If you know the principles and you know what you don't know about the details, you can pick up any programming language you like. Consider the following program:

{line-numbers=on, lang=c}
<<[A Simple C* Program](code/iteration.c)

The program is *source code* written in *C* which is a programming language that was developed in the late 1960s to early 1970s. Essentially, the program takes the integer value `0`, increments it two times to `2`, then decrements it two times to `0` again, and then returns that `0`. Not very exciting but good enough for our purpose here.

[Source Code](https://en.wikipedia.org/wiki/Source_code "Source Code")
: Any collection of computer instructions (possibly with comments) written using some human-readable computer language, usually as text.

C has influenced the design of numerous other languages, has been standardized over the years, is supported by many tools, and is still one of the most widely used programming languages.

[C](https://en.wikipedia.org/wiki/C_(programming_language) "C")
: A general-purpose, imperative computer programming language, supporting structured programming, lexical variable scope and recursion, while a static type system prevents many unintended operations.

Unless you are reading this on paper, it is likely that the system you are reading this on has to a large extent been programmed in some flavor of C. However, C has also been criticized for being difficult to use and the source of many errors in software written in C.

Programmers tend to enjoy discussing the pros and cons of programming languages at great length. We nevertheless try to avoid that here and instead make two key observations that hopefully justify our choice. Firstly, many programming languages newer than C have adopted the look and feel of some parts of C which, secondly, happen to be surprisingly simple. We have tried to identify some of that over the course of a few years of teaching computer science classes. The outcome is a tiny subset of C that we call C\* and use throughout the book. Not just the above example is written in C\* but all other examples as well. Even Selfie is written entirely in C\*. An important advantage of using a proper subset of a widely used programming language such as C is that all programs written in the subset readily work with all tools that exist for the superset.

Let's now take a closer look at the above example which we repeat here with comments on which language elements are actually used in each line. Note that each comment starts with `//` which instructs tools that process such source code to ignore the text to the right of `//` until the end of the line. In other words, a comment in source code is meaningless to the machine but hopefully not to us.

{line-numbers=on, lang=c}
<<[Language Elements of the Simple C* Program](code/iteration-high.c)

The first line is the *declaration* of a *variable* `x` of *type* `int`.

[Declaration](https://en.wikipedia.org/wiki/Declaration_(computer_programming) "Declaration")
: Specifies properties of an identifier, that is, declares what the identifier means. Declarations are most commonly used for functions, variables, and constants.

A declaration introduces a name or *identifier* for an entity and declares what the entity is. In this case, the identifier is `x` and the entity is memory that can store a signed 32-bit integer as stated by the `int` type which is a C standard. This means in particular that no matter on which machine you run the program, `x` always refers to a signed 32-bit integer. Very cool!

[Type](https://en.wikipedia.org/wiki/Data_type "Type")
: A classification identifying one of various types of data, such as real, integer or Boolean, that determines the possible values for that type; the operations that can be done on values of that type; the meaning of the data; and the way values of that type can be stored.

Here, the identifier `x` refers to what is commonly called a program variable or just variable.

[Variable (in Computer Science)](https://en.wikipedia.org/wiki/Variable_(computer_science) "Variable (in Computer Science)")
: A storage location paired with an associated symbolic name (an identifier), which contains some known or unknown quantity of information referred to as a value. The variable name is the usual way to reference the stored value; this separation of name and content allows the name to be used independently of the exact information it represents.

This is basically how memory in C programs is introduced. Instead of registers and machine memory, C programs "talk" about such variables. However, `x` is not a variable in the sense of mathematics.

[Variable (in Mathematics)](https://en.wikipedia.org/wiki/Variable_(mathematics) "Variable (in Mathematics)")
: An alphabetic character representing a number, called the value of the variable, which is either arbitrary or not fully specified or unknown.

In other words, a program variable like `x` only approximates the mathematical notion of a variable but can never replace it because of the bounded size of  memory. That distinction is very important to understand. In fact, calling `x` something other than a variable would be even better but it's probably too late for that.

The next interesting line in our example is Line 3. This is again a declaration but this time of a *subroutine* rather than a variable.

[Subroutine](https://en.wikipedia.org/wiki/Subroutine "Subroutine")
: A sequence of program instructions that perform a specific task, packaged as a unit. This unit can then be used in programs wherever that particular task should be performed.

The subroutine is referred to by the identifier `main`, has no inputs as indicated by the empty pair of parentheses `()` but has a single output which is a signed 32-bit integer as indicated by the preceding `int` type, and consists of the sequence of *statements* in Lines 4-16 enclosed by the pair of braces `{}`. The `main` identifier thus stands for that sequence of statements.

[Statement](https://en.wikipedia.org/wiki/Statement_(computer_science) "Statement")
: The smallest standalone element of a programming language that expresses some action to be carried out. It is an instruction written in a high-level language that commands the computer to perform a specified action. A program written in such a language is formed by a sequence of one or more statements.

Subroutines are more commonly called *procedures* or *functions* even though they are obviously not functions in a mathematical sense. After variables this is another example of terminology that is different from mathematics. In the sequel we generally speak of subroutines as procedures, and as functions in special cases.

{line-numbers=on, lang=c}
<<[Informal Semantics of the Simple C* Program](code/iteration-low.c)

## Semantics

{line-numbers=off, lang=asm}
<<[Formal Semantics of the Simple C* Program in MIPS Assembly with Approximate Line Numbers](code/iteration.s)

{line-numbers=off, lang=asm}
<<[Execution of the MIPS Assembly for the Simple C* Program with Approximate Line Numbers and Profile](code/iteration.d)

## Procedures

{line-numbers=on, lang=c}
<<[A C* Program Equivalent to the Simple C* Program](code/procedure.c)

{line-numbers=off, lang=asm}
<<[Formal Semantics of the Equivalent C* Program](code/procedure.s)

## Functions versus Procedures

{line-numbers=on, lang=c}
<<[A C* Program Equivalent to the Simple C* Program Using a Function](code/function.c)

[Global Variable](https://en.wikipedia.org/wiki/Global_variable "Global Variable")

[Scope](https://en.wikipedia.org/wiki/Declaration_(computer_programming) "Scope")

[Local Variable](https://en.wikipedia.org/wiki/Local_variable "Local Variable")

{line-numbers=off, lang=asm}
<<[Formal Semantics of the Equivalent C* Program Using a Function](code/function.s)

## Functions Only

{line-numbers=on, lang=c}
<<[A C* Program Equivalent to the Simple C* Program Using Just Functions](code/local.c)

{line-numbers=off, lang=asm}
<<[Formal Semantics of the Equivalent C* Program Using Just Functions](code/local.s)

## Recursion

{line-numbers=on, lang=c}
<<[A C* Program with Iteration and Equivalent Recursions from Basics Chapter](code/recursion.c)

## Memory

{line-numbers=on, lang=c}
<<[A C* Program with Pointers](code/pointer.c)

{line-numbers=off, lang=asm}
<<[Formal Semantics of the C* Program with Pointers](code/pointer.s)