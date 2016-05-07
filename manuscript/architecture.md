# 3. Architecture and Language

The idea of this chapter is to explain how computers work in principle and how to program them using a set of simple examples. The focus is on understanding the relationship of computer (architecture) and programming (language) as early as possible. This is in contrast to the traditional approach of teaching both topics in separate classes, or even just teaching programming without ever explaining how the machine works. We believe that knowing how computers work in principle is important for programming. Gladly, it is not that hard to figure out how they work. The principles of *computer architecture* still remain relatively simple since the physics of a digital computer can be completely hidden by Boolean logic. To us the machine is just handling bits, true and false, nothing else. I still remember the computer architecture class that I took as freshman. I liked it a lot because everything was clean and simple.

[Computer Architecture][]
: A set of rules and methods that describe the functionality, organization, and implementation of computer systems.

Programming, on the other hand, is more difficult and can get very messy since software can grow arbitrarily complex. We believe the key to becoming a good programmer is to develop a deep sense for semantics. What is the true meaning of a piece of code? Have I truly understood what happens when the machine executes that code? There is of course also the right choice of programming languages and the professional use of software development tools but it all begins with truly understanding the meaning of code.

Imagine you are taking a class to learn a foreign language. One particularly interesting type of class is when the language is taught by speaking in that language without using any other language. This means that as soon as the class starts the teacher exclusively speaks in the language that everyone would like to learn but does not understand. This approach anyway works because the teacher may use means of communication other than spoken language such as gestures, facial expressions, and even body language. Questions may be asked in a language that everyone understands but answers are always given in the foreign language. Students are anyway encouraged to use the foreign language as soon as possible and eventually even ask questions in that language.

We do something similar here. We explain how a computer works using examples written in the language that the computer *speaks* but we do not yet understand. That language is called machine code. However, we use Boolean logic and elementary algebra that everyone is familiar with as *body language* to clarify the meaning of machine code. Hard to believe but machine code is so simple that Boolean logic and elementary algebra is enough. The only problem is that machine code is not really a language that anyone but a few computer engineers enjoy. Most code these days is actually written in higher-level programming languages. We therefore introduce in a number of examples a simple high-level programming language called C\*, pronounced *see star*. The meaning of C\* is explained using machine code as another type of body language. Interestingly, our understanding of machine code and how a computer works will also improve as a result.

Before we continue note that all these analogies are helpful and entertaining but in the end the term *programming language* is anyway an unfortunate misnomer. Its origin goes back to a time when scientists believed that the structure of natural languages can be formalized mathematically. The outcome of that belief was not that but something unforeseen, namely, the notion of formal languages and their structural properties. That research became part of the foundation for describing programming languages and machine code which are formal languages or rather formalisms for describing computation. They are not really languages in the sense of natural languages. This is a beautiful example of scientific exploration not producing the desired result but something completely different yet incredibly important.

Q> What is the difference between natural languages and programming languages?
Q>
Q> Programming languages are formalisms, not languages!

[Programming Language][]
: A formal constructed language designed to communicate instructions to a machine, particularly a computer.

## Von Neumann Architecture

![Von Neumann Architecture](images/von-neumann-architecture.jpg "Von Neumann Architecture")

Most computers including smart phones and tablets are at their core based on a computer architecture that has not changed in a long time. It is known as the *von Neumann architecture*.

[Von Neumann Architecture][]
: A computer architecture introduced in 1945 by the mathematician and physicist John von Neumann and others.

The idea is very simple. There is a *central processing unit* (CPU), also called a *processor*, that executes instructions of a computer program stored as machine code in so-called *main memory* or *memory* for short. The purpose of the program is to direct the CPU to compute something and use main memory not occupied by code for storing data. In particular, the CPU fetches instructions from memory and executes them. During code execution the CPU is directed by the instructions to read data from memory, compute something, write data to memory, and even communicate with the outside world.

[Central Processing Unit (CPU)][]
: A digital electronic circuit within a computer that carries out the instructions of a computer program by performing the basic arithmetic, logical, control and input/output (I/O) operations specified by the instructions.

The key innovation of the von Neumann architecture is that code and data are both stored in main memory. In fact, since code and data are just bits there is no difference in representation either.

[Memory][]
: Hardware device that stores information for immediate use in a computer; it is synonymous with the term "primary storage".

Since code can be seen as data and vice versa, code is really just pure information known as *software* clearly distinct from physical hardware. The von Neumann architecture is thus a machine model for executing software.

[Software][]
: That part of a computer system that consists of encoded information or computer instructions, in contrast to the physical hardware from which the system is built.

Now, how does code and data get into a computer, and out? This is done through so-called *input/output* (I/O) devices such as keyboards and screens but also network and storage adapters, for example. Storage adapters are usually connected to "secondary storage" which is non-volatile storage containing code and data. In contrast, main memory is typically volatile meaning it loses its content when power is cut. However, volatility of memory is a property not relevant in the von Neumann architecture. We can thus ignore it.

[Input/Output (I/O)][]
: The communication between an information processing system, such as a computer, and the outside world, possibly a human or another information processing system.

But how does a computer with empty memory load code into memory to execute it? In other words, how does the CPU know what to do if there are no instructions on what to do? Keep in mind that when turning on a computer the only thing the CPU can do is to follow the instructions of a computer program. This is a typical paradox in computer science called *bootstrapping* derived from the phrase "to pull oneself up by one's bootstraps". Even more amusingly, there is also the related story of the Baron Munchausen who pulled himself (and his horse) out of a swamp by his pigtail.

Well, in most computers there is a special program called a *bootloader* stored in special non-volatile memory from which the CPU fetches instructions and executes them if main memory is empty (initially or after a loss of memory). The bootloader contains instructions that direct the CPU to load code into main memory from some I/O device such as the network or storage adapter. Once this is done control is turned over to main memory and the CPU from then on fetches and executes the instructions loaded into main memory.

[Booting][]
: The initialization of a computerized system.

The arguably most important piece of information a CPU needs to remember is which instruction it is currently executing and where it finds the next instruction to execute. For this purpose a CPU maintains an *instruction register* (IR) which contains the currently executed instruction and a so-called *program counter* (PC) which identifies the location of the next instruction the CPU is supposed to execute. Both IR and PC are part of the *control unit* of a CPU.

[Control Unit][]
: A component of a computer's central processing unit (CPU) that directs operation of the processor.

When a CPU is done executing an instruction it fetches the next instruction from the location identified by the PC and stores that instruction in the IR. Then the CPU decodes the instruction to find out what it is supposed to do. Lastly, the CPU executes the instruction accordingly which includes changing the PC to the location of the instruction the current instruction wants the CPU to execute next. Once the CPU is done with executing the current instruction and in particular changing the PC it fetches the next instruction identified by the PC and so on ad infinitum or until power is turned off.

[Instruction Register (IR)][]
: The part of a control unit that stores the instruction currently being executed or decoded.

Here it is important to understand that in principle a CPU really just executes one instruction after another, nothing else, but does that incredibly fast.

[Program Counter (PC)][]
: A register that indicates where a computer is in its program sequence.

Each individual instruction represents a tiny step in any computation so in the end it is only the speed of execution that enables computers to do interesting work in reasonable amounts of time. This implies that understanding how a computer works only requires knowing what these instructions do.

To facilitate fast execution a CPU typically features a number of *registers* that can be accessed much faster than main memory.

[Register][]
: A quickly accessible memory location available to a computer's central processing unit (CPU).

In fact, the IR and PC are such registers but there are also others. Registers are the fastest memory of a computer, much faster than main memory. However, because of technical and economical limitations a CPU usually features only a small amount of registers compared to main memory. An important problem is therefore to write programs that make efficient use of registers and main memory by keeping frequently needed data in registers and the rest in memory.

In addition to the control unit with the IR and the PC, a CPU also features an *arithmetic logic unit* (ALU) with its own set of registers for performing actual computation. For example, an ALU may add the values stored in two registers and save the result in a third register for further computation.

[Arithmetic Logic Unit (ALU)][]
: A digital electronic circuit that performs arithmetic and logical operations on integer binary numbers.

To summarize, the von Neumann architecture is a machine model consisting of a CPU connected to main memory for storing code and data and to I/O devices for communication. A CPU consists of a control unit for executing instructions and an arithmetic logic unit for actual computation. The typical workflow of a computer is to bootstrap first by loading code from secondary storage into main memory and then execute the loaded code. Typically, that code directs the CPU to retrieve data from the outside world through some I/O communication, perform some computation, and eventually send data back to the outside world. Data needed for computation is kept in main memory and copied into registers for actual computation.

A fundamental performance limitation of the von Neumann architecture is the connection of the CPU and memory also known as the *von Neumann bottleneck*. To perform computation the involved data as well as the involved code need to pass through that connection. However, for now we can safely ignore that limitation and rather focus on a widely used example of the von Neumann architecture.

## Low-Level Programming

In order to understand how a computer works we need to know how to program it in the language that the machine *understands*. This may sound very ambitious and difficult to do but is in fact not all that hard. The language of a computer, also called machine language, is defined by the *instruction set architecture* (ISA) of the machine's processor. There are many different processors with different ISAs but luckily they are all based on similar principles.

[Instruction Set Architecture (ISA)][]
: The part of the computer architecture related to programming, including the native data types, instructions, registers, addressing modes, memory architecture, interrupt and exception handling, and input/output (I/O).

Programming a computer in machine language is considered low-level programming in the sense of a *low level of abstraction* close to the machine rather than any of its applications. Honestly, machine language is not at all meant to be used as formalism in which software is developed. It is rather designed to be efficiently executable and otherwise a target of software development tools that automatically translate software written on higher levels of abstraction more appropriate for humans. However, there are very simple and beautiful ISAs that are not only widely used in real processors but also for teaching computer architecture. One such ISA is *MIPS*.

[Microprocessor without Interlocked Pipeline Stages (MIPS)][]
: An instruction set architecture (ISA) developed by MIPS Technologies (formerly MIPS Computer Systems, Inc.).

MIPS is so simple it is actually fun to learn it, never mind the interlocked pipeline stages. To make things even simpler we decided to focus on the 32-bit version of MIPS called *MIPS32* where everything happens at the granularity of 32 bits. There are newer versions of MIPS with support of more bits for better performance. We can safely ignore them. Also, out of the 43 available MIPS32 instructions we only use a subset of 17 instructions that we call *MIPSter*. Most importantly, MIPSter is a proper subset of MIPS32, that is, all MIPSter code runs on MIPS32 machines but not vice versa.

Before going through the list of MIPSter instructions, we need to know the registers and memory architecture of our MIPSter processor. Similar to the instructions, the registers are also just a subset of the registers of a real MIPS32 processor. All MIPSter registers including the IR and the PC are 32-bit each. This means that each register contains exactly 32 bits.  In addition to the 32-bit IR and the 32-bit PC there are, yes, 32 general-purpose 32-bit registers in the ALU plus two more special-purpose 32-bit registers called the *hi* and the *lo* register. This gives us a total of 36 32-bit registers in the CPU. In a real MIPS processor there are a few more registers but we can again safely ignore them.

The only missing piece is memory. Our MIPSter machine features 64MB of main memory, that is, 2^26^ bytes or 8 times 2^26^ equal to 2^29^ bits. The size of memory could be less or more but is ultimately determined by the capabilities of the processor. We have chosen 64MB because memory of that size can directly be accessed by all MIPSter instructions.

MIPSter memory like most main memory today is *byte-addressed*. This means that each byte in memory has its own address with the first byte being at address 0, the next at address 1, and so on. However, MIPSter memory, again like most main memory, is also *word-aligned*. Unsurprisingly, the word size in MIPSter is four bytes, that is, well, 32 bits. This means we can only access memory in chunks of four bytes or 32 bits and we can only do so at word boundaries. For example, if we would like to read the first byte in memory at address 0 we would have to read the whole first word in memory at address 0 containing not just the first byte but also the bytes at addresses 1, 2, and 3. Moreover, if we would like to read, say, the sixth byte in memory at address 5 we would have to read the second word in memory at address 4 containing the bytes at addresses 4, 5, 6, and 7. In other words, memory access can only be done at addresses that are multiples of four.

Why is it done like that? Simple. Accessing memory in larger chunks is faster and can easily be done through parallelization. To access 32 rather than 8 bits in one step we only need 32 rather than 8 wires between CPU and memory. There is of course also a price to pay which is space for the wires and energy for using them but that is a story for another day.

Now, let us do a quick calculation here. With 36 registers times 32 bits a MIPSter CPU can store 1,152 bits in total. Each bit can either be zero or one. As a result, a MIPSter CPU can be in [2^1152^](http://www.wolframalpha.com/input/?i=2%5E1152) different *states* which is a number with 347 decimal digits, and this does not even include main memory yet. MIPSter memory can store 2^29^ equal to 536,870,912 bits and thus be in [2^536870912^](http://www.wolframalpha.com/input/?source=nav&i=2%5E536870912) different states which is a number with 161,614,249 decimal digits, seriously. In case you are wondering how to compute such numbers check out [Wolfram Alpha](http://www.wolframalpha.com "Wolfram Alpha").

[State][]
: A technical term for all the stored information, at a given instant in time, to which a digital circuit or computer program has access. The output of a circuit or program at any time is completely determined by its current inputs and its state.

We mention the notion of state here because it is important to realize that a computer is really just a machine that can distinguish a very large but still finite number of different states. If we had a way to store the state somewhere we could stop the machine and then reload the state ten years later to have the machine continue exactly where it left off. Well, closing the lid of a laptop putting it to sleep and then opening the lid again waking the machine up is exactly that, except maybe for the ten years. This can in principle be done with any digital circuit.

Turning a computer off and then on again in hope of getting the machine to work again is also related to state. It is essentially a way to set the machine to the state with all bits zero, also called the initial state. That state is assumed to be *safe* in the sense that the machine should be able to go from there to other *safe* states that are useful. How does the machine go there? Well, it goes there by executing a program. The only problem is that the program may also direct the machine to go to undesirable or *unsafe* states. This happens when the program contains bugs. So, in order to distinguish good from bad behavior we could partition the set of all machine states into *safe* and *unsafe* states and then check if a program ever takes the machine to an unsafe state. Computer scientists and increasingly also programmers are actually doing that with the help of advanced software development tools. However, the ongoing challenge is to handle the enormous amounts of machine states. Buggy software will therefore be with us in the foreseeable future.

TODO: introduce MIPSter instructions.

You may ask yourself how we can ever run MIPSter code and see what happens. Fortunately, we do not need a real MIPS processor to run MIPSter code. Computers have this fascinating ability to imitate each other and many other things. A computer or software running on a computer that imitates another computer (or even the same computer) is called an *emulator* which is exactly what we use here.

[Emulator][]
: Hardware or software that enables one computer system (called the host) to behave like another computer system (called the guest).

If you are interested in the exact specification of MIPSter or would even like to run MIPSter code there is a MIPSter emulator called mipster implemented in selfie. The mipster emulator is able to execute MIPSter code and even output the code it executes as well as the involved machine state. The code execution output presented below is obtained with mipster.

## High-Level Programming

## A Simple C\* Program

{line-numbers=on, lang=c}
<<[A Simple C* Program](code/iteration.c)

{line-numbers=on, lang=c}
<<[Informal Semantics of the Simple C* Program](code/iteration-low.c)

{line-numbers=on, lang=c}
<<[Language Elements of the Simple C* Program](code/iteration-high.c)

{line-numbers=off, lang=asm}
<<[Formal Semantics of the Simple C* Program in MIPS Assembly with Approximate Line Numbers](code/iteration.s)

{line-numbers=off, lang=asm}
<<[Execution of the MIPS Assembly for the Simple C* Program with Approximate Line Numbers and Profile](code/iteration.d)

## Another Simple C\* Program

{line-numbers=on, lang=c}
<<[A C* Program Equivalent to the Simple C* Program](code/procedure.c)

{line-numbers=off, lang=asm}
<<[Formal Semantics of the Equivalent C* Program](code/procedure.s)

## Functions versus Procedures

{line-numbers=on, lang=c}
<<[A C* Program Equivalent to the Simple C* Program Using a Function](code/function.c)

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

[computer architecture]: https://en.wikipedia.org/wiki/Computer_architecture "Computer Architecture"
[programming language]:
[programming language]: https://en.wikipedia.org/wiki/Programming_language "Programming Language"

[von neumann architecture]: https://en.wikipedia.org/wiki/Von_Neumann_architecture "Von Neumann Architecture"
[central processing unit (cpu)]: https://en.wikipedia.org/wiki/Central_processing_unit "Central Processing Unit"
[memory]: https://en.wikipedia.org/wiki/Computer_memory "Computer Memory"
[software]: https://en.wikipedia.org/wiki/Software "Software"
[input/output (i/o)]: https://en.wikipedia.org/wiki/Input/output "Input/Output"
[booting]: https://en.wikipedia.org/wiki/Booting "Booting"
[control unit]: https://en.wikipedia.org/wiki/Control_unit "Control Unit"
[instruction register (ir)]: https://en.wikipedia.org/wiki/Instruction_register "Instruction Register"
[program counter (pc)]: https://en.wikipedia.org/wiki/Program_counter "Program Counter"
[register]: https://en.wikipedia.org/wiki/Processor_register "Processor Register"
[arithmetic logic unit (alu)]: https://en.wikipedia.org/wiki/Arithmetic_logic_unit "Arithmetic Logic Unit"

[instruction set architecture (isa)]: https://en.wikipedia.org/wiki/Instruction_set "Instruction Set Architecture"
[microprocessor without interlocked pipeline stages (mips)]: https://en.wikipedia.org/wiki/MIPS_instruction_set "MIPS"

[state]: https://en.wikipedia.org/wiki/State_(computer_science) "State"

[emulator]: https://en.wikipedia.org/wiki/Emulator "Emulator"

[machine code]: https://en.wikipedia.org/wiki/Machine_code "Machine Code"
[opcode]: https://en.wikipedia.org/wiki/Opcode "Opcode"
[assembly]: https://en.wikipedia.org/wiki/Assembly_language "Assembly Language"
[mnemonic]: https://en.wikipedia.org/wiki/Mnemonic "Mnemonic"
[addressing modes]: https://en.wikipedia.org/wiki/Addressing_mode "Addressing Modes"
[branch]: https://en.wikipedia.org/wiki/Branch_(computer_science) "Branch"

[high-level programming]: https://en.wikipedia.org/wiki/High-level_programming_language "High-Level Programming"
[c]: https://en.wikipedia.org/wiki/C_(programming_language) "C"
[declaration]: https://en.wikipedia.org/wiki/Declaration_(computer_programming) "Declaration"
[global variable]: https://en.wikipedia.org/wiki/Global_variable "Global Variable"
[scope]: https://en.wikipedia.org/wiki/Declaration_(computer_programming) "Scope"
[subroutine]: https://en.wikipedia.org/wiki/Subroutine "Subroutine"
[local variable]: https://en.wikipedia.org/wiki/Local_variable "Local Variable"

[imperative]: https://en.wikipedia.org/wiki/Imperative_programming "Imperative Programming"
[statement]: https://en.wikipedia.org/wiki/Statement_(computer_science) "Statement"
[declarative]: https://en.wikipedia.org/wiki/Declarative_programming "Declarative Programming"
[assignment]: https://en.wikipedia.org/wiki/Assignment_(computer_science) "Assignment"
[expression]: https://en.wikipedia.org/wiki/Expression_(computer_science) "Expression"
[conditional]: https://en.wikipedia.org/wiki/Conditional_(computer_programming) "Conditional"
[while]: https://en.wikipedia.org/wiki/While_loop "While Loop"
[return]: https://en.wikipedia.org/wiki/Return_statement "Return Statement"