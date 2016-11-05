# 4. State {#state}

Computation is the evolution of state. At any given time, a computer stores a very large amount of bits in registers and memory. We call that the state of the machine. Then the processor executes one instruction which directs it to change a very small number of bits creating a new state. That process of change of state continues until the machine is turned off.

Software on source code and in particular machine code level specifies for each state what the next state is. There are the data bits that are being changed and the code bits that determine that change. In this chapter, we explain how on machine level registers and memory represent state and how machine code describes change of that state. We also show how source code provides a higher-level view of that which is an important step towards learning how to code.

## Memory

### Declarations

[Declaration](https://en.wikipedia.org/wiki/Declaration_(computer_programming) "Declaration")
: Specifies properties of an identifier: it declares what a word (identifier) means. Declarations are most commonly used for functions, variables, constants, and classes. Beyond the name (the identifier itself) and the kind of entity (function, variable, etc.), declarations typically specify the data type (for variables and constants), or the type signature (for functions). The term "declaration" is frequently contrasted with the term "definition", but meaning and usage varies significantly between languages.

### Definitions

## Control Flow

[Control Flow](https://en.wikipedia.org/wiki/Control_flow "Control Flow")
: The order in which individual statements, instructions or function calls of an imperative program are executed or evaluated. The emphasis on explicit control flow distinguishes an imperative programming language from a declarative programming language.

When reading source code the starc compiler does in fact just try to recognize such symbols, also called *tokens*. The process is very simple and called *lexical analysis*.

[Lexical Analysis](https://en.wikipedia.org/wiki/Lexical_analysis "Lexical Analysis")
: The process of converting a sequence of characters (such as in a computer program or web page) into a sequence of tokens (strings with an identified "meaning"). A program that performs lexical analysis may be called a lexer, tokenizer, or scanner.

The compiler reads one character after another until it [recognizes a symbol](http://github.com/cksystemsteaching/selfie/blob/f0f9f756d9602efaed192026979cbf12d657f77f/selfie.c#L1984-L2225), after discarding whitespace and comments, of course. Once it recognizes a symbol it stores that symbol and then continues reading more characters until it recognizes the next symbol and so on until it reaches the end of the file. If the compiler reads a sequence of characters that does not constitute a symbol it reports an error and terminates. Try it! Just take the "Hello World!" program and modify it such that it contains something that is neither whitespace nor a comment nor a C\* symbol. Then run starc to see what happens.

## Program Counter

[Program Counter (PC)](https://en.wikipedia.org/wiki/Program_counter "Program Counter (PC)")
: A processor register that indicates where a computer is in its program sequence. In most processors, the PC is incremented after fetching an instruction, and holds the memory address of ("points to") the next instruction that would be executed. Instructions are usually fetched sequentially from memory, but control transfer instructions change the sequence by placing a new value in the PC. These include branches (sometimes called jumps), subroutine calls, and returns. A transfer that is conditional on the truth of some assertion lets the computer follow a different sequence under different conditions. A branch provides that the next instruction is fetched from somewhere else in memory. A subroutine call not only branches but saves the preceding contents of the PC somewhere. A return retrieves the saved contents of the PC and places it back in the PC, resuming sequential execution with the instruction following the subroutine call.

## Statements

## Procedures

### Recursion