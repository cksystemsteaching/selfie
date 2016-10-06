# 3. Encoding {#encoding}

Information, whatever it is, needs to be encoded in bits for a computer to handle it. Since `selfie.c` is a sequence of characters let us first look at how characters are encoded. After that we explain how sequences of characters form larger constructs such as strings, identifiers, and even whole numbers and machine instructions and how they are encoded and also decoded on the machine.

## Characters

We mention in the [previous chapter](#semantics) that the characters in `selfie.c` are [ASCII](https://en.wikipedia.org/wiki/ASCII "ASCII") characters encoded in eight bits, that is, one byte according to the [UTF-8](https://en.wikipedia.org/wiki/UTF-8 "UTF-8") standard.

X> According to UTF-8 (and ASCII), the uppercase letter `U`, for example, is encoded in the 8-bit sequence `01010101`.

Both ASCII and UTF-8 are essentially one-to-one mappings from bits to characters written down in a table. Each 8-bit sequence is associated with exactly one character. For a computer that table is only relevant when the machine receives characters from a keyboard and sends characters to a screen. Then, the machine needs to know the ASCII code for each key on the keyboard to remember which key was pressed and it needs to know which shape of character to draw on the screen for each bit sequence. Internally, however, characters are just 8-bit sequences, with selfie and a lot of other software as well.

Let us pause for a moment and reflect about this. The above bit sequence could really still mean anything. The encoding standards for characters are just agreements on how to associate bits and characters but there is still no meaning.

X> The bit sequence `01010101` is also binary for the [decimal number](https://en.wikipedia.org/wiki/Decimal) `85`.

So what is it now, `U` or `85`? The answer is both, and anything else. As mentioned in the [previous chapter](#semantics), meaning comes from change. When the machine draws `U` for `01010101` on the screen then `01010101` stands for `U` in that moment but in the next moment the machine could increment `01010101` according to elementary arithmetic making `01010101` represent `85`.

But how does selfie and in particular the starc compiler actually read characters from files such as `selfie.c`? It turns out that all characters are [read from left to right](http://github.com/cksystemsteaching/selfie/blob/58503341fdff87ef993b469bc6353d75dd8ee9fd/selfie.c#L1595) using just a single line of source code in `selfie.c`. Similarly, all characters written to files and the screen are [written from left to right](http://github.com/cksystemsteaching/selfie/blob/58503341fdff87ef993b469bc6353d75dd8ee9fd/selfie.c#L1469) using just one line of code in `selfie.c`. For further details on what the code means refer to the comments in the code.

In general, we only provide links to code with comments so that text explaining code is not duplicated here. You may want read the code in `selfie.c` as if it was some sort of mechanical English. There are a lot of comments whenever the code is not sufficiently self-explanatory. In other words, reading code and comments is part of the experience of reading this book!

## Comments

Now, what is a comment in code anyway? A comment is text that the compiler ignores completely. It is only there for people to read and understand the code. In C\*, a comment is all text to the right of two slashes `//` until the end of the line. There is a lot of that in the beginning of `selfie.c`. It actually takes a bit of scrolling down to see the [first line of code](http://github.com/cksystemsteaching/selfie/blob/0d76fc92d8a79db612973153d133f14eb35efae6/selfie.c#L76) that means something to the machine and is not a comment.

If we were to remove all comments from `selfie.c` the result would still be semantically equivalent to `selfie.c` from the perspective of the machine. In fact, we can safely remove even more characters called whitespace without changing any semantics.

## Whitespace

[Whitespace Character](https://en.wikipedia.org/wiki/Whitespace_character "Whitespace Character")
: Any character or series of characters that represent horizontal or vertical space in typography. When rendered, a whitespace character does not correspond to a visible mark, but typically does occupy an area on a page.

Whitespace characters are invisible but still important for formatting source code yet they are typically irrelevant in terms of semantics. While this is true for many programming languages including C and C\* it is not true in general. There are programming languages in which whitespace does make a semantical difference. This is important to check when learning new programming languages.

The starc compiler considers the space, the tabulator, the line feed, and the carriage return characters whitespace and ignores them when reading source code:

{line-numbers=off}
```
> ./selfie -c selfie.c
./selfie: this is selfie's starc compiling selfie.c
./selfie: 166707 characters read in 6652 lines and 864 comments
./selfie: with 94033(56.49%) characters in 29064 actual symbols
...
```

Out of all the characters in `selfie.c` only a little more than half of the characters are actually considered code. The rest is whitespace and characters in comments. The code in `selfie.c` that starc uses to [ignore whitespace and comments](http://github.com/cksystemsteaching/selfie/blob/1de4c78a109a13e384aa2e4b8b126227b08f0e9a/selfie.c#L1710-L1770) works by reading characters from left to right, one after the other, and discarding them until a character is found that is not whitespace and not occurring in a comment. This may also continue until the end of the file is reached without finding such a character. Important for us here is to understand that the machine really only looks at one character at a time from start to end of the file.

Let us have a look at the following ["Hello World!" program](https://en.wikipedia.org/wiki/%22Hello,_World!%22_program) written in C\*:

{line-numbers=on, lang=c}
<<[A "Hello World!" Program](code/hello-world.c)

and run the code as follows (ignoring the compiler warning):

{line-numbers=off}
```
> ./selfie -c manuscript/code/hello-world.c -m 1
./selfie: this is selfie's starc compiling manuscript/code/hello-world.c
./selfie: warning in manuscript/code/hello-world.c in line 1: type mismatch, int expected but int* found
./selfie: 595 characters read in 20 lines and 9 comments
./selfie: with 80(13.45%) characters in 39 actual symbols
./selfie: 0 global variables, 1 procedures, 1 string literals
./selfie: 1 calls, 2 assignments, 1 while, 0 if, 0 return
./selfie: 600 bytes generated with 145 instructions and 20 bytes of data
./selfie: this is selfie's mipster executing manuscript/code/hello-world.c with 1MB of memory
Hello World!manuscript/code/hello-world.c: exiting with exit code 0
./selfie: this is selfie's mipster terminating manuscript/code/hello-world.c
...
```

There is a lot of whitespace for increasing the readability of the code as well as comments for explaining what the code does. In fact, only a little more than ten percent of the characters are actual code. Note that `"Hello World!"` is printed on the console right before the program exits.

Removing all whitespace and comments, also called minification, results in the following version:

{line-numbers=on, lang=c}
<<[Minified "Hello World!" Program](code/hello-world-minified.c)

with this output when running it:

{line-numbers=off}
```
> ./selfie -c manuscript/code/hello-world-minified.c -m 1
./selfie: this is selfie's starc compiling manuscript/code/hello-world-minified.c
./selfie: warning in manuscript/code/hello-world-minified.c in line 1: type mismatch, int expected but int* found
./selfie: 80 characters read in 0 lines and 0 comments
./selfie: with 80(100.00%) characters in 39 actual symbols
./selfie: 0 global variables, 1 procedures, 1 string literals
./selfie: 1 calls, 2 assignments, 1 while, 0 if, 0 return
./selfie: 600 bytes generated with 145 instructions and 20 bytes of data
./selfie: this is selfie's mipster executing manuscript/code/hello-world-minified.c with 1MB of memory
Hello World!manuscript/code/hello-world-minified.c: exiting with exit code 0
./selfie: this is selfie's mipster terminating manuscript/code/hello-world-minified.c
...
```

This time all characters are actual code but otherwise the behavior is the same with `"Hello World!"` appearing on the console just like before.

[Minification](https://en.wikipedia.org/wiki/Minification_(programming) "Minification")
: The process of removing all unnecessary characters from source code without changing its functionality. These unnecessary characters usually include white space characters, new line characters, and comments, which are used to add readability to the code but are not required for it to execute.

Minification is useful for improving performance and saving bandwidth when communicating source code among machines. We only mention it here to show that whitespace and comments have typically no meaning for machines. In fact, both versions of the code are semantically equivalent. How can we check that? We can have selfie generate machine code for both as follows:

{line-numbers=off}
```
> ./selfie -c manuscript/code/hello-world.c -o hello-world.m -c manuscript/code/hello-world-minified.c -o hello-world-minified.m
./selfie: this is selfie's starc compiling manuscript/code/hello-world.c
...
./selfie: 600 bytes with 145 instructions and 20 bytes of data written into hello-world.m
./selfie: this is selfie's starc compiling manuscript/code/hello-world-minified.c
...
./selfie: 600 bytes with 145 instructions and 20 bytes of data written into hello-world-minified.m
```

and then check that both files are indeed identical:

{line-numbers=off}
```
> diff -s hello-world.m hello-world-minified.m
Files hello-world.m and hello-world-minified.m are identical
```

## Strings

In computer science sequences of characters such as `Hello World!` or in fact sequences of any kind of symbols are called *strings*.

[String](https://en.wikipedia.org/wiki/String_(computer_science) "String")
: A finite sequence of characters taken from some finite alphabet.

In selfie, for example, `Hello World!` is a string whose alphabet is in fact the printable ASCII characters UTF-8-encoded in eight bits, that is, one byte per character. However, the question is how such strings are handled and in particular encoded and stored in the memory of a computer.

[Memory](https://en.wikipedia.org/wiki/Computer_memory "Memory")
: Hardware device that stores information for immediate use in a computer; it is synonymous with the term "primary storage".

Logically, memory is *storage* for bits as well as *addresses* for identifying those bits. Memory addresses are usually natural numbers from zero or some positive number to some larger positive number. To save addresses and increase speed of access, most memory is *byte-addressed*, that is, each address refers to a whole byte and not just a single bit. The size of byte-addressed memory, that is, the number of bytes that can be stored is the difference between the smallest and largest address plus one. The number of bits that can be stored is therefore eight times that value.

X> The obvious way of storing UTF-8-encoded strings such as our `Hello World!` string in byte-addressed memory is by identifying an address in memory, say, 42 and then storing the ASCII code of the first character `H` there. Then, the next character `e` is stored at address 43 and so on. Finally, the last character `!` is stored at address 53 since there are 12 characters in `Hello World!`. In other words, the string is stored *contiguously* at *increasing* addresses in memory.
X>
X> But how does the machine know where the string ends? Simple. Right after the last character `!`, at address 54, we store the value 0, also called *null*, which is the ASCII code that is here not used for anything else but to indicate the end of a string. In other words, storing an UTF-8-encoded string requires as many bytes as there are characters in the string plus one. A string stored this way is called a [*null-terminated*](https://en.wikipedia.org/wiki/Null-terminated_string) string.

In selfie, strings are stored [contiguously](http://github.com/cksystemsteaching/selfie/blob/a1f9a4270fa799430141c0aa68748b34bd5208cb/selfie.c#L1990-L2018) in memory and [null-terminated](http://github.com/cksystemsteaching/selfie/blob/a1f9a4270fa799430141c0aa68748b34bd5208cb/selfie.c#L2020) but what are the alternatives? We could store the number of characters in a string or the address of the last character in front of the string. Some systems do that but not selfie. Also, we could store the string non-contiguously in memory but would then need to remember where the characters are. This would require more space to store that information and more time to find the characters but enable us to store strings even if sufficiently large contiguous memory was not available. These are interesting and fundamental tradeoffs that will become more relevant later. Important for us here is to know that there is a choice.

## String Literals

You may have noticed the double quotes enclosing the `Hello World!` string in the "Hello World!" program. There are other sequences of characters in the program such as [`foo`](https://en.wikipedia.org/wiki/Foobar), for example, that also look like strings but are not enclosed with double quotes. The difference is that `"Hello World!"` is meant to be *literally* `Hello World!` whereas `foo` is an *identifier* that provides a name for something. If we were to change `foo` consistently in the whole program to an unused identifier such as `bar`, for example, the program would be semantically equivalent to the original version with `foo`. Changing `"Hello World!"` on the other hand would really change the output of the program. Try it!

[String Literal](https://en.wikipedia.org/wiki/String_literal "String Literal")
: The representation of a string value within the source code of a computer program.

String literals in C\* such as `"Hello World!"` make it convenient to read and write source code that needs to output text, for example. We make extensive use of string literals in `selfie.c` with [strings for reporting compiler errors](http://github.com/cksystemsteaching/selfie/blob/2613856aba61735e89ff42d98964d69637cb3111/selfie.c#L335-L362) as just one example.

The code in `selfie.c` that actually [recognizes a string literal](http://github.com/cksystemsteaching/selfie/blob/38cf8f87dd0e0ae12216ddb6b368f2ed3a35e55e/selfie.c#L2006-L2041) in source code, after reading a double quote outside of a comment, first allocates memory not used by anyone to store the string. Then it reads one character at a time and stores the characters contiguously in memory until it reads another double quote. It then stores a null to terminate the string. This code ultimately determines how string literals in C\* are handled.

## Character Literals

There is also the notion of *character literals* in C\* which we use in `selfie.c` in a number of situations, for example, for [identifying characters that represent letters](http://github.com/cksystemsteaching/selfie/blob/1520a42d446517d60e197d019977fadf471f3941/selfie.c#L1835-L1850) and for [identifying characters that represent digits](http://github.com/cksystemsteaching/selfie/blob/1520a42d446517d60e197d019977fadf471f3941/selfie.c#L1851-L1860).

[Character Literal](https://en.wikipedia.org/wiki/Character_literal "Character Literal")
: The representation of a character value within the source code of a computer program.

A character literal in C\* such as `'a'`, for example, is a single character `a` enclosed with single quotes. However, character literals are actually quite different from string literals. A character literal represents the ASCII code of the enclosed character whereas a string literal is a sequence of characters which may contain any number of characters including just one or even none denoted by `""`. Note that `''`, on the other hand, is meaningless.

X> So, what is the difference between, say, `'a'` and `"a"`?
X>
X> The character literal `'a'` is the *ASCII code* of the character `a` whereas the string literal `"a"` is an *address* in memory where the ASCII code of `a` followed by null is stored.

The code in `selfie.c` that [identifies characters other than letters and digits](http://github.com/cksystemsteaching/selfie/blob/2067b468a2ce5df91afb9e9b3a476be85fefe95a/selfie.c#L124-L147) is another example which shows how character literals are used. Take `'{'` as an example. If we were to replace `'{'` with `123` the semantics of the code would not change because 123 is the ASCII code of `{`. In other words, `'{'` stands for `123`, that is, `'{'` is really just a human-readable version of the ASCII code of `{`.

The code in `selfie.c` that [recognizes a character literal](http://github.com/cksystemsteaching/selfie/blob/38cf8f87dd0e0ae12216ddb6b368f2ed3a35e55e/selfie.c#L1981-L2005) in source code, after reading a single quote outside of a comment, reads the next character and then stores the ASCII code of that character. It then looks for the second single quote and, if it is there, returns the ASCII code. Again, this code ultimately determines how character literals in C\* are handled.

## Identifiers

Let us now go back to the notion of identifiers and our example of the identifier `foo` in the "Hello World!" program. An identifier like `foo` is just a name of something.

[Identifier](https://en.wikipedia.org/wiki/Identifier "Identifier")
: Token (also called symbol) which names a language entity. Some of the kinds of entities an identifier might denote include variables, types, labels, subroutines, and packages.

Identifiers in C\* can indeed denote different kinds of entities. But, for now, we only need to know that, unlike string literals, identifiers in C\* always begin with a letter. After that there may appear letters, digits, and underscores `_` in any order but no other characters. Why is that? Because this is how the machine knows when an identifier begins and ends. Remember, identifiers are not enclosed by any special characters like double quotes, for example.

The code in `selfie.c` that [recognizes an identifier](http://github.com/cksystemsteaching/selfie/blob/1520a42d446517d60e197d019977fadf471f3941/selfie.c#L1915-L1938) in source code, after reading a letter outside of a comment, first allocates memory not used by anyone to store the identifier, just like a string. Then it reads one character at a time and stores the characters contiguously in memory until it reads a character that is neither a letter nor a digit nor an underscore. It then stores a null to terminate the identifier. However, before deciding whether it has just recognized an identifier the code checks if it has actually recognized a *reserved identifier* or *keyword*.

## Keywords

C\* features a number of [keywords](http://github.com/cksystemsteaching/selfie/blob/22ab60a28037ae5d367ccf1de1d09a8b2e1fe555/grammar.md#L11) with special meaning that you can nevertheless safely ignore for now. The "Hello World!" program, for example, uses the `int` keyword twice and the `while` keyword once.

[Keyword](https://en.wikipedia.org/wiki/Keyword_(computer_programming) "Keyword")
: In a computer language, a reserved word (also known as a reserved identifier) is a word that cannot be used as an identifier, such as the name of a variable, function, or label – it is "reserved from use". This is a syntactic definition, and a reserved word may have no meaning. A closely related and often conflated notion is a keyword which is a word with special meaning in a particular context. This is a semantic definition. The terms "reserved word" and "keyword" are often used interchangeably – one may say that a reserved word is "reserved for use as a keyword".

Since the keywords in C\* all begin with a letter they should not be mistaken for identifiers. The code in `selfie.c` that [distinguishes keywords from identifiers](http://github.com/cksystemsteaching/selfie/blob/1520a42d446517d60e197d019977fadf471f3941/selfie.c#L1888-L1903) compares potential identifiers with all keywords to implement that distinction.

## Integers

Numbers are important and computers are incredibly good at working with them. Not surprisingly, it is very easy to talk about numbers in C\* and compute with them. For now, we look at how numbers are represented in source code and how they are encoded in memory. Numbers in selfie are *signed integers*, that is, whole numbers, positive or negative.

[Integer](https://en.wikipedia.org/wiki/Integer "Integer")
: A number that can be written without a fractional component (from the Latin integer meaning "whole").

Beyond that there is no support of, say, fixed-point or even floating-point numbers in C\*. However, it is always possible to write code in C\* based on integers that would support them. For example, there is code in `selfie.c` for printing profile information that [computes the fixed-point ratio of two integers as percentage](http://github.com/cksystemsteaching/selfie/blob/22ab60a28037ae5d367ccf1de1d09a8b2e1fe555/selfie.c#L1549-L1578) with up to two fractional digits.

Numbers, positive or negative, are encoded, like everything else, in bits. Let us go back to the earlier example of the decimal number `85`.

X> As mentioned before, the decimal number `85` in binary is represented by the 8-bit sequence `01010101`. In fact, seven bits are enough for `85` since leading zeros are unnecessary. So, actually, `85` is just `1010101`.

Both representations look different but mean the same thing and are even based on the same [numeral system](https://en.wikipedia.org/wiki/Numeral_system) using [positional notation](https://en.wikipedia.org/wiki/Positional_notation). The only difference is their *base* or *radix*.

[Radix](https://en.wikipedia.org/wiki/Radix "Radix")
: The number of unique digits, including zero, used to represent numbers in a positional numeral system.

While `1010101` is a binary number with base 2, the decimal number `85` is obviously encoded with base 10 in the *hindu-arabic* numeral system.

[Hindu-Arabic Numeral System](https://en.wikipedia.org/wiki/Hindu%E2%80%93Arabic_numeral_system "Hindu-Arabic Numeral System")
: A positional decimal numeral system and the most common for the symbolic representation of numbers in the world.

X> The value represented by `85` is obviously `8`\*10+`5` using base 10, or equivalently, (((((`1`\*2+`0`)\*2+`1`)\*2+`0`)\*2+`1`)\*2+`0`)\*2+`1` as represented by `1010101` using base 2.

Selfie does in fact implement exactly the above computation of a [recurrence relation](https://en.wikipedia.org/wiki/Recurrence_relation) for encoding numbers but only for numbers represented in decimal notation. An extension to other bases is nevertheless easy to do. Think about it and try!

The encoding is done in the procedure [`atoi`](http://github.com/cksystemsteaching/selfie/blob/3e2931dd960265d643086b6d82daee0d628301a2/selfie.c#L1408-L1457) which stands for *ascii-to-integer*. This is a [standard procedure](https://en.wikipedia.org/wiki/C_string_handling) that converts a sequence of ASCII characters representing digits in positional notation to an integer value.

X> Note that the value represented by `85` can also be computed by `8`\*10^1+`5`\*10^0 using powers of base 10, or equivalently, `1`\*2^6+`0`\*2^5+`1`\*2^4+`0`\*2^3+`1`\*2^2+`0`\*2^1+`1`\*2^0 as represented by `1010101` using powers of base 2. However, since the digits are read from left to right, computing the recurrence relation is easier.

## Integer Literal

[Integer Literal](https://en.wikipedia.org/wiki/Integer_literal "Integer Literal")
: An integer whose value is directly represented in source code.

Actually, there is another reason why identifiers start with a letter. It is because knowing upon reading the first character whether we are dealing with an identifier (or keyword) or a number makes the code that does this much simpler.

## Symbols

## Words

You may have noticed in the comments of the "Hello World!" program that the characters `"Hello World!"` are actually stored in chunks of four characters and printed accordingly. We can even see that by slowing down selfie, as before, by running in this case three mipsters on top of each other. Give it a few seconds and you will see for yourself:

{line-numbers=off}
```
> ./selfie -c manuscript/code/hello-world.c -o hello-world.m -c selfie.c -o selfie.m -m 2 -l selfie.m -m 1 -l hello-world.m -m 1
./selfie: this is selfie's starc compiling manuscript/code/hello-world.c
...
./selfie: 600 bytes with 145 instructions and 20 bytes of data written into hello-world.m
./selfie: this is selfie's starc compiling selfie.c
...
./selfie: 125948 bytes with 29970 instructions and 6068 bytes of data written into selfie.m
./selfie: this is selfie's mipster executing selfie.m with 2MB of memory
selfie.m: 125948 bytes with 29970 instructions and 6068 bytes of data loaded from selfie.m
selfie.m: this is selfie's mipster executing selfie.m with 1MB of memory
selfie.m: 600 bytes with 145 instructions and 20 bytes of data loaded from hello-world.m
selfie.m: this is selfie's mipster executing hello-world.m with 1MB of memory
Hello World!hello-world.m: exiting with exit code 0
selfie.m: this is selfie's mipster terminating hello-world.m
...
selfie.m: exiting with exit code 0
selfie.m: this is selfie's mipster terminating selfie.m
...
selfie.m: exiting with exit code 0
./selfie: this is selfie's mipster terminating selfie.m
...
```

The string `"Hell"` appears first on the console. Then, after a while, the string `"o Wo"` appears. Finally, the string `"rld!"` appears and selfie terminates, slowly.



The machine that the mipster emulator in selfie emulates handles everything, code and data, in chunks of 32 bits, that is, four bytes. Such a chunk is called a *machine word* or just a *word*.

[Word](https://en.wikipedia.org/wiki/Word_(computer_architecture) "Word")
: A term for the natural unit of data used by a particular processor design. A word is basically a fixed-sized group of digits that are handled as a unit by the instruction set or the hardware of the processor. The number of digits in a word (the word size, word width, or word length) is an important characteristic of any specific processor design or computer architecture.

## Instructions