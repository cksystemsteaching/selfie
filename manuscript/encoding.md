# 3. Encoding {#encoding}

Information, whatever it is, needs to be encoded in bits for a computer to handle it. Since `selfie.c` is a sequence of characters let us first look at how characters are encoded.

## Characters

We mention in the [previous chapter](#semantics) that the characters in `selfie.c` are [ASCII](https://en.wikipedia.org/wiki/ASCII "ASCII") characters encoded in eight bits, that is, one byte according to the [UTF-8](https://en.wikipedia.org/wiki/UTF-8 "UTF-8") standard.

X> According to UTF-8 (and ASCII), the uppercase letter `U`, for example, is encoded in the 8-bit sequence `01010101`.

Both ASCII and UTF-8 are essentially one-to-one mappings from bits to characters written down in a table. Each 8-bit sequence is associated with exactly one character. For a computer that table is only relevant when the machine receives characters from a keyboard and sends characters to a screen. Then, the machine needs to know the ASCII code for each key on the keyboard to remember which key was pressed and it needs to know which shape of character to draw on the screen for each bit sequence. Internally, however, characters are just 8-bit sequences, with selfie and a lot of other software as well.

Let us pause for a moment and reflect about this. The above bit sequence could really still mean anything. The encoding standards for characters are just agreements on how to associate bits and characters but there is still no meaning.

X> The bit sequence `01010101` is also binary for the decimal number 85.

So what is it now, `U` or 85? The answer is both, and anything else. As mentioned in the [previous chapter](#semantics), meaning comes from change. When the machine draws `U` for `01010101` on the screen then `01010101` stands for `U` in that moment but in the next moment the machine could increment `01010101` according to elementary arithmetic making `01010101` represent 85.

But how does selfie actually read characters from files such as `selfie.c`? It turns out that selfie does [read](http://github.com/cksystemsteaching/selfie/blob/58503341fdff87ef993b469bc6353d75dd8ee9fd/selfie.c#L1595) all characters using just a single line of source code in `selfie.c`. Similarly, all characters written to files and the screen are [written](http://github.com/cksystemsteaching/selfie/blob/58503341fdff87ef993b469bc6353d75dd8ee9fd/selfie.c#L1469) using just one line of code in `selfie.c`. For further details on what the code means refer to the comments in the code.

In general, we only provide links to code with comments so that text explaining code is not duplicated here. You may want read the code in `selfie.c` as if it was some sort of mechanical English. There are a lot of comments whenever the code is not sufficiently self-explanatory. In other words, reading code and comments is part of the experience of reading this book!

## Comments

Now, what is a comment in code anyway? A comment is text that the machine ignores completely. It is only there for people to read and understand the code. In C\*, a comment is all text to the right of two slashes `//` until the end of the line. There is a lot of that in the beginning of `selfie.c`. It actually takes a bit of scrolling down to see the [first line of code](http://github.com/cksystemsteaching/selfie/blob/0d76fc92d8a79db612973153d133f14eb35efae6/selfie.c#L76) that means something to the machine and is not a comment.

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

Out of all the characters in `selfie.c` only a little more than half of the characters are actually considered code. The rest is whitespace and characters in comments. The [code](http://github.com/cksystemsteaching/selfie/blob/1de4c78a109a13e384aa2e4b8b126227b08f0e9a/selfie.c#L1710-L1770) in `selfie.c` that starc uses to ignore whitespace and comments works by reading characters from left to right, one after the other, and discarding them until a character is found that is not whitespace and not occurring in a comment. This may also continue until the end of the file is reached without finding such a character. Important for us here is to understand that the machine really only looks at one character at a time from start to end of the file.

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

In computer science sequences of characters such as `"Hello World!"` or in fact sequences of any kind of symbols are called *strings*.

[String](https://en.wikipedia.org/wiki/String_(computer_science) "String")
: A finite sequence of characters taken from some finite alphabet.

In selfie, for example, `"Hello World!"` is a string whose alphabet is in fact the printable ASCII characters UTF-8-encoded in eight bits, that is, one byte per character. However, the question is how such strings are handled and in particular encoded and stored in the memory of a computer.

[Memory](https://en.wikipedia.org/wiki/Computer_memory "Memory")
: Hardware device that stores information for immediate use in a computer; it is synonymous with the term "primary storage".

Logically, memory is *storage* for bits as well as *addresses* for identifying those bits. Memory addresses are usually natural numbers from zero or some positive number to some larger positive number. To save addresses and increase speed of access, most memory is *byte-addressed*, that is, each address refers to a whole byte and not just a single bit. The size of byte-addressed memory, that is, the number of bytes that can be stored is the difference between the smallest and largest address plus one. The number of bits that can be stored is therefore eight times that value.

X> The obvious way of storing UTF-8-encoded strings such as our `"Hello World!"` string in byte-addressed memory is by identifying an address in memory, say, 42 and then storing the ASCII code of the first character `H` there. Then, the next character `e` is stored at address 43 and so on. Finally, the last character `!` is stored at address 53 since there are 12 characters in `"Hello World!"`. In other words, the string is stored *contiguously* at *increasing* addresses in memory.
X>
X> But how does the machine know where the string ends? Simple. Right after the last character `!`, at address 53, we store the value 0, also called *null*, which is the ASCII code that is here not used for anything else but to indicate the end of a string. In other words, storing an UTF-8-encoded string requires as many bytes as there are characters in the string plus one. A string stored this way is called a [*null-terminated*](https://en.wikipedia.org/wiki/Null-terminated_string) string.

With selfie, strings are stored [contiguously](http://github.com/cksystemsteaching/selfie/blob/a1f9a4270fa799430141c0aa68748b34bd5208cb/selfie.c#L1990-L2018) in memory and [null-terminated](http://github.com/cksystemsteaching/selfie/blob/a1f9a4270fa799430141c0aa68748b34bd5208cb/selfie.c#L2020) but what are the alternatives? We could store the number of characters in a string or the address of the last character in front of the string. Some systems do that but not selfie. Also, we could store the string non-contiguously in memory but would then need to remember where the characters are. This would require more space to store that information and more time to find the characters but enable us to store strings even if sufficiently large contiguous memory was not available. These are interesting and fundamental tradeoffs that will become more relevant later. Important for us here is to know that there is a choice.

You may have noticed the double quotes around the `"Hello World!"` string in the "Hello World!" program. There are other sequences of characters in the program such as [`foo`](https://en.wikipedia.org/wiki/Foobar), for example, that also look like strings but are not enclosed with double quotes. The difference is that the `"Hello World!"` string is meant to be *literally* `Hello World!` whereas `foo` is an *identifier* that provides a name for something. If we were to change `foo` consistently in the whole program to `bar`, for example, the program would be semantically equivalent to the original version with `foo`. Try it!

[String Literal](https://en.wikipedia.org/wiki/String_literal "String Literal")
: The representation of a string value within the source code of a computer program.

String literals such as `"Hello World!"` make it convenient to read and write source code that needs to output text, for example. We make extensive use of string literals in `selfie.c` with [strings for reporting compiler errors](http://github.com/cksystemsteaching/selfie/blob/2613856aba61735e89ff42d98964d69637cb3111/selfie.c#L335-L362) as just one example.

There is also the notion of *character literals* which we use in `selfie.c` in a number of situations, for example, for identifying [characters that represent letters](http://github.com/cksystemsteaching/selfie/blob/2613856aba61735e89ff42d98964d69637cb3111/selfie.c#L1821-L1827).

[Character Literal](https://en.wikipedia.org/wiki/Character_literal "Character Literal")
: The representation of a character value within the source code of a computer program.

A character literal in source code such as `'a'`, for example, is a single character `a` enclosed with single quotes. However, character literals are actually quite different from string literals. A character literal represents the ASCII code of the enclosed character whereas a string literal is a sequence of characters which may contain any number of characters including just one or even none denoted by `""`.  This also means that `''` is meaningless.

X> So, what is the difference between, say, `'a'` and `"a"`?
X>
X> The character literal `'a'` is the *ASCII code* of the character `a` whereas the string literal `"a"` is an *address* in memory where the ASCII code of `a` followed by null is stored.

The code in `selfie.c` that identifies [relevant characters other than letters and digits](http://github.com/cksystemsteaching/selfie/blob/2067b468a2ce5df91afb9e9b3a476be85fefe95a/selfie.c#L124-L147) is another example which explains what character literals are. Take `'{'` as an example. If we were to replace `'{'` with `123` the semantics of the code would not change because 123 is the ASCII code of `{`. In other words, `'{'` stands for `123`, that is, `'{'` is really just a human-readable version of the ASCII code of `{`.



## Identifiers

[Identifier](https://en.wikipedia.org/wiki/Identifier "Identifier")
: Token (also called symbol) which names a language entity. Some of the kinds of entities an identifier might denote include variables, types, labels, subroutines, and packages.

## Integers

[Integer](https://en.wikipedia.org/wiki/Integer "Integer")
: A number that can be written without a fractional component (from the Latin integer meaning "whole").

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