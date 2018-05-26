# 3. Encoding {#encoding}

Information, whatever it is, needs to be encoded in bits for a computer to handle it. Since `selfie.c` is a sequence of characters let us first look at how characters are encoded. After that we explain how sequences of characters form larger constructs such as strings, identifiers, and even positive and negative numbers. We also recall parts of elementary arithmetics and explain how that works on a computer.

Interestingly, the encoding of numbers can also be used to represent information on machine level. For example, the encoding of memory addresses and machine instructions can be done in the same or a similar way than the encoding of numbers. We explain that here as well.

## Characters

We mention in the [previous chapter](#semantics) that the characters in `selfie.c` are [ASCII](https://en.wikipedia.org/wiki/ASCII "ASCII") characters encoded in eight bits, that is, one byte according to the [UTF-8](https://en.wikipedia.org/wiki/UTF-8 "UTF-8") standard.

X> According to UTF-8 (and ASCII), the uppercase letter `U`, for example, is encoded in the 8-bit sequence `01010101`.

Both ASCII and UTF-8 are essentially one-to-one mappings from bits to characters written down in a table. Each 8-bit sequence is associated with exactly one character. For a computer that table is only relevant when the machine receives characters from a keyboard and sends characters to a screen. Then, the machine needs to know the ASCII code for each key on the keyboard to remember which key was pressed and it needs to know which shape of character to draw on the screen for each bit sequence. Internally, however, characters are just 8-bit sequences, with selfie and a lot of other software as well.

Let us pause for a moment and reflect about this. The above bit sequence could really still mean anything. The encoding standards for characters are just agreements on how to associate bits and characters but there is still no meaning.

X> The bit sequence `01010101` is also binary for the [decimal number](https://en.wikipedia.org/wiki/Decimal) `85`.

So what is it now, `U` or `85`? The answer is both, and anything else. As mentioned in the [previous chapter](#semantics), meaning comes from change. When the machine draws `U` for `01010101` on the screen then `01010101` stands for `U` in that moment but in the next moment the machine could increment `01010101` according to elementary arithmetic making `01010101` represent `85`.

But how does selfie and in particular the starc compiler actually read characters from files such as `selfie.c`? It turns out that all characters are [read from left to right](http://github.com/cksystemsteaching/selfie/blob/6069120cb8d50fd31880f69e7f0f83c387913140/selfie.c#L1820) using just a single line of source code in `selfie.c`. Similarly, all characters written to files and the screen are [written from left to right](http://github.com/cksystemsteaching/selfie/blob/6069120cb8d50fd31880f69e7f0f83c387913140/selfie.c#L1639) using just one line of code in `selfie.c`. For further details on what the code means refer to the comments in the code.

In general, we only provide links to code with comments so that text explaining code is not duplicated here. You may want read the code in `selfie.c` as if it was some sort of mechanical English. There are a lot of comments whenever the code is not sufficiently self-explanatory. In other words, reading code and comments is part of the experience of reading this book!

## Comments

Now, what is a comment in code anyway? A comment is text that the compiler ignores completely. It is only there for people to read and understand the code. In C\*, a comment is all text to the right of two slashes `//` until the end of the line. There is a lot of that in the beginning of `selfie.c`. It actually takes a bit of scrolling down to see the [first line of code](http://github.com/cksystemsteaching/selfie/blob/6069120cb8d50fd31880f69e7f0f83c387913140/selfie.c#L85) that means something to the machine and is not a comment.

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
./selfie: 176408 characters read in 7083 lines and 969 comments
./selfie: with 97779(55.55%) characters in 28914 actual symbols
...
```

Out of all the characters in `selfie.c` only a little more than half of the characters are actually considered code. The rest is whitespace and characters in comments. The code in `selfie.c` that starc uses to [ignore whitespace and comments](http://github.com/cksystemsteaching/selfie/blob/6069120cb8d50fd31880f69e7f0f83c387913140/selfie.c#L1858-L1913) works by reading characters from left to right, one after the other, and discarding them until a character is found that is not whitespace and not occurring in a comment. This may also continue until the end of the file is reached without finding such a character. Important for us here is to understand that the machine really only looks at one character at a time from start to end of the file.

Let us have a look at the following ["Hello World!" program](https://en.wikipedia.org/wiki/%22Hello,_World!%22_program) written in C\*:

{line-numbers=on, lang=c}
<<[A "Hello World!" Program](code/hello-world.c)

and run the [code](http://github.com/cksystemsteaching/selfie/blob/a7fcb70c1683802c644f0cd1af3892696f68f4bd/manuscript/code/hello-world.c) as follows (ignoring the compiler warning):

{line-numbers=off}
```
> ./selfie -c manuscript/code/hello-world.c -m 1
./selfie: this is selfie's starc compiling manuscript/code/hello-world.c
./selfie: warning in manuscript/code/hello-world.c in line 5: type mismatch, int expected but int* found
./selfie: 729 characters read in 22 lines and 11 comments
./selfie: with 80(10.97%) characters in 39 actual symbols
./selfie: 1 global variables, 1 procedures, 1 string literals
./selfie: 1 calls, 2 assignments, 1 while, 0 if, 0 return
./selfie: 600 bytes generated with 144 instructions and 24 bytes of data
./selfie: this is selfie's mipster executing manuscript/code/hello-world.c with 1MB of physical memory
Hello World!manuscript/code/hello-world.c: exiting with exit code 0 and 0.00MB of mallocated memory
./selfie: this is selfie's mipster terminating manuscript/code/hello-world.c with exit code 0 and 0.00MB of mapped memory
...
```

There is a lot of whitespace for increasing the readability of the code as well as comments for explaining what the code does. In fact, only a little more than ten percent of the characters are actual code. Note that `"Hello World!"` is printed on the console right before the program exits.

Removing all whitespace and comments, also called minification, results in the following version:

{line-numbers=on, lang=c}
<<[Minified "Hello World!" Program](code/hello-world-minified.c)

with this output when running the [code](http://github.com/cksystemsteaching/selfie/blob/a7fcb70c1683802c644f0cd1af3892696f68f4bd/manuscript/code/hello-world-minified.c):

{line-numbers=off}
```
> ./selfie -c manuscript/code/hello-world-minified.c -m 1
./selfie: this is selfie's starc compiling manuscript/code/hello-world-minified.c
./selfie: warning in manuscript/code/hello-world-minified.c in line 1: type mismatch, int expected but int* found
./selfie: 80 characters read in 0 lines and 0 comments
./selfie: with 80(100.00%) characters in 39 actual symbols
./selfie: 1 global variables, 1 procedures, 1 string literals
./selfie: 1 calls, 2 assignments, 1 while, 0 if, 0 return
./selfie: 600 bytes generated with 144 instructions and 24 bytes of data
./selfie: this is selfie's mipster executing manuscript/code/hello-world-minified.c with 1MB of physical memory
Hello World!manuscript/code/hello-world-minified.c: exiting with exit code 0 and 0.00MB of mallocated memory
./selfie: this is selfie's mipster terminating manuscript/code/hello-world-minified.c with exit code 0 and 0.00MB of mapped memory
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
./selfie: 600 bytes with 144 instructions and 24 bytes of data written into hello-world.m
./selfie: this is selfie's starc compiling manuscript/code/hello-world-minified.c
...
./selfie: 600 bytes with 144 instructions and 24 bytes of data written into hello-world-minified.m
```

and then check that both files are indeed identical:

{line-numbers=off}
```
> diff -s hello-world.m hello-world-minified.m
Files hello-world.m and hello-world-minified.m are identical
```

## Strings

In computer science sequences of characters such as `Hello World!` are called *strings*.

[String](https://en.wikipedia.org/wiki/String_(computer_science) "String")
: A finite sequence of characters taken from some finite alphabet.

In selfie, for example, `Hello World!` is a string whose alphabet is in fact the printable ASCII characters UTF-8-encoded in eight bits, that is, one byte per character. However, the question is how such strings are handled and in particular encoded and stored in the memory of a computer.

[Memory](https://en.wikipedia.org/wiki/Computer_memory "Memory")
: Hardware device that stores information for immediate use in a computer; it is synonymous with the term "primary storage".

Logically, memory is *storage* for bits as well as *addresses* for identifying those bits. Memory addresses are usually natural numbers from zero or some positive number to some larger positive number. To save addresses and increase speed of access, most memory is *byte-addressed*, that is, each address refers to a whole byte and not just a single bit. The size of byte-addressed memory, that is, the number of bytes that can be stored is the difference between the smallest and largest address plus one. The number of bits that can be stored is therefore eight times that value.

X> The obvious way of storing UTF-8-encoded strings such as our `Hello World!` string in byte-addressed memory is by identifying an address in memory, say, 42 and then storing the ASCII code of the first character `H` there. Then, the next character `e` is stored at address 43 and so on. Finally, the last character `!` is stored at address 53 since there are 12 characters in `Hello World!`. In other words, the string is stored *contiguously* at *increasing* addresses in memory.
X>
X> But how does the machine know where the string ends? Simple. Right after the last character `!`, at address 54, we store the value 0, also called *null*, which is the ASCII code that is here not used for anything else but to indicate the end of a string. In other words, storing an UTF-8-encoded string requires as many bytes as there are characters in the string plus one. A string stored this way is called a [*null-terminated*](https://en.wikipedia.org/wiki/Null-terminated_string) string.

In selfie, strings are stored [contiguously](http://github.com/cksystemsteaching/selfie/blob/6069120cb8d50fd31880f69e7f0f83c387913140/selfie.c#L2086-L2116) in memory and [null-terminated](http://github.com/cksystemsteaching/selfie/blob/6069120cb8d50fd31880f69e7f0f83c387913140/selfie.c#L2118) but what are the alternatives? We could store the number of characters in a string or the address of the last character in front of the string. Some systems do that but not selfie. Also, we could store the string non-contiguously in memory but would then need to remember where the characters are. This would require more space to store that information and more time to find the characters but enable us to store strings even if sufficiently large contiguous memory was not available. These are interesting and fundamental tradeoffs that will become more relevant later. Important for us here is to know that there is a choice.

## String Literals

You may have noticed the double quotes enclosing the `Hello World!` string in the "Hello World!" program. There are other sequences of characters in the program such as [`foo`](https://en.wikipedia.org/wiki/Foobar), for example, that also look like strings but are not enclosed with double quotes. The difference is that `"Hello World!"` is meant to be *literally* `Hello World!` whereas `foo` is an *identifier* that provides a name for something. If we were to change `foo` consistently in the whole program to an unused identifier such as `bar`, for example, the program would be semantically equivalent to the original version with `foo`. Changing `"Hello World!"` on the other hand would really change the output of the program. Try it!

[String Literal](https://en.wikipedia.org/wiki/String_literal "String Literal")
: The representation of a string value within the source code of a computer program.

String literals in C\* such as `"Hello World!"` make it convenient to read and write source code that needs to output text, for example. We make extensive use of string literals in `selfie.c` with [strings for reporting compiler errors](http://github.com/cksystemsteaching/selfie/blob/6069120cb8d50fd31880f69e7f0f83c387913140/selfie.c#L357-L384) as just one example.

The code in `selfie.c` that actually [recognizes a string literal](http://github.com/cksystemsteaching/selfie/blob/6069120cb8d50fd31880f69e7f0f83c387913140/selfie.c#L2086-L2121) in source code, after reading a double quote outside of a comment, first allocates memory not used by anyone to store the string. Then it reads one character at a time and stores the characters contiguously in memory until it reads another double quote. It then stores a null to terminate the string. This code ultimately determines how string literals in C\* are handled.

## Character Literals

There is also the notion of *character literals* in C\* which we use in `selfie.c` in a number of situations, for example, for [identifying characters that represent letters](http://github.com/cksystemsteaching/selfie/blob/6069120cb8d50fd31880f69e7f0f83c387913140/selfie.c#L1915-L1929) and for [identifying characters that represent digits](http://github.com/cksystemsteaching/selfie/blob/6069120cb8d50fd31880f69e7f0f83c387913140/selfie.c#L1931-L1940).

[Character Literal](https://en.wikipedia.org/wiki/Character_literal "Character Literal")
: The representation of a character value within the source code of a computer program.

A character literal in C\* such as `'a'`, for example, is a single character `a` enclosed with single quotes. However, character literals are actually quite different from string literals. A character literal represents the ASCII code of the enclosed character whereas a string literal is a sequence of characters which may contain any number of characters including just one or even none denoted by `""`. Note that `''`, on the other hand, is meaningless.

X> So, what is the difference between, say, `'a'` and `"a"`?
X>
X> The character literal `'a'` is the *ASCII code* of the character `a` whereas the string literal `"a"` is an *address* in memory where the ASCII code of `a` followed by null is stored.

The code in `selfie.c` that [identifies characters other than letters and digits](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L134-L156) is another example which shows how character literals are used. Take `'{'` as an example. If we were to replace `'{'` with `123` the semantics of the code would not change because 123 is the ASCII code of `{`. In other words, `'{'` stands for `123`, that is, `'{'` is really just a human-readable version of the ASCII code of `{`.

The code in `selfie.c` that [recognizes a character literal](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L2061-L2084) in source code, after reading a single quote outside of a comment, reads the next character and then stores the ASCII code of that character. It then looks for the second single quote and, if it is there, returns the ASCII code. Again, this code ultimately determines how character literals in C\* are handled.

## Identifiers

Let us now go back to the notion of identifiers and our example of the identifier `foo` in the "Hello World!" program. An identifier like `foo` is just a name of something.

[Identifier](https://en.wikipedia.org/wiki/Identifier "Identifier")
: A name that identifies (that is, labels the identity of) either a unique entity or a unique class of entities. Some of the kinds of entities an identifier might denote include variables, types, and subroutines.

Identifiers in C\* can indeed denote different kinds of entities. But, for now, we only need to know that, unlike string literals, identifiers in C\* always begin with a letter. After that there may appear letters, digits, and underscores `_` in any order but no other characters. Why is that? Because this is how the machine knows when an identifier begins and ends. Remember, identifiers are not enclosed by any special characters like double quotes, for example.

The code in `selfie.c` that [recognizes an identifier](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L1995-L2017) in source code, after reading a letter outside of a comment, first allocates memory not used by anyone to store the identifier, just like a string. Then it reads one character at a time and stores the characters contiguously in memory until it reads a character that is neither a letter nor a digit nor an underscore. It then stores a null to terminate the identifier. However, before deciding whether it has just recognized an identifier the code checks if it has actually recognized a *reserved identifier* or *keyword*.

## Keywords

C\* features a number of [keywords](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/grammar.md#L11) with special meaning that you can nevertheless safely ignore for now. The "Hello World!" program, for example, uses the `int` keyword twice and the `while` keyword once.

[Keyword](https://en.wikipedia.org/wiki/Keyword_(computer_programming) "Keyword")
: In a computer language, a reserved word (also known as a reserved identifier) is a word that cannot be used as an identifier, such as the name of a variable, function, or label – it is "reserved from use". This is a syntactic definition, and a reserved word may have no meaning. A closely related and often conflated notion is a keyword which is a word with special meaning in a particular context. This is a semantic definition. The terms "reserved word" and "keyword" are often used interchangeably – one may say that a reserved word is "reserved for use as a keyword".

Since the keywords in C\* all begin with a letter they should not be mistaken for identifiers. The code in `selfie.c` that [distinguishes keywords from identifiers](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L1968-L1983) compares potential identifiers with all keywords to implement that distinction.

## Integers

Numbers are important and computers are incredibly good at working with them. Not surprisingly, it is very easy to talk about numbers in C\* and compute with them. For now, we look at how numbers are represented in source code and how they are encoded in digital memory. Numbers in selfie are *signed integers*, that is, whole numbers, positive or negative.

[Integer](https://en.wikipedia.org/wiki/Integer "Integer")
: A number that can be written without a fractional component (from the Latin integer meaning "whole"). For example, 21, 4, 0, and −2048 are integers, while 9.75 and 5.5 are not. The set of integers consists of zero (0), the natural numbers (1, 2, 3, ...), also called whole, counting, or positive numbers, and their additive inverses (the negative numbers, that is −1, −2, −3, ...).

T> In computer science integers are sometimes specifically qualified to be *unsigned*. In this case, they are meant to represent zero and positive numbers but no negative numbers. Integers may explicitly be called *signed* to emphasize that they are also meant to represent negative numbers.

Beyond signed integers there is no support of, say, [fixed-point](https://en.wikipedia.org/wiki/Fixed-point_arithmetic) or even [floating-point](https://en.wikipedia.org/wiki/Floating_point) numbers in C\*. However, it is always possible to write code in C\* based on integers that would support them. For example, there is code in `selfie.c` for printing profiling information that [computes the fixed-point ratio of two integers as percentage](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L1605-L1622) with up to two fractional digits.

Numbers, positive or negative, are encoded, like everything else, in bits. Let us go back to the earlier example of the decimal number `85`.

X> As mentioned before, the decimal number `85` in binary is represented by the 8-bit sequence `01010101`. In fact, seven bits are enough for `85` since leading zeros are unnecessary. So, actually, `85` is just `1010101`.

Both representations look different but mean the same thing and are even based on the same [numeral system](https://en.wikipedia.org/wiki/Numeral_system) using [positional notation](https://en.wikipedia.org/wiki/Positional_notation). The only difference is their *base* or *radix*.

[Radix](https://en.wikipedia.org/wiki/Radix "Radix")
: The number of unique digits, including zero, used to represent numbers in a positional numeral system.

Most importantly, arithmetic operations such as addition and subtraction work the same way for any base greater than one as long as we use the same base for the operands of the operation. For example, manually adding two binary numbers works just like adding two decimal numbers, more on that below.

While `1010101` is a binary number with base 2, the decimal number `85` is obviously encoded with base 10 in the *hindu-arabic* numeral system.

[Hindu-Arabic Numeral System](https://en.wikipedia.org/wiki/Hindu%E2%80%93Arabic_numeral_system "Hindu-Arabic Numeral System")
: A positional decimal numeral system and the most common for the symbolic representation of numbers in the world.

X> The value represented by `85` is obviously `8`\*10+`5` using base 10, or equivalently, (((((`1`\*2+`0`)\*2+`1`)\*2+`0`)\*2+`1`)\*2+`0`)\*2+`1` as represented by `1010101` using base 2.

Selfie does in fact implement exactly the above computation of a [recurrence relation](https://en.wikipedia.org/wiki/Recurrence_relation) for encoding numbers but only for numbers represented in decimal notation. An extension to other bases is nevertheless easy to do. Think about it and try!

The encoding is done in the procedure [`atoi`](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L1409-L1457) which stands for *ascii-to-integer*. This is a [standard procedure](https://en.wikipedia.org/wiki/C_string_handling) that converts a sequence of ASCII characters representing digits in positional notation to an integer value.

X> Note that the value represented by `85` can also be computed by `8`\*10^1^+`5`\*10^0^ using powers of base 10, or equivalently, `1`\*2^6^+`0`\*2^5^+`1`\*2^4^+`0`\*2^3^+`1`\*2^2^+`0`\*2^1^+`1`\*2^0^ as represented by `1010101` using powers of base 2. However, since the digits are read from left to right, computing the recurrence relation is easier.

Selfie also implements the procedure symmetric to `atoi` called [`itoa`](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L1459-L1603) which obviously stands for *integer-to-ascii*. It works by dividing the given integer by the desired base repeatedly until the quotient is zero and saving the remainders during the process. At the end, the sequence of remainders is reversed (hindu-arabic) and then returned.

X> Suppose we would like to convert the value of `85` to a string `"85"` that shows the value in decimal. This works by dividing `85` by the base 10 resulting in the quotient `8` and the remainder `5`, which we save as a string `"5"`. We then divide quotient `8` by 10 which is quotient `0` and append the remainder, which is `8`, to the string `"5"` resulting in the string `"58"`. Quotient `0` terminates the conversion. The resulting string `"58"` in reverse is the desired string `"85"`.

The implementation of `itoa` in selfie not only supports decimal but also binary, [octal](https://en.wikipedia.org/wiki/Octal) (base 8), and [hexadecimal](https://en.wikipedia.org/wiki/Hexadecimal) (base 16) notation. We prepared a simple program called [`integer.c`](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/manuscript/code/integer.c) that prints the value represented by `85` in all possible ways supported by selfie as follows:

{line-numbers=off}
```
> ./selfie -c manuscript/code/integer.c selfie.c -m 1
./selfie: this is selfie's starc compiling manuscript/code/integer.c
...
./selfie: this is selfie's mipster executing manuscript/code/integer.c with 1MB of physical memory
85 in decimal:     85
'U' in ASCII:      85
"85" string:       85
85 in hexadecimal: 0x55
85 in octal:       00125
85 in binary:      1010101
manuscript/code/integer.c: exiting with exit code 0 and 0.00MB of mallocated memory
./selfie: this is selfie's mipster terminating manuscript/code/integer.c with exit code 0 and 0.12MB of mapped memory
...
```

T> Numbers in hexadecimal, such as `0x55` for example, are printed with a leading `0x` to emphasize that they use base 16. Similarly, a leading `00` indicates that the following number uses base 8 as in `00125`, for example.

You may check for yourself that `0x55` and `00125` do in fact represent the value `85` by computing `5`\*16+`5` and (`1`\*8+`2`)\*8+`5`.

T> For hexadecimal notation six digits more than the ten digits of decimal notation are needed. More specifically, the values `10`, `11`, `12`, `13`, `14`, and `15` need to be represented. The standard representation is to use the uppercase letters `A`, `B`, `C`, `D`, `E`, and `F`, respectively. For example, `0xFF` stands for the value `15`\*16+`15` which is `255`.

Hexadecimal and octal notation are popular in computer science because their digits represent blocks of four and three bits, respectively. In other words, their bases are powers of four and three, respectively, of the base 2 of binary notation. Hexadecimal and octal notation are therefore convenient and compact notation for binary numbers. The base 10 of decimal notation is not a power of the base 2. Digits in decimal notation therefore do not evenly correspond to blocks of bits.

X> Both `0x55` and `00125` represent the value `1010101` in binary, that is, two blocks of four bits `0101 0101` and three blocks of three bits `001 010 101`, respectively. A block of four bits such as `0101` is called a [nibble](https://en.wikipedia.org/wiki/Nibble) which corresponds to exactly one hexadecimal digit such as here `0x5`.

The actual encoding of numbers in the memory of a digital computer, however, is not in hexadecimal or octal but usually in binary. Before continuing to negative numbers let us point out that there is a way to represent numbers that is even more basic than binary. It is called *unary* and works by simply using an alphabet with a single digit for counting the value of a number.

[Unary Numeral System](https://en.wikipedia.org/wiki/Unary_numeral_system)
: The bijective base-1 numeral system. It is the simplest numeral system to represent natural numbers: in order to represent a number N, an arbitrarily chosen symbol representing the value 1 is repeated N times.

Q> The decimal number `85`, for example, is in unary `1111111111111111111111111111111111111111111111111111111111111111111111111111111111111`

Well, have you noticed the enormous difference in length between unary and other representations with higher bases?

Q> For example, `85` in unary obviously requires more than forty times more digits than the two digits of `85` and still more than ten times more digits than the eight bits of `01010101`.
Q>
Q> In fact, the situation is worse since, for example, seven bits are actually enough to represent `85`. Even worse, seven bits can represent up to 128 different values, that is, in the representation chosen here, all decimal numbers between 0 and 127 inclusive. Thus unary requires up to eighteen times more digits than a 7-bit binary number. One more bit almost doubles the difference. Then, unary needs up to 32 times more digits than an 8-bit binary number.

The fundamental reason for the difference in size between different notations is that any representation with a base greater than one is *exponentially* more succinct than unary. However, representations with base greater than one are only different in size by a *constant factor*. For example, octal and hexadecimal representations are only three and four times, respectively, more succinct than binary. A larger alphabet makes even less of a difference, that is, *logarithmically* less in the size of the alphabet. ASCII, for example, is only seven times more succinct than binary although there are 128 ASCII characters.

| Encoding | Alphabet | Base (Radix, Size of Alphabet) | # Digits in Values {$$}n>1{/$$} | # Values in Digits {$$}n>0{/$$} |
| - | - | -: | -: | -: |
| [Unary](https://en.wikipedia.org/wiki/Unary_numeral_system "Unary") | {1} | 1 | {$$}n{/$$} | {$$}n{/$$} |
| [Binary](https://en.wikipedia.org/wiki/Binary_number "Binary") | {0,1} | 2 | {$$}\lceil\frac{log(n)}{log(2)}\rceil{/$$} | {$$}2^n{/$$} |
| [Octal](https://en.wikipedia.org/wiki/Octal "Octal") | {0,1,2,3,4,5,6,7} | 8 | {$$}\lceil\frac{log(n)}{log(8)}\rceil{/$$} | {$$}8^n{/$$} |
| [Decimal](https://en.wikipedia.org/wiki/Decimal "Decimal") | {0,1,2,3,4,5,6,7,8,9} | 10 | {$$}\lceil\frac{log(n)}{log(10)}\rceil{/$$} | {$$}10^n{/$$} |
| [Hexadecimal](https://en.wikipedia.org/wiki/Hexadecimal "Hexadecimal") | {0,1,2,3,4,5,6,7,8,9, | 16 | {$$}\lceil\frac{log(n)}{log(16)}\rceil{/$$} | {$$}16^n{/$$} |
| | A,B,C,D,E,F} | | | |

### Integer Arithmetics

Fortunately, elementary arithmetics with binary numbers works just like it does with decimal numbers or any other representation with base greater than one. For example, adding two numbers in any such representation works as usual by adding their digits from right to left while carrying any *overflow* to the left. Only unary is different! Elementary arithmetics with unary numbers is obviously done by, imagine, *string concatenation*.

X> Let us add the values 85 and, say, 170.
X>
X> Remember from school? Starting from the right we find that 5+0=5. Thus the rightmost digit of the result is 5. Then, with 8+7=15 the second rightmost digit is 5. Since 15>9 there is an overflow that needs to be considered next. With 1+1=2 we obtain the leftmost digit and the final result of 255.
X>
X> Let us now add both numbers in binary, that is, 01010101 for 85 and 10101010, which is binary for 170. It works in just the same way.
X>
X> Since 1+0=1 there is no overflow here. Thus the result of 11111111, which is binary for 255, can easily be obtained by just adding the individual digits. In general though, one adds two binary numbers just like decimal numbers, digit by digit from right to left, while carrying any overflow to the left.
X>
X> Adding both numbers in hexadecimal, that is, 0x55 and 0xAA, works similarly, in this case also without overflow. With 5+A=F the result is 0xFF, which is hexadecimal for 255.

In binary numbers the leftmost and rightmost bits have a meaning similar to the leftmost and rightmost digits in decimal numbers. The rightmost bit, also called *least significant bit*, determines if the number is even or odd. For example, `01010101` represents an odd number whereas `10101010` an even number. The leftmost bit, also called *most significant bit*, represents the greatest value. Thus `10101010` stands for a number larger than what `01010101` stands for.

[Least Significant Bit (LSB)](https://en.wikipedia.org/wiki/Least_significant_bit "Least Significant Bit (LSB)")
: The bit in a binary number that appears rightmost and determines if the number is even (0) or odd (1).

[Most Significant Bit (MSB)](https://en.wikipedia.org/wiki/Most_significant_bit "Most Significant Bit (MSB)")
: The bit in a binary number that appears leftmost and has the greatest value.

Now, what happens if we try to add two numbers where the result exceeds the number of digits necessary to represent them individually? For example, what if we compute 255+1=256 in binary? In this case, that is, 11111111+00000001, the result is 100000000, a binary number with 9 bits rather than the 8 bits representing 255. This is not a problem if we have more than 8 bits. However, with computers everything is finite, in particular memory. Moreover, arithmetic operations are on most machines implemented for bit strings with a fixed size such as 8 bits. On such machines adding 11111111 and 00000001 results in what is called *arithmetic overflow*.

[Arithmetic Overflow](https://en.wikipedia.org/wiki/Arithmetic_overflow "Arithmetic Overflow")
: Occurs when an arithmetic operation attempts to create a numeric value that is too large to be represented within the available storage space.

How can we deal with arithmetic overflow? There are two approaches that can be combined: detection and semantics. If the occurrence of an arithmetic overflow can be detected one can discard the computation and do something else. For this purpose most processors feature a so-called *carry bit* or *carry flag* which is set if an arithmetic operation causes an overflow indicated by a *carry out of the most significant bit*. In our example, the 9-th bit in 100000000 is that carry bit.

In terms of semantics, if the result of an arithmetic overflow has a defined value, one may be able to use that value in a meaningful way. For example, a common semantics for n-bit arithmetics is to compute everything modulo 2^n^, also referred to as *wrap-around semantics* or just *wrap around*. For example, 255+1=256 modulo 2^8^=256 modulo 256=0, which is exactly what 100000000 in an 8-bit system stands for. There are applications that are correct even when such wrap-arounds occur.

[Modulo](https://en.wikipedia.org/wiki/Modulo_operation "Modulo")
: The remainder after division of one number by another, also called modulus.

Arithmetic overflow nevertheless is the cause of numerous software bugs and even costly accidents. Restricting the space available for representing something that can be arbitrarily large such as numbers has serious consequences. Integer arithmetics are always an approximation of real arithmetics. For correctness, computer applications need to be properly adapted to work for integer arithmetics, not real arithmetics.

### Signed Integers

Now, what about subtraction and negative numbers? Ideally, we would like to represent not just *positive* but also *negative* numbers just using bits with integer arithmetics on them still intact. Obviously, one bit, or more generally one digit, is enough to encode the *sign* of a number, that is, distinguish positive from negative numbers. Fortunately, however, there is an overall encoding scheme that works without changing integer arithmetics such as addition. In fact, subtraction will work by using addition, as previously discussed, with negative numbers.

So, how can we represent -85 and compute something like, say, 127-85? Again, fortunately, there is a representation of negative numbers that works for any representation with base greater than one and makes addition work like subtraction. We simply take the so-called *radix complement* to encode a negative number which only requires us to fix the number of digits that we intend to support. Subtracting a number then works by adding its complement and ignoring the overflow beyond the supported number of digits.

X> Let us compute 127-85 in the decimal system.
X>
X> The radix (ten's) complement of 85 for, say, 3-digit numbers is 10^3^-85=1000-85=915.
X>
X> Then, we exploit that 127-85 can be written as (127+(10^3^-85))-10^3^ which simplifies to (127+915)-1000=1042-1000=42 (what a coincidence). Subtracting 1000 is easily done by just ignoring the overflow of 127+915 into the fourth digit.
X>
X> So, supporting, say, 4-digit numbers works in just the same way, that is, by ignoring the fifth rather than the fourth digit: 127-85=(127+(10^4^-85))-10^4^=(127+(10000-85))-10000=(127+9915)-10000=10042-10000=42.

You may still ask how computing 1000-85 is any easier than computing 127-85 directly. Well, it is not but the radix complement of a number happens to be equal to the so-called *diminished radix complement* of that number plus one, which is in fact easier to compute than the radix complement.

X> The diminished radix (nines') complement of 85 for, say, again 3-digit numbers is (10^3^-1)-85=(1000-1)-85=999-85=914.
X>
X> The term 999-85 can easily be computed by complementing each digit of 85, again for 3-digit numbers, with respect to the diminished base 10-1=9, that is, by subtracting each digit of 85 from 9.
X>
X> So, 914 is obtained by computing: 9-0=9 (since the leftmost digit of 85 in a 3-digit system is 0), 9-8=1, and 9-5=4.
X>
X> Finally, we have that 127-85=(127+(((1000-1)-85)+1))-1000=(127+((999-85)+1))-1000=(127+(914+1))-1000=(127+915)-1000=1042-1000=42.

T> By the way, the position of the apostrophe in nines' complement is not by chance. It indicates that we mean the *diminished* radix complement with radix ten. The term nine's complement refers to the (undiminished) radix complement with radix nine. Hence the term ten's complement refers to the radix complement with radix ten.

Back to our example. What happens if we actually try to compute 85-127 instead? Let us go through that computation as well.

X> Assuming again a 3-digit system we have that: 85-127=(85+(((1000-1)-127)+1))-1000=(85+((999-127)+1))-1000=(85+(872+1))-1000=(85+873)-1000=958-1000=-42.
X>
X> Seems to work fine. However, in this case there is no overflow since 85+873=958<1000. The trick to solve this problem is simple. We just do not subtract 1000. That's it. In fact, 958 is the ten's complement of 42 in a 3-digit system and thus the correct representation of -42.

Using the ten's complement for representing negative numbers really means that the leftmost digit represents the sign. In the decimal system, an even leftmost digit indicates that we are dealing with a positive number. Conversely, an odd leftmost digit such as the 9 in 958 means that the number is actually meant to be negative. This implies that with n digits and the ten's complement for negative numbers we can represent signed integers i with -10^n^/2-1 < i < 10^n^/2. For example, in a 3-digit system we can represent signed integers i with -501 < i < 500. In other words, we can still represent 1000 numbers with 3 digits but offset by 500 into the negative numbers.

Now, how does a computer represent negative numbers? The short answer: the exact same way as in the decimal system, just in binary. In other words, a negative number may be represented in binary by its two's complement (remember binary has base 2). Just like before, the two's complement of a number is computed by taking the ones' complement of that number and adding one to it. This time, however, computing the diminished radix complement, that is, the ones' complement is particularly easy. It is done by simply inverting the bits.

X> Let us assume that we are still dealing with bytes, that is, 8 bits for each number. We are interested in computing 127-85 where both numbers are represented in binary.
X>
X> The ones' complement of 01010101, which is again binary for 85, is 10101010.
X>
X> The two's complement of 01010101 is therefore 10101010+1=10101011 and thus stands for -85.
X>
X> Computing 127-85 in binary is done by just adding 01111111, which is again binary for 127, and 10101011, and finally subtracting 100000000 which is actually done by simply ignoring the carry bit. The result is thus 01111111+10101011=100101010-100000000=00101010, which is binary for 42.
X>
X> Conversely, computing 85-127 in binary works as follows.
X>
X> The ones' complement of 01111111 is 10000000.
X>
X> The two's complement of 01111111 is therefore 10000000+1=10000001.
X>
X> To compute 85-127 we compute 01010101+10000001=11010110, which is binary for the two's complement of 42. This time we do not subtract 100000000, again by ignoring the carry bit which is not set anyway.

Using two's complement for representing negative numbers a byte can in total represent signed integer values i from -128 to 127, that is, with -2^8^/2-1 = -2^7^-1 = -129 < i < 128 = 2^7^ = 2^8^/2. Our running example fits these constraints. Moreover, the most significant bit has taken over a different role than before. It indicates if a number is positive or negative. For example, 01111111 represents a positive number whereas 10000000 stands for a negative number.

[Ones' Complement](https://en.wikipedia.org/wiki/Ones%27_complement "One's Complement")
: All bits of the number inverted, that is, 0s swapped for 1s and vice versa.

[Two's Complement](https://en.wikipedia.org/wiki/Two%27s_complement "Two's Complement")
: Given an n-bit number i with -2^n^/2-1 = -2^n-1^-1 < i < 2^n-1^ = 2^n^/2, the complement of i with respect to 2^n^, that is, 2^n^-i which is equal to the ones' complement of i plus one.

[Most Significant Bit (MSB)](https://en.wikipedia.org/wiki/Most_significant_bit "Most Significant Bit (MSB)")
: The bit in a binary number that appears leftmost and has the greatest value or, if the number represents a signed integer in two's complement, determines if the integer is positive (0) or negative (1).

T> In sum, subtraction of signed integers that are represented in binary code using two's complement for negative numbers works as follows:
T>
T> Given two signed integers x and y, x-y=x+y'+1 where y' is the ones' complement of y, ignoring the carry bit of the sum x+y'+1.
T>
T> Step by step, we compute:
T>
T> 1. the ones' complement y' of y by inverting all bits of y.
T> 2. the two's complement of y by computing y'+1.
T> 3. the sum x+y'+1 by adding x to y'+1 ignoring the carry bit of the sum.

Finally, what happened to the problem of arithmetic overflow? It is still there. Only the carry bit is now insufficient to detect it. When can an overflow actually occur? Simple. Only when adding two numbers with the same sign! The result of an overflow is a number with the opposite sign. Thus we need to distinguish two cases: adding two positive numbers resulting in a negative number and adding two negative numbers resulting in a positive number. Both cases follow wrap-around semantics similar to unsigned integers.

X> With 8 bits and two's complement the result of 01111111+00000001 which represents 127+1 is 10000000 which stands for -128.
X>
X> Similarly, the result of 10000000-00000001 which represents -128-1 is 10000000+11111111=01111111 which stands for 127.

In the first case, the MSBs of the two numbers are zero, since both represent positive numbers, and the MSB of the result is one. The second case is the exact opposite. How can we detect this? Easy. There is an overflow either if there is a carry *into* the MSB of the result but not *out* into the carry bit (wrapping two positive numbers into a negative number), or else if there is no carry *into* the MSB but *out* into the carry bit (wrapping two negative numbers into a positive number). Most processors feature an *overflow bit* or *overflow flag* that is set accordingly, that is, by a so-called *exclusive or* between the carry into and out of the MSB. An exclusive or of two bits is true if and only if the bits are different. Note, however, that just like the carry bit has no meaning when adding signed integers, the overflow bit has no meaning when adding unsigned integers.

T> There are many other ways to do integer arithmetics on computers including the handling of overflows! What you have seen here is just the arguably most prevalent choice which we therefore use in selfie as well.
T>
T> Most important for you is to be aware of the issue and know what your choice of system actually does when it comes to numbers.

## Integer Literals

Similar to character and string literals, source code written in C\* may contain integer values, also called integer literals, written in decimal notation.

[Integer Literal](https://en.wikipedia.org/wiki/Integer_literal "Integer Literal")
: An integer whose value is directly represented in source code.

The code in selfie that [reads integer literals](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L2019-L2059) is next to the code that reads identifiers. Similar to the characters of an identifier, the digits of an integer literal are first read and stored in a string. However, that string is then converted to an integer value using the `atoi` procedure.

T> Recall that identifiers may also contain digits but must start with a letter. This requirement makes it easy for the compiler to distinguish integer literals from identifiers upon reading the first character. This is in fact the reason why identifiers are usually required to start with a letter.

What about negative numbers then? Can we write integer literals in C\* that represent negative values? The answer is yes, very conveniently in fact, for example, by writing `-85` which obviously represents the value -85. However, this notation is only an abbreviation for `0 - 85` which obviously represents the same value. When reading integer literals such as `-85` the starc compiler does in fact generate code that [subtracts](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L3058) the positive value 85 from 0 to obtain the negative value -85.

## Symbols

Among all language elements of C\* we have seen identifiers and keywords as well as character, string, and integer literals. The only missing elements are operator symbols and symbols for structuring source code. The [complete list of C\* symbols](http://github.com/cksystemsteaching/selfie/blob/e7ee49fb71eae1de5efc24435ab2b3ad4764c803/grammar.md#L13-L33), also called *tokens*, is surprisingly small. Our ["Hello World!" Program](http://github.com/cksystemsteaching/selfie/blob/a7fcb70c1683802c644f0cd1af3892696f68f4bd/manuscript/code/hello-world.c) does not contain all possible symbols but at least one from each category, that is, keywords, identifiers, literals, operator symbols, and symbols for structuring source code.

## Machine Words

So, before continuing let us point out that character, string, and integer literals are the only way to describe data in C\* programs. All other language elements of C\* including keywords and identifiers are there to describe code and manage memory! We already know that characters are encoded in bytes and strings are stored contiguously in byte-addressed memory. What about integers then? To answer that question we need to take a closer look at how a computer handles data.

First of all, in addition to memory, most computers contain at least one *processor* or *central processing unit* (CPU) connected to memory and other hardware. While memory stores information the CPU performs actual computation with that information.

[Central Processing Unit (CPU)](https://en.wikipedia.org/wiki/Central_processing_unit "Central Processing Unit (CPU)")
: The electronic circuitry within a computer that carries out the instructions of a computer program by performing the basic arithmetic, logical, control and input/output (I/O) operations specified by the instructions.

Instead of operating directly on memory, most CPUs load data from memory into *registers*, then perform some computation with that data, and finally store the result back in memory. The reason is performance. The registers of a CPU are by far the fastest storage available in a computer.

[Register](https://en.wikipedia.org/wiki/Processor_register "Register")
: A quickly accessible location available to a digital processor's central processing unit (CPU). Registers usually consist of a small amount of fast storage, although some registers have specific hardware functions. Registers are typically addressed by mechanisms other than main memory.

Most registers of a CPU have the same size, that is, accommodate the same number of bits. Usually, data goes back and forth between memory and registers in chunks of that size called *machine words* or just *words*.

[Word](https://en.wikipedia.org/wiki/Word_(computer_architecture) "Word")
: The natural unit of data used by a particular processor design. A word is a fixed-sized piece of data handled as a unit by the instruction set or the hardware of the processor. The number of bits in a word (the word size, word width, or word length) is an important characteristic of any specific processor design or computer architecture.

The processor that the mipster emulator implements has a word size of 32 bits. In fact, virtually everything on that machine happens at the level of words. Loading data from memory and storing it back, arithmetic and logical operations among registers, and even fetching code from memory for execution, as we see below. The reason is again performance. Involving 32 bits in parallel in all operations is obviously faster than working with bits individually. You probably know that there are machines with even larger word sizes for even greater speed such as 64-bit machines, for example. We stick to 32-bit words though since it makes things easier for two reasons.

The first reason is that the size of an integer in C\* is also 32 bits encoding the sign in the MSB and the value in the remaining 31 LSBs in two's complement. This means that a single mipster register can hold exactly one C\* integer value. Beautiful!

T> A signed integer in C\* can in total represent signed integer values i from -2147483648 to 2147483647 since -2^32^/2-1 = -2^31^-1 = -2147483649 < i < 2147483648 = 2^31^ = 2^32^/2. In `selfie.c` the largest positive value is called [`INT_MAX`](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L227) while the smallest negative value is called [`INT_MIN`](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L228).

We prepared another simple program called [`negative.c`](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/manuscript/code/negative.c) that prints the numerical value represented by `-85`, and of `INT_MAX` and `INT_MIN` for reference, in all possible ways supported by selfie as follows:

{line-numbers=off}
```
> ./selfie -c manuscript/code/negative.c selfie.c -m 1
./selfie: this is selfie's starc compiling manuscript/code/negative.c
...
./selfie: this is selfie's mipster executing manuscript/code/negative.c with 1MB of physical memory
    -85 in decimal:     -85
    -85 in hexadecimal: 0xFFFFFFAB
    -85 in octal:       0037777777653
    -85 in binary:      11111111111111111111111110101011
INT_MAX in decimal:     2147483647
INT_MAX in hexadecimal: 0x7FFFFFFF
INT_MAX in octal:       0017777777777
INT_MAX in binary:      01111111111111111111111111111111
INT_MIN in decimal:     -2147483648
INT_MIN in hexadecimal: 0x80000000
INT_MIN in octal:       0020000000000
INT_MIN in binary:      10000000000000000000000000000000
manuscript/code/negative.c: exiting with exit code 0 and 0.00MB of mallocated memory
./selfie: this is selfie's mipster terminating manuscript/code/negative.c with exit code 0 and 0.12MB of mapped memory
...
```

The second reason for using 32-bit words is that memory addresses in mipster and ultimately in C\* are then 32 bits as well. This means in particular that the content of a register can also be seen as a memory address and not just an integer value. However, there is one important detail. On a mipster machine, memory is not only byte-addressed but also *word-aligned* for access. This means that words can only be accessed in memory at addresses that are multiples of four, the word size in bytes.

T> The byte-addressed and word-aligned memory in mipster can only be accessed in whole words at addresses 0, 4, 8, 12, and so on. The word at address 0, for example, then contains the four bytes at addresses 0, 1, 2, and 3.

An interesting question is which bits in a word are used to represent which bytes in memory. The two standard choices are determined by the *endianness* of a processor.

[Endianness](https://en.wikipedia.org/wiki/Endianness "Endianness")
: The order of the bytes that compose a digital word in computer memory. Words may be represented in big-endian or little-endian format. When storing a word in big-endian format the most significant byte, which is the byte containing the most significant bit, is stored first and the following bytes are stored in decreasing significance order with the least significant byte, which is the byte containing the least significant bit, thus being stored at last place. Little-endian format reverses the order of the sequence and stores the least significant byte at the first location with the most significant byte being stored last.

Interestingly, the endianness of a mipster machine is irrelevant since there is no way to access data in sizes other than word size directly in memory at addresses that are not multiples of the word size. In general, however, this is not true. Most processors allow accessing memory such that endianness does make a difference. We have deliberately ruled that out in selfie to make things simpler. Another simplification in selfie is the absence of any native support of *bitwise operations*.

[Bitwise Operation](https://en.wikipedia.org/wiki/Bitwise_operation "Bitwise Operation")
: Operates on one or more bit patterns or binary numerals at the level of their individual bits. It is a fast, simple action directly supported by the processor, and is used to manipulate values for comparisons and calculations.

Why would we want support of that anyway? Well, how do we read and modify individual bits in registers and eventually memory if everything happens at word granularity? This is where bitwise operations come in. There are typically bitwise logical operations such as bitwise *NOT*, *AND*, and *OR* operations as well as bitwise shift operations such as *left shift* and *logical right shift* operations.

Bitwise operations have in common that they treat integers and words purely as sequences of bits. For example, a left shift operation shifts the bits in an integer or word to the left by a given amount of bits while shifting in zeros into the LSB. The logical right shift operation does the exact opposite.

We prepared another simple program called [`bitwise.c`](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/manuscript/code/bitwise.c) that prints the numerical value 3 in binary and decimal notation and then shifts it repeatedly by six bits to the left until it reaches 0. The program also performs a bitwise OR operation of all intermediate values and prints the result. The program then reverses direction and shifts the most recent value before reaching 0 repeatedly by six bits to the right until it reaches 0 again:

{line-numbers=off}
```
> ./selfie -c manuscript/code/bitwise.c selfie.c -m 1
./selfie: this is selfie's starc compiling manuscript/code/bitwise.c
...
./selfie: this is selfie's mipster executing manuscript/code/bitwise.c with 1MB of physical memory
00000000000000000000000000000011 in binary = 3 in decimal
00000000000000000000000011000000 in binary = 192 in decimal
00000000000000000011000000000000 in binary = 12288 in decimal
00000000000011000000000000000000 in binary = 786432 in decimal
00000011000000000000000000000000 in binary = 50331648 in decimal
11000000000000000000000000000000 in binary = -1073741824 in decimal
11000011000011000011000011000011 in binary = -1022611261 in decimal
11000000000000000000000000000000 in binary = -1073741824 in decimal
00000011000000000000000000000000 in binary = 50331648 in decimal
00000000000011000000000000000000 in binary = 786432 in decimal
00000000000000000011000000000000 in binary = 12288 in decimal
00000000000000000000000011000000 in binary = 192 in decimal
00000000000000000000000000000011 in binary = 3 in decimal
manuscript/code/bitwise.c: exiting with exit code 0 and 0.00MB of mallocated memory
...
```

But how did we do this if there is no native support of bitwise operations? Well, we use integer arithmetics and wrap-around semantics to provide bitwise OR, [left shift](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L1297-L1309), and [logical right shift](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L1311-L1333) operations in selfie.

T> Multiplying a signed integer with 2^n^ shifts the bits representing the integer value to the left by n bits even if the value is negative provided two's complement and wrap-around semantics upon arithmetic overflow is used.

In the `bitwise.c` program we shift the bits representing the integer value 3 to the left by six bits by multiplying the value repeatedly with 64=2^6^ until the value wraps around and becomes negative.

T> Adding two signed integers corresponds to a bitwise OR operation if the bits at the same index in both integers are never both 1 avoiding any carry bit to be set.

The `bitwise.c` program demonstrates that by performing a bitwise OR operation on all intermediate values through simple integer addition.

T> Dividing a signed integer with 2^n^ shifts the bits representing the integer value to the right by n bits if the value is positive. If it is negative, [the sign bit can be reset before performing the division and then restored n bits to the right](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L1321-L1326).

The `bitwise.c` program applies that method to shift the bits to the right repeatedly by six bits back to their original position.

Interestingly, the bitwise OR, left shift, and logical right shift operations presented here are sufficient to implement all of selfie!

Before moving on let us quickly revisit how characters and strings are stored in memory. In selfie characters are represented by 8 bits. A 32-bit word may therefore hold up to four characters. This is in fact done to store the characters of strings in memory. A character literal, however, is stored in the eight LSBs of a word leaving the remaining bits blank.

X> The string literal `"Hello World!"` is stored in four 32-bit words located contiguously in memory accommodating the substrings `"Hell"`, `"o Wo"`, and `"rld!"` as well as the value 0 in the fourth word to terminate the string. The ASCII code of the letter `H` is stored in the eight LSBs of the first word, the ASCII code of the following letter `e` in the eight bits directly to the left of the eight LSBs, and so on.

Try the following command to see that our "Hello World!" program does actually print the characters in chunks of four by printing the three words containing the characters directly on the console. The command creates three mipsters on top of each other slowing down the execution of the program to the extent that the behavior is really visible:

{line-numbers=off}
```
> ./selfie -c manuscript/code/hello-world.c -o hello-world.m -c selfie.c -o selfie.m -m 1 -l selfie.m -m 1 -l hello-world.m -m 1
...
```

This is nice but how do we then access individual characters of a string? Simple, by using our bitwise operations, of course! Selfie implements [loading](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L1335-L1345) and [storing](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L1347-L1360) characters of strings in memory accordingly.

So, on the machine everything related to data happens at the granularity of words. Interesting. What is even more fascinating is that even memory addresses and all machine code is handled at that granularity as well.

## Memory Addresses

The address of a byte or in fact a word in memory is obviously a positive number. On a mipster machine and many others as well, memory addresses are also represented by words. Thus the word size of such machines determines how many memory addresses can be distinguished and, as a consequence, how much memory can be accessed. A mipster machine, for example, supports up to 64MB of byte-addressed and word-aligned memory. Addressing that memory thus requires the 26 LSBs out of the 32 bits of a word. The remaining 6 MSBs are unused.

X> The address of where the string literal `"Hello World!"` is stored in memory is an example of such a memory address represented by a word.

Let us reflect on that for a moment. So, on a mipster machine, the 32 bits of a word can be used to encode characters, signed integers, and even memory addresses! That's right and this is not all. Even machine instructions are represented by words which is our next topic.

## Instructions

The code of a mipster machine is represented by a sequence of machine words where each word encodes a machine instruction. It is that easy and actually true for many other processors as well. The exact specification of the encoding as well as the meaning of each instruction is provided by the *instruction set architecture* or *ISA* for short.

[Instruction Set Architecture (ISA)](https://en.wikipedia.org/wiki/Instruction_set "Instruction Set Architecture (ISA)")
: The part of the computer architecture related to programming, including the native data types, instructions, registers, addressing modes, memory architecture, interrupt and exception handling, and external I/O. An ISA includes a specification of the set of opcodes (machine language), and the native commands implemented by a particular processor. An instruction set is the interface between a computer's software and its hardware, and thereby enables the independent development of these two computing realms.

Let us have another look at the first few lines of the assembly code in `selfie.s` presented in the previous chapter:

{line-numbers=off}
```
0x0(~1): 0x24080007: addiu $t0,$zero,7
0x4(~1): 0x24094000: addiu $t1,$zero,16384
0x8(~1): 0x01090019: multu $t0,$t1
0xC(~1): 0x00004012: mflo $t0
0x10(~1): 0x00000000: nop
0x14(~1): 0x00000000: nop
0x18(~1): 0x25081B38: addiu $t0,$t0,6968
0x1C(~1): 0x251C0000: addiu $gp,$t0,0
0x20(~1): 0x24080FFF: addiu $t0,$zero,4095
0x24(~1): 0x24094000: addiu $t1,$zero,16384
0x28(~1): 0x01090019: multu $t0,$t1
0x2C(~1): 0x00004012: mflo $t0
0x30(~1): 0x00000000: nop
0x34(~1): 0x00000000: nop
0x38(~1): 0x25083FFC: addiu $t0,$t0,16380
0x3C(~1): 0x8D1D0000: lw $sp,0($t0)
0x40(~1): 0x0C007029: jal 0x7029[0x1C0A4]
0x44(~1): 0x00000000: nop
```

Each line represents one machine instruction. The first line, for example, reads like this. The hexadecimal number `0x0` is the word-aligned memory address of the instruction in memory. The expression `(~1)` is the approximate line number of the source code, in this case `selfie.c`, that was compiled to this instruction. The 32-bit word `0x24080007` is in fact the binary encoded version of the instruction itself. Finally, `addiu $t0,$zero,7` is the human-readable assembly version of the instruction. This means in particular that `0x24080007` and `addiu $t0,$zero,7` are semantically equivalent. The 32-bit word `0x24080007` in binary stored at address `0x0` in memory is thus the only thing that the machine needs, the rest is for us to make it readable.

The machine code in `selfie.m` presented in the previous chapter contains just that binary code, that is, `0x24080007` followed by `0x24094000` from the second line in `selfie.s` and so on. To prepare the machine for executing that code we only need to load `selfie.m` into memory starting at address `0x0` and then tell the machine to execute the code. How this is done is part of the next chapter.

So, how do we know that `0x24080007` represents `addiu $t0,$zero,7`? This is specified precisely by the ISA of the widely used MIPS processor family.

[MIPS](https://en.wikipedia.org/wiki/MIPS_instruction_set "MIPS")
: A reduced instruction set computer (RISC) instruction set architecture (ISA) developed by MIPS Technologies (formerly MIPS Computer Systems, Inc.). The early MIPS architectures were 32-bit, with 64-bit versions added later. Multiple revisions of the MIPS instruction set exist, including MIPS I, MIPS II, MIPS III, MIPS IV, MIPS V, MIPS32, and MIPS64. The current revisions are MIPS32 (for 32-bit implementations) and MIPS64 (for 64-bit implementations).

The mipster emulator implements a strict subset of the instructions of the MIPS32 processor which we call *MIPSter*. In fact, mipster only implements [17](http://github.com/cksystemsteaching/selfie/blob/4d7d38e6bda22f02ab34abbae5040d17e8856bce/selfie.c#L705-L765) out of the more than 40 instructions of MIPS32. The starc compiler generates MIPSter code that runs on mipster and thus, at least in principle, also on a real MIPS32 processor. The converse is not true, of course. MIPS32 code does in general not run on mipster but that is not a problem here.

Let us go back to the above example. The `addiu` string in `addiu $t0,$zero,7` is an assembly mnemonic of the *operation code* or *opcode*, for short, that identifies the operation to be performed while the remaining `$t0,$zero,7` are three operands of that operation.

[Opcode](https://en.wikipedia.org/wiki/Opcode "Opcode")
: The portion of a machine language instruction that specifies the operation to be performed. Beside the opcode itself, most instructions also specify the data they will process, in the form of operands.

In our example, `addiu` instructs the processor to add the value of the integer `7` to the value stored in register `$zero` (which is always 0) and store the result in register `$t0` (which will thus contain the value 7 after executing the instruction).

A MIPS processor has 32 32-bit registers that can be used for this purpose. They are numbered from 0 to 31. The register `$zero` is obviously register 0 while the register `$t0`, less obviously, happens to be register 8. The only missing piece of information is that `addiu` is represented by the opcode 9. Now, how do we get from there to `0x24080007`?

We take the opcode 9 (`001001`), register 0 (`00000`), register 8 (`01000`), and value 7 (`0000000000000111`) and put them together in binary as follows:

`001001 00000 01000 0000000000000111`

If you merge that into a 32-bit word you get `0x24080007`. The MIPS32 ISA specifies that the six MSBs encode the opcode 9, the next five bits encode the second (!) operand register 0, the following five bits encode the first (!) operand register 8, and lastly the remaining sixteen LSBs encode the third operand value 7, in 16-bit two's complement in fact so it could even be a negative value. The fact that the third operand is treated by `addiu` as an integer value rather than, say, a number identifying a register is called *immediate* addressing hence the `i` in `addiu`. Immediate addressing is one of various so-called *addressing modes*. The `u` in `addiu` stands for unsigned which is misleading. Its actual meaning is that arithmetic overflows with `addiu` are ignored while wrap-around semantics apply.

[Addressing Mode](https://en.wikipedia.org/wiki/Addressing_mode)
: An aspect of the instruction set architecture in most central processing unit (CPU) designs. The various addressing modes that are defined in a given instruction set architecture define how machine language instructions in that architecture identify the operand(s) of each instruction.

But why does the ISA provision five bits for the first and second operand? Because five bits allow us to address exactly the 2^5^=32 different registers of the machine. The six bits for the opcode obviously allow us to distinguish up to 2^6^=64 different opcodes but we actually do not need that many. Now, think about the range of values that can be encoded in two's complement in the sixteen bits for the third operand! This is the range of values that we can get into a register such as `$t0$` with a single `addiu` instruction. In other words, we can use that instruction to initialize registers. Cool!

Note that the value in register `$zero` is assumed to be 0 at all times. This is in fact needed for initializing registers using the `addiu` instruction. There exists MIPS assembly in which such intention is made explicit by using *pseudo instructions*. Here, the pseudo instruction `movi $t0,7`, for example, could be used instead but would anyhow just be a short version of `addiu $t0,$zero,7`. The remaining sixteen instructions of MIPSter are just as simple, we introduce them on the fly as needed.

So, how does the starc compiler generate such code? It uses bitwise operations, of course, that is, bitwise OR and left shifting in particular. There are in total three different formats in MIPS32 depending on the opcode. The actual source code in `selfie.c` for [encoding machine instructions](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L4139-L4189) is nevertheless pretty straightforward.

An interesting feature of the implementation of selfie in a single file is that the source code for [decoding machine instructions](http://github.com/cksystemsteaching/selfie/blob/d5b7b78fa8db215544159718cb41a7406d39da78/selfie.c#L4191-L4290), which is used by the mipster emulator and selfie's disassembler, is right after the code for encoding instructions. Decoding machine code performs the exact inverse to encoding machine code extracting the opcode and operands that were originally encoded. It is done by a combination of left and logical right shifting. See for yourself how this works in the code! It may look technical but is actually very simple.

## Summary

In this chapter we have seen how characters, strings, identifiers, integers, and even machine instructions are encoded and decoded, and how all that allows us to represent source and machine code using just bits. We even understand now some of the output of the starc compiler when compiling our "Hello World!" program, for example:

{line-numbers=off}
```
> ./selfie -c manuscript/code/hello-world.c -m 1
./selfie: this is selfie's starc compiling manuscript/code/hello-world.c
...
./selfie: 729 characters read in 22 lines and 11 comments
./selfie: with 80(10.97%) characters in 39 actual symbols
./selfie: 1 global variables, 1 procedures, 1 string literals
./selfie: 1 calls, 2 assignments, 1 while, 0 if, 0 return
./selfie: 600 bytes generated with 144 instructions and 24 bytes of data
...
```

The compiler counts `characters`, `lines`, `comments`, `whitespace`, and `symbols` in source code, and `instructions` and `bytes of data` in the generated machine code. The information about `global variables`, `procedures`, `calls`, `assignments`, `while`, `if`, and `return` will become clear in the next chapter.

But there is still something missing here. Why is all of this encoded the way it is and not some other way? There are two important reasons:

1. Time: Depending on the encoding, data can be processed faster or slower, even fundamentally faster or slower in the sense that some encoding may not allow reasonably fast processing at all.

    But why do we not always pick the encoding that supports the fastest possible processing? We could do that but it could make the actual encoding process slow and in some cases even fundamentally slow, and because:

2. Space: The amount of bits needed to encode data can vary significantly and even fundamentally depending on the encoding scheme.

X> Take unary versus binary encoding of numbers, for example. Unary encoding requires exponentially more space than binary encoding. Fortunately, even though binary encoding is so much more compact than unary, arithmetics on binary numbers can still be done very fast. This is why binary encoding for numbers is actually a good choice.
X>
X> The encoding of strings is another interesting example. Squeezing four characters rather than just, say, one character into a word saves four times the space in our case but makes accessing strings slower. However, access time is not fundamentally slower in the sense that accessing a single character is only slower by some constant amount of time due to the involved bitwise operations.

Machine instructions are also encoded such that code size is compact while decoding them, which is ultimately done in hardware by the machine, is still fast. This is, of course, extremely important since every single instruction a processor executes needs to be decoded into opcode and operands before execution.

In computer science the trade off between time and space shows up in all kinds of situations. Encoding information is just one example. The important lesson here is to be aware of the trade off and understand that [there is no such thing as a free lunch!](https://en.wikipedia.org/wiki/There_ain%27t_no_such_thing_as_a_free_lunch)
