# 2. Semantics {#semantics}

When it comes to computers a *bit* is the first thing we should know about and understand. The only thing that computers do is handle enormous amounts of bits, nothing else.

[Bit](https://en.wikipedia.org/wiki/Bit "Bit")
: The basic unit of information in computing and digital communications. A bit can have only one of two values which are most commonly represented as either a 0 or 1. The term bit is a portmanteau of binary digit.

There are two fundamental reasons why computers use bits and nothing else. The first reason is that the two values of a bit can readily be distinguished by electronic circuits using different levels of voltage, say, low voltage for 0 and high voltage for 1. Distinguishing more values is possible and would be exciting to see but has largely not yet happened for technological reasons. The second reason is that whatever you can say using any number of values per digit greater than two you can also say using two values with only an insignificant difference in the number of digits you need to say the same thing. More on that in the [next chapter](#encoding).

Selfie is a program written in the programming language C. Before we try to understand what that means we first look at selfie as the machine sees it. Selfie is implemented in a single file called `selfie.c` which currently consists of around one hundred and fifty thousand characters.

[Character](https://en.wikipedia.org/wiki/Character_(computing) "Character")
: A unit of information that roughly corresponds to a grapheme, grapheme-like unit, or symbol, such as in an alphabet or syllabary in the written form of a natural language. Examples of characters include *letters*, numerical *digits*, common *punctuation marks* (such as "." or "-"), and *whitespace*. The concept also includes *control characters*, which do not correspond to symbols in a particular natural language, but rather to other bits of information used to process text in one or more languages. Examples of control characters include *carriage return*, *line feed*, and *tab*, as well as instructions to printers or other devices that display or otherwise process text.

You may see for yourself by using the `less` command:

{line-numbers=off}
```
> less selfie.c
```

For example, the first three lines of `selfie.c` are:

{line-numbers=off}
```
// Copyright (c) 2015-2016, the Selfie Project authors. All rights reserved.
// Please see the AUTHORS file for details. Use of this source code is
// governed by a BSD license that can be found in the LICENSE file.
```

What you see here are so-called ASCII characters representing `selfie.c`. Since a computer can only handle bits, each character is actually encoded and stored in a number of bits which in this case is done according to the ASCII standard.

[American Standard Code for Information Interchange (ASCII)](https://en.wikipedia.org/wiki/ASCII "American Standard Code for Information Interchange (ASCII)")
: 7-bit encoding scheme for 128 characters: numbers 0 to 9, lowercase letters a to z, uppercase letters A to Z, basic punctuation symbols, control codes that originated with Teletype machines, and a space.

On machine level, each ASCII character is thus represented by seven bits. What we see when we invoke `less` is merely a human-readable version of these bits. However, the ASCII characters in `selfie.c` are actually encoded according to the UTF-8 standard which uses eight rather than seven bits per character.

[UTF-8](https://en.wikipedia.org/wiki/UTF-8 "UTF-8")
: (Universal Character Set Transformation Format - 8-bit) A character encoding capable of encoding all possible characters (called code points) in Unicode. The encoding is variable-length and uses 8-bit code units. It is designed for backward compatibility with ASCII.

Backward compatibility means here that the UTF-8 encoding of a given character is the ASCII encoding of that character when ignoring the eighth bit. More on encoding can be found in the [next chapter](#encoding).

To get a better feel of the size of `selfie.c` run in a terminal the `wc` command which counts characters, words, and lines in a file:

{line-numbers=off}
```
> wc selfie.c
    6443   18660  158772 selfie.c
```

The output means that `selfie.c` at the time of invoking the command consisted of 158,772 characters in 18,660 words and 6,443 lines. According to `wc` a *word* is a so-called string of characters delimited by whitespace characters. A *line* is a string of characters delimited by a so-called newline character such as carriage return or line feed.

[String](https://en.wikipedia.org/wiki/String_(computer_science) "String")
: A finite sequence of characters taken from some finite alphabet.

The alphabet is here ASCII characters UTF-8-encoded in eight bits. Since a unit of eight bits is very common in computer systems there is a well-known term for that unit called a byte.

[Byte](https://en.wikipedia.org/wiki/Byte "Byte")
: A unit of digital information in computing and telecommunications that most commonly consists of eight bits.

We can easily verify that `selfie.c` consists of the same number of bytes than characters by using the command `wc -c` which reports the number of bytes in a file:

{line-numbers=off}
```
> wc -c selfie.c
    158772 selfie.c
```

In other words, for a computer `selfie.c` is in fact a sequence of bits, sometimes called *bit string*, with eight times 158,772 bits, that is, 1,270,176 bits.