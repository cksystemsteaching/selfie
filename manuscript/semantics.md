# 2. Semantics {#semantics}

When it comes to computers a *bit* is the first thing we may want to know about and understand. The only thing that computers really do on the level of the machine is handle enormous amounts of bits, nothing else.

[Bit](https://en.wikipedia.org/wiki/Bit "Bit")
: The basic unit of information in computing and digital communications. A bit can have only one of two values which are most commonly represented as either a 0 or 1. The term bit is a portmanteau of binary digit.

There are two fundamental reasons why computers use bits and nothing else. The first reason is that the two values of a bit can readily be distinguished by electronic circuits using different levels of voltage, say, low voltage for 0 and high voltage for 1. Distinguishing more values is possible and would be exciting to see but has largely not yet happened for technological reasons. The second reason is that whatever you can say using any number of values per digit greater than two you can also say using two values with only an insignificant difference in the number of digits you need to say the same thing. More on that in the [next chapter](#encoding).

Selfie is a program written in some programming language. We eventually explain what that means but before doing so we first look at selfie as we and the machine see it. Selfie is fully contained in a single file called `selfie.c` which currently consists of around one hundred and fifty thousand characters.

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

What you see here is called source code where the first few lines are in fact comments that will be ignored by the machine.

[Source Code](https://en.wikipedia.org/wiki/Source_code "Source Code")
: Any collection of computer instructions (possibly with comments) written using some human-readable computer language, usually as text.

The characters of source code like `selfie.c` are usually encoded in bits according to the ASCII standard. Remember, since computers can only handle bits everything needs to be encoded in bits.

[American Standard Code for Information Interchange (ASCII)](https://en.wikipedia.org/wiki/ASCII "American Standard Code for Information Interchange (ASCII)")
: 7-bit encoding scheme for 128 characters: numbers 0 to 9, lowercase letters a to z, uppercase letters A to Z, basic punctuation symbols, control codes that originated with Teletype machines, and a space.

On machine level, each character is thus represented by seven bits. What we see when we invoke `less` is merely a human-readable version of these bits. To get a better feel of the size of `selfie.c` run in a terminal the command `wc -m selfie.c` which counts the characters in `selfie.c`:

{line-numbers=off}
```
> wc -m selfie.c
  158914 selfie.c
```

The output means that `selfie.c` at the time of invoking the command consisted of 158,914 characters. By the way, the `-m` part of the command is called an option that directs, in this case, `wc` to output the number of characters. However, we should mention that the characters in `selfie.c` are actually encoded according to the newer UTF-8 standard which uses eight rather than seven bits per character.

[UTF-8](https://en.wikipedia.org/wiki/UTF-8 "UTF-8")
: (Universal Character Set Transformation Format - 8-bit) A character encoding capable of encoding all possible characters (called code points) in Unicode. The encoding is variable-length and uses 8-bit code units. It is designed for backward compatibility with ASCII.

When it comes to selfie we nevertheless speak of ASCII-encoded characters because of that backward compatibility. Here this means that the UTF-8 encoding of a given character is exactly the ASCII encoding of that character when simply ignoring the eighth bit. More on encoding characters can be found in the [next chapter](#encoding).

Since a unit of eight bits is very common in computer systems there is a well-known term for that unit called a byte.

[Byte](https://en.wikipedia.org/wiki/Byte "Byte")
: A unit of digital information in computing and telecommunications that most commonly consists of eight bits.

We can easily verify that `selfie.c` consists of the same number of bytes than characters by using the command `wc -c selfie.c` with the `-c` option which directs `wc` to report the number of bytes in `selfie.c`:

{line-numbers=off}
```
> wc -c selfie.c
  158914 selfie.c
```

In other words, for a computer `selfie.c` is in fact a sequence of eight times 158,914 bits, that is, 1,271,312 bits. The key question addressed by this book is where the meaning of these bits comes from.

Q> Where does semantics come from and how do we create it on a machine?

The source code of selfie is ultimately a sequence of bits. How do they get their meaning? Bits, as is, have no meaning, they are just bits. Characters, by the way, are no different. Characters, as is, have no meaning either, they are just symbols, and can anyway be encoded in bits. Meaning is created by the person reading or writing them. But when it comes to a machine the meaning of bits and thus characters or any kind of symbol has to be created mechanically. The key insight is that the meaning of bits is in the process of changing bits, not in the bits themselves.

X> Let us take two numbers, say 7 and [42](https://en.wikipedia.org/wiki/Phrases_from_The_Hitchhiker%27s_Guide_to_the_Galaxy "42"), and then add 7 to 42. What we obviously get is 49 transforming 7 and 42 into 49.

The process of adding 7 to 42, according to the rules of elementary arithmetic, makes 7 and 42 represent numbers rather than something else. But if we just look at 7 and 42 they could mean anything. In this example, elementary arithmetic provides meaning, namely the semantics of natural numbers. This is why it is so important to learn elementary arithmetic in school. It tells us what numbers are, not just how to add, subtract, multiply, and divide them!

[Elementary Arithmetic](https://en.wikipedia.org/wiki/Elementary_arithmetic "Elementary Arithmetic")
: The simplified portion of arithmetic that includes the operations of addition, subtraction, multiplication, and division.

Virtually all modern computers include circuitry for performing elementary arithmetic but they do so with binary rather than decimal numbers since computers only handle bits. Our example of 7 and 42 in binary is just as simple.

X> The number 7 in binary is 111. The number 42 in binary is 101010. Adding 111 to 101010 works in exactly the same way than adding 7 to 42. The result is 110001 which is binary for 49.

Again, adding 111 to 101010 makes 111 and 101010 represent numbers while they could otherwise represent anything. More on encoding numbers in binary can be found in the [next chapter](#encoding).

[Binary Number](https://en.wikipedia.org/wiki/Binary_number "Binary Number")
: A number expressed in the binary numeral system or base-2 numeral system which represents numeric values using two different symbols: typically 0 (zero) and 1 (one).

It may be hard to believe but knowing elementary arithmetic is enough to understand this book. The source code of selfie, that is, the around one hundred and fifty thousand characters of `selfie.c` represented by around one million bits get their meaning in pretty much the same way than having bits represent numbers: by changing them. The only difference is that the process of change is a bit more involved than elementary arithmetic.

T> The semantics of bits on a machine is created by changing these bits!

Let us have a closer look at how this works with selfie. Try the `make` command:

{line-numbers=off}
```
> make
  cc -w -m32 -D'main(a,b)=main(a,char**argv)' selfie.c -o selfie
```

The `make` command invokes the `cc` command which *compiles* the file `selfie.c` into a file called `selfie` (without the `.c` extension) as directed by the `-o` option, ignoring the other options for clarity. In other words, the sequence of bits representing `selfie.c` is changed into another sequence of bits representing `selfie`. The difference between the two sequences is that the former represents source code whereas the latter represents machine code.

[Machine Code](https://en.wikipedia.org/wiki/Machine_code "Machine Code")
: A sequence of instructions executed directly by a computer's central processing unit (CPU).

The key idea is that both sequences are supposed to have the same semantics. However, `selfie` is executable by a machine whereas `selfie.c` is not, at least not purposefully, yet `selfie.c` is human-readable and writable in particular. The process of changing `selfie.c` into `selfie` is called compilation which is done by a compiler such as the above cc compiler.

[Compiler](https://en.wikipedia.org/wiki/Compiler "Compiler")
: A computer program that transforms source code written in a programming language (the source language) into another computer language (the target language), with the latter often having a binary form known as object or machine code. The most common reason for converting source code is to create an executable program.

This means that we now have a version of selfie that we can run on our machine! Let us try and run selfie using the command `./selfie`:

{line-numbers=off}
```
> ./selfie
  ./selfie: usage: selfie { -c source | -o binary | -s assembly | -l binary } [ -m size ... | -d size ... | -y size ... ]
```

Selfie requires using at least one option to do anything useful and therefore responds with its usage pattern and then terminates without doing anything else. To do something useful, let us try the first `-c` option on, well, `selfie.c` itself:

{line-numbers=off}
```
> ./selfie -c selfie.c
  ./selfie: this is selfie's starc compiling selfie.c
```

Now, things are taking off. Selfie includes a compiler, just like the cc compiler, that we call starc and invoke with the `-c` option. The starc compiler is capable of compiling all of selfie including itself. By now you realize why selfie is called selfie but the story continues.

After compiling `selfie.c` starc only stores the machine code internally but does not write it to a file. To do that we need to use the `-o` option:

{line-numbers=off}
```
> ./selfie -c selfie.c -o selfie.m
  ./selfie: this is selfie's starc compiling selfie.c
  ./selfie: writing code into output file selfie.m
```

This produces a file called `selfie.m` that contains machine code compiled from `selfie.c` using the starc compiler in `selfie` rather than the cc compiler. This means that by now we have three different sequences of bits in `selfie.c`, `selfie`, and `selfie.m` that are all supposed to have the same semantics. The only difference between `selfie` and `selfie.m` is that `selfie` is executable on our computer whereas `selfie.m` is executable on a computer that we do not have. This is not the end of the story though.

The reason why starc targets a different machine than cc is because it makes starc a lot simpler. But how do we execute `selfie.m`? Well, selfie not only includes the starc compiler, it also includes mipster, which is an emulator of the computer that can execute `selfie.m` and any other machine code generated by starc. That computer is so simple that everyone can understand it in a short time even though it corresponds to parts of a real machine.

[Emulator](https://en.wikipedia.org/wiki/Emulator "Emulator")
: Software that enables one computer system (called the host) to behave like another computer system (called the guest).

We execute `selfie.m` by first loading it using the `-l` option and then running it by invoking mipster using the `-m` option:

{line-numbers=off}
```
> ./selfie -l selfie.m -m 1
  ./selfie: loading code from input file selfie.m
  ./selfie: this is selfie's mipster executing selfie.m with 1MB of memory
  selfie.m: usage: selfie { -c source | -o binary | -s assembly | -l binary } [ -m size ... | -d size ... | -y size ... ]
  selfie.m: exiting with exit code 0
  ./selfie: this is selfie's mipster terminating selfie.m
  ./selfie: profile: total,max(ratio%)@addr,2max(ratio%)@addr,3max(ratio%)@addr
  ./selfie: calls: 1474,486(33.00%)@0x22A0,242(16.42%)@0x2300,121(8.21%)@0x88
  ./selfie: loops: 150,120(80.00%)@0x3914,30(20.00%)@0x1DC,0(0.00%)
  ./selfie: loads: 10371,486(4.68%)@0x22B4,242(2.33%)@0x2314,122(1.17%)@0x3914
  ./selfie: stores: 6261,486(7.76%)@0x22A4,242(3.86%)@0x2304,122(1.94%)@0x391C
```

After loading `selfie.m` the `-m 1` option directs mipster to emulate a computer with 1MB of memory for executing `selfie.m`. Since `selfie.m` is invoked without any options, which could appear after the `-m 1` option, it responds just like before with its usage pattern and then terminates. Then mipster terminates and outputs a summary of its builtin performance profiler.

[Profiling](https://en.wikipedia.org/wiki/Profiling_(computer_programming) "Profiling")
: A form of dynamic program analysis that measures, for example, the space (memory) or time complexity of a program, the usage of particular instructions, or the frequency and duration of function calls. Most commonly, profiling information serves to aid program optimization.

We later use profiling to explain performance-related issues of selfie. But now, let us try something cool. Since mipster is part of selfie we can even have mipster execute machine code for selfie generated by starc without writing the code into a file:

{line-numbers=off}
```
> ./selfie -c selfie.c -m 1
  ./selfie: this is selfie's starc compiling selfie.c
  ./selfie: this is selfie's mipster executing selfie.c with 1MB of memory
  selfie.c: usage: selfie { -c source | -o binary | -s assembly | -l binary } [ -m size ... | -d size ... | -y size ... ]
  selfie.c: exiting with exit code 0
  ./selfie: this is selfie's mipster terminating selfie.c
  ./selfie: profile: total,max(ratio%)@addr(line#),2max(ratio%)@addr(line#),3max(ratio%)@addr(line#)
  ./selfie: calls: 1474,486(33.00%)@0x22A0(~1166),242(16.42%)@0x2300(~1172),121(8.21%)@0x88(~76)
  ./selfie: loops: 150,120(80.00%)@0x3914(~1451),30(20.00%)@0x1DC(~187),0(0.00%)
  ./selfie: loads: 10371,486(4.68%)@0x22B4(~1166),242(2.33%)@0x2314(~1172),122(1.17%)@0x3914(~1451)
  ./selfie: stores: 6261,486(7.76%)@0x22A4(~1166),242(3.86%)@0x2304(~1172),122(1.94%)@0x391C(~1451)
```

The output is just like before except for the approximate source code line numbers in the profile. Those are only available if executing machine code generated in the same run rather than loading machine code. Never mind if you do not understand what this means. It will become clear later.

Let us maintain our momentum and do something even cooler than before. We now compile `selfie.c` with starc and then execute the generated code on mipster only to have the generated code compile `selfie.c` again, all in the same run. This requires 2MB rather than 1MB for mipster and will take starc a few minutes to complete depending on the speed of our machine because executing starc on mipster is slower than executing starc directly on our machine. However, it does work and this is what counts here:

{line-numbers=off}
```
> ./selfie -c selfie.c -m 2 -c selfie.c
  ./selfie: this is selfie's starc compiling selfie.c
  ./selfie: this is selfie's mipster executing selfie.c with 2MB of memory
  selfie.c: this is selfie's starc compiling selfie.c
  selfie.c: exiting with exit code 0
  ./selfie: this is selfie's mipster terminating selfie.c
  ./selfie: profile: total,max(ratio%)@addr(line#),2max(ratio%)@addr(line#),3max(ratio%)@addr(line#)
  ./selfie: calls: 45721539,15289024(33.44%)@0x22A0(~1166),7770217(17.00%)@0x2300(~1172),7509926(16.44%)@0x243C(~1183)
  ./selfie: loops: 2575420,2143980(83.33%)@0x5C28(~1962),271556(10.54%)@0x2B34(~1254),68294(2.65%)@0x4CCC(~1708)
  ./selfie: loads: 315084532,15289024(4.85%)@0x22B4(~1166),7770217(2.46%)@0x2314(~1172),7509926(2.38%)@0x2450(~1183)
  ./selfie: stores: 193136537,15289024(7.91%)@0x22A4(~1166),7770217(4.02%)@0x2304(~1172),7509926(3.88%)@0x2440(~1183)
```

We can even verify that starc generates the same machine code independently of whether it runs directly on our machine or on mipster. We simply have starc generate machine code into two different files called `selfie1.m` and `selfie2.m`:

{line-numbers=off}
```
> ./selfie -c selfie.c -o selfie1.m -m 2 -c selfie.c -o selfie2.m
  ./selfie: this is selfie's starc compiling selfie.c
  ./selfie: writing code into output file selfie1.m
  ./selfie: this is selfie's mipster executing selfie1.m with 2MB of memory
  selfie1.m: this is selfie's starc compiling selfie.c
  selfie1.m: writing code into output file selfie2.m
  selfie1.m: exiting with exit code 0
  ./selfie: this is selfie's mipster terminating selfie1.m
  ./selfie: profile: total,max(ratio%)@addr(line#),2max(ratio%)@addr(line#),3max(ratio%)@addr(line#)
  ./selfie: calls: 45722248,15289262(33.44%)@0x22A0(~1166),7770336(17.00%)@0x2300(~1172),7510045(16.44%)@0x243C(~1183)
  ./selfie: loops: 2575475,2143980(83.33%)@0x5C28(~1962),271559(10.54%)@0x2B34(~1254),68294(2.65%)@0x4CCC(~1708)
  ./selfie: loads: 315089390,15289262(4.85%)@0x22B4(~1166),7770336(2.46%)@0x2314(~1172),7510045(2.38%)@0x2450(~1183)
  ./selfie: stores: 193139498,15289262(7.91%)@0x22A4(~1166),7770336(4.02%)@0x2304(~1172),7510045(3.88%)@0x2440(~1183)
```

Both files generated by starc are indeed identical. To verify that try the `diff` command as follows:

{line-numbers=off}
```
> diff -s selfie1.m selfie2.m
  Files selfie1.m and selfie2.m are identical
```

This is called the fixed point of a self-compiling compiler. If we continue generating machine code for starc using starc the machine code will remain the same. So, we still have only three different sequences of bits in `selfie.c`, `selfie`, and `selfie.m` that are supposed to have the same semantics. In particular, if we run `selfie.m` on mipster to compile `selfie.c` the result will again be an exact copy of `selfie.m`. However, there is a fourth sequence with the same semantics that we can generate with selfie. It represents a human-readable version of the machine code in `selfie.m` written in what is called assembly.

[Assembly](https://en.wikipedia.org/wiki/Assembly_language "Assembly Language")
: A low-level programming language for a computer, or other programmable device, in which there is a very strong (generally one-to-one) correspondence between the language and the architecture's machine code instructions.

Try the `-s` option to have selfie generate assembly as follows:

{line-numbers=off}
```
> ./selfie -c selfie.c -s selfie.s
  ./selfie: this is selfie's starc compiling selfie.c
  ./selfie: writing assembly into output file selfie.s
```

{line-numbers=off}
```
> ./selfie -c selfie.c -d 1
  ./selfie: this is selfie's starc compiling selfie.c
  ./selfie: this is selfie's mipster executing selfie.c with 1MB of memory
  selfie.c: $pc=0x0(~76): 0x24080007: addiu $t0,$zero,7: $t0=0,$zero=0 -> $t0=7
  selfie.c: $pc=0x4(~76): 0x24094000: addiu $t1,$zero,16384: $t1=0,$zero=0 -> $t1=16384
  selfie.c: $pc=0x8(~76): 0x01090019: multu $t0,$t1: $t0=7,$t1=16384,$lo=0 -> $lo=114688
  selfie.c: $pc=0xC(~76): 0x00004012: mflo $t0: $t0=7,$lo=114688 -> $t0=114688
  selfie.c: $pc=0x10(~76): 0x00000000: nop
  selfie.c: $pc=0x14(~76): 0x00000000: nop
  selfie.c: $pc=0x18(~76): 0x25081844: addiu $t0,$t0,6212: $t0=114688,$t0=114688 -> $t0=120900
  selfie.c: $pc=0x1C(~76): 0x251C0000: addiu $gp,$t0,0: $gp=0,$t0=120900 -> $gp=120900
  selfie.c: $pc=0x20(~76): 0x24080FFF: addiu $t0,$zero,4095: $t0=120900,$zero=0 -> $t0=4095
  selfie.c: $pc=0x24(~76): 0x24094000: addiu $t1,$zero,16384: $t1=16384,$zero=0 -> $t1=16384
  selfie.c: $pc=0x28(~76): 0x01090019: multu $t0,$t1: $t0=4095,$t1=16384,$lo=114688 -> $lo=67092480
  selfie.c: $pc=0x2C(~76): 0x00004012: mflo $t0: $t0=4095,$lo=67092480 -> $t0=67092480
  selfie.c: $pc=0x30(~76): 0x00000000: nop
  selfie.c: $pc=0x34(~76): 0x00000000: nop
  selfie.c: $pc=0x38(~76): 0x25083FFC: addiu $t0,$t0,16380: $t0=67092480,$t0=67092480 -> $t0=67108860
  selfie.c: $pc=0x3C(~76): 0x8D1D0000: lw $sp,0($t0): $sp=0,$t0=0x3FFFFFC -> $sp=67108832=memory[0x3FFFFFC]
  selfie.c: $pc=0x40(~76): 0x0C007054: jal 0x7054[0x1C150]: $ra=0x0 -> $ra=0x48,$pc=0x1C150
  ...
  selfie.c: $pc=0x48(~76): 0x27BDFFFC: addiu $sp,$sp,-4: $sp=67108840,$sp=67108840 -> $sp=67108836
  selfie.c: $pc=0x4C(~76): 0xAFA20000: sw $v0,0($sp): $v0=0,$sp=0x3FFFFE4 -> memory[0x3FFFFE4]=0=$v0
  selfie.c: $pc=0x50(~76): 0x8FA40000: lw $a0,0($sp): $a0=1,$sp=0x3FFFFE4 -> $a0=0=memory[0x3FFFFE4]
  selfie.c: $pc=0x54(~76): 0x27BD0004: addiu $sp,$sp,4: $sp=67108836,$sp=67108836 -> $sp=67108840
  selfie.c: $pc=0x58(~76): 0x24020FA1: addiu $v0,$zero,4001: $v0=0,$zero=0 -> $v0=4001
  selfie.c: $pc=0x5C(~76): 0x0000000C: syscall
  selfie.c: exiting with exit code 0
  ./selfie: this is selfie's mipster terminating selfie.c
  ./selfie: profile: total,max(ratio%)@addr(line#),2max(ratio%)@addr(line#),3max(ratio%)@addr(line#)
  ./selfie: calls: 1474,486(33.00%)@0x22A0(~1166),242(16.42%)@0x2300(~1172),121(8.21%)@0x88(~76)
  ./selfie: loops: 150,120(80.00%)@0x3914(~1451),30(20.00%)@0x1DC(~187),0(0.00%)
  ./selfie: loads: 10371,486(4.68%)@0x22B4(~1166),242(2.33%)@0x2314(~1172),122(1.17%)@0x3914(~1451)
  ./selfie: stores: 6261,486(7.76%)@0x22A4(~1166),242(3.86%)@0x2304(~1172),122(1.94%)@0x391C(~1451)
```

{line-numbers=off}
```
> ./selfie -c selfie.c -o selfie.m -m 2 -l selfie.m -m 1
  ./selfie: this is selfie's starc compiling selfie.c
  ./selfie: writing code into output file selfie.m
  ./selfie: this is selfie's mipster executing selfie.m with 2MB of memory
  selfie.m: loading code from input file selfie.m
  selfie.m: this is selfie's mipster executing selfie.m with 1MB of memory
  selfie.m: usage: selfie { -c source | -o binary | -s assembly | -l binary } [ -m size ... | -d size ... | -y size ... ]
  selfie.m: exiting with exit code 0
  selfie.m: this is selfie's mipster terminating selfie.m
  selfie.m: profile: total,max(ratio%)@addr(line#),2max(ratio%)@addr(line#),3max(ratio%)@addr(line#)
  selfie.m: calls: 1474,486(33.00%)@0x22A0,242(16.42%)@0x2300,121(8.21%)@0x88
  selfie.m: loops: 150,120(80.00%)@0x3914,30(20.00%)@0x1DC,0(0.00%)
  selfie.m: loads: 10371,486(4.68%)@0x22B4,242(2.33%)@0x2314,122(1.17%)@0x3914
  selfie.m: stores: 6261,486(7.76%)@0x22A4,242(3.86%)@0x2304,122(1.94%)@0x391C
  selfie.m: exiting with exit code 0
  ./selfie: this is selfie's mipster terminating selfie.m
  ./selfie: profile: total,max(ratio%)@addr(line#),2max(ratio%)@addr(line#),3max(ratio%)@addr(line#)
  ./selfie: calls: 2168736,544911(25.18%)@0x22A0(~1166),238853(11.02%)@0x243C(~1183),183104(8.44%)@0x2300(~1172)
  ./selfie: loops: 481100,393216(81.96%)@0x19AF4(~5926),56455(11.73%)@0x193CC(~5771),30225(6.28%)@0x19A30(~5907)
  ./selfie: loads: 17097834,544911(3.18%)@0x22B4(~1166),393228(2.29%)@0x19AF4(~5926),393216(2.29%)@0x19B1C(~5927)
  ./selfie: stores: 9648305,544911(5.64%)@0x22A4(~1166),393216(4.07%)@0x19B40(~5927),238853(2.47%)@0x2440(~1183)
```

{line-numbers=off}
```
> ./selfie -c selfie.c -o selfie3.m -s selfie3.s -y 4 -l selfie3.m -y 2 -c selfie.c -o selfie4.m -s selfie4.s
  ./selfie: this is selfie's starc compiling selfie.c
  ./selfie: writing code into output file selfie3.m
  ./selfie: writing assembly into output file selfie3.s
  ./selfie: this is selfie's hypster executing selfie3.m with 4MB of memory
  selfie3.m: loading code from input file selfie3.m
  selfie3.m: this is selfie's hypster executing selfie3.m with 2MB of memory
  selfie3.m: this is selfie's starc compiling selfie.c
  selfie3.m: writing code into output file selfie4.m
  selfie3.m: writing assembly into output file selfie4.s
  selfie3.m: exiting with exit code 0
  selfie3.m: this is selfie's hypster terminating selfie3.m
  selfie3.m: exiting with exit code 0
  ./selfie: this is selfie's hypster terminating selfie3.m
```