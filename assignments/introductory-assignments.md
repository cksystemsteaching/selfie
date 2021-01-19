# Introductory Assignments

Welcome to the Introduction to Computer Science supplementary material. This document provides you with content, examples, and exercises to help you learn and understand the course material.

## The following information is shared via the course's slack channel.

- Lectures
- Recordings
- Class schedule

## Resources

- Lectures
- [Slides](https://www.icloud.com/keynote/0J_SKB-ofwiuxg-lCag-s-gOA#selfie)
- [Selfie: Computer Science for Everyone](https://leanpub.com/selfie)

---

- [Introductory Assignments](#introductory-assignments)
	- [The following information is shared via the course's slack channel.](#the-following-information-is-shared-via-the-courses-slack-channel)
	- [Resources](#resources)
- [Introduction](#introduction)
	- [Bit Representation](#bit-representation)
		- [Examples](#examples)
	- [Decimal System](#decimal-system)
		- [Examples](#examples-1)
		- [Exercises](#exercises)
	- [Binary Numbers](#binary-numbers)
		- [Examples](#examples-2)
		- [Exercises](#exercises-1)
	- [MSB & LSB](#msb--lsb)
		- [Examples](#examples-3)
		- [Exercises](#exercises-2)
	- [Byte](#byte)
		- [Examples](#examples-4)
		- [Exercises](#exercises-3)
	- [ASCII](#ascii)
		- [Examples](#examples-5)
		- [Exercises](#exercises-4)
	- [Unicode](#unicode)
	- [Different Notations](#different-notations)
		- [Examples](#examples-6)
	- [Unary](#unary)
		- [Examples](#examples-7)
	- [Octal](#octal)
		- [Examples](#examples-8)
		- [Exercises](#exercises-5)
	- [Nibble](#nibble)
		- [Examples](#examples-9)
	- [Hexadecimal](#hexadecimal)
		- [Examples](#examples-10)
		- [Exercises](#exercises-6)
	- [Computation](#computation)
	- [State Space](#state-space)
		- [Examples](#examples-11)
		- [Exercises](#exercises-7)
	- [Software](#software)
		- [Natural Numbers](#natural-numbers)
	- [Binary Number Names & Prefixes](#binary-number-names--prefixes)
		- [Examples](#examples-12)
		- [Exercises](#exercises-8)
	- [Signed and unsigned integer](#signed-and-unsigned-integer)
		- [One's complement](#ones-complement)
		- [Two's complement](#twos-complement)
			- [From decimal digit into two's complement](#from-decimal-digit-into-twos-complement)
			- [From two's complement into decimal](#from-twos-complement-into-decimal)
		- [Numbers we can represent](#numbers-we-can-represent)
		- [Exercises](#exercises-9)
	- [Arithmetics](#arithmetics)
		- [Integer arithmetics](#integer-arithmetics)
			- [Examples](#examples-13)
			- [Exercises](#exercises-10)
		- [Arithmetic overflow](#arithmetic-overflow)
- [Architecture](#architecture)
	- [Binary vs. Decimal](#binary-vs-decimal)
	- [Von Neumann architecture](#von-neumann-architecture)
		- [Central Processing Unit (CPU)](#central-processing-unit-cpu)
			- [Examples](#examples-14)
			- [Exercises](#exercises-11)
		- [Program Counter (PC)](#program-counter-pc)
		- [Random access memory (RAM)](#random-access-memory-ram)
			- [Examples](#examples-15)
			- [Exercises](#exercises-12)
		- [Memory-bus](#memory-bus)
			- [Examples](#examples-16)
	- [Code vs. Data](#code-vs-data)
- [Compilers](#compilers)
	- [Compiler](#compiler)
	- [The Emulator](#the-emulator)
	- [Instructions](#instructions)
	- [RISC-V](#risc-v)

---

# Introduction

## Bit Representation

First and foremost, as far as computers are concerned, everything is a number, in fact, a binary number. A computer stores everything as a series of 0's and 1's. This representation is called a [bit](https://en.wikipedia.org/wiki/Bit). A bit can only have one of two values, most commonly represented as a 0 and a 1. In actual electronic hardware, value 1 is typically represented by high voltage, and value 0 by low voltage.

### Examples

When we write bit values, we use the 0b extension in front of the bit-value.

0b101010 = 42 as decimal number

0b101010 = \* symbol in the [ASCII Table](ascii-table.md)

Here we can see that a series of 0's and 1's can be interpreted in different ways.

## Decimal System

A decimal number is a number represented in base 10, in which there are ten possible values for each digit (0–9). When these digits are concatenated to make strings of numbers, they are interpreted column by column. Beginning at the far right and moving to the left, we have the 1's column, the 10's column, the 100's column, and so forth.  The one's column is 10^{0}=1, and the tens column is 10^{1}=10, the hundreds column is 10^{2}=100, and so on.

### Examples

For example, with a 4-digit sequence of 1011, the decimal (base 10) interpretation looks as follows. For the far-right column, we take 1\*10^{0}=1, the second column from the right is 1\*10^{1}=10, the third column from the right 0\*10^{2}=0 and the far left column 1\*10^{3}=1000. When adding all four values 1+10+0+1000 together, we get the value 1011 as a decimal representation.


| 4-digit sequence | 1         | 0         | 1         | 1         | Value  |
| ---------------- | --------- | --------- | --------- | --------- | ------ |
| Notation         | 1\*10^{3} | 0\*10^{2} | 1\*10^{1} | 1\*10^{0} |        |
| Representation   | 1000      | 0         | 10        | 1         | = 1011 |

### Exercises

- Write the number 1337 in scientific notation.
- Write the number 267938 in scientific notation.

## Binary Numbers

A [binary number](https://en.wikipedia.org/wiki/Binary_number) is a number represented in base 2, in which there are only two possible values for each digit (0 and 1). The 0 and 1 correspond to low and high voltage values stored on a computer. Although it might be possible for a computer to hold more than two voltage values and therefore support a base larger than 2, it would be challenging to support the ten voltage values required to support a base 10 number system in hardware. A familiarity with base 2 helps understand how a computer stores and interprets data.

Binary numbers interpreted that each bit (the name for a binary digit) holds the value 2 raised to an increasing exponent. We begin with the right-most bit (also called the LSB = least significant bit), which has the value 2^{0}=1, or the one's column. The next bit holds the value 2^{1}=2, or the twos column. In base 10, each column is ten times larger than the one before it. In base 2, each column's value grows by 2.

**Binary notation**:

| MSB   |       |       |       |       |       |       | LSB   |
| ----- | ----- | ----- | ----- | ----- | ----- | ----- | ----- |
| 2^{7} | 2^{6} | 2^{5} | 2^{4} | 2^{3} | 2^{2} | 2^{1} | 2^{0} |
| 128   | 64    | 32    | 16    | 8     | 4     | 2     | 1     |


### Examples

**Binary to Decimal**

As shown with the base 10 decimal system and a 4-digit sequence of 1011, in the base 2 binary system, we convert the value into a base 10 number. Starting from the right-most or LSB (least significant bit), we calculate 1\*2^{0}=1, the second column from the right is 1\*2^{1}=2, the third column from the right is 0\*2^{2}=0, and the left-most or MSB (most significant bit) is 1\*2^{3}=8. Now we add all 4 values together, 1+2+0+8 = 11. In this interpretation, with a 4-digit sequence, we get the value 11 as base 10 decimal number.

| 4-digit sequence | 1        | 0        | 1        | 1        | Value |
| ---------------- | -------- | -------- | -------- | -------- | ----- |
| Notation         | 1\*2^{3} | 0\*2^{2} | 1\*2^{1} | 1\*2^{0} |       |
| Representation   | 8        | 0        | 2        | 1        | = 11  |

**Decimal to Binary**

We have seen above how to convert binary to decimal numbers, but how do we convert a decimal number into a binary number.

An easy method of converting decimal to binary number equivalents is to write down the decimal number and to continually divide-by-2 ([modulo](https://en.wikipedia.org/wiki/Modulo_operation)) to give a result and a remainder of either a "1" or a "0" until the final result equals zero. If the result is not a whole number, it is rounded down before it is used in the next division.

Converting the decimal number 42 (base 10) into its binary equivalent.

| Value | Divide by | Result | Remainder |     |
| ----- | --------- | ------ | --------- | --- |
| 42    | 2         | 21     | 0         | LSB |
| 21    | 2         | 10.5   | 1         |
| 10    | 2         | 5      | 0         |
| 5     | 2         | 2.5    | 1         |
| 2     | 2         | 1      | 0         |
| 1     | 2         | 0.5    | 1         | MSB |

Dividing each decimal number by "2", as shown, will give a result plus a remainder.

If the decimal number being divided is even, then the result will be whole, and the remainder will be equal to "0". If the decimal number is odd, then the result will not divide entirely, and the remainder will be a "1".

The binary result is obtained by placing all the remainders in order with the least significant bit (LSB) being at the top and the most significant bit (MSB) being at the bottom.

Now we can write the value from down-up with the leading MSB as 101010.

### Exercises

- What is a binary number?
- What is the value of the 5-digit sequence 10101?
- What is the value of the 8-digit sequence 10110110?

## MSB & LSB

The most significant bit on the far-left in the binary representation represents the greatest value. The least significant bit on the right-most can show if a number is even or odd. If the LSB is 1, then it is an even number, and if the LSB is 0, the number is odd.

### Examples

| 128 | 64  | 32  | 16  | 8   | 4   | 2   | 1   | Value |
| --- | --- | --- | --- | --- | --- | --- | --- | :---: |
| 0   | 1   | 0   | 1   | 0   | 1   | 0   | 1   | = 85  |

In the example with the value 85, the LSB is 1, representing an odd value.

| 128 | 64  | 32  | 16  | 8   | 4   | 2   | 1   | Value |
| --- | --- | --- | --- | --- | --- | --- | --- | :---: |
| 1   | 0   | 1   | 0   | 1   | 0   | 1   | 0   | = 170 |

In the example with the value 170, the LSB is 0, representing an even value.

### Exercises

- Is the value 101010 even or odd?
- Is the value 111 even or odd?
- Is the value 11101 even or odd?
- Is the value 111110 even or odd?
 ## Byte

Since a unit of eight bits is very common in computer systems, there is a well-known term for that unit called a byte.

[Byte](https://en.wikipedia.org/wiki/Byte): A unit of digital information in computing and telecommunications that most commonly consists of eight bits.

### Examples

A bit sequence of 0b10101010 = 170 in decimal notation and consists of 8 bits and represents 1 byte.

So, if we talk about bytes, we mean sequences of 8 bits.

### Exercises

- What is the smallest number representable by an (unsigned) byte?
- What is the largest number representable by an (unsigned) byte?

## ASCII

Previously we established that as far as computers are concerned, everything is a binary number. But how do computers handle letters or text, just like the very document you are reading right now?

[ASCII](https://en.wikipedia.org/wiki/ASCII) is used to map characters to 7 bit wide integers and vice versa. So while characters are still integers to a computer, we can use the ASCII map to interpret those integers as human-readable characters that can be printed to a screen.

Reference: [ASCII Table](ascii-table.md)

### Examples

| Representation |    |     |     |     |     |
|----------------|----|-----|-----|-----|-----|
| **Decimal**    | 72 | 101 | 108 | 108 | 111 |
| **ASCII**      | H  | e   | l   | l   | o   |

### Exercises

- How many different characters can be represented in ASCII?
- What is the decimal representation of your first name?
- What is the ASCII representation of the decimal numbers 115, 101, 108, 102, 105, 101?

## Unicode

[Unicode](https://en.wikipedia.org/wiki/Unicode) is a technology standard for the consistent encoding, representation, and handling of text expressed in most of the world's writing systems. 
Unicode can be implemented by different character encodings. The Unicode standard defines Unicode Transformation Formats (UTF) UTF-8, UTF-16, UTF-32, and several other encodings.

One of the most commonly used encodings is [UTF-8](https://en.wikipedia.org/wiki/UTF-8), a variable-width character encoding used for electronic communication. 
UTF-8 can encode all 1,112,064 valid character code points in Unicode using one to four one-byte (8-bit) code units. It was designed for backward compatibility with ASCII: the first 128 characters of Unicode, which correspond one-to-one with ASCII, are encoded using a single byte with the same binary value as ASCII and the most-significant-bit as an indicator for Unicode, so that valid ASCII text is valid UTF-8-encoded Unicode as well. 


So how many bits do we need to represent 120000 different characters?

We need at least 17-bit = 2^{17} = 131072 > 120000 characters.

In UTF-32, we use a fixed-length encoding with 32-bit. It is rarely used and inefficient because it often uses an unnecessary amount of bits to represent a character.

In UTF-16, we use a variable-length encoding that uses 16-bit or 32-bit to represent characters.

Selfie uses UTF-8 as an encoding scheme for Unicode; it is a variable-length encoding and can represent 8, 16, 24, or 32-bits. It is very widely used and efficient.

For example, the character `U` in decimal is `85`, and the binary representation is `0b01010101`, which are 8-bits or 1-byte to represent one character.

## Different Notations

| Encoding    | Alphabet                        | Base (Radix, Size of Alphabet) | # Values in Digits n>0 |
| ----------- | ------------------------------- | ------------------------------ | ---------------------- |
| Unary       | 1                               | 1                              | n                      |
| Binary      | 0,1                             | 2                              | 2^{n}                  |
| Octal       | 0,1,2,3,4,5,6,7                 | 8                              | 8^{n}                  |
| Decimal     | 0,1,2,3,4,5,6,7,8,9             | 10                             | 10^{n}                 |
| Hexadecimal | 0,1,2,3,4,5,6,7,8,9,A,B,C,D,E,F | 16                             | 16^{n}                 |


[Radix](https://en.wikipedia.org/wiki/Radix): The number of unique digits, including zero, represents numbers in a positional numeral system.

### Examples

|      | Encoding    | Representation |
| ---- | ----------- | -------------- |
| 42   | Binary      | 0b101010       |
| 42   | Octal       | 0o52           |
| 42   | Decimal     | 42             |
| 42   | Hexadecimal | 0x2A           |
| "42" | String      | 42             |
| '*'  | ASCII       | 42             |

## Unary

The [Unary Numeral System](https://en.wikipedia.org/wiki/Unary_numeral_system) is the most straightforward numeral system to represent natural numbers.

### Examples

The number 42 represented in the unary numeral system:

111111111111111111111111111111111111111111

That is 42 ones in a row.

## Octal

The [Octal](https://en.wikipedia.org/wiki/Octal) (base 8) notation is popular in computer science because it is represented in blocks of three bits.

Each digit of an octal number is represented by three bits. Conversely, an octal number can easily be generated from a binary number by grouping three bits each.

**Octal notation**

| MSB   |       |       |       |       |       |       | LSB   |
| ----- | ----- | ----- | ----- | ----- | ----- | ----- | ----- |
| 8^{7} | 8^{6} | 8^{5} | 8^{4} | 8^{3} | 8^{2} | 8^{1} | 8^{0} |
| 2M    | 262K  | 32K   | 4K    | 512   | 64    | 8     | 1     |

**Octal numbers**

| Decimal | 3-bit Binary | Octal    |
| ------- | ------------ | -------- |
| 0       | 000          | 0        |
| 1       | 001          | 1        |
| 2       | 010          | 2        |
| 3       | 011          | 3        |
| 4       | 100          | 4        |
| 5       | 101          | 5        |
| 6       | 110          | 6        |
| 7       | 111          | 7        |
| 8       | 001 000      | 10 (1+0) |
| 9       | 001 001      | 11 (1+1) |
| 10      | 001 010      | 12 (1+2) |

### Examples

**Example 1**

We are converting the decimal value 42 into the binary number 0b101010. As the next step, we group the binary number into three bits each. When we group these values into three bits each, we get 101 and 010.

Now we can convert each three-bit value into an octal representation:

The first sequence of three bits: 101

|        | 4   | 2   | 1   | Value |
| ------ | --- | --- | --- | :---: |
| Binary | 1   | 0   | 1   |  = 5  |

The second sequence of three bits: 010

|        | 4   | 2   | 1   | Value |
| ------ | --- | --- | --- | :---: |
| Binary | 0   | 1   | 0   |  = 2  |

We see that the first three-bit value converts into 5, and the second three-bit value converts into 2.

That means we get a final value of 52 or in octal notation 0o52.

**Example 2**

Converting a octal number into a binary numbers works like follows:

|             |                       |
| ----------- | :-------------------- |
| Octal       | 0o52                  |
| Polynomial  | = (5\*8^1) + (2\*8^0) |
| Calculation | = 40 + 2              |
| Decimal     | 42                    |

### Exercises

- What is the octal representation of the decimal value 16?
- What is the octal representation of the binary number 0b100100?
- What is the decimal representation of the octal value 173?

## Nibble

A [nibble](https://en.wikipedia.org/wiki/Nibble) is a block of four bits.
A Block of four bits corresponds to precisely one hexadecimal digit.

### Examples

For example, the bit value 0b1010 is 4 bits long and called a nibble, it represents the decimal value 10.

| 8   | 4   | 2   | 1   | Value |
| --- | --- | --- | --- | :---: |
| 1   | 0   | 1   | 0   | = 10  |

## Hexadecimal

The [Hexadecimal](https://en.wikipedia.org/wiki/Hexadecimal) (base 16) notation is popular in computer science because it is represented in blocks of four bits (nibble or half-a-byte). Each group of four bits can have possible values between "0000" (0) and "1111" (8+4+2+1=15), giving a total of 16 different number combinations from 0 to 15. Since 16 in the decimal system is the fourth power of two (2^{4}), there is a direct relationship between the numbers 2 and 16.

| Decimal Number | 4-bit Binary Number | Hexadecimal Number |
| -------------- | ------------------- | ------------------ |
| 0              | 0000                | 0                  |
| 1              | 0001                | 1                  |
| 2              | 0010                | 2                  |
| 3              | 0011                | 3                  |
| 4              | 0100                | 4                  |
| 5              | 0101                | 5                  |
| 6              | 0110                | 6                  |
| 7              | 0111                | 7                  |
| 8              | 1000                | 8                  |
| 9              | 1001                | 9                  |
| 10             | 1010                | A                  |
| 11             | 1011                | B                  |
| 12             | 1100                | C                  |
| 13             | 1101                | D                  |
| 14             | 1110                | E                  |
| 15             | 1111                | F                  |


When we write hexadecimal notation, we use 0x to emphasize that we talk about hexadecimal.

### Examples

For example, we can show the hexadecimal, binary and octal representation of the decimal number 42:

| Dec | Hex  | Bin      | Oct  |
| --- | ---- | -------- | ---- |
| 42  | 0x2A | 0b101010 | 0o52 |


Further, we can convert the decimal number 2020 into hexadecimal:

For example, the decimal number 2020 gets converted into binary with modulo-2, and we get a result of 0b11111100100. We group the bits into four's starting from the right-hand side (0b0111 1110 0100). Then we find the Decimal equivalent for each group of four-bits. Finally, we can convert the decimal equivalent into the hexadecimal representation.

| Notation    | 4-bit block | 4-bit block | 4-bit block |
| ----------- | ----------- | ----------- | ----------- |
| Binary      | 0111        | 1110        | 0100        |
| Decimal     | 7           | 14          | 4           |
| Hexadecimal | 7           | E           | 4           |

The hexadecimal equivalent of the binary number 0b111 1110 0100 is 0x7E4.

### Exercises

- Convert the binary number 0b1100100100011111 into the hexadecimal representation.
- Convert the hexadecimal number 64B1D into the binary representation.

## Computation

Computation is essentially a sequence of state transitions. A computer stores a very large but still finite amount of bits in memory and registers at any given time. The values of all these bits together are what we call the state of the machine. Then the processor executes one instruction, which directs it to change the values of a very small number of bits creating a new state. That process of change from one state to the next continues until the machine is turned off.

[State](https://en.wikipedia.org/wiki/State_(computer_science)): The state of a digital logic circuit or computer program is a technical term for all the stored information, at a given instant in time, to which the circuit or program has access. Its current inputs and its state entirely determine the output of a digital circuit or computer program at any time.

Software on source and machine code level specifies for each state what the next state is. There are the data bits that are being changed and the code bits that determine that change. Input is typically modeled by data bits changed by something other than the processor, such as a keyboard.

Machine code or bits describe the change of a state.

## State Space

As we saw before, a bit can have two possible values, 0 and 1. Now we are going to talk about the state space of 1 or more bits. With N bits, we can distinguish 2^{N} states.

### Examples

| Bits | # of States | Scientific Notation |
| ---- | ----------- | ------------------- |
| 2    | 4           | 2^{2}               |
| 3    | 8           | 2^{3}               |
| 4    | 16          | 2^{4}               |
| 5    | 32          | 2^{5}               |
| 6    | 64          | 2^{6}               |
| 7    | 128         | 2^{7}               |
| 8    | 256         | 2^{8}               |

As shown above, 2 bits can have four possible states (00,01,10,11), and when we add one bit, the state space grows exponentially.

### Exercises

Write your answers in Scientific Notation.

- How many states can we distinguish with 1 byte?
- How many states can we distinguish with 64 bits?

## Software

Software instructs a computer what to do in a computation. Thus computation defines the meaning of software.

### Natural Numbers

An infinite set of numbers can be bigger than another infinite set of numbers. ([Georg Cantor's theorem](https://en.wikipedia.org/wiki/Cantor%27s_theorem))

N: 0,1,2,3,4,... -> Infinite set of Natural Numbers. (syntax)

{0,1,2} -> A subset of a infinite set of Natural Numbers.

P(N) -> Power-set of all subsets {0},{0,1},{0,1,2,3},... (infinite amount of software)

## Binary Number Names & Prefixes

Today, as microcontroller and microprocessor systems become increasingly larger, the individual binary digits (bits) are now grouped into eight's to form a single byte.

| Number of Binary Digits (bits) | Common Name |
| ------------------------------ | ----------- |
| 1                              | Bit         |
| 4                              | Nibble      |
| 8                              | Byte        |
| 16                             | Word        |
| 32                             | Double Word |
| 64                             | Quad Word   |

**Binary - base 2**:

The computer industry has historically used the units kilobyte, megabyte, gigabyte, and the corresponding symbols KB, MB, and GB, in at least two slightly different measurement systems. In citations of main memory (RAM) capacity, gigabyte customarily means 1073741824 bytes. This value is a power of 1024, and 1024 is a [power of two](https://en.wikipedia.org/wiki/Power_of_two) (2^{10}). This usage is referred to as a binary measurement.

| Prefix | Symbol | Scientific Notation |
| ------ | ------ | ------------------- |
| kibi-  | Ki     | 2^{10}              |
| mebi-  | Mi     | 2^{20}              |
| gibi-  | Gi     | 2^{30}              |
| tebi-  | Ti     | 2^{40}              |
| pebi-  | Pi     | 2^{50}              |
| exbi-  | Ei     | 2^{60}              |

**Decimal - base 10:**

The industry uses the multipliers kilo, mega, giga, etc., in a manner consistent with their meaning in the [International System of Units](https://en.wikipedia.org/wiki/International_System_of_Units) (SI), namely as powers of 1000.
For example, a 500-gigabyte hard disk holds 500000000000 bytes, and a 1 Gbit/s (gigabit per second) Ethernet connection transfers data at a nominal speed of 1000000000 bit/s. In contrast with the binary prefix usage, this use is described as a decimal prefix, as 1000 is a [power of 10](https://en.wikipedia.org/wiki/Powers_of_10) (10^{3}).

| Prefix | Symbol | Scientific Notation |
| ------ | ------ | ------------------- |
| kilo-  | k      | 10^{3}              |
| mega-  | M      | 10^{6}              |
| giga-  | G      | 10^{9}              |
| tera-  | T      | 10^{12}             |
| peta-  | P      | 10^{15}             |
| exa-   | E      | 10^{18}             |

### Examples

**binary - base 2**

| Value          | Scientific Notation | Result       | Symbol |
| -------------- | ------------------- | ------------ | ------ |
| 1024 bytes     | 2^{10}              | = 1 kibibyte | KiB    |
| 1024 kibibytes | 2^{20}              | = 1 mebibyte | MiB    |
| 1024 mebibytes | 2^{30}              | = 1 gibibyte | GiB    |
| 1024 gibibytes | 2^{40}              | = 1 tebibyte | TiB    |

For example, 1 kibibyte = 1024 byte = 8192 bits.

**decimal - base 10**

| Value          | Scientific Notation | Result       | Symbol |
| -------------- | ------------------- | ------------ | ------ |
| 1000 bytes     | 10^{3}              | = 1 kilobyte | kB     |
| 1000 kilobytes | 10^{6}              | = 1 megabyte | MB     |
| 1000 megabytes | 10^{9}              | = 1 gigabyte | GB     |
| 1000 gigabytes | 10^{12}             | = 1 terabyte | TB     |

For example, 1 kilobyte = 1000 bytes = 8000 bits.

**state space - storage**

In this example, we want to show how many different states a digital circuit computer with 120GB of storage can have.

\# states = 2^{\# of bits}

\# states = 2^{120GB \* 10^{9} giga \* 8 bit}

\# states = 2^{120\*10^{9}\*8}

\# states = 2^{960 000 000 000}

A digital circuit computer with 120GB of storage can distinguish 2^{960 000 000 000} states.

**state-space - memory**

In this example, we want to show how many different states a digital circuit computer with 2GB of memory can have.

\# states = 2^{\# of bits}

\# states = 2^{2GB \* 2^30 gibi \* 8 bit}

\# states = 2^{2^{1} \* 2^{30} \* 2^{3}}

\# states = 2^{2^{34}}

\# states = 2^{17 179 869 184}

A digital circuit computer with 2GB of memory can distinguish 2^{17 179 869 184} states.

### Exercises

- How many different states can a digital computer with 4GB of memory have?
- How many different states can a digital computer with 80GB of storage have?

## Signed and unsigned integer

Bytes can represent numbers as well as alphabetic characters. But if we want to represent negative numbers, we have to use a sign bit.

### One's complement

The [one's complement](https://en.wikipedia.org/wiki/Signed_number_representations) is used to represent negative numbers.

**8-bit representation**

We only use 7 bits for the value and the MSB for the sign with a simple sign bit.
If the MSB is a 1, it represents a `-` (minus sign); else, it is a `+` (plus sign).


| bit values |  +/-  |  64   |  32   |  16   |   8   |   4   |   2   |   1   | Decimal Value |
| :--------- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | ------------: |
| bits       |   0   |   0   |   1   |   0   |   1   |   0   |   0   |   1   |            41 |
| bits       |   1   |   0   |   1   |   0   |   1   |   0   |   0   |   1   |           -41 |


**Reason why we don't use the one's complement in practice:**

| bit values |  +/-  |  64   |  32   |  16   |   8   |   4   |   2   |   1   | Decimal Value |
| :--------- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | ------------: |
| bits       |   0   |   0   |   0   |   0   |   0   |   0   |   0   |   0   |             0 |
| bits       |   1   |   0   |   0   |   0   |   0   |   0   |   0   |   0   |            -0 |

We get two representations for 0, but we only need one.

### Two's complement

Integers are also commonly represented by using [two's complement](https://en.wikipedia.org/wiki/Two%27s_complement) notation, in which the left-most bit indicates the sign: If the leading bit is 1, we subtract 2^{n} to get the [integer](https://en.wikipedia.org/wiki/Integer_(computer_science)) corresponding to an n-bit number in this notation. Two's complement allows performing subtraction using an addition. For example, the arithmetic operation 42-7 is equal to 42+(-7), and plus-minus 7 is the two's complement of minus 7.

**Using the binary number system**:

Unsigned:

- an unsigned byte can express the numbers 0 .. 255
- two unsigned bytes can express the numbers 0 .. 65535

[Signed](https://en.wikipedia.org/wiki/Signed_number_representations) (two's complement):

- a signed byte can express the numbers -128 .. 127
- two signed bytes can express the numbers -32768 .. 32767


For example, -1 is the signed byte 0xff or 0b11111111. In this way, a signed byte can express the numbers -128 .. 127. That means we can use the formula -2^{n-1} to 2^{n-1}-1 to calculate the range.

#### From decimal digit into two's complement

If we want to show a positive representation, we can show this just as in the one's complement, so the sign bit is zero.

If we want to represent 41 in two's complement, we fill in the needed bits.

| bit values |  +/-  |  64   |  32   |  16   |   8   |   4   |   2   |   1   | Decimal Value |
| :--------- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | ------------: |
| bits       |   0   |   0   |   1   |   0   |   1   |   0   |   0   |   1   |            41 |


To show the value of -41 in two's complement, we need to follow a three-step plan.

In the first step, we convert the decimal digit into the positive value in binary.

| bit values |  +/-  |  64   |  32   |  16   |   8   |   4   |   2   |   1   | Decimal Value |
| :--------- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | ------------: |
| bits       |   0   |   0   |   1   |   0   |   1   |   0   |   0   |   1   |            41 |


In the second step, we invert all binary digits so that a 0 converts into a 1 and a 1 converts into a 0. 

In the example with -41 that looks as follows:

| bit values |  +/-  |  64   |  32   |  16   |   8   |   4   |   2   |   1   | Decimal Value |
| :--------- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | ------------: |
| bits       |   1   |   1   |   0   |   1   |   0   |   1   |   1   |   0   |           -86 |

We got the MSB with 1 as the sign bit.

In the third step, we need to add 1 to the result of step two.

| bit values |  +/-  |  64   |  32   |  16   |   8   |   4   |   2   |   1   | Decimal Value |
| :--------- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | ------------: |
| bits       |   1   |   1   |   0   |   1   |   0   |   1   |   1   |   1   |           -87 |

That means the value of -87 is the two's complement representation of -41.

**Complementary value**

If we can represent the highest value with 7 bits, we can represent 2^{7}=128 values. As seen in the last example, we got a complement of -87, which means if we calculate 128-87, we get 41, then we also use the sign bit and get as a result -41. That means a two's complement representation of -41 shows us the [complement](https://en.wikipedia.org/wiki/Method_of_complements) of -41 in that 7-bit range.

**Summary**

For a two's complement representation, we need to follow a three-step plan:

1) Convert the decimal digit into the positive representation of the value.
2) We invert all digits. (0 -> 1 and 1 -> 0)
3) We add 1 to the result of step two.

#### From two's complement into decimal

If we want to convert the two's complement representation of -41 into the decimal digit -41, we need to follow the three converting steps from above but in the other direction.

Two's complement representation of -41:

| bit values |  +/-  |  64   |  32   |  16   |   8   |   4   |   2   |   1   | Decimal Value |
| :--------- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | ------------: |
| bits       |   1   |   1   |   0   |   1   |   0   |   1   |   1   |   1   |           -87 |

In the first step, add 1 to the two's complement representation.

| bit values |  +/-  |  64   |  32   |  16   |   8   |   4   |   2   |   1   | Decimal Value |
| :--------- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | ------------: |
| bits       |   1   |   1   |   0   |   1   |   0   |   1   |   1   |   0   |           -86 |

In the second step, invert all bits.

| bit values |  +/-  |  64   |  32   |  16   |   8   |   4   |   2   |   1   | Decimal Value |
| :--------- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | ------------: |
| bits       |   0   |   0   |   1   |   0   |   1   |   0   |   0   |   1   |            41 |

In the third step, add a leading sign bit.

| bit values |  +/-  |  64   |  32   |  16   |   8   |   4   |   2   |   1   | Decimal Value |
| :--------- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | ------------: |
| bits       |   1   |   0   |   1   |   0   |   1   |   0   |   0   |   1   |           -41 |

With these steps, we generate the decimal number -41 from the two's complement representation.

### Numbers we can represent

In the unsigned range, we can represent:

| Bits | Base 2     | Range                                 |
| ---- | ---------- | ------------------------------------- |
| 8    | 2^8 - 1    | 0 to 255                              |
| 16   | 2^{16} - 1 | 0 to 65,536                           |
| 32   | 2^{32} - 1 | 0 to 4,294,967,296                    |
| 64   | 2^{64} - 1 | 0 to 18,​446,​744,​073,​709,​551,​616 |

In the signed range (one's complement), we can represent:

| Bits | Base 2                    | Range                                                   |
| ---- | ------------------------- | ------------------------------------------------------- |
| 8    | -2^{8-1}-1 to 2^{8-1}-1   | -127 to 127                                             |
| 16   | -2^{16-1}-1 to 2^{16-1}-1 | -32,767 to 32,767                                       |
| 32   | -2^{32-1}-1 to 2^{32-1}-1 | -2,147,483,647 to 2,147,483,647                         |
| 64   | -2^{64-1}-1 to 2^{64-1}-1 | -9,223,372,036,854,775,807 to 9,223,372,036,854,775,807 |


In the signed range (two's complement), we can represent:

| Bits | Base 2                  | Range                                                   |
| ---- | ----------------------- | ------------------------------------------------------- |
| 8    | -2^{8-1} to 2^{8-1}-1   | -128 to 127                                             |
| 16   | -2^{16-1} to 2^{16-1}-1 | -32,768 to 32,767                                       |
| 32   | -2^{32-1} to 2^{32-1}-1 | -2,147,483,648 to 2,147,483,647                         |
| 64   | -2^{64-1} to 2^{64-1}-1 | -9,223,372,036,854,775,808 to 9,223,372,036,854,775,807 |

### Exercises

**Range**

How many numbers can we represent with 32 and 64 bit as 
- an unsigned integer?
- a signed integer in one's complement?
- a signed integer in two's complement?

**Convert**

How can we represent the value -42 with the
- one's complement?
- two's complement?

How can we represent the value -1 with the 
- one's complement?
- two's complement?

How can we represent the value -12 with the 
- one's complement?
- two's complement?

## Arithmetics

### Integer arithmetics

Fortunately, elementary arithmetics with binary numbers work like decimal numbers or any other representation with a base greater than one. For example, adding two numbers in any such representation works by adding their digits from right to left while carrying any overflow to the left. 

#### Examples

**Example**:

Let us add the values 85 and 170. 

Starting from the right, we find that 5+0=5. Thus the rightmost digit of the result is 5.

|       | 10^{2} | 10^{1} | 10^{0} |
| ----- | -----: | -----: | -----: |
|       |        |      8 |      5 |
| +     |      1 |      7 |      0 |
| **=** |        |        |  **5** |

Then, with 8+7=15, the second rightmost digit is 5. Since 15>9, there is an overflow that needs to be considered next. 

|       |    10^{2} | 10^{1} | 10^{0} |
| ----- | --------: | -----: | -----: |
|       |           |      8 |      5 |
| +     |         1 |      7 |      0 |
| **=** | (carry 1) |  **5** |  **5** |

With 1+1=2, we obtain the leftmost digit and the final result of 255. 

|       | 10^{2} | 10^{1} | 10^{0} |
| ----- | -----: | -----: | -----: |
|       |        |      8 |      5 |
| +     |      1 |      7 |      0 |
| **=** |  **2** |  **5** |  **5** |

**Example**:

Let us now add both numbers in binary that is, 01010101 for 85 and 10101010, which is binary for 170. It works in just the same way. 

|     | 2^{7} | 2^{6} | 2^{5} | 2^{4} | 2^{3} | 2^{2} | 2^{1} | 2^{0} |          |
| --- | ----- | ----- | ----- | ----- | ----- | ----- | ----- | ----- | -------- |
|     | 0     | 1     | 0     | 1     | 0     | 1     | 0     | 1     | =85      |
| +   | 1     | 0     | 1     | 0     | 1     | 0     | 1     | 0     | =170     |
|     | **1** | **1** | **1** | **1** | **1** | **1** | **1** | **1** | **=255** |

Since 1+0=1, there is no overflow here. Thus the result of 11111111, which is binary for 255, can easily be obtained by just adding the individual digits. 

In general, though, one adds two binary numbers, just like decimal numbers, digit by digit from right to left, while carrying any overflow to the left.

#### Exercises

Convert the decimal numbers into binary (8-bit representation) and add them together:
- 42 + 101 = ?
- 147 + 13 = ?
- 13 + 37 = ?

### Arithmetic overflow

What happens if we try to add two numbers where the result exceeds the number of digits necessary to represent them individually? For example, what if we compute 255+1=256 in binary? 

In this case, we get a binary number with 9 bits rather than the 8 bits representing 255. 

|       | 2^{7} | 2^{6} | 2^{5} | 2^{4} | 2^3}  | 2^{2} | 2^{1} | 2^{0} |
| ----- | ----- | ----- | ----- | ----- | ----- | ----- | ----- | ----- |
|       | 1     | 1     | 1     | 1     | 1     | 1     | 1     | 1     |
| +     | 0     | 0     | 0     | 0     | 0     | 0     | 0     | 1     |
| **1** | **0** | **0** | **0** | **0** | **0** | **0** | **0** | **0** |

If we have more than 8 bits, this is not a problem. However, with computers, everything is finite, in particular memory. 
 
Moreover, arithmetic operations are on most machines implemented for bit strings with a fixed size, such as 8 bits. On such machines adding 11111111 and 00000001 results in what is called arithmetic overflow.

[Arithmetic Overflow](https://en.wikipedia.org/wiki/Arithmetic_overflow): This occurs when an arithmetic operation attempts to create a numeric value too large to be represented within the available storage space.

How can we deal with arithmetic overflow? Two approaches can be combined: detection and semantics. If an arithmetic overflow is detected, one can discard the computation and do something else. 

For this purpose, most processors feature a so-called carry bit or [carry flag](https://en.wikipedia.org/wiki/Carry_flag). The carry flag is set if an arithmetic operation causes an overflow indicated by a carry out of the most significant bit. In our example, the 9-th bit in 100000000 is that carry bit.

In terms of semantics, if the result of an arithmetic overflow has a defined value, one may be able to use that value in a meaningful way. For example, a common semantics for n-bit arithmetics is to compute everything modulo 2^{n}, also referred to as wrap-around semantics, or wrap around. 

For example, 255+1=256 modulo 2^8=256 modulo 256=0, which is precisely what 100000000 in an 8-bit system stands for. Some applications are correct even when such wrap-around occurs.

[Modulo](https://en.wikipedia.org/wiki/Modulo_operation): The remainder after division of one number by another, also called modulus.

Arithmetic overflow nevertheless is the cause of numerous software bugs and even costly accidents. Restricting the space available for representing something that can be arbitrarily large such as numbers, has serious consequences. Integer arithmetics are always an approximation of real arithmetics. For correctness, computer applications need to be appropriately adapted to work for integer arithmetics, not real arithmetics.

---

# Architecture

## Binary vs. Decimal

Computers encode all information in binary representation since they also use a binary representation at the hardware level. For example, 0 is represented by a voltage of -5V or the state not electrically charged and 1, by a voltage +5V or the state electrically charged.

Since the states (i.e., 0 and 1) are represented by different voltage levels on the electrical level, it is better to have only a few states. The reasons for this are based on physics: By things like heat or other electrical disturbances, the voltage levels can be changed easily. So it is easier to compensate for these fluctuations with two different states than it would be with, say, ten states - which would correspond to the decimal system usually used by humans. To distinguish between all states, one would have to increase the generally possible voltage, which would lead to increased power consumption. Additionally, the hardware levels logic to calculate with multiple states would be much more complicated than the case with only two states.

The second reason is that we get a storage problem because decimal numbers need more characters than bits; we talk about three times more characters than the base-2 binary system.

## Von Neumann architecture

Today, most general-purpose computers are based on what is known as the von Neumann model or von Neumann architecture.

[Von Neumann architecture](https://en.wikipedia.org/wiki/Von_Neumann_architecture): A computer architecture, described in 1945 by the mathematician and physicist John von Neumann and others, for an electronic digital computer with parts consisting of a central processing unit (CPU) where arithmetic operations (that part is called an Arithmetic Logic Unit - ALU) are done, and processor registers (those supply operands, the object or quantity to operate on) to the ALU and store the results of ALU operations); a control unit containing an instruction register (to hold the currently executed instruction) and a *program counter* (indicates where a computer is in its program sequence); a memory to store both data and instructions (code); external mass storage; and input and output mechanisms.

**von Neumann architecture**

- Central Processing Unit (CPU)
	+ Arithmetic Logic Unit (ALU)
		* that does arithmetic operations
	+ Processor registers
		* that supply operands, the object or quantity that is operated on
	+ Control unit
		* Instruction register
			- to store the currently executed instruction
		* Program counter
			- indicates where a computer is in its program sequence
- Memory that stores data and instructions
- External mass storage
- Input and output mechanisms

A von Neumann machine is a [stored-program computer](https://en.wikipedia.org/wiki/Stored-program_computer), which stores both code and data in the same memory. In fact, in memory, there is no distinction between code and data. A von Neumann machine fetches code from memory and executes it. The code will, in turn, instruct the machine to load data from memory into registers, perform some computation on registers, and finally store the results back in memory. 

**fetching vs. loading from memory**

It is essential to understand that bits fetched from memory and executed happen to represent code at that given moment while bits loaded from memory into registers, then modified, and finally stored back in memory represent data at that given moment.

### Central Processing Unit (CPU)

In selfie, the von Neumann architecture is a 64-bit machine, which means the CPU has a bit-width of 64-bit. It also contains 32 general-purpose registers (processor registers) with 64-bit. With five bits, we can talk to all 32 general-purpose registers (2^{5}), where the ID's go from 0 to 31. 

The 32 general-purpose registers in selfie are defined as Global Constants:

Global [Constant](https://en.wikipedia.org/wiki/Constant_(computer_programming)): A constant with global scope, meaning that it is visible (hence accessible) throughout the program and the program cannot alter its value during normal execution, i.e., the value is constant.

| Label | Register Address |
| --- 	| ---	|
|	ZR	|  = 0	|
|	RA	|  = 1	|
|	SP	|  = 2	|
|	GP	|  = 3	|
|	TP	|  = 4	|
|	T0	|  = 5	|
|	T1	|  = 6	|
|	T2	|  = 7	|
|	FP	|  = 8	|
|	S1	|  = 9	|
|	A0	|  = 10	|
|	A1	|  = 11	|
|	A2	|  = 12	|
|	A3	|  = 13	|
|	A4	|  = 14	|
|	A5	|  = 15	|
|	A6	|  = 16	|
|	A7	|  = 17	|
|	S2	|  = 18	|
|	S3	|  = 19	|
|	S4	|  = 20	|
|	S5	|  = 21	|
|	S6	|  = 22	|
|	S7	|  = 23	|
|	S8	|  = 24	|
|	S9	|  = 25	|
|	S10	|  = 26	|
|	S11	|  = 27	|
|	T3	|  = 28	|
|	T4	|  = 29	|
|	T5	|  = 30	|
|	T6	|  = 31	|

In the CPU, an [arithmetic logic unit](https://en.wikipedia.org/wiki/Arithmetic_logic_unit) (ALU) is a combinational digital circuit that performs arithmetic and [bitwise operations](https://en.wikipedia.org/wiki/Bitwise_operation) on integer binary numbers.
The inputs to an ALU are the data to be operated on, called [operands](https://en.wikipedia.org/wiki/Operand), and a code indicating the operation to be performed; the ALU's output is the result of the performed operation. 

#### Examples

When we talk about the von Neumann architecture in selfie, one would ask where it is defined or how we could read the different parameters up?

In the Github Repository, we can look into the `selfie.c` file to clear that up. 

For example, if we want to know with how many bits the CPU architecture in selfie is defined, we can search for `WORDSIZEINBITS`, and there we find `uint64_t WORDSIZEINBITS = 64; // 8 * WORDSIZE`, which means the CPU's bit-width is 64-bit or 8-byte.

#### Exercises

Search in the `selfie.c` file: 

- How many registers are implemented in selfie? 
- What is the size of an unsigned integer in selfie?

### Program Counter (PC)

How does a computer know what to execute? After all, the bits in memory could mean anything. They could be code; they could be data, anything. But the answer to that question can anyway not be any more straightforward.

Processors based on the von Neumann architecture feature a special-purpose register as part of their control unit called the program counter (PC). The PC in selfie is a special-purpose 64-bit register.

[Program Counter (PC)](https://en.wikipedia.org/wiki/Program_counter): A processor register that indicates where a computer is in its program sequence. In most processors, the PC is incremented after fetching an instruction and holds the memory address of (points to) the next instruction that would be executed. Instructions are usually fetched sequentially from memory, but control transfer instructions change the sequence by placing a new PC value. These include branches (sometimes called jumps), subroutine calls, and returns. 

- A control transfer on some assertion's truth lets the computer follow a different sequence under different conditions. 
- A branch provides that the next instruction is fetched from somewhere else in memory. 
- A subroutine call not only branches but saves the preceding contents of the PC somewhere. 
- A return retrieves the PC's saved contents and places it back in the PC, resuming sequential execution with the instruction following the subroutine call.

Each instruction instructs the processor to perform some computation and determines the next value of the PC so that the processor knows where in memory the next instruction is stored. That sequence of PC values is called control flow.

[Control Flow](https://en.wikipedia.org/wiki/Control_flow): The order in which individual statements, instructions, or function calls of an imperative program are executed or evaluated. The emphasis on explicit control flow distinguishes an imperative programming language from a declarative programming language.

[Imperative Programming](https://en.wikipedia.org/wiki/Imperative_programming): A programming paradigm that uses statements that change the program's state. In much the same way that the imperative mood in natural languages expresses commands, an imperative program consists of commands for the computer to perform. Imperative programming focuses on describing how a program operates.

Many programming languages support imperative programming, but it is not the only programming paradigm. Declarative programming is an important alternative that is also supported by many programming languages but handles program state differently.

[Declarative Programming](https://en.wikipedia.org/wiki/Declarative_programming): A programming paradigm - a style of building the structure and elements of computer programs - expresses the logic of a computation without describing its control flow.

Intuitively, rather than saying imperatively how to change state, declarative programming focuses on declaring what needs to change. While spelling out how to change state can become tedious with imperative programming spelling out what to change can become burdensome with declarative programming. Yet both paradigms have their essential use cases, and a port of selfie to a declarative programming language would be very nice to have but remains future work for now.

### Random access memory (RAM)

The great thing about a von Neumann architecture is that it stores code and data in the same memory. In selfie, the main memory has 4 GB, which means 2^{32} bytes or 2^{35} bits of memory are available for use. 

How do we get to such numbers? 


When writing 4 GB in scientific notation, we get: 

2^{2} \* 2^{30} \* 2{3} = 2{35}

Where: 

- Quantity of 4 = 2^{2}, 
- 2^{30} stands for Giga and 
- 2^{3} stands for 8 when we convert from bytes to bits.

We know that 4 GB of memory are 2^{35} bit, but how is that memory split up into smaller pieces?

Most registers of a CPU have the same size, that is, accommodate the same number of bits. Usually, data goes back and forth between memory and registers in chunks of that size called machine words or just words.

[Word](https://en.wikipedia.org/wiki/Word_(computer_architecture)): The natural unit of data used by a particular processor design. A word is a fixed-sized piece of data handled as a unit by the instruction set or the processor's hardware. The number of bits in a word (the word size, word width, or word length) is an essential characteristic of any specific processor design or computer architecture.

Usually, a single word has 32 bit, as we can see in `selfie.c`. That means a double word has 64 bit, but for simplification, when we talk about a word in selfie, we mean 64 bit.

The processor (CPU) that the mipster emulator in selfie implements has a size of 64 bits. Virtually everything on that machine happens at the level of words. Loading data from memory and storing it back, arithmetic and logical operations among registers, and even fetching code from memory for execution. The reason is again performance. Involving 64 bits in parallel in all operations is faster than working with bits individually. However, there are two more reasons why we use a 64-bit machine. The first reason is that the size of an integer in C\* (a subset of C) is also 64 bits. That means that a single mipster register can hold precisely one C\* integer value.

[Emulator](https://en.wikipedia.org/wiki/Emulator): Software that enables one computer system (called the host) to behave like another computer system (called the guest).

How many different integer values can 64 bits represent? Well, 2^{64} values, but what are they? 
That depends on how we interpret them. In C\*, integers are interpreted as unsigned; an integer value is either zero or positive.

> An unsigned integer in C\* can in total represent integer values i from 0 to 18446744073709551615 = 2^{64}-1. 
> In `selfie.c`, that value is called `UINT64_MAX` which is the largest unsigned 64-bit integer value.

However, we may also interpret 64-bit integers as signed integers in two's complement, with the MSB encoding the sign and the remaining 63 LSBs encoding the value. The number of different integer values that can be represented is nevertheless the same.

> A signed 64-bit integer can in total represent values from -9223372036854775808 to 9223372036854775807 since -2^{64-1} to 2^{64-1}-1. 
> In `selfie.c`, the largest positive signed integer value is defined as `INT64_MAX` while the smallest negative value is `INT64_MIN`.

The second reason for using 64-bit words is that memory addresses in mipster and ultimately in C\* are then 64 bits. In particular, that means that a register's content can also be seen as a memory address and not just an integer value. However, there is one crucial detail. On a mipster machine, memory is not only byte-addressed but also word-aligned for access. That means that words can only be accessed in memory at addresses that are multiples of eight, the word size in bytes (64 bits = 8 bytes).

> The byte-addressed and word-aligned memory in mipster can only be accessed in whole words at addresses 0, 8, 16, 24, and so on. 
> These addresses are values in bytes. The word at address 0, for example, then contains the eight bytes at addresses 0, 1, 2, 3, 4, 5, 6, and 7.

1. word = 0
2. word = 8
3. word = 16
4. word = 24
5. word = ...

On a mipster machine, the 64 bits of a word can encode characters, integers, memory addresses, and machine instructions.

#### Examples

The string literal `"Hello World!    "` is stored in two 64-bit words located contiguously in memory accommodating the substrings `"Hello Wo"` and `"rld!    "` as well as the value 0 (null) in the third word to terminate the string. The ASCII code of the letter `H` is stored in the eight LSBs of the first word, the ASCII code of the following letter `e` in the eight bits directly to the left of the eight LSBs, and so on.

#### Exercises

Search in the `selfie.c` file:

- What is the number of registers in the CPU?
- What is the word size in bits?

Calculate:

- How many states can we store in 4 GB of main memory?
- How many states can we store in the von Neumann architecture of selfie? (all components of the CPU and the main memory)
- How many words can we address in 4 GB of main memory?
- How many bits do we need to talk to all possible words in 4 GB?

### Memory Bus

In a machine that follows a von Neumann architecture, the bandwidth between the CPU (where all the work gets done) and memory is minimal compared to the amount of memory. 
The main memory and CPU are connected via the memory bus to communicate; this is the bottleneck of a von Neumann machine and the main factor for speed.

The memory bus in selfie has 64 wires to transfer a double word or just word between CPU and main memory. That means we use one wire for each bit.

The von Neumann bottleneck is a limitation on [throughput](https://en.wikipedia.org/wiki/Throughput) (data transfer rate) caused by computer architecture.

[Throughput](https://en.wikipedia.org/wiki/Throughput): Amount of work performed per unit of time.

[Latency](https://en.wikipedia.org/wiki/Latency): Amount of time (or delay) to perform work.

Speed is generally characterized in terms of throughput, the amount of work done per unit of time, and in latency, the amount of time to do some work, particularly before some other work can be done. The difference is explained with a simple example. 

#### Examples

Imagine a fiber optic cable connecting, say, New York City and San Francisco, and a truck loaded with DVDs driving from New York City to San Francisco. 
Which one provides higher throughput and which one lower latency? Surprisingly, it may very well be possible that the truck offers higher throughput. However, delivering just a single bit by truck may take days. Thus the truck provides terrible latency not suitable to host, say, a Zoom call.

| Performance | Unit                                                                                        |
| ----------- | ------------------------------------------------------------------------------------------- |
| throughput  | million instructions per second ([MIPS](https://en.wikipedia.org/wiki/Instructions_per_second))                                                      |
| latency     | nanoseconds (ns), microseconds (us), milliseconds (ms), seconds (s), minutes (m), hours (h) |

## Code vs. Data

A computer cannot distinguish between code and data. It all depends on the context. Something is interpreted as code if the program counter points to the corresponding address in memory, and this word is loaded as instruction into the processor. It is interpreted as data when it gets processed as data. A machine word could be data and code at the same time. As already mentioned, this depends on how it is interpreted.

# Compilers

## Compiler

Compiling selfie.c into an executable program is done by executing `make` in the terminal.


```sh
make
cc -Wall -Wextra -O3 -m64 -D'uint64_t=unsigned long long' selfie.c -o selfie
```

The `make` command invokes the `cc` command, which compiles the file `selfie.c` into a file called `selfie` (without the .c extension) as directed by the `-o` option, ignoring the other options for clarity. In other words, the sequence of bits representing `selfie.c` is changed into another sequence of bits representing `selfie`. The difference between the two sequences is that `selfie.c` represents source code, whereas `selfie` represents machine code.

The key idea is that both sequences are supposed to have the same semantics. However, `selfie` is executable by a computer, whereas `selfie.c` is not, at least not purposefully, yet `selfie.c` is human-readable and writable in particular. The process of changing `selfie.c` into `selfie` is called compilation, which is done by a compiler such as the above cc compiler.

[Machine Code](https://en.wikipedia.org/wiki/Machine_code) A sequence of instructions executed directly by a computer's central processing unit (CPU).

[Compiler](https://en.wikipedia.org/wiki/Compiler) A computer program that transforms source code written in a programming language (the source language) into another computer language (the target language), with the latter often having a binary form known as an object or machine code. The most common reason for converting source code is to create an executable program.

Now we have a version of selfie that we can run on our machine.

```sh
./selfie
```

**Output**:

```sh
synopsis: ./selfie { -c { source } | -o binary | [ -s | -S ] assembly | -l binary } [ ( -m | -d | -r | -y ) 0-4096 ... ]
```

Selfie requires using at least one option to do anything useful and therefore responds with its usage pattern and then terminates without doing anything else. 


To do something useful, we compile selfie with its own compiler named starc that is invoked by the option `-c`.

```sh
./selfie -c selfie.c
```

**Output**:

```sh
./selfie: selfie compiling selfie.c with starc
./selfie: 293026 characters read in 10278 lines and 1384 comments
./selfie: with 175311(59.83%) characters in 42447 actual symbols
./selfie: 401 global variables, 526 procedures, 423 string literals
./selfie: 2555 calls, 1170 assignments, 86 while, 814 if, 465 return
./selfie: symbol table search time was 2 iterations on average and 48626 in total
./selfie: 167872 bytes generated with 38720 instructions and 12992 bytes of data
./selfie: init:    lui: 2141(5.52%), addi: 14078(36.35%)
./selfie: memory:  ld: 6474(16.72%), sd: 6080(15.70%)
./selfie: compute: add: 2944(7.60%), sub: 707(1.82%), mul: 414(1.06%)
./selfie: compute: divu: 73(0.18%), remu: 29(0.07%)
./selfie: compare: sltu: 675(1.74%)
./selfie: control: beq: 904(2.33%), jal: 3667(9.47%), jalr: 526(1.35%)
./selfie: system:  ecall: 8(0.02%)
```

After compiling `selfie.c` starc only stores the machine code internally but does not write it to a file. To do that, we need to use the `-o` option:

```sh
./selfie -c selfie.c -o selfie.m
```

The command produces a file called `selfie.m` that contains machine code compiled from `selfie.c` using the starc compiler in `selfie` rather than the cc compiler. The process is called self-compilation.

## The Emulator

Selfie includes the starc compiler, but it also includes mipster, an emulator of the computer that can execute `selfie.m`, and any other machine code generated by starc.

[Emulator](https://en.wikipedia.org/wiki/Emulator) Software that enables one computer system (called the host) to behave like another computer system (called the guest).

We execute `selfie.m` by first loading it using the `-l` option and then running it by invoking mipster using the -m` option:

```sh
./selfie -l selfie.m -m 1
```

**Output**:

```sh
./selfie: 171968 bytes with 38720 instructions and 12992 bytes of data loaded from selfie.m
./selfie: selfie executing selfie.m with 1MB physical memory on mipster
synopsis: selfie.m { -c { source } | -o binary | [ -s | -S ] assembly | -l binary } [ ( -m | -d | -r | -y ) 0-4096 ... ]
./selfie: selfie.m exiting with exit code 0 and 0.00MB mallocated memory
./selfie: selfie terminating selfie.m with exit code 0
./selfie: summary: 65383 executed instructions [20.45% nops] and 0.17MB(17.57%) mapped memory
./selfie: init:    lui: 27(0.04%), addi: 27228(41.64%)
./selfie: memory:  ld: 14518(22.20%), sd: 9197(14.06%)
./selfie: compute: add: 1574(2.40%), sub: 1433(2.19%), mul: 1740(2.66%)
./selfie: compute: divu: 610(0.93%), remu: 379(0.57%)
./selfie: compare: sltu: 858(1.31%)
./selfie: control: beq: 1121(1.71%), jal: 4460(6.82%), jalr: 2107(3.22%)
./selfie: system:  ecall: 131(0.20%)
./selfie: profile: total,max(ratio%)@addr,2max,3max
./selfie: calls:   2107,611(28.99%)@0x34E0,327(15.51%)@0x36F4,327(15.51%)@0x3E0C
./selfie: loops:   184,75(40.76%)@0x56E4,63(34.23%)@0x194,45(24.45%)@0x4F08
./selfie: loads:   14518,611(4.20%)@0x34F4,611(4.20%)@0x34F8,611(4.20%)@0x3508
./selfie: stores:  9197,611(6.64%)@0x34E4,611(6.64%)@0x34EC,327(3.55%)@0x36F8
./selfie: CPU+memory:    reads+writes,reads,writes[reads/writes]
./selfie: heap segment:  862,674,188[3.58]
./selfie: gp register:   2810,2809,1[2809.00]
./selfie: data segment:  3116,3093,23[134.47]
./selfie: ra register:   8172,4086,4086[1.00]
./selfie: sp register:   44852,29129,15723[1.85]
./selfie: s0 register:   14231,10272,3959[2.59]
./selfie: stack total:   67255,43487,23768[1.82]
./selfie: stack segment: 19738,10751,8987[1.19]
./selfie: a0 register:   6093,1996,4097[0.48]
./selfie: a1 register:   121,0,121[0.00]
./selfie: a2 register:   121,0,121[0.00]
./selfie: a6 register:   1,0,1[0.00]
./selfie: a7 register:   131,0,131[0.00]
./selfie: args total:    6467,1996,4471[0.44]
./selfie: t0 register:   28395,14202,14193[1.00]
./selfie: t1 register:   12774,6394,6380[1.00]
./selfie: t2 register:   3076,1538,1538[1.00]
./selfie: t3 register:   252,126,126[1.00]
./selfie: temps total:   44497,22260,22237[1.00]
```

After loading `selfie.m`, the `-m 1` option directs mipster to emulate a computer with 1 megabyte of memory (abbreviated 1MB) for executing `selfie.m`. Since `selfie.m` is invoked without any options, which could appear after the `-m 1` option, it responds, just like selfie without options before, with its usage pattern and then terminates after that mipster terminates and outputs a summary of its built-in performance profiler.

[Profiling](https://en.wikipedia.org/wiki/Profiling_(computer_programming)) A form of dynamic program analysis that measures, for example, the space (memory) or time complexity of a program, the usage of particular instructions, or the frequency and duration of function calls. Most commonly, profiling information serves to aid program optimization.

Profiling is also used to explain performance-related issues in selfie. 

We can also have mipster execute machine code generated by starc without writing the code into a file:

```sh
./selfie -c selfie.c -m 1
```

The output is like before except for the approximate source code line numbers in the profile.

**Example**

We now compile `selfie.c` with starc and then execute the generated machine code on mipster only to have that code compile selfie.c again, all in the same run.

```sh
./selfie -c selfie.c -m 3 -c selfie.c
```

We can verify that starc generates the same machine code independently of whether it runs directly on our machine or mipster. We have starc generate machine code into two different files called `selfie1.m` and `selfie2.m`.

```sh
./selfie -c selfie.c -o selfie1.m -m 3 -c selfie.c -o selfie2.m
```

Both files generated by starc are indeed identical. To verify that, we use the `diff` command.

```sh
diff -s selfie1.m selfie2.m
```

Output

```sh
Files selfie1.m and selfie2.m are identical.
```

## Instructions

The code of a mipster machine is represented by a sequence of machine words where each 64-bit word encodes, in fact, two rather than one machine instruction since each instruction only requires 32 bits. It is that easy and accurate for many other processors as well. The exact specification of the encoding and the meaning of each instruction is provided by the instruction set architecture or ISA for short.

[Instruction Set Architecture (ISA)](https://en.wikipedia.org/wiki/Instruction_set) The part of the computer architecture related to programming, including the native data types, instructions, registers, addressing modes, memory architecture, interrupt and exception handling, and external I/O. An ISA includes a specification of the set of opcodes (machine language) and the native commands implemented by a particular processor. An instruction set is an interface between a computer's software and its hardware, thereby enabling the independent development of these two computing realms.

We can represent a human-readable version called assembly of the machine code with the following code.

```sh
./selfie -c selfie.c -S selfie.s
```

[Assembly](https://en.wikipedia.org/wiki/Assembly_language): A low-level programming language for a computer, or another programmable device, in which there is a very strong (generally one-to-one) correspondence between the language and the architecture's machine code instructions.

The part of selfie that generates assembly is called a disassembler.

[Disassembler](https://en.wikipedia.org/wiki/Disassembler) A computer program that translates machine language into assembly language - the inverse operation to that of an assembler.

Selfie does not implement an assembler, though.
The starc compiler generates machine code right away without going through assembly first (requiring an assembler to generate machine code from that assembly).

First 10 lines of the `selfie.s` file:

```
0x0(~1): 0x000392B7: lui t0,0x39
0x4(~1): 0xFC028293: addi t0,t0,-64
0x8(~1): 0x00028193: addi gp,t0,0
0xC(~1): 0x00000513: addi a0,zero,0
0x10(~1): 0x0D600893: addi a7,zero,214
0x14(~1): 0x00000073: ecall
0x18(~1): 0x00750513: addi a0,a0,7
0x1C(~1): 0x00800293: addi t0,zero,8
0x20(~1): 0x025572B3: remu t0,a0,t0
0x24(~1): 0x40550533: sub a0,a0,t0
```

What you see is a human-readable version of the machine code in `selfie.m`. The purpose of `selfie.s` is to study `selfie.m` and eventually understand its semantics.

Each line represents one machine instruction.

**Example**

The fifth line `0x10(~1): 0x0D600893: addi a7,zero,214`, for example, reads like this.

The hexadecimal number `0x10` is the 32-bit word-aligned memory address of the instruction in memory.

The expression `(~1)` is the approximate line number of the source code, in this case, `selfie.c`, compiled to this instruction.

The 32-bit word `0x0D600893` is, in fact, the binary encoded version of the instruction itself, and `addi $a7,$zero,214` is the instruction's human-readable assembly version.

This means in particular that `0x0D600893` and `addi $a7,$zero,214` are semantically equivalent. 

The 32-bit word `0x0D600893` in binary stored at address `0x10` in memory is thus the only thing that the machine needs; the rest is for us to make it readable.

## RISC-V

We know that `0x0D600893` represents `addi $a7,$zero,214` because it is specified precisely by the ISA of the open RISC-V processor family.

RISC-V is an open-source architecture we use in this class, and RISC-U is the RISC-V subset targeted, emulated, and virtualized by selfie.

[RISC-V](https://en.wikipedia.org/wiki/RISC-V) an available instruction set architecture (ISA) based on established reduced instruction set computing (RISC) principles. In contrast to most ISAs, the RISC-V ISA can be freely used for any purpose, permitting anyone to design, manufacture, and sell RISC-V chips and software. While not the first open architecture, it is significant because it is designed to be useful in a wide range of devices. The instruction set also has a substantial supporting software body, which avoids new instruction sets' usual weakness.

The mipster emulator implements a strict subset of 64-bit RISC-V instructions, which we call RISC-U. Mipster only implements 14 (32-bit-wide) out of several dozen RISC-V instructions. The starc compiler generates RISC-U code that runs on mipster and is compatible with the official RISC-V toolchain and runs, at least in principle, on real RISC-V processors.

When talking about formal languages, it is essential to distinguish between the [syntax](https://en.wikipedia.org/wiki/Syntax) and the [semantics](https://en.wikipedia.org/wiki/Semantics) of that language.

**Example** 

In the above example, the `addi` string in `addi $a7,$zero,214` is an assembly mnemonic of the operation code or opcode, for short, that identifies the operation to be performed. In contrast, the remaining `$a7,$zero,214` are three operands of that operation.

[Opcode](https://en.wikipedia.org/wiki/Opcode) The portion of a machine language instruction that specifies the operation to be performed. Besides the opcode itself, most instructions also specify the data they will process, in the form of operands.

In our example, `addi` instructs the processor to add the value of the integer `214` to the value stored in register `$zero` (which is always 0) and store the result in register `$a7` (which will thus contain the value 214 after executing the instruction).

A 64-bit RISC-V processor has 32 64-bit registers that can be used for this purpose. They are numbered from 0 to 31. The register `$zero` is the register 0 while the register `$a7`, less obviously, happens to be the register 17. The only missing piece of information is that `addi` is represented by the opcode 19. Now, how do we get from there to `0x0D600893`?

We take:

- the opcode 19 (`0010011`),
- register 17 (`10001`),
- register 0 (`00000`),
- and value 214 (`000011010110`) 
 
and put them together in binary as follows:

`000011010110 00000 000 10001 0010011`

If you merge that into a 32-bit word, you get `0x0D600893`.

The RISC-V ISA specifies that:

- The twelve MSBs encode the third operand value 214, in 12-bit two's complement, in fact, so it could even be a negative value.
- The next five bits encode the second operand register 0, followed by three bits set to 0.
- The next five bits encode the first operand register 17.
- The remaining seven LSBs then encode the opcode 19.

The third operand is treated by `addi` as an integer value rather than, say, a number identifying a register, which is called immediate addressing hence the `i` in `addi`. Immediate addressing is one of the various so-called addressing modes.

[Addressing Mode](https://en.wikipedia.org/wiki/Addressing_mode) An aspect of the instruction set architecture in most central processing unit (CPU) designs. The various addressing modes defined in a given instruction set architecture to define how machine language instructions in that architecture identify each instruction's operand(s).

But why does the ISA provision five bits for the first and second operand? Because five bits allow us to address exactly the 2^{5}=32 different machine registers. The opcode's seven bits allow us to distinguish up to 2^{6}=64 different opcodes, but we do not need that many. Now, think about the range of values that can be encoded in two's complement in the twelve bits for the third operand! This is the range of values that we can get into a register, such as `$a7` with a single `addi` instruction. In other words, we can use that instruction to initialize registers. 

Note that the value in register `$zero` is assumed to be 0 at all times. This is, in fact, needed for initializing registers using the `addi` instruction. There exists RISC-U assembly in which such intention is made explicit by using pseudo instructions. Here, the pseudo instruction `movi $a7,214`, for example, could be used instead but would anyhow be a short version of `addi $a7,$zero,214`. The remaining thirteen instructions of RISC-U are introduced later.
