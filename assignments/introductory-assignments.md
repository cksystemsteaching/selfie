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

# 1) Introduction

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

ASCII is used to map characters to 7 bit wide integers and vice versa. So while characters are still integers to a computer, we can use the ASCII map to interpret those integers as human-readable characters that can be printed to a screen.

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

Today, as micro controller or microprocessor systems become increasingly larger, the individual binary digits (bits) are now grouped into 8's to form a single byte.

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

---

# 2) Architecture

## Binary vs. Decimal

Computers encode all information in binary representation since they also use a binary representation at the hardware level. For example, 0 is represented by a voltage of -5V or the state "not electrically charged" and 1, by a voltage +5V or the state "electrically charged".

Since the states (i.e., 0 and 1) are represented by different voltage levels on the electrical level, it is better to have only a few states. The reasons for this are based on physics: By things like heat or other electrical disturbances, the voltage levels can be changed easily. So it is easier to compensate for these fluctuations with two different states than it would be with, say, ten states - which would correspond to the decimal system usually used by humans. To distinguish between all states, one would have to increase the generally possible voltage, which would lead to increased power consumption. Additionally, the hardware levels logic to calculate with multiple states would be much more complicated than the case with only two states.

The second reason is that we get a storage problem because decimal numbers need more characters than bits; we talk about three times more characters than the base-2 binary system.

## Von Neumann architecture

Today, most general-purpose computers are based on what is known as the *von Neumann model* or *von Neumann architecture*.

[Von Neumann architecture](https://en.wikipedia.org/wiki/Von_Neumann_architecture): A computer architecture, described in 1945 by the mathematician and physicist John von Neumann and others, for an electronic digital computer with parts consisting of a *central processing unit* (CPU) where arithmetic operations (that part is called an *Arithmetic Logic Unit* - ALU) are done, and *processor registers* (those supply operands, the object or quantity to operate on) to the ALU and store the results of ALU operations); a *control unit* containing an *instruction register* (to hold the currently executed instruction) and a *program counter* (indicates where a computer is in its program sequence); a *memory* to store both data and instructions (code); external *mass storage*; and *input and output* mechanisms.

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

It is essential to understand that bits *fetched* from memory and executed happen to represent *code* at that given moment while bits *loaded* from memory into registers, then modified, and finally stored back in memory represent *data* at that given moment.

### Central Processing Unit (CPU)

In Selfie the von Neumann architecture is defined as a 64-bit machine, which means the CPU has a bit-width of 64-bit. It also contains 32 general-purpose registers (processor registers) with 64-bit. With just 5 bits, we can talk to all 32 general-purpose registers (2^{5}), where the ID's go from 0 to 31. 

The **32 general-purpose register** in Selfie are defined as **Global Constants**:

**Global [Constant](https://en.wikipedia.org/wiki/Constant_(computer_programming))**: A constant with global scope, meaning that it is visible (hence accessible) throughout the program and the program cannot alter its value during normal execution, i.e., the value is constant.

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

When we talk about the von Neumann architecture in Selfie, one would ask where it is defined or how we could read the different parameters up?

In the Github Repository, we can look into the `selfie.c` file to clear that up. 

For example, if we want to know how many bits the CPU architecture is defined, we could search for `cpubitwidth`, and there we can find `uint64_t CPUBITWIDTH = 64; // double word` that means the CPU's bit-width is 64 or 8-byte. The comment `// double word` will explain under the topic *Random access memory (RAM)*.

#### Exercises

Search in the `selfie.c` file: 

- How many registers are implemented in Selfie? 
- What is the size of a register in Selfie?

### Program Counter (PC)

How does a computer "know" what to execute? After all, the bits in memory could mean anything. They could be code; they could be data, anything. But the answer to that question can anyway not be any more straightforward.

Processors based on the von Neumann architecture feature a special-purpose register as part of their control unit called the *program counter* (PC). The PC in Selfie is a special-purpose 64-bit register.

[Program Counter (PC)](https://en.wikipedia.org/wiki/Program_counter): A processor register that indicates where a computer is in its program sequence. In most processors, the PC is incremented after fetching an instruction and holds the memory address of ("points to") the next instruction that would be executed. Instructions are usually fetched sequentially from memory, but control transfer instructions change the sequence by placing a new PC value. These include branches (sometimes called jumps), subroutine calls, and returns. 

- A *control transfer* on some assertion's truth lets the computer follow a different sequence under different conditions. 
- A *branch* provides that the next instruction is fetched from somewhere else in memory. 
- A *subroutine call* not only branches but saves the preceding contents of the PC somewhere. 
- A *return* retrieves the PC's saved contents and places it back in the PC, resuming sequential execution with the instruction following the subroutine call.

Each instruction instructs the processor to perform some computation and determines the next value of the PC so that the processor "knows" where in memory the next instruction is stored. That sequence of PC values is called *control flow*.

[Control Flow](https://en.wikipedia.org/wiki/Control_flow): The order in which individual statements, instructions, or function calls of an imperative program are executed or evaluated. The emphasis on explicit control flow distinguishes an **imperative programming** language from a **declarative programming** language.

[Imperative Programming](https://en.wikipedia.org/wiki/Imperative_programming): A programming paradigm that uses statements that change the program's state. In much the same way that the imperative mood in natural languages expresses commands, an imperative program consists of commands for the computer to perform. Imperative programming focuses on describing how a program operates.

Many programming languages support imperative programming, but it is not the only programming paradigm. Declarative programming is an important alternative that is also supported by many programming languages but handles program state differently.

[Declarative Programming](https://en.wikipedia.org/wiki/Declarative_programming): A programming paradigm - a style of building the structure and elements of computer programs - expresses the logic of a computation without describing its control flow.

Intuitively, rather than saying imperatively how to change state, declarative programming focuses on declaring what needs to change. While spelling out how to change state can become tedious with imperative programming spelling out what to change can become burdensome with declarative programming. Yet both paradigms have their essential use cases, and a port of Selfie to a declarative programming language would be very nice to have but remains future work for now.

### Random access memory (RAM)

The great thing in a von Neumann architecture is storing code and data in the same memory. In Selfie the main memory is implemented with 4 GB, which means 2^{32} bytes or 2^{35} bits of memory are available for use. 

How do we get to such numbers? 

When write 4 GB in scientific notation, we get: 

2^{2} \* 2^{30} \* 2{3} = 2{35}

Where: 

- Quantity of 4 = 2^{2}, 
- 2^{30} stands for Giga and 
- 2^{3} stands for 8 when we convert from bytes to bits.

Now we know that 4 GB of memory is 2^{35} bit, but how is that large memory split up into smaller pieces?

Most registers of a CPU have the same size, that is, accommodate the same number of bits. Usually, data goes back and forth between memory and registers in chunks of that size called machine words or just words.

[Word](https://en.wikipedia.org/wiki/Word_(computer_architecture)): The natural unit of data used by a particular processor design. A word is a fixed-sized piece of data handled as a unit by the instruction set or the processor's hardware. The number of bits in a word (the word size, word width, or word length) is an essential characteristic of any specific processor design or computer architecture.

Usually, a word has 32 bit, as we can see in `selfie.c`. That means a double word has 64 bit, but for simplification, when we talk about a word in Selfie, we mean 64 bit.

The processor (CPU) that the mipster emulator in Selfie implements has a size of 64 bits. Virtually everything on that machine happens at the level of words. Loading data from memory and storing it back, arithmetic and logical operations among registers, and even fetching code from memory for execution. The reason is again performance. Involving 64 bits in parallel in all operations is faster than working with bits individually. However, there are two more reasons why we use a 64-bit machine. The first reason is that the size of an integer in C\* (a subset of C) is also 64 bits. That means that a single mipster register can hold precisely one C\* integer value.

[Emulator](https://en.wikipedia.org/wiki/Emulator): Software that enables one computer system (called the host) to behave like another computer system (called the guest).

How many different integer values can 64 bits represent? Well, 2^{64} values, but what are they? 
That depends on how we interpret them. In C\* integers are interpreted as *unsigned*, an integer value is either zero or a positive number.

> An unsigned integer in C\* can in total represent integer values i from 0 to 18446744073709551615 = 2^{64}-1. 
> In `selfie.c`, that value is called `UINT64_MAX` which is the largest unsigned 64-bit integer value.

However, we may also interpret 64-bit integers as signed in *two's complement* with the MSB encoding the sign and the remaining 63 LSBs encoding the value. The number of different integer values that can be represented is nevertheless the same.

> A signed 64-bit integer can in total represent signed integer values i from -9223372036854775808 to 9223372036854775807 since -2^{64-1} to 2^{64-1}-1. 
> In `selfie.c`, the largest positive integer value is called `INT64_MAX` while the smallest negative integer value is called `INT64_MIN`.

The second reason for using 64-bit words is that memory addresses in mipster and ultimately in C\* are then 64 bits as well. In particular, that means that a register's content can also be seen as a memory address and not just an integer value. However, there is one crucial detail. On a mipster machine, memory is not only byte-addressed but also word-aligned for access. That means that words can only be accessed in memory at addresses that are multiples of eight, the word size in bytes (64 bits = 8 bytes).

> The byte-addressed and word-aligned memory in mipster can only be accessed in whole words at addresses 0, 8, 16, 24, and so on. 
> These addresses are values in bytes. The word at address 0, for example, then contains the eight bytes at addresses 0, 1, 2, 3, 4, 5, 6, and 7.

1. word = 0
2. word = 8
3. word = 16
4. word = 24
5. word = ...

Let us reflect on that for a moment. So, on a mipster machine, the 64 bits of a word can be used to encode characters, integers, and even memory addresses! That's right, and this is not all. Even machine instructions are represented by words which we will discuss later.

#### Examples

The string literal `"Hello World!    "` is stored in two 64-bit words located contiguously in memory accommodating the substrings `"Hello Wo"` and `"rld!    "` as well as the value 0 (null) in the third word to terminate the string. The ASCII code of the letter `H` is stored in the eight LSBs of the first word, the ASCII code of the following letter `e` in the eight bits directly to the left of the eight LSBs, and so on.

#### Exercises

Search in the `selfie.c` file:

- What is the size of the registers in the CPU?
- What is the word size in Selfie?

Calculate:

- How many states can we store in 4 GB of main memory?
- How many states can we store in the von Neumann architecture of Selfie? (all components of the CPU and the main memory)
- How many words can we address in 4 GB of main memory?
- How many bits do we need to talk to all possible words in 4 GB?

### Memory-bus

In a machine that follows a von Neumann architecture, the bandwidth between the CPU (where all the work gets done) and memory is minimal compared to the amount of memory. 
The main memory and CPU are connected via the memory-bus to communicate; this is the bottleneck of a von Neumann machine and the main factor for speed.

The data-bus in Selfie has 64 wires to transfer a double word or just word between CPU and main memory. That means we use one wire for each bit.

The von Neumann bottleneck is a limitation on [throughput](https://en.wikipedia.org/wiki/Throughput) (data transfer rate)  caused by computer architecture.

[Throughput](https://en.wikipedia.org/wiki/Throughput): Amount of work performed per unit of time.

[Latency](https://en.wikipedia.org/wiki/Latency): Amount of time (or delay) to perform work.

Speed is generally characterized in terms of *throughput*, the amount of work done per unit of time, and *latency*, the amount of time to do some work, particularly before some other work can be done. The difference is usually explained with a simple example. 

#### Examples

Imagine a fiber optic cable connecting, say, New York City and San Francisco, and a truck loaded with DVDs driving from New York City to San Francisco. 
Which one provides higher throughput and which one lower latency? Surprisingly, it may very well be possible that the truck offers higher throughput. However, delivering just a single bit by truck may take days. Thus the truck provides terrible latency not suitable to host, say, a Zoom call.

| Performance | Unit                                                                                        |
| ----------- | ------------------------------------------------------------------------------------------- |
| throughput  | million instructions per second ([MIPS](https://en.wikipedia.org/wiki/Instructions_per_second))                                                      |
| latency     | nanoseconds (ns), microseconds (us), milliseconds (ms), seconds (s), minutes (m), hours (h) |

## Code vs. Data

A computer cannot distinguish between code and data. It all depends on the context. Something is interpreted as code if the program counterpoints the corresponding address in memory, and this word is loaded as instruction into the processor. It is interpreted as data when it gets processed as data. A machine word could be data and code at the same time. As already mentioned, this depends on how it is interpreted.