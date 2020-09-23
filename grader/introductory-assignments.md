# Introductory Assignments

Welcome to the Introduction to Operating Systems supplementary material. This document provides you with content, examples and exercises to help you learn the course content.

## This information is shared via the course's slack channel.

- Lectures
- Recordings
- Class schedule

## Resources

- Lectures
- [Slides](https://www.icloud.com/keynote/0J_SKB-ofwiuxg-lCag-s-gOA#selfie)
- [Selfie: Computer Science for Everyone](https://leanpub.com/selfie)

---

## 1) Introduction

### Bit Representation

First and foremost, as far as the computer is concerned, there is no way to move "past numbers" because, to the computer, everything is a number. A computer stores everything as a series of 0's and 1's. This representation is called a bit. A [bit](https://en.wikipedia.org/wiki/Bit) can only have one of two values, which are most commonly represented as either a 0 or 1. The value 1 means high voltage, and the value 0 means low voltage in computer systems. 

**Example**:

When we write bit values we use the 0b extension in front of the bit-value.

0b101010 = 42 as decimal number

0b101010 = \* symbol in the ASCII table

Here we can see that a series of 0's and 1's can be interpreted in different ways.

### Decimal System

A decimal number is a number represented in base 10, in which there are ten possible values for each digit (0–9). When these digits are concatenated to make strings of numbers, they are interpreted column by column. Beginning at the far right and moving to the left, we have the 1's column, the 10's column, the 100's column, and so forth.  The one's column is 10^{0}=1, and the tens column is 10^{1}=10, the hundreds column is 10^{2}=100, and so forth. 

**Examples**:

For example, with a 4-digit sequence of 1011, the decimal (base 10) interpretation looks as following. For the far-right column, we take 1\*10^{0}=1, the second column from the right is 1\*10^{1}=10, the third column from the right 0\*10^{2}=0 and the far left column 1\*10^{3}=1000. When adding all 4 values 1+10+0+1000 together, we get the value 1011 as a decimal representation.


| 4-digit sequence | 1         | 0         | 1         | 1         | Value  |
| ---------------- | --------- | --------- | --------- | --------- | ------ |
| Notation         | 1\*10^{3} | 0\*10^{2} | 1\*10^{1} | 1\*10^{0} |        |
| Representation   | 1000      | 0         | 10        | 1         | = 1011 |

**Exercise**:

- Write the number 1337 in exponential notation.
- Write the number 267938 in exponential notation.

### Binary Numbers

A [binary number](https://en.wikipedia.org/wiki/Binary_number) is a number represented in base 2, in which there are only 2 possible values for each digit (0 and 1). The 0 and 1 correspond to low and high voltage values stored in a computer. Although it might be possible for a computer to store more than two voltage values and therefore support a base larger than 2, it would be challenging to support the 10 voltage values required to support a base 10 number system in hardware. A familiarity with base 2 helps understand how a computer stores and interprets data.

Binary numbers interpreted that each bit (the name for a binary digit) holds the value 2 raised to an increasing exponent. We begin with the right-most bit (also called the LSB = least significant bit), which holds the value 2^{0}=1, or the one's column. The next bit holds the value 2^{1}=2, or the twos column. In base 10, each column is ten times larger than the one before it. In base 2, each column's value grows by 2. 

**Examples**:

As shown with the base 10 decimal system and a 4-digit sequence of 1011, in the base 2 binary system, we convert the value into a base 10 number. Starting from the right-most or LSB (least significant bit), we calculate 1\*2^{0}=1, the second column from the right is 1\*2^{1}=2, the third column from the right is 0\*2^{2}=0, and the left-most or MSB (most significant bit) is 1\*2^{3}=8. Now we add all 4 values together, 1+2+0+8 = 11. In this interpretation, with a 4-digit sequence, we get the value 11 as base 10 decimal number.

| 4-digit sequence | 1        | 0        | 1        | 1        | Value |
| ---------------- | -------- | -------- | -------- | -------- | ----- |
| Notation         | 1\*2^{3} | 0\*2^{2} | 1\*2^{1} | 1\*2^{0} |       |
| Representation   | 8        | 0        | 2        | 1        | = 11  |

**Exercise**:

- What is a binary number?
- What is the value of the 5-digit sequence 10101?
- What is the value of the 8-digit sequence 10110110?

### MSB & LSB

The most significant bit on the far-left in the binary representation represents the greatest value. The lest significant bit on the right-most can show if a number is even or odd. If the LSB is 1, then it is an even number, and if the LSB is 0, the number is odd.

**Examples**:

| 128 | 64  | 32  | 16  | 8   | 4   | 2   | 1   | Value |
| --- | --- | --- | --- | --- | --- | --- | --- | ----- |
| 0   | 1   | 0   | 1   | 0   | 1   | 0   | 1   | = 85  |

In the example with the value 85, the LSB is 1 so it represents an odd value.

| 128 | 64  | 32  | 16  | 8   | 4   | 2   | 1   | Value |
| --- | --- | --- | --- | --- | --- | --- | --- | ----- |
| 1   | 0   | 1   | 0   | 1   | 0   | 1   | 0   | = 170 |

In the example with the value 170, the LSB is 0 so it represents an even value.

**Exercises**:

- Is the value 101010 even or odd?
- Is the value 111 even or odd?
- Is the value 11101 even or odd?
- Is the value 111110 even or odd?
  

### Byte

Since a unit of eight bits is very common in computer systems there is a well-known term for that unit called a byte.

[Byte](https://en.wikipedia.org/wiki/Byte) : A unit of digital information in computing and telecommunications that most commonly consists of eight bits.

**Examples**:

A bit sequence of 0b10101010 = 170 in decimal notation and consists of 8 bits and represents 1 byte.

So, if we talk about bytes we mean sequences of 8 bits.

### Different Notations

| Encoding    | Alphabet                        | Base (Radix, Size of Alphabet) | # Values in Digits n>0 |
| ----------- | ------------------------------- | ------------------------------ | ---------------------- |
| Unary       | 1                               | 1                              | n                      |
| Binary      | 0,1                             | 2                              | 2^{n}                  |
| Octal       | 0,1,2,3,4,5,6,7                 | 8                              | 8^{n}                  |
| Decimal     | 0,1,2,3,4,5,6,7,8,9             | 10                             | 10^{n}                 |
| Hexadecimal | 0,1,2,3,4,5,6,7,8,9,A,B,C,D,E,F | 16                             | 16^{n}                 |
			

[Radix](https://en.wikipedia.org/wiki/Radix) : The number of unique digits, including zero, used to represent numbers in a positional numeral system.

**Examples**:

|      | Encoding    | Representation |
| ---- | ----------- | -------------- |
| 42   | Binary      | 0b101010       |
| 42   | Octal       | 0o52           |
| 42   | Decimal     | 42             |
| 42   | Hexadecimal | 0x2A           |
| "42" | String      | 42             |
| '*'  | ASCII       | 42             |

### Unary

The [Unary Numeral System](https://en.wikipedia.org/wiki/Unary_numeral_system) is the simplest numeral system to represent natural numbers. 

**Examples**:

The number 42 represented in the unary numeral System:

111111111111111111111111111111111111111111

That are 42 ones in a row. 
