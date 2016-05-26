# 2. Logic and Numbers

{#logic}

There are a few things to clarify before going into more detail. Digital computers encode everything, data as well as code, in bits. A key insight to understanding how they work is that all the bits stored in a computer's memory and on a computer's storage device and even all the bits communicated across a network of computers have no a-priori meaning whatsoever. They are just bits. It is only the operations with and on them that give them meaning. We even need to tell a computer which bits are actually meant to be treated as code rather than data and should thus be loaded into its processor and be executed. That code directs the processor to manipulate the remaining bits (and sometimes even the code bits themselves if they represent so-called self-modifying code) to perform a computation. The behavior of the code is ultimately determined by the construction of the processor and the system in which it is embedded. However, in the end a computer does nothing but manipulating impressive amounts of bits.

Since everything is encoded in bits, computer science is on a very abstract level all about *strings*, sequences of characters, which may be sequences of bits but also, for convenience and performance, but not necessity, sequences of any kind of symbols. The text you are reading here is just that, a sequence of so-called *ASCII* characters. ASCII is a standard that maps 7-bit sequences to characters so that computers, which store the text you are reading here in such 7-bit sequences, can be programmed to map them to human readable characters for showing them on a screen. Conversely, when pressing a key on a keyboard the 7-bit sequence for the character represented by that key is generated for further processing. By the way, 7 bits can encode 128 different sequences enabling 128 different ASCII characters. This used to be enough but has long been advanced to many other standards with UTF-8 the most popular right now. Newer standards support more characters (emojis!) yet without changing the principle. In particular, any such standard is unnecessary for the machine. It is just for our convenience and performance. If we could read bit strings naturally these standards would be unnecessary and our keyboards only had two keys. The same is also true for other human-machine interfaces such as touch screens and audio speakers. They dramatically increase the performance of human-machine interaction but ultimately do not change what can in principle be computed.

Sure, you may say that for proper interaction we still need to agree on what those bit strings mean but that problem also exists with ASCII strings and in general with any kind of signal. Computers really create meaning by how they manipulate bits. Computer science and thus this book is about giving these purely syntactic, meaningless bit strings a *semantics*, that is, a meaning that we can all agree on. Fortunately, there are certain kinds of objects that have well-understood and widely agreed upon semantics, for example: natural numbers! The semantics of natural numbers, like all semantics, is given by operations on them, so in this case by *arithmetics*. The importance of natural numbers and the fortunate fact that many operations on them can be approximated *effectively* and then performed *efficiently*, if represented as bit strings in a certain way, has made them an integral part of any modern processor. We will therefore look at how this is done to the extent necessary. Other important objects that enjoy formal semantics and effective and efficient implementations such as real numbers, for example, are not covered in this book since they do not add anything beyond what the treatment of natural numbers can do for us here.

To facilitate subsequent discussions, we are now going, in a bit more detail, over the basics of (1) strings, as universal representation of information, (2) positive and (3) negative numbers, as effective and efficient example of using bit strings for representation.

## Strings

Q> What is the difference between mathematics and computer science?
Q>
Q> Mathematics is about numbers (among other things), computer science is about strings!

*Strings*, in contrast to numbers, are the fundamental object of discourse in computer science. Anything can be seen as and represented by a string. Digital computers happen to represent everything in *bit strings*, sequences of bits where each *bit* may either be 0 or 1. Thus the *alphabet* of digital computers only consists of 0 and 1, also called the *Boolean values*.

X> We will use the following 8-bit bit string as running example: 01010101

[String](https://en.wikipedia.org/wiki/String_(computer_science) "String")
: A finite sequence of characters taken from some finite alphabet.

[Bit](https://en.wikipedia.org/wiki/Bit "Bit")
: The basic unit of information in computing and digital communications. A bit can have only one of two values which are most commonly represented as either a 0 or 1. The term bit is a portmanteau of binary digit.

In principle, a computer could operate on the level of individual bits. However, processing information in larger chunks in parallel generally increases performance. For example, some early computers were able to operate on the level of *bytes*, eight bits, at once. Nowadays computers process information on the level of *words*, that is, two (16 bits), four (32 bits), eight (64 bits), or even sixteen bytes (128 bits), at once. Unless stated otherwise, we use the term word, in the context of machine models, to denote four bytes (32 bits).

X> Since 01010101 contains 8 bits it is also an example of a byte.

[Byte](https://en.wikipedia.org/wiki/Byte "Byte")
: A unit of digital information in computing and telecommunications that most commonly consists of eight bits.

[Word](https://en.wikipedia.org/wiki/Word_(computer_architecture) "Word")
: A term for the natural unit of data used by a particular processor design. A word is basically a fixed-sized group of digits that are handled as a unit by the instruction set or the hardware of the processor. The number of digits in a word (the word size, word width, or word length) is an important characteristic of any specific processor design or computer architecture.

Now, how do we actually encode *characters* other than 0 and 1 using, well, 0s and 1s? Easy. We only need to write down the characters we would like to encode and then define a (surjective) mapping from bit strings to characters. The first such definition was ASCII which is actually bijective for 7-bit strings. Since bytes became later the norm as the unit of data in many computers ASCII was extended to eight bits. For example, the most recent extension is the UTF-8 standard, which is the most popular such standard today.

X> According to the ASCII and UTF-8 standards 01010101 stands for the uppercase letter U.

T> The first lesson to learn here is that for a computer 01010101 is still just 01010101 and not the letter U.
T>
T> The only thing we did is that we wrote down a mapping from bit strings to characters, something a computer is not aware of. Only if we program the computer to, say, draw the shape of the letter U on a screen that mapping also exists for the computer. However, even then there is no semantics yet. Read on for that.

[Character](https://en.wikipedia.org/wiki/Character_(computing) "Character")
: A unit of information that roughly corresponds to a grapheme, grapheme-like unit, or symbol, such as in an alphabet or syllabary in the written form of a natural language. Examples of characters include *letters*, numerical *digits*, common *punctuation marks* (such as "." or "-"), and *whitespace*. The concept also includes *control characters*, which do not correspond to symbols in a particular natural language, but rather to other bits of information used to process text in one or more languages. Examples of control characters include *carriage return* or *tab*, as well as instructions to printers or other devices that display or otherwise process text.

[American Standard Code for Information Interchange (ASCII)](https://en.wikipedia.org/wiki/ASCII "American Standard Code for Information Interchange (ASCII)")
: 7-bit encoding scheme for 128 characters: numbers 0 to 9, lowercase letters a to z, uppercase letters A to Z, basic punctuation symbols, control codes that originated with Teletype machines, and a space.

[UTF-8](https://en.wikipedia.org/wiki/UTF-8 "UTF-8")
: (Universal Character Set Transformation Format - 8-bit) A character encoding capable of encoding all possible characters (called code points) in Unicode. The encoding is variable-length and uses 8-bit code units. It is designed for backward compatibility with ASCII.

## Numbers

Let us now focus on *numbers*. Arithmetics defines the semantics of natural numbers. Since virtually all modern processors feature arithmetic instructions for, say, the elementary operations addition, subtraction, multiplication, and division of (bounded versions of) natural numbers computers can be thought of "knowing" what numbers are, even if they have no code to run. The semantics is already implemented by the silicon of the processor. Important for us is to understand how numbers are represented by bit strings and other notational systems.

[Number](https://en.wikipedia.org/wiki/Number "Number")
: A mathematical object used to count, measure, and label. The original examples are the *natural numbers* 1, 2, 3, and so forth.

Before worrying about how to represent numbers using bit strings we step back for a moment and look at the arguably most naive way of representing numbers. Say, we would like to represent the (decimal) number 10. We could just write ten 1s, that is, 1111111111. This scheme has actually been around for a long time and is called *unary* code. It only uses a single digit hence the name.

Using one more digit, say, 0 takes us to *binary* code. The (decimal) number 10 in binary is 1010 because the value of a digit in binary is computed with *base* or *radix* 2, rather than base 10 in, well, decimal code. So, 1010 in binary is equal to 1\*2^3^+0\*2^2^+1\*2^1^+0\*2^0^=8+0+2+0=10 in decimal. Other popular notations are *octal* code with base 8 and *hexadecimal* code with base 16. The (decimal) number 10 in octal is 12 (1\*8^1^+2\*8^0^=8+2=10) and in hexadecimal the letter A (10\*16^0^=10 since A stands for the value ten; the letters B, C, D, E, and F stand for the values eleven, twelve, thirteen, fourteen, and fifteen, respectively). The reason both notations are popular is because a digit in octal and hexadecimal represents three and four bits, respectively, making them convenient for representing binary code. Since a byte consists of two four bit strings, also called *nibbles*, hexadecimal code is particularly convenient for representing byte-aligned binary code. It takes exactly two hexadecimal digits to denote a byte.

Q> Have you noticed the enormous difference in length between unary and binary numbers?
Q>
Q> For example, 85 in unary obviously requires more than ten times more digits than the 8 bits of 01010101.
Q>
Q> In fact, the situation is worse since 7 bits are actually enough to represent 85. Even worse, 7 bits can represent up to 128 different values, that is, in the representation chosen here, all decimal numbers between 0 and 127 inclusive. Thus unary requires up to eighteen times more digits than a 7-bit binary number. One more bit almost doubles the difference. Then, unary needs up to 32 times more digits than an 8-bit binary number.

The fundamental reason for the difference in size between different notations is that any code with a base greater than one is *exponentially* more succinct than unary code. However, codes with base greater than one are only different in size by a *constant factor*. For example, octal and hexadecimal code is only three and four times, respectively, more succinct than binary code. A larger alphabet makes even less of a difference, that is, *logarithmically* less in the size of the alphabet. ASCII, for example, is only seven times more succinct than binary code although there are 128 ASCII characters.

| Encoding | Alphabet | Base (Radix, Size of Alphabet) | # Digits in Values {$$}n>1{/$$} | # Values in Digits {$$}n>0{/$$} |
| - | - | -: | -: | -: |
| [Unary](https://en.wikipedia.org/wiki/Unary_numeral_system "Unary") | {1} | 1 | {$$}n{/$$} | {$$}n{/$$} |
| [Binary](https://en.wikipedia.org/wiki/Binary_number "Binary") | {0,1} | 2 | {$$}\lceil\frac{log(n)}{log(2)}\rceil{/$$} | {$$}2^n{/$$} |
| [Octal](https://en.wikipedia.org/wiki/Octal "Octal") | {0,1,2,3,4,5,6,7} | 8 | {$$}\lceil\frac{log(n)}{log(8)}\rceil{/$$} | {$$}8^n{/$$} |
| [Decimal](https://en.wikipedia.org/wiki/Decimal "Decimal") | {0,1,2,3,4,5,6,7,8,9} | 10 | {$$}\lceil\frac{log(n)}{log(10)}\rceil{/$$} | {$$}10^n{/$$} |
| [Hexadecimal](https://en.wikipedia.org/wiki/Hexadecimal "Hexadecimal") | {0,1,2,3,4,5,6,7,8,9, | 16 | {$$}\lceil\frac{log(n)}{log(16)}\rceil{/$$} | {$$}16^n{/$$} |
| | A,B,C,D,E,F} | | | |

Once again note that 01010101 may stand for the (decimal) number 85 or the letter U or any other object. It is only the operations on 01010101 that define its semantics.

T> Some programming languages feature certain prefixes that determine if a number is meant to be interpreted as binary, octal, decimal, or hexadecimal.
T>
T> Standard prefixes are "0b" for binary, "0" for octal, nothing for decimal, and "0x" for hexadecimal, that is, our example may be written 0b01010101 = 0125 = 85 = 0x55.

Fortunately, elementary arithmetics works for binary numbers just like it does for decimal numbers or any other code with base greater than one. For example, adding two numbers in any such code works as usual by adding their digits from right to left while carrying any *overflow* to the left. Only unary code is different! Elementary arithmetics with unary code is done by, imagine, *string concatenation*.

X> Let us add 85 and, say, 170.
X>
X> Remember from school? Starting from the right we find that 5+0=5. Thus the rightmost digit of the result is 5. Then, with 8+7=15 the second rightmost digit is 5. Since 15>9 there is an overflow that needs to be considered next. With 1+1=2 we obtain the leftmost digit and the final result of 255.
X>
X> Let us now add both numbers in binary, that is, 01010101 for 85 and 10101010, which is binary for 170. It works in just the same way.
X>
X> Since 1+0=1 there is no overflow here. Thus the result of 11111111, which is binary for 255, can easily be obtained by just adding the individual digits. In general though, one adds two binary numbers just like decimal numbers, digit by digit from right to left, while carrying any overflow to the left.
X>
X> Adding both numbers in hexadecimal, that is, 0x55 and 0xAA, works similarly, in this case also without overflow. With 5+A=F the result is 0xFF, which is hexadecimal for 255.

In binary numbers the leftmost and rightmost bits have a meaning similar to the leftmost and rightmost digits in decimal numbers. The rightmost bit, also called *least significant bit*, determines if the number is even or odd. For example, 01010101 represents an odd number whereas 10101010 an even number. The leftmost bit, also called *most significant bit*, represents the greatest value. Thus 10101010 stands for a number larger than 01010101.

[Least Significant Bit (LSB)](https://en.wikipedia.org/wiki/Least_significant_bit "Least Significant Bit (LSB)")
: The bit in a binary number that appears rightmost and determines if the number is even (0) or odd (1).

[Most Significant Bit (MSB)](https://en.wikipedia.org/wiki/Most_significant_bit "Most Significant Bit (MSB)")
: The bit in a binary number that appears leftmost and has the greatest value.

Now, what happens if we try to add two numbers where the result exceeds the number of digits necessary to represent them individually? For example, what if we compute 255+1=256 in binary? In this case, that is, 11111111+00000001, the result is 100000000, a binary number with 9 bits rather than the 8 bits representing 255. This is not a problem if we have more than 8 bits. However, with computers everything is finite, in particular memory. Moreover, arithmetic operations are on most machines implemented for bit strings with a fixed size such as 8 bits. On such machines adding 11111111 and 00000001 results in what is called *arithmetic overflow*.

[Arithmetic Overflow](https://en.wikipedia.org/wiki/Arithmetic_overflow "Arithmetic Overflow")
: Occurs when an arithmetic operation attempts to create a numeric value that is too large to be represented within the available storage space.

How can we deal with arithmetic overflow? There are two approaches that can be combined: detection and semantics. If the occurrence of an arithmetic overflow can be detected one can discard the computation and do something else. For this purpose most processors feature a so-called *carry bit* or *carry flag* which is set if an arithmetic operation causes an overflow indicated by a *carry out of the most significant bits*. In our example, the 9-th bit in 100000000 is that carry bit.

In terms of semantics, if the result of an arithmetic overflow has a defined value, one may be able to use that value in a meaningful way. For example, a common semantics for n-bit arithmetics is to compute everything modulo 2^n^, also referred to as *wrap-around semantics* or just *wrap around*. For example, 255+1=256 modulo 2^8^=256 modulo 256=0, which is exactly what 100000000 in an 8-bit system stands for. There are applications that are correct even when such wrap-arounds occur.

[Modulo](https://en.wikipedia.org/wiki/Modulo_operation "Modulo")
: The remainder after division of one number by another, also called modulus.

Arithmetic overflow nevertheless is the cause of numerous software bugs and even costly accidents. Restricting the space available for representing something that can be arbitrarily large such as numbers has serious consequences. Computer arithmetics are always an approximation of real arithmetics. For correctness, computer applications need to be properly adapted to work for computer arithmetics, not real arithmetics. This is the reason why we keep emphasizing that computer science and mathematics are closely related but still quite different.

## Integers

Now, what about subtraction and negative numbers? Ideally, we would like our bit strings to represent not just *positive* but also *negative* numbers, also called *integers*, with elementary arithmetics on them still intact. Obviously, one bit, or more generally one digit, is enough to encode the *sign* of a number, that is, distinguish positive from negative numbers. Fortunately, however, there is an overall encoding scheme that works without changing elementary arithmetics such as addition. In fact, subtraction will work by using addition, as previously discussed, with negative numbers.

[Integer](https://en.wikipedia.org/wiki/Integer "Integer")
: A number that can be written without a fractional component. For example, 21, 4, 0, and −2048 are integers, while 9.75 and 5.5 are not. The set of integers consists of zero (0), the natural numbers (1, 2, 3, ...), also called whole, counting, or positive numbers, and their additive inverses (the negative numbers, that is −1, −2, −3, ...).

T> In computer science integers are sometimes specifically qualified to be *unsigned*. In this case, they are meant to represent zero and positive numbers but no negative numbers. Integers may explicitly be called *signed* to emphasize that they are also meant to represent negative numbers.

So, how can we represent -85 and compute something like, say, 127-85? Again, fortunately, there is a representation of negative numbers that works for any code with base greater than one and makes addition work like subtraction. We simply take the so-called *radix complement* to encode a negative number which only requires us to fix the number of digits that we intend to support. Subtracting a number then works by adding its complement and ignoring the overflow beyond the supported number of digits.

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

Now back to bit strings. How does a computer represent negative numbers? The short answer: the exact same way as in the decimal system, just in binary. In other words, a negative number may be represented in binary by its two's complement (remember binary has base 2). Just like before, the two's complement of a number is computed by taking the ones' complement of that number and adding one to it. This time, however, computing the diminished radix complement, that is, the ones' complement is particularly easy. It is done by simply inverting the bits.

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

Using two's complement for representing negative numbers a byte can in total represent signed integers i from -128 to 127, that is, with -2^8^/2-1 = -2^7^-1 = -129 < i < 128 = 2^7^ = 2^8^/2. Our running example fits these constraints. Moreover, the most significant bit has taken over a different role than before. It indicates if a number is positive or negative. For example, 01111111 represents a positive number whereas 10000000 stands for a negative number.

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

T> There are many other ways to do elementary arithmetics on computers including the handling of overflows! What you have seen here is just the arguably most prevalent choice.
T>
T> Most important for you is to be aware of the issue and know what your choice of system actually does when it comes to numbers.