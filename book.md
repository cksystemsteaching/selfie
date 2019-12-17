# Computer Science for All

### by Christoph Kirsch

#### Acknowledgements

This book is the result of many years of teaching and working with students and colleagues around the world. I am grateful to my group of students and faculty in Salzburg who, over the years, helped me with refining and deepening my understanding of computer science. I am also particularly grateful to my colleague Professor Raja Sengupta at UC Berkeley who challenged me to the point that made me start developing the Selfie Project which is the foundation of this book. The design of the Selfie compiler is inspired by the Oberon compiler of Professor Niklaus Wirth from ETH Zurich. The design of the Selfie microkernel is inspired by microkernels of Professor Jochen Liedtke from University of Karlsruhe.

## Introduction

Computer science is a mystery to so many and yet more and more people use computers every day in one form or another. There are increasingly many people with all kinds of backgrounds other than computer science that may even code every day. At schools, colleges, universities, and companies around the world there is hardly anyone left who is not confronted with the machine and its code. But even for people just using the machine in their hands, on their desks, and in the cloud there is often that unsatisfactory experience of not understanding what is really going on. This book will empower you to turn your smart phone, tablet, and laptop into what they are supposed to be: the most fascinating and powerful tools ever created by humans rather than the seemingly unavoidable nightmare of so many people, amateurs and professionals alike.

We should emphasize that the book is not about how to use any particular device such as a smart phone or an office app such as Word or Excel. There are plenty of books about that. The goal here is more ambitious than that and you will be challenged accordingly. The idea is to explain the absolute basics of computer science in order to develop a fundamental understanding of what software is and how it works in general on any hardware, ultimately enabling you to make informed decisions involving computers and solve whatever computer problem comes along. The key challenge in doing so is to have you understand that everything can in principle be automated by a computer but only by breaking down the solution of a problem into the tiniest steps that a mindless machine can follow. Laying out even the most obvious parts of a solution is in fact what computer scientists do. Seeing that will make you sharpen your mind considerably and even change the way you think.

While a book about computer science for all may sound appealing it actually requires commitment to understand the material even though we tried very hard to simplify everything as much as possible. The reason is that computers and software are so expressive that it is unlikely that any other computational machine in the future will be more expressive. Anything that can be computed can be computed now, provided you have enough time, space, and energy. That power comes with a level of complexity that is unavoidable but a lot of fun to explore.

This book is based on the [Selfie Project](http://selfie.cs.uni-salzburg.at), an educational software system that has grown out of many years of teaching undergraduate and graduate classes in computer science. The key observation is that understanding computer science and software in particular can only be achieved by understanding how software translates all the way down to the machine. Selfie shows how to do that. This may sound difficult but can actually be done in a systematic fashion with a strong focus on basic principles.

Selfie is software that can translate *itself* to code that can be executed by a computer. This is called *self-compilation*. But selfie even includes software that can mimic a computer that can execute the code of selfie. This is called *self-execution*. And, selfie can even do that on behalf of other computers but also itself. This is called *self-hosting*. By now your mind might be spinning but you at least understand why selfie is called selfie.

Why is the *self* so important? Because it shows how meaning is created systematically on a machine. Selfie is software written in some programming language. However, selfie defines the meaning of that language which implies that selfie defines its own meaning. This is very similar to an English dictionary written in English. The only difference is that selfie defines meaning formally in such a way that a machine can run selfie and thus any software written in the language in which selfie is written.

The book begins with a bit of groundwork emphasizing the fact that everything happening on a digital device is encoded in bits, and nothing else. The only reason why these machines are so powerful and in fact computationally universal is the enormous amount of bits they can store and the speed and energy efficiency at which they can manipulate these bits. This insight is key to understanding information technology and therefore emphasized throughout the book. We begin with examples of how every day information such as numbers, characters, text, images, video and even code is all encoded in just bits. We also show how those bits are later decoded back to their original form making them accessible to humans again.

The next topic is a simple yet representative machine model of virtually any digital device available today. The model is in fact a subset of an existing, fully realistic machine that we developed during the course of teaching undergraduate students for two decades. The goal is to enable you to develop an intuition of how computers work on the level of bits, which is surprisingly simple to do. Most of the complexity of modern digital devices is due to performance optimizations which we deliberately leave out to keep things accessible. Instead we focus on developing an early intuition on what code and data is, what the difference is, and the fact that both are anyway encoded in just bits. This chapter also includes a simple model of digital memory and exposes you to fundamental properties that have direct counterparts in the real world, as it is often the case with computer science, such as the decision of whether to throw away something (forget) or keeping it (memorize).

With the machine model in mind, you will appreciate the fact that developing software directly on the machine is possible but too cumbersome and errorprone. It is therefore time to introduce the notion of high-level programming languages and, after that, the notion of software development tools that enable building the most complex systems ever created by humans. Similar to the machine model, we introduce a simple yet representative programming language which is, again, a subset of an existing, in fact still widely used programming language called C. The language we use has also been developed during years of teaching. The idea of this chapter is to show how simple programs written in that language are actually run on a computer using the previously introduced machine model. Here there are plenty of opportunities to point out fundamental questions such as how long and how much memory and energy it takes to solve a problem and whether a problem can be solved at all. The latter, for example, explains why computers sometime become unresponsive for unpredictable amounts of time driving their users mad.

Even the most convenient high-level programming languages are by far not enough to enable developers build the systems we see today. Like all engineers they need tools to do it. Software development tools as a topic is interesting because their design explains a lot about what software is. In fact, the tools define what a program written in a programming language actually means. This is usually done through language translation. Thus exposing you to the design of the tools is key to showing how meaning is given to code, at least in principle. There are fascinating analogies in the real world such as the self-referential paradox that an English dictionary defines the meaning of English using English. The same is true with software development tools. They are usually written in the programming language to which they give meaning. The difference to English though is that there is no paradox here. Showing how that works is our goal. You will then start asking questions about computers you would have never been able to ask before. We envision the outcome to be new insights into what is possible and what is not, enabling you to develop more confidence when it comes to assessing new technology such as artifical intelligence and self-driving cars.

One of the key breakthroughs of recent years is that computation has become a utility just like electricity and water. Cloud computing and, in the near future, edge computing creates enormous potential, just like the reliable availability of power and water. The key enabling technology is virtualization which is a concept whose understanding is elusive even to many computer science students. However, we believe we have found a way to teach virtualization even to broad audiences based on a combination of our machine model, programming language, and tool set. The idea is to demonstrate how software can create the illusion of any machine, in particular the one it runs on, very efficiently. This is another form of self-referentialy that is fundamental in computer science. Seeing that enables you to grasp the full extent of the universality of digital computing.

Readers should be at least 14 years old and planning to obtain or already holding at least a high school degree. The only prerequisite will be an understanding of elementary arithmetic (addition, subtraction, multiplication, and division of whole numbers) and Boolean logic (logical AND, OR, and NEGATION of true and false statements). Both topics are anyway revisited in the book.

## Information

Computer science is about the automation of everything. Think of something you would like to do but then not do it yourself but have a machine do it for you. Whether this is always possible is still being debated but not our concern here. Well, we believe that it is always possible but many people and thus companies often underestimate the enormous complexity involved in seemingly simple tasks such as driving a car. The issue is that whatever problem you are trying to solve you first need to *encode* the *information* involved in solving the problem in such a way that a machine can handle it. And then you need to tell the machine every single step of how to *manipulate* that information which is tedious even for extremely simple tasks such as adding two numbers. Finally, you need to *decode* the result back into something a human can experience.

Let us take a look at an example. Suppose we would like a machine add two decimal numbers, say, 85 and 7. However, a digital computer cannot even handle 85 and 7. It can only handle *bits*, 0s and 1s. So, the first step is to encode 85 and 7 in bits. In fact, we say we encode them as *binary* number. Then we need to tell the machine how to add the two numbers, but not as 85 and 7, but rather in their binary form. Finally, the result will be a number but of course encoded in binary. We therefore need to take those bits and decode them back to a more human-readable form which is hopefully 92.

### Bits

A *bit* is a unit of information that can distinguish exactly two different things. In fact, we say that a bit can be in exactly one out of two different *states*. It can be either 0 or 1, on or off, true or false, or whatever we want to call it. The only thing that is relevant about a bit is that it is always in exactly one out of two states. And the only thing a computer can do is storing bits and changing bits from one state to the other and back, that is, from, say, 0 to 1 and from 1 to 0.

How can then a bit be used to do anything useful beyond that? Well, by taking more than one bit, of course. Let us take two bits. Now, we can suddenly be in *four* different states denoted by, say, 00, 01, 10, and 11, which could be used to encode the decimal numbers 0, 1, 2, and 3, but not more. What if we take three bits? It is then *eight* different states, that is, 000, 001, 010, 011, 100, 101, 110, and 111, which allow us to encode, say, the decimal numbers 0 through 7. By now, we can already anticipate how this continues. With each additional bit, the number of different states that we can be in *doubles*! This is huge. It is called *exponential* growth.

Let us look a bit closer at how many states a growing number of bits can be in. One bit can be in two states, two bits can be in four states, and so on. So, it is 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024 states, and so on. This is like the tables up to ten (bits) but of a computer scientist! You may have actually seen these numbers before but probably never knew where they came from. Try continuing the series yourself with more bits! 2048, 4096,... You will quickly run out of room.

Imagine, your cell phone can probably store a few billion bits. How many states is that? Far more than there are atoms in the known universe! Just in your pocket! This also means that the bits in your phone can be in so many different states that your phone would have long turned to dust before being able to try out all possible states these bits can be in. Conversely, it is unlikely that the bits in your phone will ever be in a state they have been in before since some bits are usually used to keep track of time and other environmental factors such as battery health which keep changing over time.

So, what is it that your cell phone or any other computer does? Well, it really just stores an enormous amount of bits that are in a given state, which means each of those bits is either 0 or 1. And then the machine identifies at least one of those bits and then changes it from 0 to 1 if the bit was 0, and from 1 to 0 if the bit was 1. We call that change a *bit flip*. After that flip, the computation is either finished or the machine identifies another bit, or even the same bit as before, and flips that bit, and so on. Such a sequence of bit flips is what we call *computation*.

Everything you see the machine does, play a song, play a movie, call someone, send a text, and so on is done by just storing and flipping bits, and nothing else. In particular, the machine has no concept of what those bits mean, really no idea! It is us humans who are supposed to know what they mean and the rest of the chapter is about that. Ok, but how does the machine know which bits to flip? Well, it is software that *instructs* the machine to do that. Where is that software? Well, it is also encoded in the bits stored by the machine. And it is again us humans who are supposed to know what they mean. The chapter that follows this chapter is about that.

The key lesson to be learned here is to accept the fact that computers just store and flip bits. In a computer there is no text, no audio, no video, just bits. The only reason computers are so cool is because they can store incredibly many bits, billions and billions of bits, and they can flip these bits incredibly fast and efficiently, that is, they can flip billions of bits per second with very little power consumption. But still there are so many different states billions of bits can be in that a computer can never explore all possible states. This gives us room for unlimited innovation.

### Numbers

Let us go back to the example of adding the two decimal numbers 85 and 7. Do you remember how to do that by hand? Of course, you do! We go from right to left, digit by digit. First, take the two rightmost digits 5 and 7 and add them. The result is obviously 12. The 2 in 1**2** is already the rightmost digit of the sum of 85 and 7 which is obviously 9**2**. The more interesting phenomenon here is that the result of adding 5 and 7 needs an extra digit, that is, the 1 in **1**2. We need to acknowledge that by *carrying* that extra digit to the left and, in our example here, add it to 8 which results in 9, of course. And that 9 is the digit to the left of 2 in the sum of 85 and 7. Done!

The reason why we go through this is because a computer does the exact same thing, just with binary numbers. But that only works if we encode our decimal numbers properly in binary. Out of the many different ways of encoding numbers there is only one way that makes addition in binary work the same way it works in decimal. To understand how to do that we need to remind ourselves how decimal notation actually works.

Take 85, for example. The decimal number 85 represents the value **8**\*10+**5**. With an even bigger decimal number, say, 285 you should see how this works in general. It represents the value (**2**\*10+**8**)\*10+**5**. Decimal notation is positional. That means that the value of a digit, say, of 8 in 2**8**5 depends on its position relative to the digits to its right, and it depends on the number of different symbols we use per digit which is of course 10 with decimal notation, that is, the 10 different symbols 0, 1, 2, 3, 4, 5, 6, 7, 8, and 9. The number of different symbols per digit is called *base*. So, decimal notation uses base 10.

The only difference between decimal and binary notation is the number of different symbols per digit, that is, the base. With binary notation there are of course just two symbols, say, 0 and 1. Thus the base of binary notation is 2. Calculating the value of a binary number works accordingly. For example, the binary number 111 represents the decimal number 7 because (**1**\*2+**1**)\*2+**1**. The binary number 1010101 represents 85 because (((((**1**\*2+**0**)\*2+**1**)\*2+**0**)\*2+**1**)\*2+**0**)\*2+**1**. Take a piece of paper and a pen (not a computer!) and convert a few other numbers for yourself!

Also, counting in binary is just as easy as in decimal. Remember the sequence of 3-bit states from above, that is, 000, 001, 010, 011, 100, 101, 110, and 111? That sequence corresponds to the binary encoding of the decimal numbers 0, 1, 2, 3, 4, 5, 6, and 7. Try to count with four bits!

Notice that the value of a digit increases as it appears further to the left of other digits. In fact, with binary notation it increases by a factor of 2, that is, by an *order of magnitude*, for each digit to the right of it. Similarly, with decimal notation it increases by a factor of 10. This is genius. The idea is called *hindu-arabic* notation. And the thing that is arabic about it is that the value of digits depends on what is written to the right of their position rather than all other writing in Western culture where content develops from left to right.

Let us again go back to the example of adding 85 and 7. By now, we know their binary encoding, that is, 1010101 and 111. We are thus ready to perform binary addition, just like a computer. Take the rightmost bits in 101010**1** and 11**1**, also called the *least-significant bits* (LSBs). They are both 1. Adding 1 and 1 in binary is of course 10 which is 2 in decimal. This means that the LSB of the sum of 1010101 and 111 is the 0 in 1**0**. But we need to carry the 1 in **1**0, also called the *carry bit*, to the left now and add it to the second LSBs 0 and 1 in 10101**0**1 and 1**1**1. So, we are actually adding three digits now, 0 and 1 plus the carry bit 1. The result is of course 10. The 0 in 1**0** is now the second LSB of the sum and the 1 in **1**0 is the new carry bit. Now, we need to add that carry bit to the third LSBs 1 and 1 in 1010**1**01 and **1**11. This means we are adding 1 and 1 plus the carry bit 1. The result is of course 11 which is 3 in decimal. Not that hard, right? So, the 1 in 1**1** is now the third LSB of the sum and the 1 in **1**1 is the new carry bit. From now on the process continues with no further surprises until we reach the leftmost or *most-significant bits* (MSBs). Here is a summary but try to complete it yourself on a piece of paper:

```
 1010101 = 85
+0000111 =  7
—————————————
 1011100 = 92
```

Boolean logic

Unary, octal, hexadecimal

### Negative Numbers

85 - 7 = 85 + (100 - 7) - 100 =
85 + (100 - 1 - 7 + 1) - 100 =
85 + (99 - 7 + 1) - 100 =
85 + ((99 - 07) + 1) - 100 =
85 + (92 + 1) - 100 =
85 + 93 - 100 =
178 - 100 =
78

01010101
11111001
————————
01001110

### Bytes

### Characters

### Memory

### Text

### Images

### Video

### Audio

### Code

## The Machine

### Processor

### Memory

### Input/Output

### Instructions

## Programming

### Variable

### Expression

### Assignment

### Conditional

### Loop

### Procedure

### Library

### Apps

## Tools

### Translation

### Interpretation

### Semantics

## Virtualization

### Emulation

### Isolation

### The Cloud

## Glossary