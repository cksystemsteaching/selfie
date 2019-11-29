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

### Bits

### Bytes

### Memory

### Numbers

### Characters

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