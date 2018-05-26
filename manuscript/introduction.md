{mainmatter}

# 1. Introduction

{#introduction}

Computer science is a mystery to so many and yet more and more people use computers every day in one form or another. There are increasingly many people with all kinds of backgrounds other than computer science that even code every day. At schools, colleges, universities, and companies around the world there is hardly anyone left who is not confronted with the machine and its code. But even for people just using the machine in their hands, on their desks, and in the clouds there is often that unsatisfactory experience of not understanding what is really going on.

While a book about computer science for everyone may sound appealing it actually requires serious commitment to understand the material even though we tried very hard to simplify everything as much as possible. The reason is that computers and software are so expressive that it is unlikely that any other computational machine in the future will be more expressive. Anything that can be computed can be computed now, if you have enough time, space, and energy.

This book is based on the [Selfie Project](http://selfie.cs.uni-salzburg.at), an educational software system that has grown out of many years of teaching undergraduate and graduate classes in computer science. The key observation is that understanding computer science and the meaning of software in particular can only be achieved by understanding how software and data translate all the way down to the machine. Selfie shows how to do that. This may sound difficult but can actually be done in a systematic fashion with a strong focus on basic principles.

Selfie is software that can translate itself to code that can be executed by a computer. This is called *self-compilation*. But selfie even includes software that can mimic a computer that can execute the code of selfie. This is called *self-execution*. And, selfie can even do that on behalf of other computers but also itself. This is called *self-hosting*. By now your mind might be spinning but you at least understand why selfie is called selfie.

Why is the *self* so important? Because it shows how meaning is created systematically on a machine. Selfie is software written in some programming language. However, selfie defines the meaning of that language which implies that selfie defines its own meaning. This is very similar to an English dictionary written in English. The only difference is that selfie defines meaning formally in such a way that a machine can run selfie and thus any software written in the language in which selfie is written.

The book works by explaining selfie step by step while focusing on the basic principles that are necessary to understand each step. In order to follow the book you will need to run [selfie](https://github.com/cksystemsteaching/selfie) either on your computer or in the cloud. To run selfie on your computer you need a terminal and a C compiler. If you have a Mac or a Linux system, terminal and compiler are already there, and easy to get for a Windows machine. If you only have access to a web browser you can still run selfie through a cloud-based development environment, see the [README](https://github.com/cksystemsteaching/selfie/blob/master/README.md) for more details.

[Chapter 2](#semantics) introduces selfie and how to use it. The focus is on developing an idea of the problem of semantics. Computer scientists have developed all these formalisms for coding and many other things. We show how selfie can help to understand the relevant aspects of the problem.

[Chapter 3](#encoding) is an introduction to encoding and decoding basic information such as characters, strings, numbers, and even machine instructions in binary form. We use selfie to show examples and how their encoding and decoding is actually done.

[Chapter 4](#state) introduces computation as the evolution of state. Using a simple example of a program we explain what its source code means, how that source code translates to machine code that gives the source code its meaning, and how both source and machine code execute from one state to another.

Chapter 5 will be on regularity and finite state machines. We show how to control the potentially very large state space of code to simplify reasoning about its correctness.