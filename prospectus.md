### Prospectus for MIT Press (1st Revision)

c/o Marie L. Lee
Executive Editor, Computer Science & Engineering

### Preliminary Book Title

Elementary Computer Science for All

### Author

Christoph Kirsch
Professor, Department of Computer Sciences, University of Salzburg, Austria

Email: [ck@cs.uni-salzburg.at](mailto:ck@cs.uni-salzburg.at)
Web: [www.cs.uni-salzburg.at/~ck](http://www.cs.uni-salzburg.at/~ck)

#### Changes in the 1st Revision

We thank the reviewers for their valuable and insightful comments and feedback. We tried to address *all* concerns as follows:

1. Target Audience: We narrowed the target audience to senior high-school and freshman/sophomore college students and recommend the book as textbook for teachers and professors with a background in computer science.

2. Methodology: We now use the selfie system more prominently as a means to interact with the machine, as formal documentation of the concepts introduced in the book, and as template for exercises that involve modifying and enhancing its source code. We plan to use the selfie autograder for this purpose.

3. Presentation: We included a motivational chapter on selfie right after the introduction. The idea is to encourage readers to connect with the material through interaction with the selfie system and exposure to its source code.

Details:

1. We refer to selfie, whenever approriate, and explain how to interact with the system in the given context.

2. We added "Recommended Readings" sections at the end of the selfie and the information chapter. We plan to include "State of the Art" sections at the end of the remaining technical chapters.

3. We improved the material in general and on Boolean Algebra, circuits, and negative numbers, in particular. We also added three more figures on adders.

4. In the meantime we started working on the machine chapter which is still incomplete but included for your reference.

5. We updated the prospectus below to reflect the first revision.

#### Brief Description:

This is a proposal for a book on *elementary computer science* for senior high-school and freshman/sophomore college students. The book may be used as textbook by teachers and professors with a background in computer science. The idea is to explain the absolute basics of computer science with a strong focus on *intuition* rather than formalism. The book explains, similar to related books, how a computer works in principle and how to do some basic programming, but goes beyond that by exploring the general *nature* of information and computing in the context of today's reality of ubiquitous use of digital devices. This is also different from teaching computational thinking with its focus on problem solving.

Similar to elementary arithmetic with its five categories (numbers, measurement, geometry, algebra, and probabilities), we present five categories of elementary computer science in five chapters called information, machine, programming, tools, and computing. Information is on encoding and decoding information in bits. Machine is on a simple yet representative and still realistic machine model. Programming is on fundamental programming language concepts and basic algorithms. Tools is on translation and interpretation of programs with a focus on the semantics of programs. Computing is on virtualizing computation for enabling computing as utility and cloud computing. However, unlike traditional textbooks on elementary arithmetic, we use simple examples rather than formulae whenever possible.

A common theme of our book is an important concept in computer science called self-referentiality which has immediate counterparts in the real world. Think of an English dictionary written in English. The same can be done with software that defines its own meaning or constructs a virtual machine for running software everywhere including itself. Seeing what self-referentiality is and how it is resolved is key to gaining an integrated understanding of elementary computer science. Teaching self-referentiality in its various forms is inspired by a software system called selfie that we developed over many years teaching undergraduate computer science students.

Selfie is the source of most examples we use in the book and enables us to integrate our five categories of elementary computer science in one system. In a motivational chapter right after the introduction and before the five technical chapters, we encourage readers to install selfie, on their machine or in the cloud, and then interact with the system. Besides interacting with selfie, we also encourage readers to take a look at selfie's source code. In the five technical chapters, we point out to readers, whenever appropriate, to interact with selfie but also to read, understand, and even modify the relevant parts of the source code which has been written for that purpose.

Selfie is open source and available online at [selfie.cs.uni-salzburg.at](http://selfie.cs.uni-salzburg.at)

Selfie is hosted on github.com and tagged for our book at [https://github.com/cksystemsteaching/selfie/tree/elementary-computer-science]()

For an introduction to selfie and a work-in-progress attempt of the author to develop a curriculum of elementary computer science see the paper "[Selfie and the Basics](https://dl.acm.org/doi/10.1145/3133850.3133857)" by the author which appeared in the proceedings of the ACM SIGPLAN International Symposium on New Ideas, New Paradigms, and Reflections on Programming and Software (Onward!) in 2017.

#### Outstanding Features

The *focus* of the book is on elementary computer science as a whole, not just computers or programming or problem solving and so on, targeting readers with diverse backgrounds other than computer science but in need of gaining an intuitive understanding of computer science in general. We present basic principles that are simple individually and then show how to combine them towards the full capabilities of modern computing.

The *theme* of the book is the integration of basic principles of computer science through self-referentiality in its various forms. Rather than avoiding an admittedly challenging concept, we developed with the selfie system a solid foundation for resolving the inherent self-referentiality in computing and leverage that to explain how meaning is created on a mindless machine. Selfie allows us to even go beyond self-compilation and include self-referentiality in operating systems and virtualization technology in general.

The *language* of the book is casual with a focus on intuition rather than formalism, even using humor, which is unusual in a technical field such as computer science and an attempt to create an emotional bond between author and reader. In the experience of the author, teaching students majoring in fields other than computer science, emotion is particularly important to reduce the infamous pain in learning about computer science. The language of the book is in fact a personal statement of the author and deliberately kept that way to transport the author's passion about computer science.

#### The Author

Christoph Kirsch is Professor at the Department of Computer Sciences of the University of Salzburg, Austria. He received his Dr.Ing. degree from Saarland University in 1999 while at the Max Planck Institute for Computer Science in Saarbr&uuml;cken, Germany. From 1999 to 2004 he worked as Postdoctoral Researcher at the Department of Electrical Engineering and Computer Sciences of the University of California, Berkeley. He later returned to Berkeley as Visiting Scholar (2008-2013) and Visiting Professor (2014) at the Department of Civil and Environmental Engineering. His research interests are in concurrent programming, memory management, virtualization, and formal verification. Dr. Kirsch co-invented embedded programming languages and systems such as Giotto, HTL, and the Embedded Machine, and more recently co-designed high-performance, multicore-scalable concurrent data structures and memory management systems. He co-founded the International Conference on Embedded Software (EMSOFT) in 2001 and served as ACM SIGBED chair from 2011 until 2013. He has been IEEE TCAD and ACM TODAES associate editor, and is ACM Distinguished Speaker since 2017.

#### Related Titles

We relate our book to five others of which the first four are closely related while the last book (The Art of Computer Programming by Donald E. Knuth) is mentioned because of its importance in the field. We also list related books recommended by reviewers below.

The first three books essentially share with our book the broad target audience beyond computer science students while the fourth book (An Introduction to Computer Science: A Textbook for Beginners in Informatics by Gilbert Brands) targets, unlike us, undergraduate computer students specifically.

An interesting observation is that the titles of the first four books are perfect summaries of how our book is different. The first book (Code: The Hidden Language of Computer Hardware and Software by Charles Petzold) has a strong focus on code. The second book (But How Do It Know? - The Basic Principles of Computers for Everyone by J. Clark Scott) explains how computers work while the third book (The Elements of Computing Systems: Building a Modern Computer from First Principles by Noam Nisan and Shimon Schocken) explains how to build one. The fourth book (An Introduction to Computer Science: A Textbook for Beginners in Informatics by Gilbert Brands) is a traditional textbook for computer science students.

Code: The Hidden Language of Computer Hardware and Software by Charles Petzold

The book provides, similar to us, an introduction to computer science for broader audiences beyond computer science students and is therefore closely related to ours. The structure of the book is also somewhat similar to ours. The presentation and concept of the book are nevertheless quite different. There is a strong focus on what code is in many different forms in the first half of the book followed by a machine model and higher level concepts such as programs and operating systems in the second half of the book. This is quite different from our focus on the basic principles of computer science in general and our approach of integration through the selfie system in particular.

But How Do It Know? - The Basic Principles of Computers for Everyone by J. Clark Scott

The book provides, again similar to us, an introduction to computer science for broader audiences beyond computer science students and is therefore closely related to ours. The structure of the book is also somewhat similar to ours. The presentation and concept of the book are nevertheless again quite different. There is a strong focus on how a computer works in the first three quarters of the book followed by a much shorter treatment of higher level concepts such as programs and operating systems in the last quarter of the book. This is again quite different from our focus on elementary computer science with our use of self-referentiality as integrating concept.

The Elements of Computing Systems: Building a Modern Computer from First Principles by Noam Nisan and Shimon Schocken

The book provides, again similar to us, an introduction to computer science for broader audiences beyond computer science students and is therefore also closely related to ours. The structure of the book is also somewhat similar to ours. The presentation and concept of the book are nevertheless also quite different. The idea is to show how a computer is essentially built from scratch including the software stack running on top of the machine. This is obviously again quite different from our focus on elementary computer science with our use of self-referentiality as integrating concept.

An Introduction to Computer Science: A Textbook for Beginners in Informatics by Gilbert Brands

This book provides an introduction to computer science for undergraduate students. The structure of the book is similar to ours except for additional material on networking. The presentation is nevertheless also quite different. The book targets students specifically studying computer science rather than broader audiences like us. The content of the book is therefore purely technical without setting the material into context for readers that do not intend to study computer science. The concept of the book is in that sense a classical introduction to computer science similar to many introductory classes in the field.

The Art of Computer Programming by Donald E. Knuth

This book is seminal work in multiple volumes that provides comprehensive coverage of many aspects of computer science. Structure, presentation, content, and target audience of the book are very different from ours. The book is the de-facto standard encyclopedia of computer science for readers that already have formal training in computer science.

Related books recommended by reviewer #3:

1. The Pattern On The Stone: The Simple Ideas That Make Computers Work by W. Daniel Hillis
2. Understanding the Digital World: What You Need to Know about Computers, the Internet, Privacy, and Security by Brian W. Kernighan
3. Bits to Bitcoin: How Our Digital Stuff Works by Mark Stuart Day and C. A. Jennings
4. Computing for Ordinary Mortals by Robert St. Amant
5. Denning, P: Great Principles of Computing by Peter J. Denning, Craig H. Martell, et al.

We agree that these books are closely related to the proposed book. By introducing selfie into the workflow and re-targeting to a narrower audience we believe that we provide significant benefit over the existing literature.

#### Audience

Readers should have a background at the level of senior high-school and freshman/sophomore college students. The prerequisites for following the material presented here are an understanding of elementary arithmetic (addition, subtraction, multiplication, and division of whole numbers), elementary geometry (one- and two-dimensional shapes), and elementary algebra (variables, equations). The prerequisites are anyway revisited in the book.

As stated in the introduction, this book targets three groups of readers:

1. Professional user: you do not plan to become a software engineer or computer scientist but you still would like to understand the machine that you are working with every day, at least in your professional life, to an extent that enables you to use computers efficiently and effectively and, most importantly, with joy!

2. Software engineer: you would like to develop software professionally and are interested in more than just learning how to code. In particular, you are looking for a background in computer science that is going to serve as foundation for understanding not just the state of the art in software engineering now but also any future development technology whatever it may be.

3. Computer scientist: you plan to become a computer scientist, or are already one, and would like to either gain a solid understanding or revisit your understanding of the absolute basics of computer science. Even if your focus area is not covered by this book, the material presented here may still have a profound effect on how you see and approach your own field.

#### Status of the Book

The introduction, the motivational chapter on selfie, and the first chapter on encoding information in bits are complete. There is also part of the machine chapter, a preliminary outline of the remaining structure, and a preliminary glossary of the terms introduced so far.

We expect to finish the manuscript within around one year by Spring 2021. The author is on sabbatical from July 2020 until February 2021 which should make that timeline feasible.

The current word count is at around 31,000 words. We plan the length of the book to be around 120,000 words.

On average there will be at least one figure, table, or non-textual example per section. For example, there are 16 sections in the first chapter on information with 15 figures, 2 tables, and 6 non-textual examples.

#### Reviewers

This is a list of potential reviewers. All candidates on this list have played important roles in my academic career over the years and written recommendation letters for me. They are familiar with my scientific work but not with the book project on elementary computer science.

* Rajeev Alur, Professor, University of Pennsylvania, USA, [alur@cis.upenn.edu](mailto:alur@cis.upenn.edu)

* Thomas A. Henzinger, Professor, Institute of Science and Technology Austria, [tah@ist.ac.at](mailto:tah@ist.ac.at)

* Edward A. Lee, Professor Emeritus, University of California at Berkeley, USA, [eal@eecs.berkeley.edu](mailto:eal@eecs.berkeley.edu)

* Martin Rinard, Professor, Massachusetts Institute of Technology, USA, [rinard@lcs.mit.edu](mailto:rinard@lcs.mit.edu)

* Joseph Sifakis, Professor, Verimag, Grenoble, France, [joseph.sifakis@imag.fr](mailto:joseph.sifakis@imag.fr)

* Lothar Thiele, Professor, ETH Zurich, Switzerland, [thiele@ethz.ch](mailto:thiele@ethz.ch)

* Marilyn Wolf, Professor, Georgia Institute of Technology, USA, [wolf@ece.gatech.edu](mailto:wolf@ece.gatech.edu)

#### Outline and Chapter Sketches

There is an introduction followed by six chapters called Selfie, Information, Machine, Programming, Tools, and Computing. Please refer to the introduction which provides an overview of the book as well as each individual chapter.