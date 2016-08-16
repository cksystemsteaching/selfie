# 3. Encoding {#encoding}

Information, whatever it is, needs to be encoded in bits for a computer to handle it. Since `selfie.c` is a sequence of characters let us first look at how characters are encoded.

### Characters

We mention in the [previous chapter](#semantics) that the characters in `selfie.c` are [ASCII](https://en.wikipedia.org/wiki/ASCII "ASCII") characters encoded in eight bits or one byte according to the [UTF-8](https://en.wikipedia.org/wiki/UTF-8 "UTF-8") standard.

X> According to UTF-8 (and ASCII), the uppercase letter 'U', for example, is encoded in the 8-bit sequence `01010101`.

Both ASCII and UTF-8 are essentially one-to-one mappings from bits to characters written down in a table. Each 8-bit sequence is associated with exactly one character. For a computer that table is only relevant when the machine receives characters from a keyboard and sends characters to a screen. Then, the machine needs to know the ASCII code for each key on the keyboard to remember which key was pressed and it needs to know which shape of character to draw on the screen for each bit sequence. Internally, however, characters are just 8-bit sequences, with selfie and a lot of other software as well.

Let us pause for a moment and reflect about this. The above bit sequence could really still mean anything. The encoding standards for characters are just agreements on how to associate bits and characters but there is still no meaning.

X> The bit sequence `01010101` is also binary for the decimal number 85.

So what is it now, 'U' or 85? The answer is both, and anything else. As mentioned in the [previous chapter](#semantics), meaning comes from change. When the machine draws 'U' for `01010101` on the screen then `01010101` stands for 'U' in that moment but in the next moment the machine could increment `01010101` according to elementary arithmetic making `01010101` represent 85.

All the characters that selfie reads from files including `selfie.c` are [read](http://github.com/cksystemsteaching/selfie/blob/58503341fdff87ef993b469bc6353d75dd8ee9fd/selfie.c#L1595) in a single line of source code in `selfie.c`. Similarly, all characters written to files and the screen are [written](http://github.com/cksystemsteaching/selfie/blob/58503341fdff87ef993b469bc6353d75dd8ee9fd/selfie.c#L1469) in just one line of code in `selfie.c`. For further details on what the code means refer to the comments in the code. In general, we only provide links to code with comments so that text explaining code is not duplicated here.

Selfie, that is, `selfie.c` is written in the widely used programming language C, hence the extension `.c` in the name of the file.

[C](https://en.wikipedia.org/wiki/C_(programming_language) "C")
: A general-purpose, imperative computer programming language, supporting structured programming, lexical variable scope and recursion, while a static type system prevents many unintended operations.

What all of this really means is not so important right now. You only need to know that `selfie.c` is written in a tiny subset of C called C\* which is much easier to learn than all of C. This is similar to using only a tiny subset of the vocabulary of a foreign language. We designed C\* to make everything as simple as possible but still realistic. You should start reading the code in `selfie.c` as if it was some sort of mechanical English. There are a lot of comments whenever the code is not sufficiently self-explanatory. In other words, reading code and comments is part of the experience of reading this book!

#### Comments

Now, what is a comment in code anyway? A comment is text that the machine ignores completely. It is only there for people to read and understand the code. With selfie, a comment is all text to the right of two slashes `//` until the end of the line. There is a lot of that in the beginning of `selfie.c`. It actually takes a bit of scrolling down to see the [first line of code](http://github.com/cksystemsteaching/selfie/blob/0d76fc92d8a79db612973153d133f14eb35efae6/selfie.c#L76) that means something to the machine and is not a comment.

If we were to remove all comments from `selfie.c` the result would still be semantically equivalent to `selfie.c` from the perspective of the machine. In fact, we could safely remove even more characters called whitespace without changing any semantics.

#### Whitespace

[Whitespace Character](https://en.wikipedia.org/wiki/Whitespace_character "Whitespace Character")
: Any character or series of characters that represent horizontal or vertical space in typography. When rendered, a whitespace character does not correspond to a visible mark, but typically does occupy an area on a page.

Whitespace characters are invisible but still important for formatting source code yet they are typically irrelevant in terms of semantics. While this is true for many programming languages including the language in which selfie is written it is not true in general. There are programming languages in which whitespace does make a semantical difference. This is important to check when learning new programming languages.

The starc compiler considers the space, the tabulator, the line feed, and the carriage return characters whitespace and ignores them when reading source code:

{line-numbers=off}
```
> ./selfie -c selfie.c
./selfie: this is selfie's starc compiling selfie.c
./selfie: 166707 characters read in 6652 lines and 864 comments
./selfie: with 94033(56.49%) characters in 29064 actual symbols
...
```

Out of the all the characters in `selfie.c` only a little more than half of the characters are actually considered code. The rest is whitespace and characters in comments. The [code](http://github.com/cksystemsteaching/selfie/blob/1de4c78a109a13e384aa2e4b8b126227b08f0e9a/selfie.c#L1710-L1770) in `selfie.c` that starc uses to ignore whitespace and comments works by reading one character after the other and discarding them until a character is found that is not whitespace and not occurring in a comment. Of course, depending on content, this may also continue until the end of the file is reached without finding such a character. Important for us here is to understand that the machine really only looks at one character at a time from start to end of the file.

[Minification](https://en.wikipedia.org/wiki/Minification_(programming) "Minification")
: The process of removing all unnecessary characters from source code without changing its functionality. These unnecessary characters usually include white space characters, new line characters, and comments, which are used to add readability to the code but are not required for it to execute.

{line-numbers=on, lang=c}
<<[A Hello World Program](code/hello-world.c)

{line-numbers=on, lang=c}
<<[Minified Hello World Program](code/hello-world-minified.c)

### Identifiers

### Integers

[Integer](http://github.com/cksystemsteaching/selfie/blob/fa735a8561db58718cb58015bba8220a058c1c28/selfie.c#L1726-L1767 "Integer")

### Strings

[String](https://en.wikipedia.org/wiki/String_(computer_science) "String")
: A finite sequence of characters taken from some finite alphabet.

In other words, `selfie.c` is a string of 158,772 characters whose alphabet is in fact ASCII characters UTF-8-encoded in eight bits.

### Instructions