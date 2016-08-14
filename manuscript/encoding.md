# 3. Encoding {#encoding}

Information, whatever it is, needs to be encoded in bits for a computer to handle it. Since `selfie.c` is a sequence of characters let us first look at how characters are encoded.

### Characters

We mention in the [previous chapter](#semantics) that the characters in `selfie.c` are [ASCII](https://en.wikipedia.org/wiki/ASCII "ASCII") characters encoded in eight bits or one byte according to the [UTF-8](https://en.wikipedia.org/wiki/UTF-8 "UTF-8") standard.

X> According to UTF-8 (and ASCII), the uppercase letter 'U', for example, is encoded in the 8-bit sequence `01010101`.

Both ASCII and UTF-8 are essentially one-to-one mappings from bits to characters written down in a table. Each 8-bit sequence is associated with exactly one character. For a computer that table is only relevant when the machine receives characters from a keyboard and sends characters to a screen. Then, the machine needs to know the ASCII code for each key on the keyboard to remember which key was pressed and it needs to know which shape of character to draw on the screen for each bit sequence. Internally, however, characters are just 8-bit sequences, with selfie and a lot of other software as well.

Let us pause for a moment and reflect about this. The above bit sequence could really still mean anything. The encoding standards for characters are just agreements on how to associate bits and characters but there is still no meaning.

X> The bit sequence `01010101` is also binary for the decimal number 85.

So what is it now, 'U' or 85? The answer is both, and anything else. As mentioned in the [previous chapter](#semantics), meaning comes from change. When the machine draws 'U' for `01010101` on the screen then `01010101` stands for 'U' in that moment but in the next moment the machine could increment `01010101` according to elementary arithmetic making `01010101` represent 85.

All the characters that selfie reads from files including `selfie.c` are [read](http://github.com/cksystemsteaching/selfie/blob/58503341fdff87ef993b469bc6353d75dd8ee9fd/selfie.c#L1595) in a single line of code in `selfie.c`. Similarly, all characters written to files and the screen are [written](http://github.com/cksystemsteaching/selfie/blob/58503341fdff87ef993b469bc6353d75dd8ee9fd/selfie.c#L1469) in just one line of code in `selfie.c`.

For further details please refer to the comments in the code. In general, we only provide links to code with comments so that text explaining code is not duplicated here. In other words, reading code is part of the experience of reading this book and actually a lot of fun! Just be patient. Things will clear up after a while. The code is written for everyone to understand.

#### Comments

Now, what is a comment in code anyway? A comment is text that the machine ignores completely. It is only there for people to read and understand the code. Technically, a comment is simply all text to the right of two slashes `//` until the end of the line. There is a lot of that in the beginning of `selfie.c`. It actually takes a bit of scrolling down to see the [first line of code](http://github.com/cksystemsteaching/selfie/blob/0d76fc92d8a79db612973153d133f14eb35efae6/selfie.c#L76) that means something to the machine and is not a comment.

If we were to remove all comments from `selfie.c` the result would still be semantically equivalent to `selfie.c` from the perspective of the machine. In fact, we could safely remove even more characters called whitespace without changing any semantics.

#### Whitespace

Whitespace characters are invisible but still important for formatting source code yet not for semantics. By the way, this is true for many programming languages including the language in which selfie is written but not for all. This is important to check when learning new programming languages.

The starc compiler considers the space, the tabulator, the line feed, and the carriage return characters whitespace and ignores them when reading source code:

{line-numbers=off}
```
> ./selfie -c selfie.c
./selfie: this is selfie's starc compiling selfie.c
./selfie: 166707 characters read in 6652 lines and 864 comments
./selfie: with 94033(56.49%) characters in 29064 actual symbols
...
```

Out of the all the characters in `selfie.c` only a little more than half of the characters are actually considered code. The rest is whitespace and characters in comments. The [code](http://github.com/cksystemsteaching/selfie/blob/1de4c78a109a13e384aa2e4b8b126227b08f0e9a/selfie.c#L1710-L1770) in `selfie.c` that starc uses to ignore whitespace and comments works by reading one character after the other and discard them until a character is found that is not whitespace and not occurring in a comment. Of course, depending on content, this may also continue without finding such a character until the end of the file is reached. Important for us here is to understand that the machine really only looks at one character at a time from start to end of the file.

### Identifiers

### Integers

[Integer](http://github.com/cksystemsteaching/selfie/blob/fa735a8561db58718cb58015bba8220a058c1c28/selfie.c#L1726-L1767 "Integer")

### Strings

[String](https://en.wikipedia.org/wiki/String_(computer_science) "String")
: A finite sequence of characters taken from some finite alphabet.

In other words, `selfie.c` is a string of 158,772 characters whose alphabet is in fact ASCII characters UTF-8-encoded in eight bits.

### Instructions