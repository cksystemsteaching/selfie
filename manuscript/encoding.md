# 3. Encoding {#encoding}

Information, whatever it is, needs to be encoded in bits for a computer to handle it. Since `selfie.c` is a sequence of characters let us first look at how characters are encoded.

### Characters

We mention in the [previous chapter](#semantics) that the characters in `selfie.c` are [ASCII](https://en.wikipedia.org/wiki/ASCII "ASCII") characters encoded in eight bits or one byte according to the [UTF-8](https://en.wikipedia.org/wiki/UTF-8 "UTF-8") standard.

X> According to UTF-8 (and ASCII), the uppercase letter 'U', for example, is encoded in the 8-bit sequence `01010101`.

Both ASCII and UTF-8 are essentially one-to-one mappings from bits to characters written down in a table. Each 8-bit sequence is associated with exactly one character. For a computer that table is only relevant when the machine receives characters from a keyboard and sends characters to a screen. Then, the machine needs to know the ASCII code for each key on the keyboard to remember which key was pressed and it needs to know which shape of character to draw on the screen for each bit sequence. Internally, however, characters are just 8-bit sequences, with selfie and a lot of other software as well.

Let us pause for a moment and reflect about this. The above bit sequence could really still mean anything. The encoding standards for characters are just agreements on how to associate bits and characters but there is still no meaning.

X> The bit sequence `01010101` is also binary for the decimal number 85.

So what is it now, 'U' or 85? The answer is both, and anything else. As mentioned in the [previous chapter](#semantics), meaning comes from change. When the machine draws 'U' for `01010101` on the screen then `01010101` stands for 'U' in that moment but in the next moment the machine could increment `01010101` according to elementary arithmetic making `01010101` represent 85.

All the characters that selfie reads from files including `selfie.c` are [read](http://github.com/cksystemsteaching/selfie/blob/fa735a8561db58718cb58015bba8220a058c1c28/selfie.c#L1553) in a single line of code in `selfie.c`. Similarly, all characters written to files and the screen are [written](http://github.com/cksystemsteaching/selfie/blob/fa735a8561db58718cb58015bba8220a058c1c28/selfie.c#L1432) in another line of code in `selfie.c`.

### Identifiers

### Integers

[integer](http://github.com/cksystemsteaching/selfie/blob/fa735a8561db58718cb58015bba8220a058c1c28/selfie.c#L1726-L1767 "integer")

### Strings

[String](https://en.wikipedia.org/wiki/String_(computer_science) "String")
: A finite sequence of characters taken from some finite alphabet.

In other words, `selfie.c` is a string of 158,772 characters whose alphabet is in fact ASCII characters UTF-8-encoded in eight bits.

### Instructions