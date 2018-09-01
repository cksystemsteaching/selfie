# 5. Regularity {#regularity}

When reading source code the starc compiler does in fact just try to recognize such symbols, also called *tokens*. The process is very simple and called *lexical analysis*.

[Lexical Analysis](https://en.wikipedia.org/wiki/Lexical_analysis "Lexical Analysis")
: The process of converting a sequence of characters (such as in a computer program or web page) into a sequence of tokens (strings with an identified "meaning"). A program that performs lexical analysis may be called a lexer, tokenizer, or scanner.

The compiler reads one character after another until it [recognizes a symbol](https://github.com/cksystemsteaching/selfie/blob/06498c53d5fa503d0eabc25161f38feccd19135c/selfie.c#L2583-L2819), after discarding whitespace and comments, of course. Once it recognizes a symbol it stores that symbol and then continues reading more characters until it recognizes the next symbol and so on until it reaches the end of the file. If the compiler reads a sequence of characters that does not constitute a symbol it reports an error and terminates. Try it! Just take the `"Hello World!"` program and modify it such that it contains something that is neither whitespace nor a comment nor a C\* symbol. Then run starc to see what happens.