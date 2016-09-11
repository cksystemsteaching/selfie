int* main() {
  int* foo;

  // print the following string on the console
  foo = "Hello World!";

  // strings are actually stored in chunks of 4 characters in memory,
  // that is, here as "Hell", "o Wo", and "rld!" which allows us to
  // print them conveniently in chunks of 4 characters at a time

  // as long as there are characters print them
  while (*foo != 0) {
    // 1 means that we print to the console
    // foo points to a chunk of 4 characters
    // 4 means that we print 4 characters
    write(1, foo, 4);

    // go to the next chunk of 4 characters
    foo = foo + 1;
  }
}