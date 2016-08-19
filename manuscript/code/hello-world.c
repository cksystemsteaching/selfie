int* main() {
  int* x;

  // print the following string on the console
  x = "Hello World!";

  // characters are stored in chunks of 4 in memory,
  // that is, as "Hell", "o Wo", and "rld!" which
  // means that we can print them in chunks of 4

  // as long as there are characters print them
  while (*x != 0) {
    // 1 means that we print to the console,
    // x contains the 4 characters, and
    // 4 means that we print 4 characters
    write(1, x, 4);

    // go to the next 4 characters
    x = x + 1;
  }
}