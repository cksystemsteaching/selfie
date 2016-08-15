int* main() {
  int* x;

  // print the following string on the console
  x = "Hello World!";

  // printing is done in chunks of 4 characters,
  // that is, "Hell", "o Wo", and "rld!" showing
  // how the data is encoded and stored in memory

  while (*x != 0) {
    // write 4 characters at a time to the console
    // which is identified by the first parameter 1
    write(1, x, 4);

    // go to the next 4 characters
    x = x + 1;
  }
}