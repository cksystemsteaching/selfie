// global variable pointing to the "Hello World!    " string
char* foo;

// main procedure printing "Hello World!    " on the console
uint64_t main() {
  // point to the "Hello World!    " string
  foo = "Hello World!    ";

  // strings are actually stored in chunks of 8 characters in memory,
  // that is, here as "Hello Wo", and "rld!    " which allows us to
  // print them conveniently in chunks of 8 characters at a time

  // as long as there are characters print them
  while (*foo != 0) {
    // 1 means that we print to the console
    // foo points to a chunk of 8 characters
    // 8 means that we print 8 characters
    write(1, foo, 8);

    // go to the next chunk of 8 characters
    foo = foo + 1;
  }
}