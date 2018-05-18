uint64_t main() {
  uint64_t* string;

  string = "\n\nThis is a demonstration of \"escape sequences\".\nPrepending a \'\\\' to specific characters (namely: n, \', \" or \\) alters output.\n\n";

  while (*string != 0) {
    // 1 means that we print to the console
    // foo points to a chunk of 8 characters
    // 8 means that we print 8 characters
    write(1, string, 8);

    // go to the next chunk of 8 characters
    string = string + 1;
  }

  return 0;
}
