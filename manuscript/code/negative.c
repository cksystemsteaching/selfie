// printing the negative decimal number -85 in C*

// libcstar procedures for printing
void initLibrary();
void print(uint64_t* s);
void printInteger(uint64_t n);
void printHexadecimal(uint64_t n, uint64_t a);
void printOctal(uint64_t n, uint64_t a);
void printBinary(uint64_t n, uint64_t a);
void println();

uint64_t INT64_MAX;
uint64_t INT64_MIN;

uint64_t main() {
  // initialize selfie's libcstar library
  initLibrary();

  // print the integer literal -85 in decimal
  print("      -85 in decimal:     ");
  printInteger(-85);
  println();

  // print the integer literal -85 in hexadecimal
  print("      -85 in hexadecimal: ");
  printHexadecimal(-85, 0);
  println();

  // print the integer literal -85 in octal
  print("      -85 in octal:       ");
  printOctal(-85, 0);
  println();

  // print the integer literal -85 in binary
  print("      -85 in binary:      ");
  printBinary(-85, 0);
  println();

  // print INT64_MAX in decimal
  print("INT64_MAX in decimal:     ");
  printInteger(INT64_MAX);
  println();

  // print INT64_MAX in hexadecimal
  print("INT64_MAX in hexadecimal: ");
  printHexadecimal(INT64_MAX, 0);
  println();

  // print INT64_MAX in octal
  print("INT64_MAX in octal:       ");
  printOctal(INT64_MAX, 0);
  println();

  // print INT64_MAX in binary
  print("INT64_MAX in binary:      ");
  printBinary(INT64_MAX, 64);
  println();

  // print INT64_MIN in decimal
  print("INT64_MIN in decimal:     ");
  printInteger(INT64_MIN);
  println();

  // print INT64_MIN in hexadecimal
  print("INT64_MIN in hexadecimal: ");
  printHexadecimal(INT64_MIN, 0);
  println();

  // print INT64_MIN in octal
  print("INT64_MIN in octal:       ");
  printOctal(INT64_MIN, 0);
  println();

  // print INT64_MIN in binary
  print("INT64_MIN in binary:      ");
  printBinary(INT64_MIN, 64);
  println();
}