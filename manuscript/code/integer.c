// printing the decimal number 85 in C*

// libcstar procedures for printing
void initLibrary();
void print(uint64_t* s);
void printCharacter(uint64_t c);
void printString(uint64_t* s);
void printInteger(uint64_t n);
void printHexadecimal(uint64_t n, uint64_t a);
void printOctal(uint64_t n, uint64_t a);
void printBinary(uint64_t n, uint64_t a);
void println();

uint64_t main() {
  // initialize selfie's libcstar library
  initLibrary();

  // print the integer literal 85 in decimal
  print("85 in decimal:     ");
  printInteger(85);
  println();

  // print the ASCII code of 'U' (which is 85)
  printCharacter('U');
  print(" in ASCII:      ");
  printInteger('U');
  println();

  // print the string literal "85"
  printString("85");
  print(" string:       ");
  print("85");
  println();

  // print the integer literal 85 in hexadecimal
  print("85 in hexadecimal: ");
  printHexadecimal(85, 0);
  println();

  // print the integer literal 85 in octal
  print("85 in octal:       ");
  printOctal(85, 0);
  println();

  // print the integer literal 85 in binary
  print("85 in binary:      ");
  printBinary(85, 0);
  println();
}