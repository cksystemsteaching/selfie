// printing the negative decimal number -85 in C*

// libcstar procedures for printing
void initLibrary();
void print(int* s);
void printInteger(int n);
void printHexadecimal(int n, int a);
void printOctal(int n, int a);
void printBinary(int n, int a);
void println();

int INT_MAX;
int INT_MIN;

int main() {
  // initialize selfie's libcstar library
  initLibrary();

  // print the integer literal -85 in decimal
  print("    -85 in decimal:     ");
  printInteger(-85);
  println();

  // print the integer literal -85 in hexadecimal
  print("    -85 in hexadecimal: ");
  printHexadecimal(-85, 0);
  println();

  // print the integer literal -85 in octal
  print("    -85 in octal:       ");
  printOctal(-85, 0);
  println();

  // print the integer literal -85 in binary
  print("    -85 in binary:      ");
  printBinary(-85, 0);
  println();

  // print INT_MAX in decimal
  print("INT_MAX in decimal:     ");
  printInteger(INT_MAX);
  println();

  // print INT_MAX in hexadecimal
  print("INT_MAX in hexadecimal: ");
  printHexadecimal(INT_MAX, 0);
  println();

  // print INT_MAX in octal
  print("INT_MAX in octal:       ");
  printOctal(INT_MAX, 0);
  println();

  // print INT_MAX in binary
  print("INT_MAX in binary:      ");
  printBinary(INT_MAX, 32);
  println();

  // print INT_MIN in decimal
  print("INT_MIN in decimal:     ");
  printInteger(INT_MIN);
  println();

  // print INT_MIN in hexadecimal
  print("INT_MIN in hexadecimal: ");
  printHexadecimal(INT_MIN, 0);
  println();

  // print INT_MIN in octal
  print("INT_MIN in octal:       ");
  printOctal(INT_MIN, 0);
  println();

  // print INT_MIN in binary
  print("INT_MIN in binary:      ");
  printBinary(INT_MIN, 32);
  println();
}