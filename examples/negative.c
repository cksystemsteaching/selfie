// printing the negative decimal number -7 in C*

// libcstar procedures for printing
void init_library();
void print(uint64_t* s);
void print_integer(uint64_t n);
void print_hexadecimal(uint64_t n, uint64_t a);
void print_octal(uint64_t n, uint64_t a);
void print_binary(uint64_t n, uint64_t a);
void println();

uint64_t main() {
  // initialize selfie's libcstar library
  init_library();

  // print the integer literal -7 in decimal
  print("-7 in decimal with sign:  ");
  print_integer(-7);
  println();

  // print the integer literal -7 in hexadecimal
  print("-7 in 64-bit hexadecimal: ");
  print_hexadecimal(-7, 0);
  println();

  // print the integer literal -7 in octal
  print("-7 in 64-bit octal:       ");
  print_octal(-7, 0);
  println();

  // print the integer literal -7 in binary
  print("-7 in 64-bit binary:      ");
  print_binary(-7, 0);
  println();
}