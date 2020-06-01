// printing maximum and minimum 64-bit integers in C*

// libcstar procedures for printing
void init_library();
void print(uint64_t* s);
void print_unsigned_integer(uint64_t n);
void print_integer(uint64_t n);
void print_hexadecimal(uint64_t n, uint64_t a);
void print_octal(uint64_t n, uint64_t a);
void print_binary(uint64_t n, uint64_t a);
void println();

uint64_t main() {
  // initialize selfie's libcstar library
  init_library();

  // print UINT64_MAX in decimal
  print("UINT64_MAX in decimal:     ");
  print_unsigned_integer(UINT64_MAX);
  println();

  // print UINT64_MAX in hexadecimal
  print("UINT64_MAX in hexadecimal: ");
  print_hexadecimal(UINT64_MAX, 0);
  println();

  // print UINT64_MAX in octal
  print("UINT64_MAX in octal:       ");
  print_octal(UINT64_MAX, 0);
  println();

  // print UINT64_MAX in binary
  print("UINT64_MAX in binary:      ");
  print_binary(UINT64_MAX, 64);
  println();

  // print INT64_MAX in decimal
  print(" INT64_MAX in decimal:     ");
  print_integer(INT64_MAX);
  println();

  // print INT64_MAX in hexadecimal
  print(" INT64_MAX in hexadecimal: ");
  print_hexadecimal(INT64_MAX, 0);
  println();

  // print INT64_MAX in octal
  print(" INT64_MAX in octal:       ");
  print_octal(INT64_MAX, 0);
  println();

  // print INT64_MAX in binary
  print(" INT64_MAX in binary:      ");
  print_binary(INT64_MAX, 64);
  println();

  // print INT64_MIN in decimal
  print(" INT64_MIN in decimal:     ");
  print_integer(INT64_MIN);
  println();

  // print INT64_MIN in hexadecimal
  print(" INT64_MIN in hexadecimal: ");
  print_hexadecimal(INT64_MIN, 0);
  println();

  // print INT64_MIN in octal
  print(" INT64_MIN in octal:       ");
  print_octal(INT64_MIN, 0);
  println();

  // print INT64_MIN in binary
  print(" INT64_MIN in binary:      ");
  print_binary(INT64_MIN, 64);
  println();
}