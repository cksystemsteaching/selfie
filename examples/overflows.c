// printing overflows of 64-bit integers in C*

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

  // print UINT64_MAX+1 in decimal
  print("UINT64_MAX+1 in decimal:     ");
  print_unsigned_integer(UINT64_MAX+1);
  println();

  // print UINT64_MAX+1 in hexadecimal
  print("UINT64_MAX+1 in hexadecimal: ");
  print_hexadecimal(UINT64_MAX+1, 0);
  println();

  // print UINT64_MAX+1 in octal
  print("UINT64_MAX+1 in octal:       ");
  print_octal(UINT64_MAX+1, 0);
  println();

  // print UINT64_MAX+1 in binary
  print("UINT64_MAX+1 in binary:      ");
  print_binary(UINT64_MAX+1, 64);
  println();

  // print 0-1 in decimal
  print("0-1 in decimal:              ");
  print_integer(0-1);
  print(" (as signed 64-bit integer)\n");

  // print 0-1 in decimal
  print("0-1 in decimal:              ");
  print_unsigned_integer(0-1);
  print(" (as unsigned integer)\n");

  // print 0-1 in hexadecimal
  print("0-1 in hexadecimal:          ");
  print_hexadecimal(0-1, 0);
  println();

  // print 0-1 in octal
  print("0-1 in octal:                ");
  print_octal(0-1, 0);
  println();

  // print 0-1 in binary
  print("0-1 in binary:               ");
  print_binary(0-1, 64);
  println();

  // print INT64_MAX+1 in decimal
  print("INT64_MAX+1 in decimal:      ");
  print_integer(INT64_MAX+1);
  print(" (as signed 64-bit integer)\n");

  // print INT64_MAX+1 in decimal
  print("INT64_MAX+1 in decimal:      ");
  print_unsigned_integer(INT64_MAX+1);
  print(" (as unsigned integer)\n");

  // print INT64_MAX+1 in hexadecimal
  print("INT64_MAX+1 in hexadecimal:  ");
  print_hexadecimal(INT64_MAX+1, 0);
  println();

  // print INT64_MAX+1 in octal
  print("INT64_MAX+1 in octal:        ");
  print_octal(INT64_MAX+1, 0);
  println();

  // print INT64_MAX+1 in binary
  print("INT64_MAX+1 in binary:       ");
  print_binary(INT64_MAX+1, 64);
  println();

  // print INT64_MIN-1 in decimal
  print("INT64_MIN-1 in decimal:      ");
  print_integer(INT64_MIN-1);
  print(" (as signed 64-bit integer)\n");

  // print INT64_MIN-1 in decimal
  print("INT64_MIN-1 in decimal:      ");
  print_unsigned_integer(INT64_MIN-1);
  print(" (as unsigned integer)\n");

  // print INT64_MIN-1 in hexadecimal
  print("INT64_MIN-1 in hexadecimal:  ");
  print_hexadecimal(INT64_MIN-1, 0);
  println();

  // print INT64_MIN-1 in octal
  print("INT64_MIN-1 in octal:        ");
  print_octal(INT64_MIN-1, 0);
  println();

  // print INT64_MIN-1 in binary
  print("INT64_MIN-1 in binary:       ");
  print_binary(INT64_MIN-1, 64);
  println();
}