// left shifting, bitwise ORing, and logical right shifting in C*

// libcstar procedures for printing
void init_library();
void print(uint64_t* s);
void print_integer(uint64_t n);
void print_binary(uint64_t n, uint64_t a);
void println();

// libcstar procedures for left and right shifting
uint64_t left_shift(uint64_t n, uint64_t b);
uint64_t right_shift(uint64_t n, uint64_t b);

uint64_t main() {
  uint64_t i;
  uint64_t j;
  uint64_t u;

  // initialize selfie's libcstar library
  init_library();

  // initialize the integer i to binary 0000000000000000000000000000000000000000000000000000000000000011
  i = 3;

  // initialize the integer u to i
  u = i;

  // repeat until i is equal to 0
  while (i != 0) {
    // print i in binary
    print_binary(i, 64);
    print(" in binary = ");
    print_integer(i);
    print(" in decimal");
    println();

    // remember value of i
    j = i;

    // shift i to the left by 6 bits
    i = left_shift(i, 6);

    // signed integer addition here amounts to bitwise OR because
    // the bits at the same index in u and i are never both 1 so
    // there will not be any carry bit set
    u = u + i;
  }

  // print u in binary
  print_binary(u, 64);
  print(" in binary = ");
  print_integer(u);
  print(" in decimal");
  println();

  // set i to its most recent value before it became 0
  i = j;

  // repeat until i is equal to 0
  while (i != 0) {
    // print i in binary
    print_binary(i, 64);
    print(" in binary = ");
    print_integer(i);
    print(" in decimal");
    println();

    // shift i to the right by 6 bits
    i = right_shift(i, 6);
  }
}