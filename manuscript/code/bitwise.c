// left shifting, bitwise ORing, and logical right shifting in C*

// libcstar procedures for printing
void initLibrary();
void print(uint64_t* s);
void printInteger(uint64_t n);
void printBinary(uint64_t n, uint64_t a);
void println();

// libcstar procedures for left and right shifting
uint64_t leftShift(uint64_t n, uint64_t b);
uint64_t rightShift(uint64_t n, uint64_t b);

uint64_t main() {
  uint64_t i;
  uint64_t j;
  uint64_t u;

  // initialize selfie's libcstar library
  initLibrary();

  // initialize the integer i to binary 0000000000000000000000000000000000000000000000000000000000000011
  i = 3;

  // initialize the integer u to i
  u = i;

  // repeat until i is equal to 0
  while (i != 0) {
    // print i in binary
    printBinary(i, 64);
    print(" in binary = ");
    printInteger(i);
    print(" in decimal");
    println();

    // remember value of i
    j = i;

    // shift i to the left by 6 bits
    i = leftShift(i, 6);

    // signed integer addition here amounts to bitwise OR because
    // the bits at the same index in u and i are never both 1 so
    // there will not be any carry bit set
    u = u + i;
  }

  // print u in binary
  printBinary(u, 64);
  print(" in binary = ");
  printInteger(u);
  print(" in decimal");
  println();

  // set i to its most recent value before it became 0
  i = j;

  // repeat until i is equal to 0
  while (i != 0) {
    // print i in binary
    printBinary(i, 64);
    print(" in binary = ");
    printInteger(i);
    print(" in decimal");
    println();

    // shift i to the right by 6 bits
    i = rightShift(i, 6);
  }
}