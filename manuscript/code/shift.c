// printing left and right shifted integer values in C*

// libcstar procedures for printing
void initLibrary();
void print(int* s);
void printInteger(int n);
void printBinary(int n, int a);
void println();

// libcstar procedures for left and right shifting
int leftShift(int n, int b);
int rightShift(int n, int b);

int main() {
  int i;
  int j;

  // initialize selfie's libcstar library
  initLibrary();

  // initialize the integer i to binary 00000000000000000000000000000011
  i = 3;

  // repeat until i is equal to 0
  while (i != 0) {
    // print i in binary
    printBinary(i, 32);
    print(" in binary = ");
    printInteger(i);
    print(" in decimal");
    println();

    // remember value of i
    j = i;

    // shift i to the left by 6 bits
    i = leftShift(i, 6);
  }

  // set i to its most recent value before it became 0
  i = j;

  // repeat until i is equal to 0
  while (i != 0) {
    // print i in binary
    printBinary(i, 32);
    print(" in binary = ");
    printInteger(i);
    print(" in decimal");
    println();

    // shift i to the right by 6 bits
    i = rightShift(i, 6);
  }
}