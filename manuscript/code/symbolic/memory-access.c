/*
The purpose of this code is to demonstrate the capabilities
of the monster model generator of selfie. Monster translates
the code to an SMT-LIB or BTOR2 formula that is satisfiable
if and only if the code exits with a non-zero exit code, or
performs division by zero or invalid/unsafe memory accesses.
*/

uint64_t main() {
  uint64_t* x;

  x = malloc(8);

  // detection of the following two unsafe memory accesses requires --check-block-access

  // access memory address right above memory block but well below 4GB of memory addresses
  *x = *(x + 1);

  // access memory address right below memory block but still above code segment because of _bump variable
  *x = *(x + -1);

  // detection of the following three invalid memory accesses does not require --check-block-access

  // access code segment by reaching over _bump variable
  *x = *(x + -2);

  // access memory address right above 4GB of memory addresses
  *x = *(x + ((uint64_t*) 4294967296 - x));

  // access word-unaligned memory address
  *x = *((uint64_t*) ((uint64_t) x + 1));

  return 0;
}