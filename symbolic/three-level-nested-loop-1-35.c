/*
The purpose of this code is to demonstrate the capabilities
of the monster model generator of selfie. Monster translates
the code to an SMT-LIB or BTOR2 formula that is satisfiable
if and only if the code exits with a non-zero exit code, or
performs division by zero or invalid/unsafe memory accesses.

Input == #b00110001 (== 49 == '1')
*/

uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  a = 0;
  x = malloc(8);

  read(0, x, 1);

  *x = *x - 49;

  while (*x < 15) {
    while (*x < 10) {
      while (*x < 5) {
        a = a + 1;
        *x = *x + 1;
      }

      a = a + 1;
      *x = *x + 1;
    }

    a = a + 1;
    *x = *x + 1;
  }

  a = a + 27;

  if (a == 42)
    return 1;
  else
    return 0;
}
