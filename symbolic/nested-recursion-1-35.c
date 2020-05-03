/*
The purpose of this code is to demonstrate the capabilities
of the monster model generator of selfie. Monster translates
the code to an SMT-LIB or BTOR2 formula that is satisfiable
if and only if the code exits with a non-zero exit code, or
performs division by zero or invalid/unsafe memory accesses.

Input == #b00110001 (== 49 == '1')
*/

uint64_t factorial_upwards(uint64_t n) {
  if (n >= 10)
    return n;
  else
    return n * factorial_upwards(n + 1);
}

uint64_t modified_factorial(uint64_t n) {
  if (n > 1)
    return n * modified_factorial(n - 1);
  else
    return factorial_upwards(1);
}

uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  x = malloc(8);

  read(0, x, 1);

  *x = *x - 35;

  a = modified_factorial(*x);

  //           10! * 14!
  if (a == 3628800 * 87178291200)
    return 1;
  else
    return 0;
}
