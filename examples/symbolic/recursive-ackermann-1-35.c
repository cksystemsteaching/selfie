/*
The purpose of this code is to demonstrate the capabilities
of the monster model generator of selfie. Monster translates
the code to an SMT-LIB or BTOR2 formula that is satisfiable
if and only if the code exits with a non-zero exit code, or
performs division by zero or invalid/unsafe memory accesses.

Input == #b00110001 (== 49 == '1')
*/

uint64_t ackermann(uint64_t m, uint64_t n) {
  if (m != 0) {
    if (n != 0)
      return ackermann(m - 1, ackermann(m, n - 1));
    else
      return ackermann(m - 1, 1);
  } else
    return n + 1;
}

uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  x = malloc(8);

  read(0, x, 1);

  *x = *x - 47;

  a = ackermann(1, *x);

  if (a == 4)
    return 1;
  else
    return 0;
}
