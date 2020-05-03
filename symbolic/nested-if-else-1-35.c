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

  a = 40;
  x = malloc(8);

  read(1, x, 1);
  
  if (*x > 48) {
    *x = *x - 47;

    if (*x == 2)
      a = a + *x;
    else
      a = a + (*x * 0);
  } else
    a = a + (*x * 0);

  if (a == 42)
    return 1;
  else
    return 0;
}