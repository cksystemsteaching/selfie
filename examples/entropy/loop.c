// The input byte is taken through 16 * n rounds of x = 3 * x + 1 modulo 256,
// a bijection on bytes, so the result is 0 for exactly 1 of the 256 inputs,
// however many rounds: the depth grows with n and the count does not.
uint64_t main() {
  uint64_t  n;
  uint64_t  i;
  uint64_t* x;

  n = 1; // size

  x = malloc(sizeof(uint64_t));

  *x = 0; // touch memory

  read(0, x, 1);

  i = 0;

  while (i < 16 * n) {
    *x = (3 * *x + 1) % 256;

    i = i + 1;
  }

  if (*x == 0)
    return 1;
  else
    return 0;
}
