uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t  n;
  uint64_t* x;
  uint64_t  a;
  uint64_t  b;
  uint64_t  x1;
  uint64_t  x2;

  // asserting one single-digit console argument
  n = *((uint64_t*) *(argv + 1)) % 256 - '0';
  // or else initialize n to some constant >= 0

  x = malloc(sizeof(uint64_t));

  *x = 0; // touch memory

  a = 0;
  b = 0;

  while (a < n) {
    read(0, x, 1);
    x1 = *x;
    read(0, x, 1);
    x2 = *x;

    if (x1 * x2 == 42)
       b = b + 1;

    a = a + 1;
  }

  if (b == n)
    return 1;
  else
    return 0;
}