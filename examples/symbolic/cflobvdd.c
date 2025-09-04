uint64_t main() {
  uint64_t* x;
  uint64_t  a;
  uint64_t  b;
  uint64_t  x1;
  uint64_t  x2;

  x = malloc(sizeof(uint64_t));

  *x = 0; // touch memory

  a = 0;
  b = 0;

  while (a < 2) {
    read(0, x, 1);
    x1 = *x;
    read(0, x, 1);
    x2 = *x;

    if (x1 * x2 == 42)
       b = b + 1;

    a = a + 1;
  }

  if (b == 2)
    return 1;
  else
    return 0;
}