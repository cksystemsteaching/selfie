// analyzor-input-bytes: 5
uint64_t main() {
  uint64_t  a;
  uint64_t  b;
  uint64_t* x;

  x = malloc(sizeof(uint64_t));

  *x = 0; // touch memory

  a = 0;
  b = 0;

  while (a < 5) {
    read(0, x, 1);

    if (*x == 48)
       b = b + 1;

    a = a + 1;
  }

  if (b == 5)
    return 1;
  else
    return 0;
}