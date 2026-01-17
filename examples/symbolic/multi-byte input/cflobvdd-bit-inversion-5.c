uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  x = malloc(sizeof(uint64_t));

  *x = 0; // touch memory

  read(0, x, 1);

  *x = *x - 48; // ASCII '0'

  a = 0;

  if (*x >= 16) {
    a = a + 1;
    *x = *x - 16;
  }
  if (*x >= 8) {
    a = a + 2;
    *x = *x - 8;
  }
  if (*x >= 4) {
    a = a + 4;
    *x = *x - 4;
  }
  if (*x >= 2) {
    a = a + 8;
    *x = *x - 2;
  }
  if (*x >= 1) {
    a = a + 16;
    *x = *x - 1;
  }

  if (a == 24)
    // non-zero exit code if the input is '3' (== 51)
    return 1;
  else
    return 0;
}
