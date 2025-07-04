uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  x = malloc(sizeof(uint64_t));

  *x = 0; // touch memory

  read(0, x, 1);

  if (*x >= 128) {
    a = a + 1;
    *x = *x - 128;
  }
  if (*x >= 64) {
    a = a + 2;
    *x = *x - 64;
  }
  if (*x >= 32) {
    a = a + 4;
    *x = *x - 32;
  }
  if (*x >= 16) {
    a = a + 8;
    *x = *x - 16;
  }
  if (*x >= 8) {
    a = a + 16;
    *x = *x - 8;
  }
  if (*x >= 4) {
    a = a + 32;
    *x = *x - 4;
  }
  if (*x >= 2) {
    a = a + 64;
    *x = *x - 2;
  }
  if (*x >= 1) {
    a = a + 128;
    *x = *x - 1;
  }

  if (a == 140)
    // non-zero exit code if the input is '1' (== 49 == b00110001)
    return 1;
  else
    return 0;
}
