uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  a = 33;
  x = malloc(sizeof(uint64_t));

  *x = 0; // touch memory

  read(0, x, 1);

  *x = *x - 40;

  while (*x > 0) {
    a = a + 1;
    *x = *x - 1;
  }

  if (a == 42)
    // non-zero exit code if the input is '1' (== 49 == b00110001)
    return 1;
  else
    return 0;
}
