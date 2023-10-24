uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  x = malloc(sizeof(uint64_t));

  *x = 0; // touch memory

  read(0, x, 1);

  *x = *x - 48;

  // division by zero if the input is '0' (== 48 == b00110000)
  a = 41 + (1 / *x);

  // division by zero if the input is '2' (== 50 == b00110010)
  if (*x == 2)
    a = 41 + (1 / 0);

  if (a == 42)
    // non-zero exit code if the input is '1' (== 49 == b00110001)
    return 1;
  else
    return 0;
}
