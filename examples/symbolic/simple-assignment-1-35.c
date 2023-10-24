uint64_t main() {
  uint64_t* x;

  x = malloc(sizeof(uint64_t));

  *x = 0; // touch memory

  read(0, x, 1);

  *x = *x - 6;

  if (*x > 42)
    // non-zero exit code if the input is > '0' (== 48 == b00110000)
    return 1;
  else if (*x < 42)
    // non-zero exit code if the input is < '0' (== 48 == b00110000)
    return 1;
  else
    return 0;
}
