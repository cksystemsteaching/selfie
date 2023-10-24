uint64_t factorial(uint64_t n) {
  if (n <= 1)
    return n;
  else
    return n * factorial(n - 1);
}

uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  x = malloc(sizeof(uint64_t));

  *x = 0; // touch memory

  read(0, x, 1);

  *x = *x - 39;

  // 3628800 == factorial(10)
  a = factorial(*x);

  if (a == 3628800)
    // non-zero exit code if the input is '1' (== 49 == b00110001)
    return 1;
  else
    return 0;
}
