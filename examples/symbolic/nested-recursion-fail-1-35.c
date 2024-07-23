uint64_t factorial_upwards(uint64_t n) {
  if (n >= 10)
    return n;
  else
    return n * factorial_upwards(n + 1);
}

uint64_t modified_factorial(uint64_t n) {
  if (n > 1)
    return n * modified_factorial(n - 1);
  else
    return factorial_upwards(1);
}

uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  x = malloc(sizeof(uint64_t));

  *x = 0; // touch memory

  read(0, x, 1);

  *x = *x - 35;

  // 3628800 == 10! == factorial_upwards(1)
  // factorial_upwards(1) * 87178291200 == factorial_upwards(1) * 14! == modified_factorial(14)
  a = modified_factorial(*x);

  //           10! * 14!
  if (a == 3628800 * (2724321600 * 32))
    // non-zero exit code if the input is '1' (== 49 == b00110001)
    return 1;
  else
    return 0;
}
