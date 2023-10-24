uint64_t ackermann(uint64_t m, uint64_t n) {
  if (m != 0) {
    if (n != 0)
      return ackermann(m - 1, ackermann(m, n - 1));
    else
      return ackermann(m - 1, 1);
  } else
    return n + 1;
}

uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  x = malloc(sizeof(uint64_t));

  *x = 0; // touch memory

  read(0, x, 1);

  *x = *x - 47;

  // 4 == ackermann(1, 2)
  a = ackermann(1, *x);

  if (a == 4)
    // non-zero exit code if the input is '1' (== 49 == b00110001)
    return 1;
  else
    return 0;
}
