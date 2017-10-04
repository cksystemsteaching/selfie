uint64_t x;

uint64_t f(uint64_t x) {
  while (x > 0)
    x = x - 1;

  return x;
}

uint64_t main() {
  x = 0;

  x = x + 1;

  if (x == 1)
    x = x + 1;
  else
    x = x - 1;

  return f(x);
}