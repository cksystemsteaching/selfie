uint64_t f(uint64_t x, uint64_t y) {
  while (y > 0) {
    x = x + 1;
    y = y - 1;
  }

  return x;
}

uint64_t g(uint64_t x, uint64_t y) {
  if (y > 0)
    return g(x, y - 1) + 1;
  else
    return x;
}

uint64_t main() {
  return f(1,2) - g(1,2);
}