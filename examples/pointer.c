uint64_t main() {
  uint64_t* x;

  x = malloc(2 * sizeof(uint64_t));

  *x = 0;

  *x = *x + 1;

  *(x + 1) = 0;

  x = x + 1;

  return *x;
}