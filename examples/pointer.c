uint64_t main() {
  uint64_t* x;

  x = malloc(16);

  *x = 0;

  *x = *x + 1;

  *(x + 1) = 0;

  x = x + 1;

  return *x;
}