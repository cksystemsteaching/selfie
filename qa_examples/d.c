uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  x = malloc(8);

  *x = 0; // touch memory

  read(0, x, 1);

  a = 1 / *x;

  return 0;
}
