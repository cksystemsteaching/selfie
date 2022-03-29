uint64_t* x;
uint64_t main() { uint64_t a;
  x = malloc(1); // rounded up to 8
  // touch to trigger page fault here
  *x = 0;
  // read 1 byte from console into x
  read(0, x, 1);
  a = *x;
  a = *(x + a); // segfault if input != 0
}