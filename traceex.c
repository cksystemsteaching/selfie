uint64_t g = 10;
uint64_t* p;

uint64_t main() {
  uint64_t x;
  uint64_t y;

  p = malloc(16);
  read(1, p, 15);

  x = 5;
  y = 20;

  return *p;
}
