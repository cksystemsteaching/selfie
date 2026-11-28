// The compound assignments of riscr.md: x += e, x -= e,
// and x ^= e, which riscr compiles without history. The program is C, so
// gcc compiles it as well, and make garbage-free compares the two.
//
// Every line that ends in "// garbage-free" is a compound assignment: the
// Makefile takes these lines out and checks that the program without them
// leaves the history pointer where the program with them leaves it.

void* malloc(unsigned long);

uint64_t g;

uint64_t sum_of_squares(uint64_t n) {
  uint64_t s;
  uint64_t i;

  s = 0;
  i = 0;

  while (i < n) {
    s += i * i; // garbage-free

    i = i + 1;
  }

  return s;
}

int main() {
  uint64_t  x;
  uint64_t  y;
  uint64_t  z;
  uint64_t* p;

  p = malloc(8);

  *p = 3;

  x = 5;
  y = 7;
  g = 100;

  x += y * 3 + g; // garbage-free
  x -= (y + 1) / 2; // garbage-free
  x ^= y < g; // garbage-free
  g += x; // garbage-free
  g -= 2147481600; // garbage-free
  g -= 2048; // garbage-free
  g += 2048; // garbage-free
  g += 2147481600; // garbage-free
  *p += g - x * (y - 6) % 1000; // garbage-free
  *(p + 0) ^= x + y * 2; // garbage-free

  z = sum_of_squares(4);

  return x + z + *p + g - 507;
}
