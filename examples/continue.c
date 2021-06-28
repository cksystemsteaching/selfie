uint64_t x;

uint64_t main() {
  x = 32;

  while (x == 32) {
    x = x + 2;

    continue;

    x = x + 100;
  }

  while (x < 42) {
    while (x < 40) {
      x = x + 1;

      continue;

      x = x + 100;
    }

    x = x + 1;

    continue;

    x = x + 100;
  }

  return x; // 42
}