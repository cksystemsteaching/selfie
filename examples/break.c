uint64_t x;

uint64_t main() {
  x = 32;

  while (1) {
    x = x + 2;

    break;

    x = x + 100;
  }

  while (1) {
    while (1) {
      x = x + 3;

      break;

      x = x + 100;
    }

    x = x + 5;

    break;

    x = x + 100;
  }

  while (1) {
    break;

    x = x + 100;
  }

  return x; // 42
}