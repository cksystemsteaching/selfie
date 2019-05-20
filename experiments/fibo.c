uint64_t fibonacci(uint64_t n) {
    if (n < 1)
        return 0;
    else if (n == 1)
        return 1;
    else
        return fibonacci(n-1) + fibonacci(n-2);
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t x;
  uint64_t res;

  x = input(0, 20, 1);

  res = fibonacci(x);

  return res;
}
