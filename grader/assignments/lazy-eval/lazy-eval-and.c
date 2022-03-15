uint64_t endless() {
  uint64_t x;

  while (1) {
    x = 1;
  }

  return x;
}

int main(int argc, char** argv) {
  uint64_t a;
  uint64_t b;
  uint64_t c;

  a = 1;
  b = 1;
  c = 0;

  if (a && b)
    if (a && c && endless())
      return 0;
    else
      return 42;
  else
    return 0;
}
