int main(int argc, char** argv) {
  uint64_t a;
  uint64_t b;
  uint64_t c;
  uint64_t d;

  a = 1;
  b = 0;
  c = 0;

  if (a && b || c)
    return 0;
  else
    if (c || a && b)
      return 0;
    else
      return 42;
}
