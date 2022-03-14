int main(int argc, char** argv) {
  uint64_t a;
  uint64_t b;
  uint64_t c;

  a = 1;
  b = 1;
  c = 0;

  if ((a && c) != (c && a))
    return 0;

  if (a && b)
    if (a && b && c)
      return 0;
    else
      return 42 * (a && b);
  else
    return 0;
}
