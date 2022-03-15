int main(int argc, char** argv) {
  uint64_t a;
  uint64_t b;
  uint64_t c;
  uint64_t d;

  a = 0;
  b = 0;
  c = 0;
  d = 1;

  a = b || d;
  c = b && d;

  a = !(!(d));

  if (a || b)
    if (b || c)
      return 0;
    else if (c || d)
      if ((a && b) || (a && c) || (a && d))
        return (b || c || d) * a * 42 * !b * !(c && d) * (d);
      else
        return 0;
    else
      return 0;
  else
    return 0;
}
