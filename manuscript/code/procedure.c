uint64_t x;

void p() {
  while (x > 0)
    x = x - 1;
}

uint64_t main() {
  x = 0;

  x = x + 1;

  if (x == 1)
    x = x + 1;
  else
    x = x - 1;

  p();

  return x;
}