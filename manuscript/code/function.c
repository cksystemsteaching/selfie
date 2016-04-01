int x;

int f(int x) {
  while (x > 0)
    x = x - 1;

  return x;
}

int main() {
  x = 0;

  x = x + 1;

  if (x == 1)
    x = x + 1;
  else
    x = x - 1;

  return f(x);
}