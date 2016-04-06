int f(int x, int y) {
  while (y > 0) {
    x = x + 1;
    y = y - 1;
  }

  return x;
}

int g(int x, int y) {
  if (y > 0)
    return g(x, y - 1) + 1;
  else
    return x;
}

int main() {
  return f(1,2) - g(1,2);
}