int count(int n) {
  int c;

  c = 0;

  while (c < n)
    c = c + 1;

  return c;
}

int main() {
  return count(10000);
}