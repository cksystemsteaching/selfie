int x;

int main() {
  x = 0;

  x = x + 1;

  if (x == 1)
    x = x + 1;
  else
    x = x - 1;

  while (x > 0)
    x = x - 1;

  return x;
}