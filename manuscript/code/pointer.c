int main() {
  int *x;

  x = malloc(8);

  *x = 0;

  *x = *x + 1;

  *(x + 1) = 0;

  x = x + 1;

  return *x;
}