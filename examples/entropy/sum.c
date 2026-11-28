// The sum of n input bytes is 3 for (n + 2) choose (n - 1) of the 256^n
// inputs: 1, 4, 10, 20 for n = 1, 2, 3, 4. One path, whatever the input.
uint64_t main() {
  uint64_t  n;
  uint64_t  i;
  uint64_t  s;
  uint64_t* x;

  n = 1; // size

  x = malloc(sizeof(uint64_t));

  *x = 0; // touch memory

  s = 0;
  i = 0;

  while (i < n) {
    read(0, x, 1);

    s = s + *x;

    i = i + 1;
  }

  if (s == 3)
    return 1;
  else
    return 0;
}
