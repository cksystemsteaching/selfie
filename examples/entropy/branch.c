// Each of the n input bytes is below 128 for 128^n of the 256^n inputs:
// 7 * n of 8 * n bits. Every byte is a branch: 2^n paths, and far more
// bad inputs than can be listed.
uint64_t main() {
  uint64_t  n;
  uint64_t  i;
  uint64_t  c;
  uint64_t* x;

  n = 1; // size

  x = malloc(sizeof(uint64_t));

  *x = 0; // touch memory

  c = 0;
  i = 0;

  while (i < n) {
    read(0, x, 1);

    if (*x < 128)
      c = c + 1;

    i = i + 1;
  }

  if (c == n)
    return 1;
  else
    return 0;
}
