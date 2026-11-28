// The n input bytes are the password, the digits from 0 on, for 1 of the
// 256^n inputs. A wrong byte ends the run: n + 1 paths.
uint64_t main() {
  uint64_t  n;
  uint64_t  i;
  uint64_t* x;

  n = 1; // size

  x = malloc(sizeof(uint64_t));

  *x = 0; // touch memory

  i = 0;

  while (i < n) {
    read(0, x, 1);

    if (*x != 48 + i)
      return 0;

    i = i + 1;
  }

  return 1;
}
