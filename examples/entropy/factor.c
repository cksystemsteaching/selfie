// Two numbers of n input bytes each are the factors of the product of two
// primes of n bytes for 2 of the 256^(2n) inputs, the primes in either
// order: the largest primes below 256^n times the golden ratio less one
// and below 256^n over the square root of 2, so that their bits are no
// pattern. One path, and one multiplication to undo. For n up to 4.
uint64_t main() {
  uint64_t  n;
  uint64_t  i;
  uint64_t  a;
  uint64_t  b;
  uint64_t  product;
  uint64_t* x;

  n = 1; // size

  if (n == 1)
    product = 28417; // 157 * 181
  else if (n == 2)
    product = 1876602163; // 40499 * 46337
  else if (n == 3)
    product = 123008928220799; // 10368881 * 11863279
  else
    product = 8061522714793830173; // 2654435761 * 3037000493

  x = malloc(sizeof(uint64_t));

  *x = 0; // touch memory

  a = 0;
  i = 0;

  while (i < n) {
    read(0, x, 1);

    a = a * 256 + *x;

    i = i + 1;
  }

  b = 0;
  i = 0;

  while (i < n) {
    read(0, x, 1);

    b = b * 256 + *x;

    i = i + 1;
  }

  if (a * b == product)
    return 1;
  else
    return 0;
}
