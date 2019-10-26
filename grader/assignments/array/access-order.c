int main(int argc, char** argv) {
  uint64_t a[2][2];
  uint64_t* p;

  // write consecutive numbers in row major order
  a[0][0] = 0;
  a[0][1] = 1;
  a[1][0] = 2;
  a[1][1] = 3;

  p = (uint64_t*) a;

  if (*p == 0)
    if (*(p + 1) == 1)
      if (*(p + 2) == 2)
        if (*(p + 3) == 3)
          // is row-major order
          return 0;

  // is column-major order
  return 1;
}