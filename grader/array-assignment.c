uint64_t a[2];

int main(int argc, char** argv) {
  uint64_t b[2];

  a[0] = 1;
  a[1] = 3;

  b[0] = 2;
  b[1] = 4;

  return a[0] + a[1] + b[0] + b[1];
}