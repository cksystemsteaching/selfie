uint64_t a[2];

int main(int argc, char** argv) {
  uint64_t b[2];

  a[0] = 21;
  a[1] = 10;

  b[0] = 1;
  b[1] = 10;

  return a[0] + a[1] + b[0] + b[1];
}