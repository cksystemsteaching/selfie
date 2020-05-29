uint64_t a[2];

int main(int argc, char** argv) {
  uint64_t b[2];
  uint64_t i;

  i = 0;

  a[i] = 21;
  a[i+1] = 10;

  b[i] = 1;
  b[i+1] = 10;

  return a[i] + a[1] + b[0] + b[i+1];
}
