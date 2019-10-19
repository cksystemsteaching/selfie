void change(uint64_t b[2]) {
  b[0] = 20;
  b[1] = 22;
}

int main(int argc, char** argv) {
  uint64_t a[2];

  change(a);

  return a[0] + a[1];
}