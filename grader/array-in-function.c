uint64_t a[2];

void change(uint64_t b[2]) {
  b[0] = 1;
  b[1] = 3;
}

int main(int argc, char** argv) { 
  change(a);
  return a[0] + a[1];
}