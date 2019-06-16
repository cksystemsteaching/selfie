int main(int argc, char** argv) {
  uint64_t i;
  uint64_t sum;

  sum = 0;

  for (i = 0; i < 3; i = i + 1)
    sum = sum + i;

  return sum + 39;
}