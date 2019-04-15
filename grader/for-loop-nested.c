int main(int argc, char** argv) {
  uint64_t i;
  uint64_t j;
  uint64_t sum;

  sum = 0;

  for (i = 0; i < 3; i = i + 1)
    for (j = 0; j < 3; j = j + 1)
      sum = sum + 1;

  return sum;
}