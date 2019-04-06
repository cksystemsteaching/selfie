int main(int argc, char** argv) {
  return 40 & ~((uint64_t)18446744073709551573) | 42;
}