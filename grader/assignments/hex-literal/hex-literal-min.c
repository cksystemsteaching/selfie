int main(int argc, char** argv) {
  if (((uint64_t)-0x8000000000000000) == ((uint64_t)-9223372036854775808))
    return 42;
  else
    return 0;
}