// [-c test/divu/concrete/zero_divu.c -n 2;<3,8,8,1>]
uint64_t main(uint64_t argc, uint64_t* argv) {
  return 3 / 0;
}
