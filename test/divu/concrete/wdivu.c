// [-c test/divu/concrete/wdivu.c -n 2;<3,0,0,1>]
uint64_t main(uint64_t argc, uint64_t* argv) {
  return 3 / -10;
}
