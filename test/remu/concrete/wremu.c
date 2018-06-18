// [-c test/remu/concrete/wremu.c -n 2;<3,3,3,1>]
uint64_t main(uint64_t argc, uint64_t* argv) {
  return 3 % -10;
}
