// [-c test/add/concrete/wadd_v.c -n 2;<9,-7,-7,1>]
uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t x;
  uint64_t y;
  uint64_t z;
  x = 3;
  y = -10;
  z = x + y;
  return z;
}
