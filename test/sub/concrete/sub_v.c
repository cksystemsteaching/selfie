// [-c test/sub/concrete/sub_v.c -n 2;<9,-86,-86,1>]
uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t x;
  uint64_t y;
  uint64_t z;
  x = 3;
  y = 89;
  z = x - y;
  return z;
}
