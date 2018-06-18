// [-c test/sub/concrete/geq_then.c -n 2;<10,8,8,1>]
uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t x;
  uint64_t y;
  uint64_t z;
  x = 10;
  y = 2;
  z = x - y;
  if(x >= 10) { //true case: z<8,8,1>
    return z;
  } else {
    return x;
  }
}
