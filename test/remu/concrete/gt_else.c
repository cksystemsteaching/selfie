// [-c test/remu/concrete/gt_else.c -n 2;<12,8,8,1>]
uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t x;
  uint64_t y;
  uint64_t z;
  x = 8;
  y = 2;
  z = x % y;
  if(x > 8) {
    return z;
  } else {      //false case: x[8;8]
    return x;
  }
}
