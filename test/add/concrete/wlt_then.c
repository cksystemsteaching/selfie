// [-c test/add/concrete/wlt_then.c -n 2;<10,12,12,1>]
uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t x;
  uint64_t y;
  uint64_t z;
  x = 10;
  y = 2;
  z = x + y;
  if(x < -1) { //true case: z<12,12,1>
    return z;
  } else {
    return x;
  }
}
