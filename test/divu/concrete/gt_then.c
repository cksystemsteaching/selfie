// [-c test/divu/concrete/gt_then.c -n 2;<10,5,5,1>]
uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t x;
  uint64_t y;
  uint64_t z;
  x = 10;
  y = 2;
  z = x / y;
  if(x > 9) { //true case: z<5,5,1>
    return z;
  } else {
    return x;
  }
}
