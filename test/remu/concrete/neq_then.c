// [-c test/remu/concrete/neq_then.c -n 2;<10,0,0,1>;<12,false>]
uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t x;
  uint64_t y;
  uint64_t z;
  x = 10;
  y = 2;
  z = x % y;
  if(x != 9) { //true case: z<0,0,1>
    return z;
  } else {
    return x;
  }
}
