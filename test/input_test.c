// [-c test/input_test.c -v 3 -n 2;<6,0,10,1>;<8,false>;]
uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t x;
  x = input(0, 10, 1);
  if( x < 15)
    return x;
  else
    return x;
}
