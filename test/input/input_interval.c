// [-c test/input/input_interval.c -n 2;<6,10,-10,1>]

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t x;
  x = input(10, -10, 1); //x[10;-10]
  return x;
}
