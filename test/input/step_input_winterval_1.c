// [-c test/input/step_input_winterval_1.c -n 2;<6,-10,10,7>]

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t x;
  x = input(-10, 10, 7);
  return x;
}
