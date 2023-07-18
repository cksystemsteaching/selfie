// looping for measuring overhead of timer interrupts
// as upper bound on overhead of context switching
uint64_t main() {
  uint64_t i;

  i = 0;

  while (i < 1000000000)
    i = i + 1;
}