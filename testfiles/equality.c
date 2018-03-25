uint64_t main() {
  uint64_t* x;

  x = malloc(8);

  read(0,x,1);  // symbolic [0,255]

  if (*x == 10) // -> I: [10,10] (t), II: [0,9] (f), III: [11,255] (f)
    return 1;

  return 0;
}
