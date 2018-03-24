uint64_t main() {
  uint64_t* x;

  uint64_t y;


  x = malloc(8);
  y = 10;

  read(0,x,8);

  if (*x == y)
    return 1;

  return 0;
}
