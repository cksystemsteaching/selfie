uint64_t main() {
  uint64_t* x;

  x = malloc(8);

  read(0,x,8);  // symbolic [0, UINT64_MAX] = [0,-1]

  *x = *x + 5; // [5,4]

  if (*x < 10) // [5,4] -> I: [5,-1], II: [0,4]
    return 1;  //      true:  [5,9],      [0,4]
               //      false: [10,-1],     ---
  return 0;
}
