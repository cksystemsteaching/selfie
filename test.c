uint64_t main() {
    uint64_t* x;
    uint64_t y;
    uint64_t z;


    x = malloc(8);
    y = 15;

    read(0, x, 1); // symbolic [0, 255]

    if (*x < y) {
      if (*x > y){
        z = 0;
      }
    } else {
      z = 1;
    }

    return z;
}
