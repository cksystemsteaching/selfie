uint64_t* x;

uint64_t main() {
    uint64_t y;
    uint64_t z;

    uint64_t* a;

    x = malloc(8);
    a = malloc(8);
    y = 15;
    z = 50;

    read(0, x, 1); // symbolic [0,255]
    read(0, a, 1);

    if (*a < z) {
      if (*x < y) { // T: [0,14]          - F: [15,255]
        if (*x > y) // T: [16,14] (unsat) - F: [0,14]
          z = 1;
      } else
        z = 0;

    } else {
      if (*x < y) { // T: [0,14]          - F: [15,255]
        if (*x > y) // T: [16,14] (unsat) - F: [0,14]
          z = 1;
      } else
        z = 0;
    }

    return z;
}
