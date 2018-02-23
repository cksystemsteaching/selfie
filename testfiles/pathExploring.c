uint64_t main() {
    uint64_t* x;
    uint64_t y;
    uint64_t z;

    x = malloc(8);
    y = 15;

    read(0, x, 1); // symbolic [0,255]

    if (y > *x) { // T: [0,14]          - F: [15,255]
      if (y < *x) // T: [16,14] (unsat) - F: [0,14]
        z = 1;
    } else
      z = 0;

    return z;
}
