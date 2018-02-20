uint64_t* x;

uint64_t main() {
    uint64_t y;
    uint64_t z;
    uint64_t a;
    uint64_t b;
    uint64_t c;

    x = malloc(8);

    a = 15;
    b = 10;
    c = 5;

    read(0, x, 1);        // symbolic [0, 255]

    if (*x < a) {         // x < 15
      if (*x > a){            // x > 15
        z = 1;                    // unsat TT [16,15]
      } else {            // x <= 15
        if (*x < b) {         // x < 10
          z = 0;                  // sat TFT [0,9]
        } else {              // x >= 10
          if (*x < c)             // x < 5
            z = 1;                    // unsat TFFT [10,4]
          else                    // x >= 5
            z = 0;                    // sat TFFF [10,14]
        }
      }
    } else                // x >= 15
      z = 0;                  // sat F [15,255]

    return z; // sat F
}
