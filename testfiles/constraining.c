uint64_t main() {
  uint64_t* x;
  x = malloc(8);

  read(0, x, 1); // symbolic value [0, 255]

  *x = *x + 5;   // [5, 260]       |  [0, 4]  => SAT

  // satisfiable:
                   //  | forwards  |  backwards ^
  if (*x < 10) {  //  | [5, 260]   |  [5, 9]    |
    *x = *x + 5;  //  | [10, 265]  |  [5, 14]   |

    if (*x < 20)  //  | [10, 265]  |  [10, 19]  |
    return *x;    //  | [10, 265]  |  [10, 265] |
  }               //               v


  // unsatisfiable:
  //                 //  | forwards   |  backwards ^
  // if (*x < 10) {  //  | [5, 260]   |  [16, 9]   | => UNSAT
  //   *x = *x + 5;  //  | [10, 265]  |  [16, 260] |

  //   if (*x > 20)  //  | [10, 265]  |  [21, 265] |
  //     return *x;  //  | [10, 265]  |  [10, 265] |
  // }               //               v            


  return -1;
}
