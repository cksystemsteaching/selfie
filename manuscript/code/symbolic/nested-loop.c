/* 
The purpose of this code is to demonstrate the capabilities
of the monster model generator of selfie. Monster translates
the code to an SMT-LIB or BTOR2 formula that is satisfiable
if and only if the code exits with a non-zero exit code.

Solutions: (#b00000011, #b00000000)
           (#b00000010, #b00000001)
           (#b00000001, #b00000010)
           (#b00000000, #b00000011)
*/

uint64_t main() {
  uint64_t  a;
  uint64_t* x;
  uint64_t* y;

  a = 0;
  x = malloc(8);
  y = malloc(8);

  read(1, x, 1);
  read(1, y, 1);

  while(*x < 5) {

    while(*y < 5) {
      a = a + 1;
      *y = *y + 1;
    }
    
    a = a + 1;
    *x = *x + 1;
  }

  if (a == 7)
    return 1;
  else
    return 0;
}