/* 
The purpose of this code is to demonstrate the capabilities
of the monster model generator of selfie. Monster translates
the code to an SMT-LIB or BTOR2 formula that is satisfiable
if and only if the code exits with a non-zero exit code.

Solutions: #b00101000
           #b00110010
           #b00110100
*/

uint64_t main() {
  uint64_t  a;
  uint64_t* x;

  a = 0;
  x = malloc(8);

  read(1, x, 1);
  
  if(*x > 42) {
    *x = *x - 1;
    
    if(*x > 50)
      *x = *x - 1;
    else
      *x = *x + 1;
  } else
    *x = *x + 10;

  if(*x == 50)
    return 1;
  else
    return 0;
}