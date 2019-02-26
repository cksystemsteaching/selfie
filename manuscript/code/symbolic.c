/* The purpose of this code is to demonstrate the capabilities
   of the monster symbolic execution engine of selfie. Monster
   translates the code to an SMT-LIB formula that is satisfiable
   if and only if the code exits with a non-zero exit code. */

uint64_t main() {
  uint64_t* x;

  x = malloc(8);

  read(1, x, 1);

  if (*x > 42)
  	return 1;
  else if (*x < 42)
  	return 1;
  else
  	return 0;
}