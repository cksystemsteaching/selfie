int x;          // this is a global variable declaration

int main() {    // this is a global function declaration
  x = 0;        // this is an assignment statement

  x = x + 1;    // this is an assignment statement

  if (x == 1)   // this is an if statement with
    x = x + 1;  // an assignment statement in the true case and
  else
    x = x - 1;  // an assignment statement in the false case

  while (x > 0) // this is a while statement with
    x = x - 1;  // an assignment statement in the true case

  return x;     // this is a return statement
}