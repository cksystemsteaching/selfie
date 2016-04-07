int x;          // this declares a globally visible variable called x
                // that represents a signed 32-bit integer value

int main() {    // this declares a globally visible function called main
                // that returns a signed 32-bit integer value

  // here the value of x is undefined

  x = 0;        // this assigns the value 0 to x

  // here the value of x is 0

  x = x + 1;    // this reads the value of x, adds 1 to it, and then
                // assigns the result to x

  // here the value of x is 1

  if (x == 1)   // this checks if the value of x is 1 and, if true,
    x = x + 1;  // increases the value of x by 1,
  else          // or else, if false,
    x = x - 1;  // decreases the value of x by 1

  // here the value of x is 2

  while (x > 0) // this checks if the value of x is greater than 0, and,
    x = x - 1;  // if true, decreases the value of x by 1, and then repeats
                // this until the value of x is not greater than 0 anymore

  // here the value of x is 0

  return x;     // this returns the value of x
}