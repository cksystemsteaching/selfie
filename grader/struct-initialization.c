struct empty_struct { };

struct empty_struct* my_struct;

uint64_t main(uint64_t argc, uint64_t* argv) { 
  my_struct = malloc(8);
}