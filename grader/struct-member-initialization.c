struct trivial_struct { 
  uint64_t member;
};

struct trivial_struct* my_struct;

uint64_t main(uint64_t argc, uint64_t* argv) { 
  my_struct = malloc(8);

  my_struct->member = 123;

  return 123;
}