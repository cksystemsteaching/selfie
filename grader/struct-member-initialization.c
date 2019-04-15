struct trivial_struct { 
  uint64_t member;
};

struct trivial_struct* my_struct;

int main(int argc, char** argv) { 
  my_struct = malloc(8);

  my_struct->member = 123;

  return 123;
}