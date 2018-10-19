struct nested_struct {
  uint64_t member;
  struct nested_struct* another_struct;
};

struct nested_struct* my_struct;

uint64_t main(uint64_t argc, uint64_t* argv) { 
  my_struct = malloc(16);

  my_struct->another_struct = malloc(16);
  my_struct->another_struct->member = 123;

  return my_struct->another_struct->member;
}
