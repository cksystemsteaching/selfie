struct nested_struct {
  uint64_t member;
  struct nested_struct* another_struct;
};

struct nested_struct* my_struct;

uint64_t modify_member(struct nested_struct* parameter) {
  uint64_t previous;

  previous = parameter->another_struct->member;

  parameter->another_struct->member = 321;

  return previous;
}

int main(int argc, char** argv) { 
  my_struct = malloc(16);

  my_struct->another_struct = malloc(16);
  my_struct->another_struct->member = 123;

  return modify_member(my_struct) == 123 && my_struct->another_struct->member == 321;
}
