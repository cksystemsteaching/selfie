struct nested_struct {
  uint64_t member;
  struct nested_struct* another_struct;
};

struct nested_struct* my_struct;

int main(int argc, char** argv) { 
  my_struct = malloc(16);

  my_struct->another_struct = malloc(16);
  my_struct->another_struct->member = 123;

  return my_struct->another_struct->member;
}
