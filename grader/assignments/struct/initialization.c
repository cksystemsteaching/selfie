struct empty_struct { };

struct empty_struct* my_struct;

int main(int argc, char** argv) { 
  my_struct = malloc(8);
}