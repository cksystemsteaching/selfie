uint64_t write(uint64_t fd, uint64_t* buffer, uint64_t bytes_to_write);

uint64_t pthread_create();
uint64_t pthread_join(uint64_t* wstatus);

uint64_t lr(uint64_t address);
uint64_t sc(uint64_t address, uint64_t value);

uint64_t* id;
uint64_t* c;

uint64_t allocate_id() {
  uint64_t value;

  value = lr((uint64_t) id);

  while (sc((uint64_t) id, value + 1)) {
    value = lr((uint64_t) id);
  }

  return value;
}

void print_integer(uint64_t i) {
  // single character number
  *c = 32 * 256 + 48 + i;
  write(1, c, 2);
}

int main(int argc, char** argv) { 
  uint64_t pid1;
  uint64_t pid2;
  uint64_t pid3;
  uint64_t* s;
  uint64_t* results;
  uint64_t i;

  id = malloc(8);

  *id = 0;

  s = malloc(8);

  c = malloc(8);

  init_stack();

  push(allocate_id());
  push(allocate_id());
  push(allocate_id());
  push(allocate_id());
  push(allocate_id());
  push(allocate_id());
  push(allocate_id());
  push(allocate_id());

  // 3^2 processes
  pid1 = pthread_create();
  pid2 = pthread_create();
  pid3 = pthread_create();

  print_integer(pop());

  // do not wait for child-threads of the parent-process
  if (pid3 == 0)
    pid2 = 0;
  if (pid2 == 0)
    pid1 = 0;

  if (pid1)
    pthread_join(s);
  if (pid2)
    pthread_join(s);
  if (pid3)
    pthread_join(s);
}
