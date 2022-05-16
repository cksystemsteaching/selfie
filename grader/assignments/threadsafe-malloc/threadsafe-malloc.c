uint64_t write(uint64_t fd, uint64_t* buffer, uint64_t bytes_to_write);

uint64_t pthread_create();
uint64_t pthread_join(uint64_t* wstatus);

uint64_t* c;

void print_integer(uint64_t i) {
  // single character number
  *c = 32 * 256 + 48 + i;
  write(1, c, 2);
}

int main(int argc, char** argv) {
  uint64_t pid;
  uint64_t* sum;
  uint64_t* sum2;

  sum2 = malloc(8);

  c = malloc(8);

  pid = pthread_create();

  sum = malloc(8 * 2);


  if (pid) {
    pthread_join(sum2);

    *sum = 11;
    *(sum + 1) = 12;

    sum2 = (uint64_t*) *sum2;

    return *sum + *(sum + 1) + *sum2 + *(sum2 + 1);
  } else {
    *sum = 9;
    *(sum + 1) = 10;

    return (uint64_t) sum;
  }

  //return 0;
}