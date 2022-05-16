uint64_t write(uint64_t fd, uint64_t* buffer, uint64_t bytes_to_write);

uint64_t pthread_create();
uint64_t pthread_join(uint64_t* wstatus);

int main(int argc, char** argv) {
  uint64_t pid;
  uint64_t* sum;
  uint64_t* sum2;

  sum2 = malloc(8);

  pid = pthread_create();

  sum = malloc(8 * 2);

  if (pid) {
    // main thread

    pthread_join(sum2);

    // sum2 points to sum which points to 18 and 19
    // so dereference to make sum2 point directly to 18 and 19
    sum2 = (uint64_t*) *sum2;

    *sum = 2;
    *(sum + 1) = 3;

    // success: 2 + 3 + 18 + 19 = 42
    // failure: 2 + 3 + 2 + 3 = 10  (18 and 19 were overwritten)
    return *sum + *(sum + 1) + *sum2 + *(sum2 + 1);

  } else {
    // child thread

    *sum = 18;
    *(sum + 1) = 19;

    return (uint64_t) sum;
  }
}
