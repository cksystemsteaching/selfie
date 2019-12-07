uint64_t sizeof_uint64 = 8;
uint64_t number_of_forks = 3;

// global variable for pointing to the "Hello World!    " string
uint64_t* foo;

// main procedure for printing "Hello World!    " on the console
int main(int argc, char** argv) {
  uint64_t pid;
  uint64_t times_to_wait;
  uint64_t i;
  uint64_t* status;

  times_to_wait = 0;

  // create 2^3 processes
  i = 0;

  while (i < number_of_forks) {
    pid = fork();

    if (pid != 0)
      times_to_wait = times_to_wait + 1;
    else
      times_to_wait = 0;

    i = i + 1;
  }

  // point to the "Hello World!    " string
  foo = "Hello World!    ";

  // strings are actually stored in chunks of 8 characters in memory,
  // that is, here as "Hello Wo", and "rld!    " which allows us to
  // print them conveniently in chunks of 8 characters at a time

  // as long as there are characters print them
  while (*foo != 0) {
    // 1 means that we print to the console
    // foo points to a chunk of 8 characters
    // 8 means that we print 8 characters
    write(1, foo, 8);

    // go to the next chunk of 8 characters
    foo = foo + 1;
  }

  status = malloc(sizeof_uint64);

  i = 0;

  while (i < times_to_wait) {
    wait(status);

    i = i + 1;
  }
}