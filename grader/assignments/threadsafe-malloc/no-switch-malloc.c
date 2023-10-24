uint64_t write(uint64_t fd, uint64_t* buffer, uint64_t bytes_to_write);

uint64_t pthread_create();
uint64_t pthread_join(uint64_t* wstatus);

uint64_t* foo;
uint64_t child;

int main(int argc, char** argv) {
  uint64_t pid;

  foo = "Hello World!    ";

  child = 0;

  pid = pthread_create();

  if (pid) {
    // main thread

    // make sure child is executed first
    // variable is shared
    while (child == 0) {}

    write(1, foo + 1, 8);

    return 0;

  } else {
    // child thread
    child = 1;

    // see if we switch back to main (parent)
    malloc(sizeof(uint64_t));

    write(1, foo, 8);

    return 0;
  }
}
