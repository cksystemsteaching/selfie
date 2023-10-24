uint64_t lr(uint64_t address);
uint64_t sc(uint64_t address, uint64_t value);

uint64_t pthread_create();
uint64_t pthread_join(uint64_t* wstatus);

// used to force context switches
// there are no process children, so this does nothing
uint64_t wait(uint64_t* wstatus);

uint64_t child = 0;

int main(int argc, char** argv) {
  uint64_t* address;
  uint64_t* status;
  uint64_t pid;
  uint64_t x;

  address = malloc(sizeof(uint64_t));
  *address = 10;

  status = malloc(sizeof(uint64_t));

  pid = pthread_create();

  if (pid == 0) {
    // child
    child = 1;

    x = lr(address);

    wait((uint64_t*) 0);

    x = sc(address, x);

    return x; // must be 1 (failed)
  } else {
    // parent

    // make sure child is running first
    while (child == 0)
      wait((uint64_t*) 0);

    x = lr(address);

    if (x == 10) {
      if (sc(address, 42))
        return 7; // parent sc may not fail but it did
    } else
      return 8; // wrong x value, something went entirely wrong

    // switch to child
    x = pthread_join(status);

    if (x == 0)
      return 9; // child sc must fail but it did not
    else if (*address == 10)
      return 6; // child sc stored a new value which it may not do

    // should be 1 * 42 = 42
    return *status * *address;
  }
}