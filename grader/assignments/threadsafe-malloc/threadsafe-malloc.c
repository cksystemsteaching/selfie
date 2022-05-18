uint64_t pthread_create();
uint64_t pthread_join(uint64_t* wstatus);
void pthread_exit(uint64_t code);

uint64_t thread;

void force_switch() {
  uint64_t pid;

  // forces a switch
  pid = pthread_create();

  // newly created thread immediately runs out
  if (pid == 0)
    pthread_exit(0);
  else
    pthread_join((uint64_t*) 0);
}

int main(int argc, char** argv) {
  uint64_t pid;
  uint64_t counter;
  uint64_t i;
  uint64_t* p1;
  uint64_t* p2;

  thread = -1;

  pid = pthread_create();

  if (thread == -1)
    thread = pid;

  // make sure the child thread is running first
  if (thread != 0)
    force_switch();

  counter = 1111108;

  i = 4;

  if (pid) {
    // parent

    // --------------- 2nd ---------------

    // reset the timer
    force_switch();

    // --------------- 4th ---------------

    p1 = malloc(16);
    p2 = malloc(16);

    pthread_join(p2); // switch

    // --------------- 6th ---------------

    // p2 points to other p2 which points to 2 and 3

    p2 = (uint64_t*) *p2;

    // now p2 directly points to 2 and 3

    *p1 = 2;
    *(p1 + 1) = 3;

    return *p1 + *(p1 + 1) + *p2 + *(p2 + 1);
  } else {
    // child

    // --------------- 1st ---------------

    // reset the timer
    force_switch();

    // --------------- 3rd ---------------

    // 9 instructions from force_switch()

    // 2 instructions
    i = 0;

    // 9 instructions per loop
    // 1111108 * 9 = 9999972
    while (i < counter)
      i = i + 1;

    // 4 instructions on loop end

    // so far 9 + 2 + 9999972 + 4 = 9999987

    // 13 instructions left before switch by timeout

    // lr is 12th instruction of malloc() call

    // switch should happen in here after lr but before sc
    p2 = malloc(16);

    // --------------- 5th ---------------

    *p2 = 18;
    *(p2 + 1) = 19;

    return (uint64_t) p2;
  }
}
