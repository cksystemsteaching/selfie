uint64_t pthread_create();
uint64_t pthread_join(uint64_t* wstatus);
void pthread_exit(uint64_t code);

uint64_t wait(uint64_t* wstatus);

uint64_t thread;
uint64_t loop;

int main(int argc, char** argv) {
  uint64_t pid;
  uint64_t counter;
  uint64_t i;
  uint64_t* p1;
  uint64_t* p2;
  uint64_t counter;
  uint64_t zero;

  thread = -1;

  pid = pthread_create();

  if (thread == -1)
    thread = pid;

  // make sure the child thread is running first
  if (thread != 0)
    wait((uint64_t*) 0);

  // assert: thread == 1

  //counter = 1111108;

  if (pid == 0) {
    // child

    // ------------------------------ 1st ------------------------------

    zero = 0;

    counter = 0;

    loop = 1;

    i = 0;

    // force a context switch, reset the timer
    wait((uint64_t*) 0);

    // ------------------------------ 3rd ------------------------------

    while(zero < loop)
      counter = counter + 1;

    // endless loop forces context switch by timeout

    // ------------------------------ 5th ------------------------------

    counter = counter - 2;

    // force a context switch, reset the timer
    wait((uint64_t*) 0);

    // ------------------------------ 7th ------------------------------

    // 3 jalr instruction leftover from wait()

    // 9 instructions per loop
    // 1111109 * 9 = 9999981
    while (i < counter)
      i = i + 1;

    // 4 instructions on loop end

    // so far: 3 + 9999981 + 4 = 9999988

    // 12 instructions left

    // lr is 10th instruction of malloc() call

    // context switch should happen in here by timeout
    // after lr but before sc
    p2 = malloc(2 * sizeof(uint64_t));

    // ------------------------------ 9th ------------------------------

    *p2 = 18;
    *(p2 + 1) = 19;

    return (uint64_t) p2;

  } else {
    // parent

    // ------------------------------ 2nd ------------------------------

    // force a context switch, reset the timer
    wait((uint64_t*) 0);

    // ------------------------------ 4th ------------------------------

    loop = 0;

    // force a context switch, reset the timer
    wait((uint64_t*) 0);

    // ------------------------------ 6th ------------------------------

    // force a context switch, reset the timer
    wait((uint64_t*) 0);

    // ------------------------------ 8th ------------------------------

    p1 = malloc(2 * sizeof(uint64_t));
    p2 = malloc(sizeof(uint64_t));

    pthread_join(p2); // switch

    // ------------------------------ 10th ------------------------------

    // p2 points to other p2 which points to 2 and 3

    p2 = (uint64_t*) *p2;

    // now p2 directly points to 2 and 3

    *p1 = 2;
    *(p1 + 1) = 3;

    // 10 = 2 + 3 + 2 + 3
    // 42 = 2 + 3 + 18 + 19 (thread-safe)
    return *p1 + *(p1 + 1) + *p2 + *(p2 + 1);
  }
}
