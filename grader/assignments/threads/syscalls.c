void* malloc(unsigned long);
uint64_t  pthread_create();
uint64_t  pthread_join(uint64_t* wstatus);

uint64_t* status;

uint64_t sumChilds(uint64_t offset, uint64_t pid, uint64_t acc) {
  if (pid) {
    // this is the parent process/thread
    // => accumulate pid from pthread_create call, pid from pthread_join call and exit status code
    acc = acc + pid + pthread_join(status + offset);
    acc = acc + *(status + offset);
  }

  return acc;
}

uint64_t get_unique_offset(uint64_t pid1, uint64_t pid2, uint64_t pid3) {
  uint64_t bit0;
  uint64_t bit1;
  uint64_t bit2;

  bit0 = pid3 != 0;
  bit1 = pid2 != 0;
  bit2 = pid1 != 0;

  return (bit2 * 2 + bit1) * 2 + bit0;
}

int main(int argc, char** argv) {
  uint64_t offset;
  uint64_t pid1;
  uint64_t pid2;
  uint64_t pid3;
  uint64_t result;

  status = malloc(8 * sizeof(uint64_t));

  // 2^3 processes
  pid1 = pthread_create();
  pid2 = pthread_create();
  pid3 = pthread_create();

  offset = get_unique_offset(pid1, pid2, pid3);

  // do not wait for child-threads of the parent-process
  if (pid3 == 0)
    pid2 = 0;
  if (pid2 == 0)
    pid1 = 0;

  result = sumChilds(offset, pid3, sumChilds(offset, pid2, sumChilds(offset, pid1, 0)));

  if (pid1 != 0)
    if (pid2 != 0)
      if (pid3 != 0)
        return result;

  pthread_exit(result);
}