void* malloc(unsigned long);
uint64_t  pthread_create();
uint64_t  pthread_join(uint64_t* wstatus);

uint64_t* status;

uint64_t sumChilds(uint64_t offset, uint64_t pid, uint64_t acc) {
  if (pid) {
    // this is the parent process/thread
    // => accumulate pid from pthread_create call, pid from pthread_join call and exit status code
    acc = acc + pid + pthread_join(status + offset - 1);
    acc = acc + *(status + offset - 1);
  }

  return acc;
}

uint64_t get_unique_offset(uint64_t pid1, uint64_t pid2, uint64_t pid3) {
  uint64_t offset;

  offset = 0;

  if (pid1 != 0)
    offset = offset + 1;
  offset = offset * 2;
  if (pid2 != 0)
    offset = offset + 1;
  offset = offset * 2;
  if (pid3 != 0)
    offset = offset + 1;

  return 8 - offset;
} 

int main(int argc, char** argv) {
  uint64_t offset;
  uint64_t pid1;
  uint64_t pid2;
  uint64_t pid3;
  uint64_t result;

  status = malloc(8 * 8);

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