void* malloc(unsigned long);
uint64_t  pthread_create();
uint64_t  pthread_join(uint64_t* wstatus);

uint64_t* status;

uint64_t sumChilds(uint64_t own_pid, uint64_t pid, uint64_t acc) {
  if (pid) {
    // this is the parent process/thread
    // => accumulate pid from pthread_create call, pid from pthread_join call and exit status code
    acc = acc + pid + pthread_join(status + own_pid - 1);
    acc = acc + *(status + own_pid - 1);
  }

  return acc;
}

uint64_t get_own_pid(uint64_t pid1, uint64_t pid2, uint64_t pid3) {
  uint64_t pid;

  pid = 0;

  if (pid1 != 0)
    pid = pid + 1;
  pid = pid * 2;
  if (pid2 != 0)
    pid = pid + 1;
  pid = pid * 2;
  if (pid3 != 0)
    pid = pid + 1;

  return 8 - pid;
} 

int main(int argc, char** argv) {
  uint64_t own_pid;
  uint64_t pid1;
  uint64_t pid2;
  uint64_t pid3;
  uint64_t result;

  status = malloc(8 * 8);

  // 2^3 processes
  pid1 = pthread_create();
  pid2 = pthread_create();
  pid3 = pthread_create();

  own_pid = get_own_pid(pid1, pid2, pid3);

  // do not wait for child-threads of the parent-process
  if (pid3 == 0)
    pid2 = 0;
  if (pid2 == 0)
    pid1 = 0;

  result = sumChilds(own_pid, pid3, sumChilds(own_pid, pid2, sumChilds(own_pid, pid1, 0)));

  if (pid1 != 0)
    if (pid2 != 0)
      if (pid3 != 0)
        return result;

  pthread_exit(result);
}