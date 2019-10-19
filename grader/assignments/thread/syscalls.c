void* malloc(unsigned long);
uint64_t  pthread_create();
uint64_t  pthread_join(uint64_t* wstatus);

uint64_t sumChilds(uint64_t pid, uint64_t acc) {
  uint64_t* s;

  s = malloc(8);

  if (pid) {
    // this is the parent process/thread
    // => accumulate pid from pthread_create call, pid from pthread_join call and exit status code
    acc = acc + pid + pthread_join(s);
    acc = acc + *s;
  }

  return acc;
}

int main(int argc, char** argv) {
  uint64_t pid1;
  uint64_t pid2;
  uint64_t pid3;
  uint64_t result;

  // 3^2 processes
  pid1 = pthread_create();
  pid2 = pthread_create();
  pid3 = pthread_create();

  // do not wait for child-threads of the parent-process
  if (pid3 == 0)
    pid2 = 0;
  if (pid2 == 0)
    pid1 = 0;

  result = sumChilds(pid3, sumChilds(pid2, sumChilds(pid1, 0)));
  
  if (pid1 != 0)
    if (pid2 != 0)
      if (pid3 != 0)
        return result;

  pthread_exit(result);
}