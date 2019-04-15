void* malloc(unsigned long);

uint64_t fork();
uint64_t wait(uint64_t* wstatus);

uint64_t sumChilds(uint64_t pid, uint64_t acc) {
  uint64_t* s;

  s = malloc(8);

  if (pid) {
    // this is the parent process
    // => accumulate pid from fork call, pid from wait call and exit status code
    acc = acc + pid + wait(s);
    acc = acc + *s;
  }

  return acc;
}

int main(int argc, char** argv) {
  uint64_t pid1;
  uint64_t pid2;
  uint64_t pid3;

  // 3^2 processes
  pid1 = fork();
  pid2 = fork();
  pid3 = fork();

  // do not wait for child-processes of the parent-process
  if (pid3 == 0)
    pid2 = 0;
  if (pid2 == 0)
    pid1 = 0;

  return sumChilds(pid3, sumChilds(pid2, sumChilds(pid1, 0)));
}