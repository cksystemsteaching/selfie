uint64_t VIRTUALMEMORYSIZE = 4294967296; // 4GB of virtual memory

int main() {
  uint64_t pid;
  uint64_t* code;

  code = (uint64_t*) VIRTUALMEMORYSIZE;

  pid = fork();
  if (pid == 0)
      exit(0);
  else
      pid = wait(code);

  return 43 + pid;
}