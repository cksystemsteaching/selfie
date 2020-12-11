uint64_t VIRTUALMEMORYSIZE = 4294967296; // 4GB of virtual memory

// computes the exit code from the status value
// exit code is in the least significant bits from 8 to 16
uint64_t wexitstatus(uint64_t status) {
  return status * 281474976710656 / 72057594037927936;
}

int main() {
  uint64_t pid1;
  uint64_t pid2;
  uint64_t* code;

  code = (uint64_t*) VIRTUALMEMORYSIZE;

  pid1 = fork();
  if (pid1 == 0)
    exit(5);
  else
    pid1 = wait(code);

  // Actually query the PID/status
  // The previous call should have failed before, but mustn't have consumed the zombie
  code = malloc(8);
  pid2 = wait(code);

  return 36 + pid1 + pid2 + wexitstatus(*code);
}