uint64_t* VIRTUALMEMORYSIZE = (uint64_t*) 4294967296; // 4GB of virtual memory
uint64_t* ELF_ENTRY_POINT = (uint64_t*) 65536; // = 0x10000 (address of beginning of code)


// computes the exit code from the status value
// exit code is in the least significant bits from 8 to 16
uint64_t wexitstatus(uint64_t status) {
  return status * 281474976710656 / 72057594037927936;
}

int main() {
  uint64_t sum;
  uint64_t pid;
  uint64_t* code;

  code = malloc(8);
  sum = 38;

  pid = fork();
  if (pid == 0)
    exit(5);
  else {
    // First invalid access - code segment
    pid = wait(ELF_ENTRY_POINT);
    sum = sum + pid;

    // Second invalid access - free region between stack and heap
    // Bump pointer allocation -> we can derive the end of the heap
    // using the most recently allocated memory block, in this case `code`
    pid = wait(code + 1);
    sum = sum + pid;

    // Third invalid address - outside the 4GiB virtual addressing space
    pid = wait(VIRTUALMEMORYSIZE);
    sum = sum + pid;
  }

  // Actually query the PID/status
  // The previous calls should have failed before and mustn't have consumed the zombie
  pid = wait(code);

  // 38 (initial) + 5 (exit code) + 2 (PID) + 3 * (-1) (wait error on invalid vaddr)
  return sum + pid + wexitstatus(*code);
}