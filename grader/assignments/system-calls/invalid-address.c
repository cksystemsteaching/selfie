uint64_t* VIRTUALMEMORYSIZE = (uint64_t*) 4294967296; // 4GB of virtual memory
uint64_t* ELF_ENTRY_POINT = (uint64_t*) 65536; // = 0x10000 (address of beginning of code)


// computes the exit code from the status value
// exit code is in the least significant bits from 8 to 16
uint64_t wexitstatus(uint64_t status) {
  return status * 281474976710656 / 72057594037927936;
}


int main() {
  uint64_t sum;
  uint64_t wait_pid;
  uint64_t fork_pid;
  uint64_t* heap_top;

  heap_top = malloc(8);
  sum = 40;

  fork_pid = fork();
  if (fork_pid == 0)
    exit(5);
  else {
    // First invalid access - code segment
    wait_pid = wait(ELF_ENTRY_POINT);
    sum = sum + wait_pid;

    // Second invalid access - free region between stack and heap
    // Bump pointer allocation -> we can derive the end of the heap
    // using the most recently allocated memory block, in this case `heap_top`
    wait_pid = wait(heap_top + 1);
    sum = sum + wait_pid;

    // Third invalid address - outside the 4GiB virtual addressing space
    wait_pid = wait(VIRTUALMEMORYSIZE);
    sum = sum + wait_pid;
  }

  // Actually query the PID/status
  // The previous calls should have failed before and mustn't have consumed the zombie
  wait_pid = wait(heap_top);

  // 40 (initial) + 5 (exit code) + 3 * (-1) (wait error on invalid vaddr) (+ child PID - child PID)
  return sum + fork_pid - wait_pid + wexitstatus(*heap_top);
}