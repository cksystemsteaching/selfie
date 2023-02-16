// computes the exit code from the status value
// exit code is in the least significant bits from 8 to 16
uint64_t wexitstatus(uint64_t status) {
  return status * 281474976710656 / 72057594037927936;
}

int main() {
  uint64_t pid;
  uint64_t* exit_code;

  // Enforce an unmapped virtual address by allocating a page-wide array
  // and not touching it
  // It must be page-wide to move the last element across potential already
  // mapped page boundaries
  // wait uses the last element, then
  exit_code = malloc(8 * 4096);

  pid = fork();
  if (pid == 0)
    // Child process - return
    exit(84);
  else
    // Parent process - wait for the child and calculate the exit code;
    wait(exit_code + 4095);

  return 21 + wexitstatus(*(exit_code + 4095)) / 4;
}