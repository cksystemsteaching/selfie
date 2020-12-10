int main() {
  uint64_t pid;
  uint64_t* code;

  // Enforce an unmapped virtual address by allocating a page-wide array
  // and not touching it
  // It must be page-wide to move the last element across potential already
  // mapped page boundaries
  // wait uses the last element, then
  code = malloc(8 * 4096);

  pid = fork();
  if (pid == 0) {
    // Child process - return
    exit(84);
  } else {
    // Parent process - wait for the child and calculate the exit code;
    wait(code + 4095);
  }

  return 21 + *(code + 4095) / 1024;
}