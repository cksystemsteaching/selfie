uint64_t* NULL = (uint64_t*) 0;

int main() {
  uint64_t fork_pid;
  uint64_t wait_pid;
  uint64_t i;

  fork_pid = fork();
  if (fork_pid == 0)
    exit(0);
  else
    wait_pid = wait(NULL);

  if (fork_pid == -1)
    return 1;
  if (wait_pid == -1)
    return 2;

  return 42 + (fork_pid - wait_pid);
}