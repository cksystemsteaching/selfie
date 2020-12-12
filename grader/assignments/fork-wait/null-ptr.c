uint64_t* NULL = (uint64_t*) 0;

int main() {
  uint64_t pid;
  uint64_t i;

  pid = fork();
  if (pid == 0)
    exit(0);
  else {
    pid = wait(NULL);
  }

  return pid;
}