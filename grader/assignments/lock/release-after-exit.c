uint64_t* foo_parent;
uint64_t* foo_child;

int main() {
  uint64_t pid;
  uint64_t* status;

  status = malloc(8);
  foo_parent = "Hello parent!   ";
  foo_child  = "Hello child!    ";

  pid = fork();
  if (pid == 0) {
    lock();
    write(1, foo_child, 16);
    // The lock will not be released intentionally before the child process terminates
    exit(0);
  } else {
    pid = wait(status);

    // If the implementation does not free the lock after the child holding it terminated,
    // this call will block indefinitely
    lock();
    write(1, foo_parent, 16);
    unlock();
    exit(0);
  }
}