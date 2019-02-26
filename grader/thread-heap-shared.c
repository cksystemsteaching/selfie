uint64_t* malloc(uint64_t size);

uint64_t pthread_create();
uint64_t pthread_join(uint64_t* status);
void     pthread_exit(uint64_t status);

uint64_t* heap_variable;

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t  tid;
  uint64_t* status;

  status = malloc(8);

  tid = pthread_create();

  if (tid)
    pthread_join(status);
  else {
    heap_variable = malloc(8);
    *heap_variable = 123;

    pthread_exit(0);
  }

  return *heap_variable == 123;
}