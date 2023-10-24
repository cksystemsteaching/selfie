void* malloc(unsigned long);

uint64_t pthread_create();
uint64_t pthread_join(uint64_t* status);
void     pthread_exit(uint64_t status);

uint64_t* heap_variable;

int main(int argc, char** argv) {
  uint64_t  tid;
  uint64_t* status;

  status = malloc(sizeof(uint64_t));

  tid = pthread_create();

  if (tid)
    pthread_join(status);
  else {
    heap_variable = malloc(sizeof(uint64_t));
    *heap_variable = 30;

    pthread_exit(12);
  }

  return *status + *heap_variable;
}