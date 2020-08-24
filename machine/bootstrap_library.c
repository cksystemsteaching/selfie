#include "bootstrap.h"
#include <stdint.h>

void early_init() {}

extern uint64_t heap_head;
extern void* initial_stack_start();
void kernel_environ_init() {
  heap_head = (uint64_t) initial_stack_start();
}

extern int main(uint64_t argc, const char** argv);
int start_init_process (uint64_t argc, const char** argv) {
  return main(argc, argv);
}
