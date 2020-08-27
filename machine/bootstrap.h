#ifndef KERN_BOOTSTRAP
#define KERN_BOOTSTRAP

#include <stdint.h>

void early_init();
void kernel_environ_init();
int start_init_process(uint64_t argc, const char** argv);

#endif /* KERN_BOOTSTRAP */
