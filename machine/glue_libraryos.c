#include "config.h"
#include "diag.h"
#include "filesystem.h"
#include "sbi_ecall.h"
#include "syscalls.h"
#include <stdint.h>

#include "compiler-utils.h"

static FILEDESC open_files[NUM_FDS];
void* heap_head;

ssize_t read(int fd, char* buf, size_t count) {
  return kread(fd, buf, count, open_files, NUM_FDS);
}

intmax_t write(int fd, const char* buf, size_t count) {
  return kwrite(fd, buf, count, open_files, NUM_FDS);
}

uint64_t open(char* filename, uint64_t flags, uint64_t mode) {
  UNUSED_VAR(mode);
  return kopen(filename, flags, open_files, NUM_FDS);
}


extern void zero_mem(uint64_t* addr, uint64_t size);
void* malloc(unsigned long size) {
  void* return_ptr;

  return_ptr = heap_head;
  heap_head += size;

#ifdef DEBUG
  printf("-- malloc: allocated 0x%x bytes at addr %p-%p\n", size, return_ptr, heap_head);
#endif /* DEBUG */

  zero_mem(return_ptr, size);

  return return_ptr;
}

void exit(int status) {
  printf(">EXIT called with exit code %x<\n", status);
  shutdown();
}
