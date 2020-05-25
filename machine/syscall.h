#ifndef KERN_SYSCALL
#define KERN_SYSCALL

#include "tinycstd.h"

ssize_t read(int fd, char* buf, size_t count);
ssize_t write(int fd, const char* buf, size_t count);
void exit(int status);
int open(const char* filename, int flags);
void* malloc(unsigned long long size); /* TODO: Not a syscall */


#endif /* KERN_SYSCALL */
