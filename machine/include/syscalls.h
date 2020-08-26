#ifndef KERN_SYSCALL
#define KERN_SYSCALL

#include "filesystem.h"
#include "tinycstd.h"

ssize_t kread(int fd, char* buf, size_t count, FILEDESC* open_files, size_t num_fds);
ssize_t kwrite(int fd, const char* buf, size_t count, FILEDESC* open_files, size_t num_fds);
int kopen(const char* filename, int flags, FILEDESC* open_files, size_t num_fds);

#endif /* KERN_SYSCALL */
