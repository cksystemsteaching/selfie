#ifndef SBI_FILES_BASE
#define SBI_FILES_BASE

#include "config.h"

#include <stdbool.h>
#include <stddef.h>

typedef struct KFILE {
  const char name[PATH_MAX_LEN];
  const char* data;
  size_t length;
} KFILE;

typedef struct FILEDESC {
  const KFILE* file;
  size_t pos;
} FILEDESC;

extern const KFILE files[];

const KFILE* find_file(const char* filename);

// File descriptor util functions
bool fd_is_stdio(int fd);
bool fd_is_valid(int fd, size_t num_fds);
FILEDESC* get_fd_entry(int fd, FILEDESC* open_files, size_t num_fds);
bool fd_entry_is_opened(FILEDESC* entry);
bool fd_is_opened(int fd, FILEDESC* open_files, size_t num_fds);

#define OPEN_FILE_FD_OFFSET 3

#endif /* SBI_FILES_BASE */
