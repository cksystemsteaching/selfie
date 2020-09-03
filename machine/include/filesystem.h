#ifndef SBI_FILES_BASE
#define SBI_FILES_BASE

#include "config.h"

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

extern const KFILE* files;

const KFILE* find_file(const char* filename);

#endif /* SBI_FILES_BASE */
