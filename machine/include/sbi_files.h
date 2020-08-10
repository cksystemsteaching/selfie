#ifndef SBI_FILES_BASE
#define SBI_FILES_BASE

#include <stddef.h>

typedef struct KFILE {
    const char name[512];
    const char* data;
    size_t length;
} KFILE;

typedef struct FILEDESC {
    const KFILE* file;
    size_t pos;
} FILEDESC;

extern const KFILE* files;

#endif /* SBI_FILES_BASE */
