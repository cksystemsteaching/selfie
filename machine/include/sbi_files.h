#ifndef SBI_FILES_BASE
#define SBI_FILES_BASE

#include <stddef.h>

typedef struct FILE {
    const char name[512];
    const char* data;
    size_t length;
} FILE;

typedef struct FILEDESC {
    const FILE* file;
    size_t pos;
} FILEDESC;

extern const FILE* files;

#endif /* SBI_FILES_BASE */
