#ifndef SBI_FILES_BASE
#define SBI_FILES_BASE

#include <stddef.h>

typedef struct FILE {
    const char name[512];
    const char* data;
    size_t length;
} FILE;

extern const FILE* files;

#endif /* SBI_FILES_BASE */
