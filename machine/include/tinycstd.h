#ifndef KERN_TINYCSTD
#define KERN_TINYCSTD

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

typedef int64_t ssize_t;

void* memmove(void* dest, const void* source, size_t num);
void* memcpy (void* destination, const void* source, size_t num);
int memcmp(const void* ptr1, const void* ptr2, size_t num);
void* memset(void* ptr, int value, size_t num);

// <string.h> String functions
uint64_t strlen(const char* str);
ssize_t strncmp(const char* first, const char* second, size_t n);
const char* strchr(const char* str, int c);

// <stdio.h> I/O functions
int printf(const char* format, ...);
void puts(const char* s);
void putc(char c);

#endif /* KERN_TINYCSTD */
