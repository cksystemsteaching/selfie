#include <stdint.h>
typedef int64_t ssize_t;
typedef uint64_t size_t;

void* memmove(void* dest, const void* source, size_t num);
void* memcpy (void* destination, const void* source, size_t num);
int memcmp(const void* ptr1, const void* ptr2, size_t num);
void* memset(void* ptr, int value, size_t num);
uint64_t strlen(const char* str);
