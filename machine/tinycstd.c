#include "tinycstd.h"

// Function required by libgcc for a freestanding environment

void* memmove(void* dest, const void* source, size_t num) {
    uint8_t* dst = (uint8_t*) dest;
    uint8_t* src = (uint8_t*) source;

    while (num > 0) {
        *(dst++) = *(src++);
        num--;
    }

    return dest;
}
void* memcpy (void* destination, const void* source, size_t num) {
    return memmove(destination, source, num);
}
void* memset(void* ptr, int value, size_t num) {
    uint8_t* charPtr = (uint8_t*) ptr;

    while (num > 0) {
        *charPtr = (uint8_t) value;

        charPtr++;
        num--;
    }

    return ptr;
}
int memcmp(const void* ptr1, const void* ptr2, size_t num) {
    uint8_t* p1 = (uint8_t*) ptr1;
    uint8_t* p2 = (uint8_t*) ptr2;

    for (size_t i = 0; i < num; i++) {
        if (p1[i] < p2[i])
            return -1;
        if (p1[i] > p2[i])
            return 1;
    }

    return 0;
}

uint64_t strlen(const char* str) {
    uint64_t len = 0;

    while (str && *(str++))
        ++len;

    return len;
}
