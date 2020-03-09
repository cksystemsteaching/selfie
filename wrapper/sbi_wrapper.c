#include "sbi/sbi_console.h"

#include <stdint.h>

int main(int argc, char** argv);


void _start() {
    main(0, (char**)0);
}


ssize_t read(int fd, void* buf, size_t count) {
    return 0;
}

ssize_t write(int fd, const void* buf, size_t count) {
    size_t i = 0;
    const char* charBuf = (const char*) buf;

    while (i < count) {
        sbi_putc(charBuf[i]);
        i++;
    }
}

void exit(int status) {
    while (1)
        ;
}

int open(const char* pathname, int flags) {
    return -1;
}

static void* heap_head = (void*)0x80000000;
void* malloc(unsigned long long size) {
    void* return_ptr;

    return_ptr = heap_head;
    heap_head += size;

    return heap_head;
}
