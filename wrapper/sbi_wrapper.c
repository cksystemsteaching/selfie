#include "sbi/sbi_console.h"

#include <stdint.h>

int main(int argc, char** argv);

void sbi_ecall_console_putc(char c) {
    asm volatile(
        "li a7, 1;"
        "li a6, 0;"
        "mv a0, %[character];" // just a test to see if it prints 'a'
        "ecall;"
        :
        : [character] "r" (c)
        : "a0", "a6", "a7"
    );
}


ssize_t read(int fd, void* buf, size_t count) {
    return 0;
}

ssize_t write(int fd, const char* buf, size_t count) {
    size_t i = 0;
    const char* charBuf = (const char*) buf;

    while (i < count) {
        sbi_ecall_console_putc(charBuf[i]);
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


static void* heap_head = (void*)0x80100000;
void* malloc(unsigned long long size) {
    void* return_ptr;

    return_ptr = heap_head;
    heap_head += size;

    return heap_head;
}

uint64_t strlen(const char* str) {
    uint64_t len = 0;

    while (str && *(str++))
        ++len;

    return len;
}

void bootstrap() {
    uint64_t val = 0xF00DBEEF;

    char* args[] = {
        "./selfie",
        (char*)0,
    };
    int i = 0;

    write(1, "Booting selfie with args: ", 26);
    sbi_ecall_console_putc('\n');

    while (args[i] != (char*)0) {
        write(1, "    ", 4);
        write(1, args[i], strlen(args[i]));
        sbi_ecall_console_putc('\n');
        i++;
    }
    write(1, "    <END>\n", 11);
    sbi_ecall_console_putc('\n');

    main(1, args);
}
