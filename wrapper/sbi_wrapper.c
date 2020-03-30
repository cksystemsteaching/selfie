#include "sbi/sbi_console.h"

#include <stdint.h>

#define NUM_FILES 1

int main(int argc, char** argv);

static char* files[NUM_FILES] = {
    "uint64_t*foo;uint64_t*main(){foo=\"Hello World!    \";while(*foo!=0){write(1,foo,8);foo=foo+1;}}",
};

static uint64_t file_pos[NUM_FILES] = {
    0
};


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


ssize_t read(int fd, char* buf, size_t count) {
    if (fd >= NUM_FILES+1) {
        return -1;
    } else {
        uint64_t num_read = 0;
        while (count) {
            uint64_t pos = file_pos[fd-1]++;
            if (files[fd-1][pos] == '\0')
                break;

            *(buf++) = files[fd-1][pos];

            --count;
            num_read++;
        }
        return num_read;
    }
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
    return 1;
}


static void* heap_head = (void*)0x80300000;
void* malloc(unsigned long long size) {
    void* return_ptr;

    return_ptr = heap_head;
    heap_head += size;

    return return_ptr;
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
        "-c",
        "hello-world.c",
        "-m",
        "1",
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
    write(1, "    <END>\n", 10);
    sbi_ecall_console_putc('\n');

    // i contains the count of command line arguments
    int exit = main(i, args);


    write(1, "\n\nFunction main terminated with exit code ", 42);
    sbi_ecall_console_putc('0' + exit);
}
