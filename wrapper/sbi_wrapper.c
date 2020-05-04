#include "sbi/sbi_console.h"

#include <stdint.h>

#include "sbi_files.h"

#define NUM_FILES 1

int main(int argc, char** argv);

void* memcpy (void* destination, const void* source, size_t num) {
    uint8_t* dst = (uint8_t*) destination;
    uint8_t* src = (uint8_t*) source;

    while (num > 0) {
        *(dst++) = *(src++);
        num--;
    }

    return destination;
}


// Choose between selfie_c and selfie_m, defined in sbi_files.h
static const char* files[NUM_FILES] = {
    selfie_m
};

static const uint64_t file_len[NUM_FILES] = {
    selfie_m_len
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
void print_hex_internal(uint64_t val, uint64_t pos, uint64_t maxLen) {
    if (pos >= maxLen)
        return;

    uint64_t rest = val % 16;
    val = val / 16;

    print_hex_internal(val, pos+1, maxLen);
    if (rest >= 0 && rest < 10) {
        sbi_ecall_console_putc('0'+rest);
    } else {
        sbi_ecall_console_putc('A'+(rest-10));
    }
}

void print_hex(uint64_t val) {
    sbi_ecall_console_putc('0');
    sbi_ecall_console_putc('x');

    print_hex_internal(val, 0, 8);
}

ssize_t read(int fd, char* buf, size_t count) {
    if (fd >= NUM_FILES+1) {
        return -1;
    } else {
        uint64_t num_read = 0;
        while (count) {
            uint64_t pos = file_pos[fd-1];
            if (file_pos[fd-1] >= file_len[fd-1])
                break;

            *(buf++) = files[fd-1][pos];

            --count;
            num_read++;
            file_pos[fd-1]++;
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

    return i;
}

void exit(int status) {
    write(1, ">EXIT called<\n", 14);
    while (1)
        ;
}

int open(const char* pathname, int flags) {
    file_pos[0] = 0;
    return 1;
}


static void* heap_head = (void*)0x80300000;
void* malloc(unsigned long long size) {
    void* return_ptr;

    return_ptr = heap_head;
    heap_head += size;

    write(1, "-- malloc: allocated ", 21);
    print_hex(size);
    write(1, " bytes at addr ", 15);
    print_hex(return_ptr);
    sbi_ecall_console_putc('-');
    print_hex(heap_head);
    sbi_ecall_console_putc('\n');

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
        "-l",
        "hello-world.c",
        "-m",
        "32",
        "-l",
        "hello-world.c",
        "-y",
        "16",
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
