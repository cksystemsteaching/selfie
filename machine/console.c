#include "console.h"
#include <stdint.h>

int console_init() {
    return 0;
}
void console_putc(int chr) {
    asm volatile(
        "li a7, 1;"
        "li a6, 0;"
        "mv a0, %[character];"
        "ecall;"
        :
        : [character] "r" (chr)
        : "a0", "a6", "a7"
    );
}
intmax_t console_puts(const char* str, size_t len) {
    size_t i = 0;

    while (i < len) {
        console_putc(*str);
        str = str + 1;
        i++;
    }

    return i;
}
