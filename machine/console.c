#include "console.h"

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
