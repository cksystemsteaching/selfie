#ifndef KERN_CONSOLE
#define KERN_CONSOLE

#include <stddef.h>
#include <stdint.h>

int console_init();
void console_putc(int chr);
intmax_t console_puts(const char* str, size_t size);

#endif /* KERN_CONSOLE */
