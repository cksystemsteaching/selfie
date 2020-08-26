#include "console.h"
#include "sbi_ecall.h"
#include <stdint.h>

int console_init() {
  return 0;
}

void console_putc(int chr) {
  sbi_ecall_sbi_putchar(chr);
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
