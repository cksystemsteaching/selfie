#include "compiler-utils.h"
#include "sbi_ecall.h"
#include "sbi_ecall_ids.h"

void sbi_ecall_sbi_putchar(int chr) {
  asm volatile (
    "li a6, " STRINGIFICATE(SBI_FUNCTION_ID_LEGACY_EXTENSION_SBI_CONSOLE_PUTCHAR) ";"
    "li a7, " STRINGIFICATE(SBI_EXTENSION_ID_LEGACY_EXTENSION_SBI_CONSOLE_PUTCHAR) ";"
    "mv a0, %[chr];"
    "ecall;"
    :
    : [chr] "r" (chr)
    : "a0", "a6", "a7"
  );
}

bool sbi_ecall_sbi_set_timer(uint64_t interrupt_at) {
  long error;

  asm volatile (
    "li a6, " STRINGIFICATE(SBI_FUNCTION_ID_TIMER_EXTENSION_SBI_SET_TIMER) ";"
    "li a7, " STRINGIFICATE(SBI_EXTENSION_ID_TIMER_EXTENSION) ";"
    "mv a0, %[interrupt_at];"
    "ecall;"
    "mv %[error], a1"
    : [error] "=r" (error)
    : [interrupt_at] "r" (interrupt_at)
    : "a7", "a6", "a1", "a0" // a1 because the SBI returns an error code in there
  );

  return (error == 0);
}

void sbi_ecall_sbi_shutdown() {
  asm volatile (
    "li a6, " STRINGIFICATE(SBI_FUNCTION_ID_LEGACY_EXTENSION_SBI_SHUTDOWN) ";"
    "li a7, " STRINGIFICATE(SBI_EXTENSION_ID_LEGACY_EXTENSION_SBI_SHUTDOWN) ";"
    "ecall"
    :
    :
    : "a6", "a7"
  );
}
