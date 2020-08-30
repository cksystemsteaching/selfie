#ifndef KERN_SBI_ECALL
#define KERN_SBI_ECALL

#include <stdbool.h>
#include <stdint.h>

// ==================== LEGACY EXTENSION ====================

void sbi_ecall_sbi_putchar(int chr);

bool sbi_ecall_sbi_set_timer(uint64_t interrupt_at);

// ==================== TIMER EXTENSION ====================

void sbi_ecall_sbi_shutdown();

#endif /* KERN_SBI_ECALL */
