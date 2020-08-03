#ifndef KERN_TRAP
#define KERN_TRAP

#include <stdint.h>
#include "context.h"

// 3.1.7 mstatus - Machine status register
// MIE, SIE and UIE enable interrupts for M-Mode, S-Mode and U-Mode, respectively
#define CSR_STATUS_MIE 3
#define CSR_STATUS_SIE 1
#define CSR_STATUS_UIE 0

#define CSR_SIE_EXTERNAL_INTS   9
#define CSR_UIE_EXTERNAL_INTS   8
#define CSR_SIE_TIMER_INTS      5
#define CSR_UIE_TIMER_INTS      4
#define CSR_SIE_SOFTWARE_INTS   1
#define CSR_UIE_SOFTWARE_INTS   0

typedef void (*trap_handler_t)(/* TODO: Context struct */);

void disable_smode_interrupts();
void enable_smode_interrupts();

void enable_smode_interrupt_types(uint64_t bitmask);
void disable_smode_interrupt_types(uint64_t bitmask);

extern void trap_handler_trampoline();
extern void trap_handler_wrapper();
void trap_handler();

void print_unhandled_trap(struct context* context, char interrupt_bit, uint64_t exception_code);

void handle_ecall(struct context* context);
void implement_syscall_exit(struct context* context);
void implement_syscall_read(struct context* context);
void implement_syscall_write(struct context* context);
void implement_syscall_openat(struct context* context);
void implement_syscall_brk(struct context* context);

char is_legal_memory_access(struct memory_boundaries* legal_memory_boundaries, uint64_t address);
void handle_instruction_page_fault(struct context* context, uint64_t sepc, uint64_t stval);
void handle_load_page_fault(struct context* context, uint64_t stval);
void handle_store_amo_page_fault(struct context* context, uint64_t stval);

void setup_smode_trap_handler(trap_handler_t handler);

#endif /* KERN_TRAP */
