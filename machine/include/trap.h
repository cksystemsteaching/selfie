#ifndef KERN_TRAP
#define KERN_TRAP

#include "config.h"

#include <stdint.h>
#include "context.h"
#include "tinycstd.h"

// 3.1.7 mstatus - Machine status register
// MIE, SIE and UIE enable interrupts for M-Mode, S-Mode and U-Mode, respectively
#define CSR_STATUS_SIE 1
#define CSR_STATUS_SPIE 5

#define CSR_SIE_TIMER_INTS 5

typedef void (*trap_handler_t)();

void disable_smode_interrupts();
void enable_smode_interrupts();

void enable_smode_interrupt_types(uint64_t bitmask);
void disable_smode_interrupt_types(uint64_t bitmask);

extern void trap_handler_wrapper();
void store_saved_registers_from_buffer_into_context(struct context* context, struct registers* registers_buffer);
void load_saved_registers_from_context_into_buffer(struct context* context, struct registers* registers_buffer);
uint64_t get_current_cpu_time();
bool set_timer_interrupt_delta(uint64_t delta);
bool set_timer_interrupt(uint64_t interrupt_at);
uint64_t trap_handler(struct registers registers_buffer);

void print_unhandled_trap(struct context* context, bool interrupt_bit, uint64_t exception_code, uint64_t stval, uint64_t sepc);

void handle_ecall(struct context* context);
void implement_syscall_exit(struct context* context);
void implement_syscalls_read_and_write(struct context* context, ssize_t (*kernel_func)(int, char*, size_t, FILEDESC*, size_t));
void implement_syscall_read(struct context* context);
void implement_syscall_write(struct context* context);
void implement_syscall_openat(struct context* context);
void implement_syscall_brk(struct context* context);

enum memory_access_type {
  memory_access_type_unknown,
  memory_access_type_lo,
  memory_access_type_mid,
  memory_access_type_hi
};
enum memory_access_type determine_memory_access_type(struct memory_boundaries* legal_memory_boundaries, uint64_t vaddr);

void signal_oom(struct context* context);
void handle_load_or_store_amo_page_fault(struct context* context, uint64_t stval);
void handle_instruction_page_fault(struct context* context, uint64_t sepc, uint64_t stval);
void handle_load_page_fault(struct context* context, uint64_t stval);
void handle_store_amo_page_fault(struct context* context, uint64_t stval);

void setup_smode_trap_handler(trap_handler_t handler);

#endif /* KERN_TRAP */
