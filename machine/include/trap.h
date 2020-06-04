#ifndef KERN_TRAP
#define KERN_TRAP

#include <stdint.h>

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

struct __attribute__((packed)) context {
  uint64_t id;
  struct pt_entry* pt;
  uint64_t program_break;
  struct trap_saved_regs* saved_regs;
  // TODO: all the other stuff
};

struct __attribute__((packed)) trap_saved_regs {
  uint64_t ra;
  uint64_t sp;
  uint64_t gp;
  uint64_t tp;
  uint64_t t0;
  uint64_t t1;
  uint64_t t2;
  uint64_t s0;
  uint64_t s1;
  uint64_t a0;
  uint64_t a1;
  uint64_t a2;
  uint64_t a3;
  uint64_t a4;
  uint64_t a5;
  uint64_t a6;
  uint64_t a7;
  uint64_t s2;
  uint64_t s3;
  uint64_t s4;
  uint64_t s5;
  uint64_t s6;
  uint64_t s7;
  uint64_t s8;
  uint64_t s9;
  uint64_t s10;
  uint64_t s11;
  uint64_t t3;
  uint64_t t4;
  uint64_t t5;
  uint64_t t6;

  uint64_t pc;
};

typedef void (*trap_handler_t)(/* TODO: Context struct */);

void disable_smode_interrupts();
void enable_smode_interrupts();

void enable_smode_interrupt_types(uint64_t bitmask);
void disable_smode_interrupt_types(uint64_t bitmask);

extern void trap_handler_wrapper();
void trap_handler();

void print_unhandled_trap(struct context* context, char interrupt_bit, uint64_t exception_code);

void handle_ecall(struct context* context);
void implement_syscall_exit(struct context* context);
void implement_syscall_read(struct context* context);
void implement_syscall_write(struct context* context);
void implement_syscall_openat(struct context* context);
void implement_syscall_brk(struct context* context);

void handle_instruction_page_fault(struct context* context, uint64_t sepc, uint64_t stval);
void handle_load_page_fault(struct context* context, uint64_t stval);
void handle_store_amo_page_fault(struct context* context, uint64_t stval);

void setup_smode_trap_handler(trap_handler_t handler);

#endif /* KERN_TRAP */
