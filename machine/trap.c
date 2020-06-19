#include "trap.h"
#include "tinycstd.h"
#include "mmu.h"

#define SCAUSE_INTERRUPT_BIT_MASK 0x8000000000000000
#define SCAUSE_EXCEPTION_CODE_MASK 0x7FFFFFFFFFFFFFFF

// if interrupt bit is 0
#define SCAUSE_EXCEPTION_CODE_ECALL 8
#define SCAUSE_EXCEPTION_CODE_INSTRUCTION_PAGE_FAULT 12
#define SCAUSE_EXCEPTION_CODE_LOAD_PAGE_FAULT 13
#define SCAUSE_EXCEPTION_CODE_STORE_AMO_PAGE_FAULT 15

#define SYSCALL_EXIT   93
#define SYSCALL_READ   63
#define SYSCALL_WRITE  64
#define SYSCALL_OPENAT 56
#define SYSCALL_BRK    214

void disable_smode_interrupts() {
    uint64_t bitmask = (1 << CSR_STATUS_SIE);

    asm volatile (
        "csrc sstatus, %[bitmask]"
        :
        : [bitmask] "r" (bitmask)
    );
}

void enable_smode_interrupts() {
    uint64_t bitmask = (1 << CSR_STATUS_SIE);

    asm volatile (
        "csrs sstatus, %[bitmask]"
        :
        : [bitmask] "r" (bitmask)
    );
}

void enable_smode_interrupt_types(uint64_t bitmask) {

}

void disable_smode_interrupt_types(uint64_t bitmask) {

}

void trap_handler() {
  uint64_t scause;
  uint64_t stval; // address where page fault occured
  uint64_t sepc;  // pc where the exception occured
  char interrupt_bit;
  uint64_t exception_code;
  struct context* context; // TODO: get this from somewhere

  asm volatile(
    "csrr %[scause], scause;"
    "csrr %[sepc], sepc;"
    "csrr %[stval], stval;"
    : [scause] "=r" (scause), [sepc] "=r" (sepc), [stval] "=r" (stval)
  );

  interrupt_bit = scause & SCAUSE_INTERRUPT_BIT_MASK;
  exception_code = scause & SCAUSE_EXCEPTION_CODE_MASK;

  if (interrupt_bit)
    // TODO: timer interrupts etc
    print_unhandled_trap(context, interrupt_bit, exception_code);
  else
    switch (exception_code) {
      case SCAUSE_EXCEPTION_CODE_ECALL:
        handle_ecall(context);
        break;
      case SCAUSE_EXCEPTION_CODE_INSTRUCTION_PAGE_FAULT:
        handle_instruction_page_fault(context, sepc, stval);
        break;
      case SCAUSE_EXCEPTION_CODE_LOAD_PAGE_FAULT:
        handle_load_page_fault(context, stval);
        break;
      case SCAUSE_EXCEPTION_CODE_STORE_AMO_PAGE_FAULT:
        handle_store_amo_page_fault(context, stval);
        break;
      default:
        print_unhandled_trap(context, interrupt_bit, exception_code);
    }

#ifdef DEBUG
  printf("trap handler has been executed (caused context %d)\n", context->id);
  printf("  scause:         0x%x\n", scause);
  printf("  syscall number: 0x%x\n", syscall_number);
#endif /* DEBUG */
}

void print_unhandled_trap(struct context* context, char interrupt_bit, uint64_t exception_code) {
  printf("unhandled trap (caused by context %d)\n", context->id);
  printf("  interrupt bit:  %d\n", interrupt_bit);
  printf("  exception code: %d\n", exception_code);
}

void handle_ecall(struct context* context) {
  uint64_t syscall_id;
  uint64_t syscall_param_0;
  uint64_t syscall_param_1;
  uint64_t syscall_param_2;

  asm volatile(
    "mv %[syscall_id], a7;"
    "mv %[syscall_param_0], a0;"
    "mv %[syscall_param_1], a1;"
    "mv %[syscall_param_2], a2;"
    : [syscall_id] "=r" (syscall_id), [syscall_param_0] "=r" (syscall_param_0)
      , [syscall_param_1] "=r" (syscall_param_1), [syscall_param_2] "=r" (syscall_param_2)
  );

  switch (syscall_id) {
    case SYSCALL_EXIT:

    case SYSCALL_READ:

    case SYSCALL_WRITE:

    case SYSCALL_OPENAT:

    case SYSCALL_BRK:

    default:
      printf("received unknown syscall '0x%x' from context %d\n", syscall_id, context->id);
  }

  // TODO
}

void implement_syscall_exit(struct context* context) {
  // TODO
}

void implement_syscall_read(struct context* context) {
  // TODO
}

void implement_syscall_write(struct context* context) {
  // TODO
}

void implement_syscall_openat(struct context* context) {
  // TODO
}

void implement_syscall_brk(struct context* context) {
  // TODO
}

void handle_instruction_page_fault(struct context* context, uint64_t sepc, uint64_t stval) {
  if (stval < context->program_break) {
    // TODO: handling faults like that is probably necessary for native hypster support
  } else
    // at the moment we raise a segfault here since we map the entire code
    // segment when loading a binary
    printf("segmentation fault: context %d tried to execute the instruction at 0x%x and faulted at 0x%x\n", context->id, sepc, stval);

#ifdef DEBUG
  printf("received instruction page fault caused by context %d\n", context->id);
  printf("  address of instruction:         0x%x\n", sepc);
  printf("  address that caused page fault: 0x%x\n", stval);
#endif /* DEBUG */
}

void handle_load_page_fault(struct context* context, uint64_t stval) {
  if (stval < context->program_break)
    kmap_page(context->pt, stval, 1);
    // TODO: also check if the address is higher than the lowest mapped page so that for example null-pointer dereferencing still causes segfaults
  // TODO: check if the page-fault was caused by stack growth and map it if that's the case
  else {
    printf("segmentation fault: context %d tried to load from address 0x%x\n", context->id, stval);
    // TODO: kill this context or something like that
  }

#ifdef DEBUG
  printf("received load page fault caused by context %d\n", context->id);
  printf("  address that caused page fault: 0x%x\n", stval);
#endif /* DEBUG */
}

void handle_store_amo_page_fault(struct context* context, uint64_t stval) {
  if (stval < context->program_break)
    kmap_page(context->pt, stval, 1);
    // TODO: also check if the address is higher than the lowest mapped page so that for example storing sth at null still causes segfaults
  // TODO: check if the page-fault was caused by stack growth and map it if that's the case
  else {
    printf("segmentation fault: context %d tried to store/AMO at address 0x%x\n", context->id, stval);
    // TODO: kill this context or something like that
  }

#ifdef DEBUG
  printf("received store/AMO page fault caused by context %d\n", context->id);
  printf("  address that caused page fault: 0x%x\n", stval);
#endif /* DEBUG */
}

void setup_smode_trap_handler(trap_handler_t handler) {
    disable_smode_interrupts();

    // 4.1.4 stvec - handler functions must be aligned on a 4 byte boundary
    if (((uint64_t)handler) & 0x03) {
        puts("setup_trap_handler: Cannot apply unaligned trap handler!\n");
        return;
    }

    // mtvec has both the base address and the vectoring mode (2 bits)
    // Use direct mode (0x00)
    uint64_t stvec = (((uint64_t)handler) & ~(0x03ULL));
    asm volatile (
        "csrw stvec, %[regValue];"
        :
        : [regValue] "r" (stvec)
    );

    enable_smode_interrupts();
}
