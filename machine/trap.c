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

struct registers temp_saved_regs;

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

void store_saved_registers_in_context(struct context* context) {
    context->saved_regs->ra  = temp_saved_regs.ra;
    context->saved_regs->sp  = temp_saved_regs.sp;
    context->saved_regs->gp  = temp_saved_regs.gp;
    context->saved_regs->tp  = temp_saved_regs.tp;
    context->saved_regs->t0  = temp_saved_regs.t0;
    context->saved_regs->t1  = temp_saved_regs.t1;
    context->saved_regs->t2  = temp_saved_regs.t2;
    context->saved_regs->s0  = temp_saved_regs.s0;
    context->saved_regs->s1  = temp_saved_regs.s1;
    context->saved_regs->a0  = temp_saved_regs.a0;
    context->saved_regs->a1  = temp_saved_regs.a1;
    context->saved_regs->a2  = temp_saved_regs.a2;
    context->saved_regs->a3  = temp_saved_regs.a3;
    context->saved_regs->a4  = temp_saved_regs.a4;
    context->saved_regs->a5  = temp_saved_regs.a5;
    context->saved_regs->a6  = temp_saved_regs.a6;
    context->saved_regs->a7  = temp_saved_regs.a7;
    context->saved_regs->s2  = temp_saved_regs.s2;
    context->saved_regs->s3  = temp_saved_regs.s3;
    context->saved_regs->s4  = temp_saved_regs.s4;
    context->saved_regs->s5  = temp_saved_regs.s5;
    context->saved_regs->s6  = temp_saved_regs.s6;
    context->saved_regs->s7  = temp_saved_regs.s7;
    context->saved_regs->s8  = temp_saved_regs.s8;
    context->saved_regs->s9  = temp_saved_regs.s9;
    context->saved_regs->s10 = temp_saved_regs.s10;
    context->saved_regs->s11 = temp_saved_regs.s11;
    context->saved_regs->t3  = temp_saved_regs.t3;
    context->saved_regs->t4  = temp_saved_regs.t4;
    context->saved_regs->t5  = temp_saved_regs.t5;
    context->saved_regs->t6  = temp_saved_regs.t6;
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

  //store_saved_registers_in_context(context); // TODO: uncomment as soon as we have proper contexts

  if (interrupt_bit)
    // TODO: timer interrupts etc
    print_unhandled_trap(context, interrupt_bit, exception_code, stval, sepc);
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
        print_unhandled_trap(context, interrupt_bit, exception_code, stval, sepc);
    }

#ifdef DEBUG
  printf("trap handler has been executed (caused context %u)\n", context->id);
  printf("  scause:         0x%x\n", scause);
  printf("  syscall number: 0x%x\n", syscall_number);
#endif /* DEBUG */
}

void print_unhandled_trap(struct context* context, char interrupt_bit, uint64_t exception_code, uint64_t stval, uint64_t sepc) {
  printf("unhandled trap (caused by context %u)\n", context->id);
  printf("  interrupt bit:  %d\n", interrupt_bit);
  printf("  exception code: %d\n", exception_code);
  printf("  stval:          0x%x\n", stval);
  printf("  sepc:           0x%p\n", sepc);
}

void handle_ecall(struct context* context) {
  uint64_t syscall_id;
  uint64_t syscall_param_0;
  uint64_t syscall_param_1;
  uint64_t syscall_param_2;

  // TODO: this currently can't be read since we dont have really contexts yet
  /*syscall_id = context->saved_regs->a7;
  syscall_param_0 = context->saved_regs->a0;
  syscall_param_1 = context->saved_regs->a1;
  syscall_param_2 = context->saved_regs->a2;*/

  switch (syscall_id) {
    case SYSCALL_EXIT:

    case SYSCALL_READ:

    case SYSCALL_WRITE:

    case SYSCALL_OPENAT:

    case SYSCALL_BRK:

    default:
      printf("received unknown syscall '0x%x' from context %u\n", syscall_id, context->id);
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

char is_legal_memory_access(struct memory_boundaries* legal_memory_boundaries, uint64_t address) {
    uint64_t page_number = address >> 12;

    if ((legal_memory_boundaries->lowest_lo_page <= page_number && page_number <= legal_memory_boundaries->highest_lo_page)
            || (legal_memory_boundaries->lowest_mid_page <= page_number && page_number <= legal_memory_boundaries->highest_mid_page)
            || (legal_memory_boundaries->lowest_hi_page <= page_number && page_number <= legal_memory_boundaries->highest_hi_page))
        return 1;
    else
        return 0;
}

void handle_instruction_page_fault(struct context* context, uint64_t sepc, uint64_t stval) {
  if (is_legal_memory_access(context->legal_memory_boundaries, stval)) {
    // TODO: handling faults like that is probably necessary for native hypster support
  } else {
    // at the moment we raise a segfault here since we map the entire code
    // segment when loading a binary
    printf("segmentation fault: context %u tried to execute the instruction at 0x%x and faulted at 0x%x\n", context->id, sepc, stval);
    // TODO: kill this context
  }

#ifdef DEBUG
  printf("received instruction page fault caused by context %u\n", context->id);
  printf("  address of instruction:         0x%x\n", sepc);
  printf("  address that caused page fault: 0x%x\n", stval);
#endif /* DEBUG */
}

void handle_load_page_fault(struct context* context, uint64_t stval) {
  if (is_legal_memory_access(context->legal_memory_boundaries, stval)
          // stack has grown but the page isnt mapped yet
          || (context->saved_regs->sp <= stval && stval <= context->legal_memory_boundaries->lowest_mid_page))
    kmap_page(context->pt, stval, 1);
  else {
    printf("segmentation fault: context %u tried to load from address 0x%x\n", context->id, stval);
    // TODO: kill this context or something like that
  }

#ifdef DEBUG
  printf("received load page fault caused by context %u\n", context->id);
  printf("  address that caused page fault: 0x%x\n", stval);
#endif /* DEBUG */
}

void handle_store_amo_page_fault(struct context* context, uint64_t stval) {
  if (is_legal_memory_access(context->legal_memory_boundaries, stval)
          // stack has grown but the page isnt mapped yet
          || (context->saved_regs->sp <= stval && stval <= context->legal_memory_boundaries->lowest_mid_page))
    kmap_page(context->pt, stval, 1);
  else {
    printf("segmentation fault: context %u tried to store/AMO at address 0x%x\n", context->id, stval);
    // TODO: kill this context or something like that
  }

#ifdef DEBUG
  printf("received store/AMO page fault caused by context %u\n", context->id);
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
