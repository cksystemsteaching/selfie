#include "trap.h"
#include "syscall.h"
#include "tinycstd.h"

#define SCAUSE_INTERRUPT_BIT_MASK 0x8000000000000000
#define SCAUSE_EXCEPTION_CODE_MASK 0x7FFFFFFFFFFFFFFF
#define SCAUSE_ECALL 8

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

void trap_handler() {
  uint64_t scause;
  uint64_t syscall_number;

  asm volatile(
    "csrr %[scause], scause;"
    "mv %[syscall_number], a7;"
    : [scause] "=r" (scause), [syscall_number] "=r" (syscall_number)
  );

  if (scause == SCAUSE_ECALL) {
    switch (syscall_number) {
      case SYSCALL_EXIT:

      case SYSCALL_READ:

      case SYSCALL_WRITE:

      case SYSCALL_OPENAT:

      case SYSCALL_BRK:

      default:
        printf("received unknown syscall '0x%x'\n", syscall_number);
    }
  }

#ifdef DEBUG
  printf("trap handler has been executed\n");
  printf("  scause:         0x%x\n", scause);
  printf("  syscall number: 0x%x\n", syscall_number);
#endif /* DEBUG */
}

void setup_smode_trap_handler(trap_handler_t handler) {
    disable_smode_interrupts();

    // 4.1.4 stvec - handler functions must be aligned on a 4 byte boundary
    if (((uint64_t)handler) & 0x03) {
        write(1, "setup_trap_handler: Cannot apply unaligned trap handler!\n", 57);
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
