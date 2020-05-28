#include "trap.h"
#include "syscall.h"

#define SCAUSE_INTERRUPT_BIT_MASK 0x8000000000000000
#define SCAUSE_EXCEPTION_CODE_MASK 0x7FFFFFFFFFFFFFFF

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
  uint64_t syscall_number;

  asm volatile(
    "csrr %[scause], scause;"
    "mv %[syscall_number], a7;"
    : [scause] "=r" (scause), [syscall_number] "=r" (syscall_number)
  );

  write(1, "trap handler has been executed\n", 31);
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
