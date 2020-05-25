#include "trap.h"

#include "syscall.h"

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

void setup_smode_trap_handler(trap_handler handler) {
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
