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

typedef void (*trap_handler)(/* TODO: Context struct */);

void disable_smode_interrupts();
void enable_smode_interrupts();

void enable_smode_interrupt_types(uint64_t bitmask);
void disable_smode_interrupt_types(uint64_t bitmask);

void setup_smode_trap_handler(trap_handler handler);

#endif /* KERN_TRAP */
