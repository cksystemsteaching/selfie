#ifndef KERN_CONFIG
#define KERN_CONFIG

#define NUM_STACK_PAGES 2
#define MAX_AMOUNT_OF_CONTEXTS 32

#define NUM_FDS 32

// The trampoline must be mapped at the same vaddr for both the kernel and
// the userspace processes. The page is mapped to the last VPN slot available
// Sv39 has 39bit adresses: 2^39 - PAGESIZE = 0x80'0000'0000 - 0x1000 = 0x7F'FFFF'F000
// According to the Sv39 documentation, the vaddr "must have bits 63–39 all equal to bit 38, or else a page-fault
// exception will occur", thus the actual vaddr is 0xFFFF'FFFF'FFFF'F000
// It will be mapped twice in the kernel address space
#define TRAMPOLINE_VADDR 0xFFFFFFFFFFFFF000UL

// The kernel's stack is mapped into virtual address space's higher half in its own address space
// as well as all userspace processes (but not accessible to those)
// This is required so that our trap handler can access the kernel stack easily.
// Due to descending full stack semantics, we need to point sp one element above the actual first stack slot
#define STACK_VADDR TRAMPOLINE_VADDR

// The top-most stack address for a user process.
// As specified by the RISC-V ELF psABI (https://github.com/riscv/riscv-elf-psabi-doc/blob/master/riscv-elf.md),
// we use a descending full stack, i.e. sp points to the last pushed element in the stack
// Thus, USERSPACE_STACK_START shall be positioned one above the actual first stack slot.
// To have a clean separation between userspace and kernel-in-userspace pages, userspace pages
// will be placed in the lower 256 GiB range (bit 38 always cleared).
#define USERSPACE_STACK_START 0x4000000000UL

#endif
