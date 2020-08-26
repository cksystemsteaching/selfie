#ifndef KERN_CONFIG
#define KERN_CONFIG

#define NUM_STACK_PAGES 2
#define MAX_AMOUNT_OF_CONTEXTS 32

#define NUM_FDS 32

// The maximum number of pages that may be allocated.
// Before paging is enabled, the kernel will assure there are PAGE_POOL_NUM_PAGES free pages
// mapped to its virtual address space. This is done to simplify management of page table nodes
// (if you want to add a node to the page table tree, it must already be mapped so that it can be
// modified) without having to manage a free page pool.
// For now, 8MiB, i.e. 1024 4k-pages, shall be enough
#define PAGE_POOL_NUM_PAGES 0x800

// The trampoline must be mapped at the same vaddr for both the kernel and
// the userspace processes. The page is mapped to the last VPN slot available
// Sv39 has 39bit adresses: 2^39 - PAGESIZE = 0x80'0000'0000 - 0x1000 = 0x7F'FFFF'F000
// According to the Sv39 documentation, the vaddr "must have bits 63–39 all equal to bit 38, or else a page-fault
// exception will occur", thus the actual vaddr is 0xFFFF'FFFF'FFFF'F000
// It will be mapped twice in the kernel address space
#define TRAMPOLINE_VADDR 0xFFFFFFFFFFFFF000ULL

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
#define USERSPACE_STACK_START 0x4000000000ULL

#define MAX_ARGV_LENGTH 24


#define INIT_FILE_PATH "selfie.m"

// The maximum length of "file system" paths
#define PATH_MAX_LEN (512 + 1)

// The time delta that will be set at the end of the trap handler before jumping back into
// the trap handler's wrapper code. This value doesn't have a fixed unit since the execution
// environment only "should provide a means of determining the period of the real-time counter
// (seconds/tick)" (RISC-V Spec. 20191213 Chapter 10.1) but isn't actually obligated to do so.
#define TIMESLICE 500000ULL

#endif
