#ifndef KERN_MMU
#define KERN_MMU

#include <stdint.h>
#include <stdbool.h>

#define PAGESIZE 4096

#define SATP_MODE_SV39 (8ULL << 60)
#define SATP_MODE_SV48 (9ULL << 60)
#define SATP_PPN_BITMASK 0x00000FFFFFFFFFFF
#define SATP_ASID_POS 44

#define SV39_PAGE_COUNT (1ULL << (40 - 12))
#define SV39_MAX_VPN 0xFFFFFFFFFFFFF

struct __attribute__((packed)) pt_entry {
  uint64_t v        : 1; // valid flag
  uint64_t r        : 1; // read flag
  uint64_t w        : 1; // write flag
  uint64_t x        : 1; // execute flag
  uint64_t u        : 1; // U-mode accessible flag
  uint64_t g        : 1; // global mapping flag
  uint64_t a        : 1; // accessed flag
  uint64_t d        : 1; // dirty flag
  uint64_t rsw      : 2; // bits can be used freely by a supervisor
  uint64_t ppn      :44; // physical page number
  uint64_t reserved :10; // reserved for future use
};

extern struct pt_entry kernel_pt[512];

extern void* initial_stack_start();

/**
 * @brief Returns the PPN of the next free page
 *
 * @return The physical page number (paddr / 2^12) of the next free page
 */
uint64_t kpalloc();
/**
 * @brief Attaches an empty page to the kernel space, zeroes it out and returns the PPN of it
 *
 * @return  The physical page number (paddr / 2^12) of the next free page
 */
uint64_t kzalloc();
/**
 * @brief Frees a PPN, to be reused
 *
 * Tells the memory manager that a page is not in use anymore and may be reallocated again
 * on a call to kpalloc. The page is attached to a free page linked list as head, with the
 * first dword pointing to the previous linked list head (->next).
 *
 * @warning Make absolutely sure to not have any referenced to the page anymore.
 * @warning Especially writing to the first dword will break the mechanism.
 *
 * @param ppn The PPN to free
 */
void kpfree(uint64_t ppn);

void kzero_page(uint64_t vpn);

// both table and (pt_at_ppn << 12) have to be valid page-aligned pointers
struct pt_entry* create_pt_entry(struct pt_entry* table, uint64_t index, uint64_t ppn, char pt_at_ppn_addr, char u_mode_accessible);

uint64_t kmap_page(struct pt_entry* table, uint64_t vaddr, char u_mode_accessible);
bool kmap_page_by_ppn(struct pt_entry* table, uint64_t vaddr, uint64_t ppn, char u_mode_accessible);
bool kmap_user_page_and_identity_map_into_kernel(struct pt_entry* table, uint64_t vaddr);

uint64_t vaddr_to_vpn(uint64_t vaddr);
uint64_t vpn_to_vaddr(uint64_t vaddr);
uint64_t vaddr_to_paddr(struct pt_entry* table, uint64_t vaddr);
uint64_t paddr_to_ppn(const void* address);
const void* ppn_to_paddr(uint64_t ppn);

bool is_valid_sv39_vaddr(uint64_t vaddr);

bool is_vaddr_mapped(struct pt_entry* table, uint64_t vaddr);

/**
 * @brief Performs an identity mapping in a page table for a given range.
 *
 * Maps all pages that host the content for the given memory range
 * from and to (exclusive) to the given table. An identity mapping is performed,
 * i.e. the virtual address resolves to an equal physical address.
 *
 * As it is not possible to partially mount pages, the start address is rounded
 * down and the end address is rounded up to page boundaries.
 *
 * @param table The page table where the pages shall be attached to
 * @param from The start of the memory range to attach (inclusive).
 * @param to The end of the memory range to attach (exclusive).
 */
void kidentity_map_range(struct pt_entry* table, const void* from, const void* to);
void kidentity_map_ppn(struct pt_entry* table, uint64_t ppn, bool u_mode_accessible);

void kdump_pt(struct pt_entry* table);

void kmap_kernel_upper_half(struct pt_entry* table);

uint64_t assemble_satp_value(struct pt_entry* table, uint16_t asid);
void kswitch_active_pt(struct pt_entry* table, uint16_t asid);

void kinit_page_pool();

uint64_t kstrlcpy_from_vspace(char* dest_kaddr, uint64_t src_vaddr, uint64_t n, struct pt_entry* table);

void kfree_page_table(struct pt_entry* root);

extern uint64_t ppn_bump;

#endif /* KERN_MMU */
