#include "mmu.h"
#include "config.h"
#include "context.h"
#include "tinycstd.h"
#include "trap.h"

#define VPN_2_BITMASK 0x7FC0000000ULL
#define VPN_1_BITMASK 0x3FE00000
#define VPN_0_BITMASK 0x1FF000

uint64_t create_pt_entry(struct pt_entry *table, uint64_t index, uint64_t ppn, char is_pt_node, char u_mode_accessible) {
  struct pt_entry* entry = (table + index);

  entry->ppn = ppn;
  entry->d = 1;
  entry->a = 1;

  if (!is_pt_node) {
    entry->x = 1;
    entry->w = 1;
    entry->r = 1;
  }

  if (u_mode_accessible)
    entry->u = 1;

  entry->v = 1;

  return ppn << 12;
}

uint64_t ppn_bump;
uint64_t used_pages = 0;
uint64_t kpalloc() {
    // page allocation is the only form of dynamic memory allocation in this kernel

    // Check for free pages in the page pool
    if (used_pages >= PAGE_POOL_NUM_PAGES)
      return 0;

    kernel_context.program_break = ppn_bump;
    kernel_context.legal_memory_boundaries.highest_lo_page = ppn_bump;

    used_pages++;
    return ppn_bump++;
}
uint64_t kzalloc() {
    uint64_t ppn = kpalloc();
    if (ppn != 0)
      kzero_page(ppn);
    return ppn;
}

void kzero_page(uint64_t vpn) {
    uint64_t* page_addr = (uint64_t*) ppn_to_paddr(vpn);

    for (size_t i = 0; i < PAGESIZE/sizeof(uint64_t); i++)
        page_addr[i] = 0;
}

struct pt_entry* retrieve_pt_entry_from_table(struct pt_entry* table, uint64_t index) {
  return (struct pt_entry*) ((uint64_t)(table + index)->ppn << 12);
}

uint64_t kmap_page(struct pt_entry* table, uint64_t vaddr, char u_mode_accessible) {
    uint64_t ppn = kzalloc();
    if (ppn == 0)
      return 0;

    if (kmap_page_by_ppn(table, vaddr, ppn, u_mode_accessible))
      return ppn;
    else
      return 0;
}
bool kmap_page_by_ppn(struct pt_entry* table, uint64_t vaddr, uint64_t ppn, char u_mode_accessible) {
  uint64_t vpn_2 = (vaddr & VPN_2_BITMASK) >> 30;
  uint64_t vpn_1 = (vaddr & VPN_1_BITMASK) >> 21;
  uint64_t vpn_0 = (vaddr & VPN_0_BITMASK) >> 12;
  struct pt_entry* mid_pt;
  struct pt_entry* leaf_pt;

  if (!table[vpn_2].v) {
    uint64_t ppn = kpalloc();
    if (ppn == 0)
      return false;

    mid_pt = (struct pt_entry*) create_pt_entry(table, vpn_2, ppn, 1, 0);
    kzero_page(ppn);
  }
  else
    mid_pt = retrieve_pt_entry_from_table(table, vpn_2);
  
  if (!mid_pt[vpn_1].v) {
    uint64_t ppn = kpalloc();
    if (ppn == 0)
      return false;

    leaf_pt = (struct pt_entry*) create_pt_entry(mid_pt, vpn_1, ppn, 1, 0);
    kzero_page(ppn);
  }
  else
    leaf_pt = retrieve_pt_entry_from_table(mid_pt, vpn_1);

  create_pt_entry(leaf_pt, vpn_0, ppn, 0, u_mode_accessible);
  return true;
}

bool kmap_user_page_and_identity_map_into_kernel(struct pt_entry* table, uint64_t vaddr) {
    uint64_t ppn;

    ppn = kmap_page(table, vaddr, true);
    if (ppn == 0)
      return false;

    kidentity_map_ppn(kernel_context.pt, ppn, false);
    return true;
}

uint64_t vaddr_to_vpn(uint64_t vaddr) {
    const uint64_t LOWEST_39_BITS = 0x7FFFFFFFFF;

    // RISC-V requires that for virtual addresses
    // bites 39 to 64 have the value of bit 38
    return ((vaddr & LOWEST_39_BITS) >> 12);
}
uint64_t vpn_to_vaddr(uint64_t vpn) {
  // Sv39 requires virtual addresses to sign-extend bit 38
  // The bitmask to OR to this is (2^64 - 1) - (2^39 - 1) = 0xFFFFFF8000000000
  const uint64_t SIGN_EXTEND_BIT38 = 0xFFFFFF8000000000;

  uint64_t vaddr = vpn << 12;

  if (vaddr & (1ULL << 38))
    vaddr |= SIGN_EXTEND_BIT38;

  return vaddr;
}
uint64_t vaddr_to_paddr(struct pt_entry* table, uint64_t vaddr) {
  uint64_t vpn_2 = (vaddr & VPN_2_BITMASK) >> 30;
  uint64_t vpn_1 = (vaddr & VPN_1_BITMASK) >> 21;
  uint64_t vpn_0 = (vaddr & VPN_0_BITMASK) >> 12;
  uint64_t offset = vaddr & 0x0FFF;
  struct pt_entry* mid_pt;
  struct pt_entry* leaf_pt;

  if (!table[vpn_2].v)
    return 0x00;
  mid_pt = (struct pt_entry*) ppn_to_paddr(table[vpn_2].ppn);

  if (!mid_pt[vpn_1].v)
    return 0x00;
  leaf_pt = (struct pt_entry*) ppn_to_paddr(mid_pt[vpn_1].ppn);

  if (!leaf_pt[vpn_0].v)
    return 0x00;

  return ((uint64_t)ppn_to_paddr(leaf_pt[vpn_0].ppn)) | offset;
}

uint64_t paddr_to_ppn(const void* address) {
    return ((uint64_t)address) >> 12;
}
const void* ppn_to_paddr(uint64_t ppn) {
    return (const void*)(ppn << 12);
}

void kidentity_map_range(struct pt_entry* table, const void* from, const void* to) {
    // By obtaining the PPNs, there's no need to do any rounding
    uint64_t ppn_from = paddr_to_ppn(from);
    uint64_t ppn_to = paddr_to_ppn(to);

    uint64_t ppn = ppn_from;

    while (ppn < ppn_to) {
        uint64_t page_vaddr = vpn_to_vaddr(ppn);

        kmap_page_by_ppn(table, page_vaddr, ppn, false);

        ppn++;
    };
}
void kidentity_map_ppn(struct pt_entry* table, uint64_t ppn, bool u_mode_accessible) {
    kmap_page_by_ppn(table, (uint64_t)ppn_to_paddr(ppn), ppn, u_mode_accessible);
}

void kdump_pt(struct pt_entry* table) {
    printf("Page Table:\n");

    for (uint64_t vpn_2 = 0; vpn_2 < 512; vpn_2++) {
        if (!table[vpn_2].v)
            continue;

        struct pt_entry* mid_pt = retrieve_pt_entry_from_table(table, vpn_2);
        uint64_t mid_vaddr = (vpn_2 << 30);
        uint64_t mid_vaddr_end = ((vpn_2+1) << 30);
        printf("|-Gigapage (VPN %x): %p-%p\n", vpn_2, mid_vaddr, mid_vaddr_end);

        if (mid_pt == NULL) {
            printf("  <invalid>\n");
        } else {
            for (uint64_t vpn_1 = 0; vpn_1 < 512; vpn_1++) {
                if (!mid_pt[vpn_1].v)
                    continue;

                struct pt_entry* leaf_pt = retrieve_pt_entry_from_table(mid_pt, vpn_1);
                uint64_t leaf_vaddr = mid_vaddr + (vpn_1 << 21);
                uint64_t leaf_vaddr_end = mid_vaddr + ((vpn_1+1) << 21);
                printf("| |-Megapage (VPN %x): %p-%p\n", vpn_1, leaf_vaddr, leaf_vaddr_end);

                if (leaf_pt == NULL) {
                    printf("    <invalid>\n");
                } else {
                    for (uint64_t vpn_0 = 0; vpn_0 < 512; vpn_0++) {
                        if (!leaf_pt[vpn_0].v)
                            continue;

                        uint64_t vaddr = leaf_vaddr + (vpn_0 << 12);
                        uint64_t vaddr_end = leaf_vaddr + ((vpn_0+1) << 12);
                        uint64_t paddr = leaf_pt[vpn_0].ppn << 12;

                        printf("| | |-Page (VPN %x): %p-%p: mapped to paddr %p\n", vpn_0, vaddr, vaddr_end, paddr);
                    }
                }
            }
        }
    }
}

void kmap_kernel_upper_half(struct pt_entry* table) {
    // Map upper-half vspace pages
    // These pages are present in both user and kernel vspace
    // Trap handler trampoline
    kmap_page_by_ppn(table, TRAMPOLINE_VADDR, paddr_to_ppn(trap_handler_wrapper), false);
    // Kernel stack
    uint64_t vaddr = STACK_VADDR - PAGESIZE;
    uint64_t ppn = paddr_to_ppn(initial_stack_start() - 1); // -1 due to full stack semantics + pointer arithmetics
    for (uint64_t i = 0; i < NUM_STACK_PAGES; i++) {
        kmap_page_by_ppn(table, vaddr, ppn, false);

        vaddr -= PAGESIZE;
        ppn--;
    }
}

uint64_t assemble_satp_value(struct pt_entry* table, uint16_t asid) {
    uint64_t table_ppn = paddr_to_ppn(table);

    return (SATP_MODE_SV39 | ((uint64_t) asid << SATP_ASID_POS) | (table_ppn & SATP_PPN_BITMASK));
}

void kswitch_active_pt(struct pt_entry* table, uint16_t asid) {
    uint64_t satpValue = assemble_satp_value(table, asid);

    // Set the SATP and SSCRATCH value (for easier kernel pt switching)
    // Also, perform a cache flush by specifying the ASID
    // We do not use global mappings -> rs1 = x0
    asm volatile(
        "csrw satp, %[value];"
        "csrw sscratch, %[value];"
        "sfence.vma zero, %[asid]" // RISC-V Priviled
        :
        : [value] "r" (satpValue), [asid] "r" (asid)
    );
}

void kinit_page_pool() {
  uint64_t pagesAllocated = 0;
  uint64_t oldPpn = ppn_bump;

  // assert: PAGE_POOL_NUM_PAGES is large enough to host all nodes in the page table, as kpalloc in kmap_page_by_ppn would return PPN 0 otherwise
  //         Thus, PAGE_POOL_NUM_PAGES shall have at least approx. 6 pages
  while (pagesAllocated < PAGE_POOL_NUM_PAGES) {
    uint64_t toAllocate = PAGE_POOL_NUM_PAGES - pagesAllocated;

    // Try to map the whole range of pages inside
    // Add +1 to upper bound ppn because kidentity_map_range is exclusive
    kidentity_map_range(kernel_pt, ppn_to_paddr(oldPpn), ppn_to_paddr(oldPpn + toAllocate + 1));
    // If the mapping process required to allocate new page table nodes, ppn_bump would be increased
    // We have to ignore the amount of PT nodes in our amount of free page pool pages because they
    // are already in use.
    uint64_t deltaAllocated = ppn_bump - oldPpn;
    pagesAllocated += toAllocate - deltaAllocated;

    oldPpn = ppn_bump;
  }

  // Reset the used pages counter
  used_pages = 0;
}

__attribute__((aligned(4096)))
struct pt_entry kernel_pt[512];
