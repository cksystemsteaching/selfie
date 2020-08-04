#include "mmu.h"
#include "tinycstd.h"
#include <stdint.h>

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
uint64_t kpalloc() {
    // TODO: zero this memory beforehand or else we will have some serious problems since the 'valid' bit in pt entries could be 1 when it should be 0
    return ppn_bump++;
}

struct pt_entry* retrieve_pt_entry_from_table(struct pt_entry* table, uint64_t index) {
  return (struct pt_entry*) ((table + index)->ppn << 12);
}

void kmap_page(struct pt_entry* table, uint64_t vaddr, char u_mode_accessible) {
    kmap_page_by_ppn(table, vaddr, kpalloc(), u_mode_accessible);
}
void kmap_page_by_ppn(struct pt_entry* table, uint64_t vaddr, uint64_t ppn, char u_mode_accessible) {
  uint64_t vpn_2 = (vaddr & VPN_2_BITMASK) >> 30;
  uint64_t vpn_1 = (vaddr & VPN_1_BITMASK) >> 21;
  uint64_t vpn_0 = (vaddr & VPN_0_BITMASK) >> 12;
  struct pt_entry* mid_pt;
  struct pt_entry* leaf_pt;

  if (!table[vpn_2].v)
    mid_pt = (struct pt_entry*) create_pt_entry(table, vpn_2, kpalloc(), 1, 0);
  else
    mid_pt = retrieve_pt_entry_from_table(table, vpn_2);
  
  if (!mid_pt[vpn_1].v)
    leaf_pt = (struct pt_entry*) create_pt_entry(mid_pt, vpn_1, kpalloc(), 1, 0);
  else
    leaf_pt = retrieve_pt_entry_from_table(mid_pt, vpn_1);

  create_pt_entry(leaf_pt, vpn_0, ppn, 0, u_mode_accessible);
}

uint64_t paddr_to_ppn(const void* address) {
    return ((uint64_t)address) >> 12;
}

void kidentity_map_range(struct pt_entry* table, void* from, void* to) {
    // By obtaining the PPNs, there's no need to do any rounding
    uint64_t ppn_from = ((uint64_t) from) >> 12;
    uint64_t ppn_to = ((uint64_t) to) >> 12;

    uint64_t ppn = ppn_from;

    while (ppn < ppn_to) {
        uint64_t page_vaddr = ppn << 12;

        kmap_page_by_ppn(table, page_vaddr, ppn, false);

        ppn++;
    };
}

void kdump_pt(struct pt_entry* table) {
    printf("Page Table:\n");

    for (uint64_t vpn_2 = 0; vpn_2 < 512; vpn_2++) {
        if (!table[vpn_2].v)
            continue;

        struct pt_entry* mid_pt = retrieve_pt_entry_from_table(kernel_pt, vpn_2);
        uint64_t mid_vaddr = (vpn_2 << 30);
        uint64_t mid_vaddr_end = ((vpn_2+1) << 30);
        printf("|-Gigapage (VPN %x): %p-%p\n", vpn_2, mid_vaddr, mid_vaddr_end);

        for (uint64_t vpn_1 = 0; vpn_1 < 512; vpn_1++) {
            if (!mid_pt[vpn_1].v)
                continue;

            struct pt_entry* leaf_pt = retrieve_pt_entry_from_table(mid_pt, vpn_1);
            uint64_t leaf_vaddr = mid_vaddr + (vpn_1 << 21);
            uint64_t leaf_vaddr_end = mid_vaddr + ((vpn_1+1) << 21);
            printf("| |-Megapage (VPN %x): %p-%p\n", vpn_1, leaf_vaddr, leaf_vaddr_end);

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

__attribute__((aligned(4096)))
struct pt_entry kernel_pt[512];
