#include "mmu.h"
#include "tinycstd.h"

#define VPN_2_BITMASK 0x7FC0000000ULL
#define VPN_1_BITMASK 0x3FE00000
#define VPN_0_BITMASK 0x1FF000

uint64_t create_pt_entry(struct pt_entry* table, uint64_t index, uint64_t ppn, char pt_at_ppn_addr, char u_mode_accessible) {
  struct pt_entry* entry = (table + index);

  entry->ppn = ppn;
  entry->d = 1;
  entry->a = 1;

  if (!pt_at_ppn_addr) {
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
  uint64_t vpn_2 = vaddr & VPN_2_BITMASK;
  uint64_t vpn_1 = vaddr & VPN_1_BITMASK;
  uint64_t vpn_0 = vaddr & VPN_0_BITMASK;
  struct pt_entry* mid_pt;
  struct pt_entry* leaf_pt;

  mid_pt = retrieve_pt_entry_from_table(table, vpn_2);
  
  if (!mid_pt->v)
    mid_pt = (struct pt_entry*) create_pt_entry(table, vpn_2, kpalloc(), 1, 0);
  
  leaf_pt = retrieve_pt_entry_from_table(mid_pt, vpn_1);

  if (!leaf_pt->v)
    leaf_pt = (struct pt_entry*) create_pt_entry(mid_pt, vpn_1, kpalloc(), 1, 0);

  create_pt_entry(leaf_pt, vpn_0, kpalloc(), 0, u_mode_accessible);
}

__attribute__((aligned(4096)))
struct pt_entry root_table[512];
