#include "diag.h"
#include "mmu.h"
#include "config.h"
#include "context.h"
#include "tinycstd.h"
#include "trap.h"
#include "numeric-utils.h"

#define VPN_2_BITMASK 0x7FC0000000ULL
#define VPN_1_BITMASK 0x3FE00000
#define VPN_0_BITMASK 0x1FF000

struct pt_entry* create_pt_entry(struct pt_entry *table, uint64_t index, uint64_t ppn, bool is_pt_node, bool u_mode_accessible) {
  assert(!(is_pt_node && u_mode_accessible));

  struct pt_entry* entry = (table + index);

  entry->ppn = ppn;

  if (!is_pt_node) {
    entry->d = 1;
    entry->a = 1;

    entry->x = 1;
    entry->w = 1;
    entry->r = 1;
  }

  if (u_mode_accessible)
    entry->u = 1;

  entry->v = 1;

  return (struct pt_entry*) ppn_to_paddr(ppn);
}

uint64_t ppn_bump;
uint64_t used_pages = 0;
uint64_t free_list_head = 0;
uint64_t kpalloc() {
  // page allocation is the only form of dynamic memory allocation in this kernel

  // At first check for freed pages in the free pages linked list
  if (free_list_head != 0) {
    // We got a freed page to reallocate
    uint64_t ppn = free_list_head;
    uint64_t* next = (uint64_t*) ppn_to_paddr(ppn);
    free_list_head = *next;

    return ppn;
  }

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

void kpfree(uint64_t ppn) {
  uint64_t* next = (uint64_t*) ppn_to_paddr(ppn);
  *next = free_list_head;
  free_list_head = ppn;
}

void kzero_page(uint64_t vpn) {
  uint64_t* page_addr = (uint64_t*) ppn_to_paddr(vpn);

  for (size_t i = 0; i < PAGESIZE / sizeof(uint64_t); i++)
    page_addr[i] = 0;
}

struct pt_entry* retrieve_pt_entry_from_table(struct pt_entry* table, uint64_t index) {
  return (struct pt_entry*) ppn_to_paddr((table + index)->ppn);
}

uint64_t kmap_page(struct pt_entry* table, uint64_t vaddr, bool u_mode_accessible) {
  uint64_t ppn = kzalloc();
  if (ppn == 0)
    return 0;

  if (kmap_page_by_ppn(table, vaddr, ppn, u_mode_accessible))
    return ppn;
  else
    return 0;
}

bool kmap_page_by_ppn(struct pt_entry* table, uint64_t vaddr, uint64_t ppn, bool u_mode_accessible) {
  uint64_t vpn_2 = (vaddr & VPN_2_BITMASK) >> 30;
  uint64_t vpn_1 = (vaddr & VPN_1_BITMASK) >> 21;
  uint64_t vpn_0 = (vaddr & VPN_0_BITMASK) >> 12;
  struct pt_entry* mid_pt;
  struct pt_entry* leaf_pt;

  if (!table[vpn_2].v) {
    uint64_t ppn = kzalloc();
    if (ppn == 0)
      return false;

    mid_pt = create_pt_entry(table, vpn_2, ppn, true, false);
  } else
    mid_pt = retrieve_pt_entry_from_table(table, vpn_2);
  
  if (!mid_pt[vpn_1].v) {
    uint64_t ppn = kzalloc();
    if (ppn == 0)
      return false;

    leaf_pt = create_pt_entry(mid_pt, vpn_1, ppn, true, false);
  } else
    leaf_pt = retrieve_pt_entry_from_table(mid_pt, vpn_1);

  create_pt_entry(leaf_pt, vpn_0, ppn, false, u_mode_accessible);
  return true;
}

bool map_and_store_in_user_vaddr_space(struct pt_entry* table, uint64_t vaddr, uint64_t data) {
  if (!is_vaddr_mapped(table, vaddr)) {
    bool map_successful = kmap_page(table, vaddr, true);
    if (!map_successful)
      return false;
  }

  *((uint64_t*) vaddr_to_paddr(table, vaddr)) = data;

  return true;
}

uint64_t upload_string_to_stack(struct pt_entry* table, const char* str, uint64_t sp) {
  uint64_t bytes_to_upload = ROUND_UP(strlen(str) + 1, sizeof(uint64_t));
  uint64_t str_vaddr = sp - bytes_to_upload;

  for (uint64_t i = 0; i < bytes_to_upload; i += sizeof(uint64_t)) {
    bool map_successful = map_and_store_in_user_vaddr_space(table, str_vaddr + i, *((uint64_t*) str));
    if (!map_successful)
      return sp;

    str = (char*) ((uint64_t*) str + 1);
  }

  return str_vaddr;
}

bool kupload_argv(struct context* context, uint64_t argc, const char** argv) {
  // basically an adapted version of selfie's algorithm

  uint64_t sp;
  uint64_t argv_strings[MAX_ARGV_LENGTH];

  sp = context->saved_regs.sp;

  for (uint64_t i = 0; i < argc; ++i) {
    uint64_t new_sp = upload_string_to_stack(context->pt, argv[i], sp);
    if (new_sp == sp)
      return false;
    sp = new_sp;

    argv_strings[i] = sp;
  }

  // push null terminator of env table
  sp -= sizeof(uint64_t);
  bool map_successful = map_and_store_in_user_vaddr_space(context->pt, sp - sizeof(uint64_t), 0);
  if (!map_successful)
    return false;

  // push null terminator for argv table
  sp -= sizeof(uint64_t);
  map_successful = map_and_store_in_user_vaddr_space(context->pt, sp - sizeof(uint64_t), 0);
  if (!map_successful)
    return false;

  // push argv pointers
  for (uint64_t i = argc; i > 0;) {
    sp -= sizeof(uint64_t);
    i -= 1;
    map_successful = map_and_store_in_user_vaddr_space(context->pt, sp, argv_strings[i]);
    if (!map_successful)
      return false;
  }

  // push argc
  sp -= sizeof(uint64_t);
  map_successful = map_and_store_in_user_vaddr_space(context->pt, sp, argc);
  if (!map_successful)
    return false;

  context->saved_regs.sp = sp;

  return true;
}

uint64_t vaddr_to_vpn(uint64_t vaddr) {
  return (vaddr >> 12);
}

uint64_t vpn_to_vaddr(uint64_t vpn) {
  // Sv39 requires virtual addresses to sign-extend bit 38
  // The bitmask to OR to this is (2^64 - 1) - (2^39 - 1) = 0xFFFFFF8000000000
  const uint64_t SIGN_EXTEND_BIT38 = 0xFFFFFF8000000000ULL;

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

  return ((uint64_t) ppn_to_paddr(leaf_pt[vpn_0].ppn)) | offset;
}

uint64_t paddr_to_ppn(const void* address) {
  return ((uint64_t) address) >> 12;
}

const void* ppn_to_paddr(uint64_t ppn) {
  return (const void*) (ppn << 12);
}

bool is_valid_sv39_vaddr(uint64_t vaddr) {
  return !(SV39_MIN_INVALID_VADDR <= vaddr && vaddr <= SV39_MAX_INVALID_VADDR);
}

bool is_user_vaddr(uint64_t vaddr) {
  return (vaddr < SV39_MIN_INVALID_VADDR);
}

bool is_vaddr_mapped(struct pt_entry* table, uint64_t vaddr) {
  return (vaddr_to_paddr(table, vaddr) != 0x00);
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

void kdump_pt(struct pt_entry* table) {
  printf("Page Table:\n");

  for (uint64_t vpn_2 = 0; vpn_2 < NUM_PT_ENTRIES_PER_PAGE_TABLE; vpn_2++) {
    if (!table[vpn_2].v)
      continue;

    struct pt_entry* mid_pt = retrieve_pt_entry_from_table(table, vpn_2);
    uint64_t mid_vaddr = (vpn_2 << 30);
    uint64_t mid_vaddr_end = ((vpn_2 + 1) << 30);
    printf("|-root level (VPN_2 %x): %p-%p\n", vpn_2, mid_vaddr, mid_vaddr_end);

    if (mid_pt == NULL)
      printf("  <invalid>\n");
    else {
      for (uint64_t vpn_1 = 0; vpn_1 < NUM_PT_ENTRIES_PER_PAGE_TABLE; vpn_1++) {
        if (!mid_pt[vpn_1].v)
          continue;

        struct pt_entry* leaf_pt = retrieve_pt_entry_from_table(mid_pt, vpn_1);
        uint64_t leaf_vaddr = mid_vaddr + (vpn_1 << 21);
        uint64_t leaf_vaddr_end = mid_vaddr + ((vpn_1 + 1) << 21);
        printf("| |-mid level (VPN_1 %x): %p-%p\n", vpn_1, leaf_vaddr, leaf_vaddr_end);

        if (leaf_pt == NULL)
          printf("    <invalid>\n");
        else {
          for (uint64_t vpn_0 = 0; vpn_0 < NUM_PT_ENTRIES_PER_PAGE_TABLE; vpn_0++) {
            if (!leaf_pt[vpn_0].v)
              continue;

            uint64_t vaddr = leaf_vaddr + (vpn_0 << 12);
            uint64_t vaddr_end = leaf_vaddr + ((vpn_0 + 1) << 12);
            uint64_t paddr = leaf_pt[vpn_0].ppn << 12;

            printf("| | |-leaf level (VPN_0 %x): %p-%p: mapped to paddr %p\n", vpn_0, vaddr, vaddr_end, paddr);
          }
        }
      }
    }
  }
}

void kmap_kernel_upper_half(struct context* context) {
  // Map upper-half vspace pages
  // These pages are present in both user and kernel vspace
  // Trap handler trampoline
  kmap_page_by_ppn(context->pt, TRAMPOLINE_VADDR, paddr_to_ppn(trap_handler_wrapper), false);
  uint64_t trampoline_vpn = vaddr_to_vpn(TRAMPOLINE_VADDR);
  context->legal_memory_boundaries.highest_hi_page = trampoline_vpn;
  // Kernel stack
  uint64_t vaddr = STACK_VADDR - PAGESIZE;
  uint64_t ppn = paddr_to_ppn(initial_stack_start() - 1); // -1 due to full stack semantics + pointer arithmetics
  for (uint64_t i = 0; i < NUM_STACK_PAGES; i++) {
    kmap_page_by_ppn(context->pt, vaddr, ppn, false);

    vaddr -= PAGESIZE;
    ppn--;
  }
  context->legal_memory_boundaries.lowest_hi_page = trampoline_vpn - NUM_STACK_PAGES;
}

uint64_t assemble_satp_value(struct pt_entry* table, uint16_t asid) {
  uint64_t table_ppn = paddr_to_ppn(table);

  return (SATP_MODE_SV39 | ((uint64_t) asid << SATP_ASID_POS) | (table_ppn & SATP_PPN_BITMASK));
}

void kswitch_active_pt(struct pt_entry* table, uint16_t asid) {
  uint64_t satp_value = assemble_satp_value(table, asid);

  // Set the SATP and SSCRATCH value (for easier kernel pt switching)
  // Also, perform a cache flush by specifying the ASID
  // We do not use global mappings -> rs1 = x0
  asm volatile (
      "csrw satp, %[value];"
      "csrw sscratch, %[value];"
      "sfence.vma zero, %[asid]" // RISC-V Priviled
      :
      : [value] "r" (satp_value), [asid] "r" (asid)
  );
}

void kinit_page_pool() {
  uint64_t pages_allocated = 0;
  uint64_t old_ppn = ppn_bump;

  // assert: PAGE_POOL_NUM_PAGES is large enough to host all nodes in the page table, as kpalloc in kmap_page_by_ppn would return PPN 0 otherwise
  //         Thus, PAGE_POOL_NUM_PAGES shall have at least approx. 6 pages
  while (pages_allocated < PAGE_POOL_NUM_PAGES) {
    uint64_t to_allocate = PAGE_POOL_NUM_PAGES - pages_allocated;

    // Try to map the whole range of pages inside
    // Add +1 to upper bound ppn because kidentity_map_range is exclusive
    kidentity_map_range(kernel_pt, ppn_to_paddr(old_ppn), ppn_to_paddr(old_ppn + to_allocate + 1));
    // If the mapping process required to allocate new page table nodes, ppn_bump would be increased
    // We have to ignore the amount of PT nodes in our amount of free page pool pages because they
    // are already in use.
    uint64_t delta_allocated = ppn_bump - old_ppn;
    pages_allocated += to_allocate - delta_allocated;

    old_ppn = ppn_bump;
  }

  // Reset the used pages counter
  used_pages = 0;
}

uint64_t kstrlcpy_from_vspace(char* dest_kaddr, uint64_t src_vaddr, uint64_t n, struct pt_entry* table) {
  // Copy the string word-wise, similar to how selfie does in down_load_string.
  // It would be possible and more efficient to check page boundaries and load the string
  // page-wise, but the implementation is not as straight-forward

  uint64_t read = 0;

  while (read < (n - 1)) {
    // If the userspace source buffer is either not valid or not mapped, we cannot continue
    // As we cannot complete the copying process, return 0
    if (!(is_user_vaddr(src_vaddr) && is_vaddr_mapped(table, src_vaddr)))
      return 0;

    // Read enough bytes to align to the next word
    // However, do not read more than requested
    // E.g. src_vaddr = 8:  8 - ( 8 % 8) = 8 - 0 = 8 ->  (8 + 8) % 8 = 0
    //      src_vaddr = 10: 8 - (10 % 8) = 8 - 2 = 6 -> (10 + 6) % 8 = 16 % 8 = 0
    uint64_t read_size = 8 - (src_vaddr % 8);
    read_size = MIN(read_size, n - 1 - read);
    uint64_t src_kaddr = vaddr_to_paddr(table, src_vaddr);

    // Perform the actual copy (1..8 bytes)
    uint64_t copied = strlcpy(dest_kaddr, src_kaddr, read_size + 1); // +1 due to \0
    read += copied;

    // Advancing the dest and src pointers by copied
    // Mix-up of integer and pointer arithmentics is irrelevant here because
    // sizeof(char) == 1
    dest_kaddr += copied;
    src_vaddr += copied;

    // If we copied less than anticipated, we probably hit a string terminator
    if (copied != read_size)
      break;
  }
  *dest_kaddr = '\0';

  return read;
}

// kfree_page_table_and_pages is intentionally not a recursive function
void kfree_page_table_and_pages(struct pt_entry* root) {
  assert(root != kernel_pt);
  assert(root != NULL);

  // Free attached pages and tree nodes
  for (uint64_t vpn_2 = 0; vpn_2 < NUM_PT_ENTRIES_PER_PAGE_TABLE; vpn_2++) {
    if (!root[vpn_2].v)
      continue;

    struct pt_entry* mid_pt = retrieve_pt_entry_from_table(root, vpn_2);

    for (uint64_t vpn_1 = 0; vpn_1 < NUM_PT_ENTRIES_PER_PAGE_TABLE; vpn_1++) {
      if (!mid_pt[vpn_1].v)
        continue;

      struct pt_entry* leaf_pt = retrieve_pt_entry_from_table(mid_pt, vpn_1);

      for (uint64_t vpn_0 = 0; vpn_0 < NUM_PT_ENTRIES_PER_PAGE_TABLE; vpn_0++) {
        if (!leaf_pt[vpn_0].v)
          continue;

        kpfree(leaf_pt[vpn_0].ppn);
      }

      kpfree(paddr_to_ppn(leaf_pt));
    }

    kpfree(paddr_to_ppn(mid_pt));
  }

  // Free page table itself
  kpfree(paddr_to_ppn(root));
}

__attribute__((aligned(4096)))
struct pt_entry kernel_pt[NUM_PT_ENTRIES_PER_PAGE_TABLE];
