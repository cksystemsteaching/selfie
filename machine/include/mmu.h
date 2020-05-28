struct __attribute__((packed)) pt_entry {
  uint64_t reserved :10; // reserved for future use
  uint64_t ppn      :44; // physical page number
  uint64_t rsw      : 2; // bits can be used freely by a supervisor
  uint64_t d        : 1; // dirty flag
  uint64_t a        : 1; // accessed flag
  uint64_t g        : 1; // global mapping flag
  uint64_t u        : 1; // U-mode accessible flag
  uint64_t x        : 1; // execute flag
  uint64_t w        : 1; // write flag
  uint64_t r        : 1; // read flag
  uint64_t v        : 1; // valid flag
};

extern struct pt_entry root_table[512];

void* palloc();

// both table and (pt_at_ppn << 12) have to be valid page-aligned pointers
uint64_t create_pt_entry(struct pt_entry* table, uint64_t index, uint64_t ppn, char pt_at_ppn_addr, char u_mode_accessible);

void map_page(uint64_t vaddr, char u_mode_accessible);
