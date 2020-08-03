#ifndef KERN_CONTEXT
#define KERN_CONTEXT

#include <stdint.h>

struct __attribute__((packed)) context {
  uint64_t id;
  struct pt_entry* pt;
  uint64_t program_break;
  struct registers* saved_regs;
  struct memory_boundaries* legal_memory_boundaries;
  // TODO: all the other stuff
};

struct __attribute__((packed)) registers {
  uint64_t ra;
  uint64_t sp;
  uint64_t gp;
  uint64_t tp;
  uint64_t t0;
  uint64_t t1;
  uint64_t t2;
  uint64_t s0;
  uint64_t s1;
  uint64_t a0;
  uint64_t a1;
  uint64_t a2;
  uint64_t a3;
  uint64_t a4;
  uint64_t a5;
  uint64_t a6;
  uint64_t a7;
  uint64_t s2;
  uint64_t s3;
  uint64_t s4;
  uint64_t s5;
  uint64_t s6;
  uint64_t s7;
  uint64_t s8;
  uint64_t s9;
  uint64_t s10;
  uint64_t s11;
  uint64_t t3;
  uint64_t t4;
  uint64_t t5;
  uint64_t t6;

  uint64_t pc;
};

struct __attribute__((packed)) memory_boundaries {
    // code, data and heap
    uint64_t lowest_lo_page;
    uint64_t highest_lo_page;
    // stack
    uint64_t lowest_mid_page;
    uint64_t highest_mid_page;
    // trap handler code
    uint64_t lowest_hi_page;
    uint64_t highest_hi_page;
};

#endif /* KERN_CONTEXT */
