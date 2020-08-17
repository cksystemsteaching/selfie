#ifndef KERN_CONTEXT
#define KERN_CONTEXT

#include "config.h"
#include "sbi_files.h"
#include <stdint.h>

struct __attribute__((packed)) registers {
  // obviously no need to save the zero register
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

struct memory_boundaries {
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

struct context {
  // the id is only set in kallocate_context() so that the lookup in kfree_context() is faster
  uint64_t id;
  struct pt_entry* pt;
  uint64_t program_break;
  struct registers saved_regs;
  struct memory_boundaries legal_memory_boundaries;
  FILEDESC open_files[32];
  // TODO: all the other stuff
};

extern struct context kernel_context;

struct context* kallocate_context(); // returns NULL if there are no free slots left atm
void kinit_context(struct context* context);
void kfree_context(uint64_t context_id);

void kupload_argv(struct context* context, int argc, char** argv);

struct context* get_currently_active_context();
struct context* schedule_next_context();

enum KILL_CONTEXT_REASON {
    KILL_CONTEXT_REASON_EXIT,
    KILL_CONTEXT_REASON_ILLEGAL_MEMORY_ACCESS,
    KILL_CONTEXT_REASON_UNKNOWN_SYSCALL,
    KILL_CONTEXT_REASON_UNHANDLED_TRAP,
    KILL_CONTEXT_REASON_OOM,
    // always add appropriate message to KILL_CONTEXT_MSG in context.c!
};
extern const char* KILL_CONTEXT_MSG[];
void kill_context(uint64_t context_id, enum KILL_CONTEXT_REASON kill_context_reason);

#endif /* KERN_CONTEXT */
