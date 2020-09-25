#include "context.h"
#include "config.h"
#include "mmu.h"
#include "tinycstd.h"
#include "trap.h"
#include "diag.h"
#include "compiler-utils.h"
#include "config.h"

struct context_manager {
  struct context context;
  bool is_used;
  struct context_manager* prev_scheduled;
  struct context_manager* next_scheduled;
};

struct context_manager all_contexts[MAX_AMOUNT_OF_CONTEXTS];

struct context kernel_context;

uint64_t num_of_used_contexts = 0;
struct context_manager* currently_active_context = &(all_contexts[0]);

struct context* kallocate_context() {
  struct context_manager* context_manager;
  struct context_manager* prev_scheduled = &all_contexts[0];
  struct context_manager* next_scheduled = &all_contexts[0];

  if (num_of_used_contexts == MAX_AMOUNT_OF_CONTEXTS)
    return NULL;

  for (size_t i = 0; i < MAX_AMOUNT_OF_CONTEXTS; ++i) {
    context_manager = &all_contexts[i];

    if (!context_manager->is_used) {
      context_manager->is_used = true;
      ++num_of_used_contexts;
      context_manager->context.id = i + 1; // id 0 is reserved for the kernel context
      
      context_manager->prev_scheduled = prev_scheduled;
      context_manager->next_scheduled = next_scheduled;
      prev_scheduled->next_scheduled = context_manager;
      next_scheduled->prev_scheduled = context_manager;

      return &context_manager->context;
    } else {
      prev_scheduled = context_manager;
      next_scheduled = context_manager->next_scheduled;
    }
  }

  return NULL; // acutally unreachable but the compiler is too dumb to see this
}

void kinit_context(struct context* context) {
  context->pt = (struct pt_entry*) ppn_to_paddr(kzalloc());
  context->saved_regs.ra  = 0;
  context->saved_regs.sp  = USERSPACE_STACK_START;
  context->saved_regs.gp  = 0;
  context->saved_regs.tp  = 0;
  context->saved_regs.t0  = 0;
  context->saved_regs.t1  = 0;
  context->saved_regs.t2  = 0;
  context->saved_regs.s0  = 0;
  context->saved_regs.s1  = 0;
  context->saved_regs.a0  = 0;
  context->saved_regs.a1  = 0;
  context->saved_regs.a2  = 0;
  context->saved_regs.a3  = 0;
  context->saved_regs.a4  = 0;
  context->saved_regs.a5  = 0;
  context->saved_regs.a6  = 0;
  context->saved_regs.a7  = 0;
  context->saved_regs.s2  = 0;
  context->saved_regs.s3  = 0;
  context->saved_regs.s4  = 0;
  context->saved_regs.s5  = 0;
  context->saved_regs.s6  = 0;
  context->saved_regs.s7  = 0;
  context->saved_regs.s8  = 0;
  context->saved_regs.s9  = 0;
  context->saved_regs.s10 = 0;
  context->saved_regs.s11 = 0;
  context->saved_regs.t3  = 0;
  context->saved_regs.t4  = 0;
  context->saved_regs.t5  = 0;
  context->saved_regs.t6  = 0;

  context->legal_memory_boundaries.lowest_lo_page = 0;
  context->legal_memory_boundaries.highest_lo_page = 0;

  context->program_break = 0;

  kmap_page(context->pt, USERSPACE_STACK_START - PAGESIZE, true);
  context->legal_memory_boundaries.lowest_mid_page = vaddr_to_vpn(USERSPACE_STACK_START) - 1;
  context->legal_memory_boundaries.highest_mid_page = vaddr_to_vpn(USERSPACE_STACK_START) - 1;

  kmap_kernel_upper_half(context); // hi region is set in here
}

void kfree_context(uint64_t context_id) {
  struct context_manager* context_manager = &all_contexts[context_id - 1];

  context_manager->is_used = false;
  --num_of_used_contexts;

  kfree_page_table_and_pages(context_manager->context.pt);
  context_manager->context.pt = NULL;

#ifdef DEBUG
  printf("freed context %u\n", context_id);
#endif /* DEBUG */

  if (num_of_used_contexts == 0)
    panic("all processes are dead");

  context_manager->prev_scheduled->next_scheduled = context_manager->next_scheduled;
  context_manager->next_scheduled->prev_scheduled = context_manager->prev_scheduled;
}

struct context* get_currently_active_context() {
  return &currently_active_context->context;
}

struct context* schedule_next_context() {
  currently_active_context = currently_active_context->next_scheduled;

  return &currently_active_context->context;
}

void print_memory_boundaries(struct context* context, char* indentation, uint8_t print_mask) {
  if (print_mask & PRINT_MEMORY_REGION_LO_MASK) {
    printf("%slowest lo page:   0x%x\n", indentation, context->legal_memory_boundaries.lowest_lo_page);
    printf("%shighest lo page:  0x%x\n", indentation, context->legal_memory_boundaries.highest_lo_page);
  }
  if (print_mask & PRINT_MEMORY_REGION_MID_MASK) {
    printf("%slowest mid page:  0x%x\n", indentation, context->legal_memory_boundaries.lowest_mid_page);
    printf("%shighest mid page: 0x%x\n", indentation, context->legal_memory_boundaries.highest_mid_page);
  }
  if (print_mask & PRINT_MEMORY_REGION_HI_MASK) {
    printf("%slowest hi page:   0x%x\n", indentation, context->legal_memory_boundaries.lowest_hi_page);
    printf("%shighest hi page:  0x%x\n", indentation, context->legal_memory_boundaries.highest_hi_page);
  }
}

const char* KILL_CONTEXT_MSG[] = {
  "context exited",
  "segfault",
  "segfault: kernel memory access",
  "unknown syscall",
  "unhandled trap",
  "out of memory",
};
void kill_context(uint64_t context_id, enum KILL_CONTEXT_REASON kill_context_reason) {
  UNUSED_VAR(kill_context_reason);

  if (get_currently_active_context()->id == context_id)
    schedule_next_context();

  kfree_context(context_id);

#ifdef DEBUG
  printf("context %u has been killed\n", context_id);
  printf("  reason: %s\n", KILL_CONTEXT_MSG[kill_context_reason]);
#endif /* DEBUG */
}
