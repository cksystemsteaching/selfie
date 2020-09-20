#include "bootstrap.h"

#include "config.h"
#include "context.h"
#include "diag.h"
#include "elf.h"
#include "filesystem.h"
#include "linker-syms.h"
#include "mmu.h"
#include "numeric-utils.h"
#include "tinycstd.h"
#include "trap.h"


extern void* initial_stack_start();
void early_init() {
  ppn_bump = paddr_to_ppn(initial_stack_start());
}

// =============================================================================

void assert_state();
void setup_kernel_context(uint64_t lowest_lo_page,  uint64_t highest_lo_page,
                          uint64_t lowest_mid_page, uint64_t highest_mid_page,
                          uint64_t lowest_hi_page,  uint64_t highest_hi_page);
void setup_kernel_pt();
void setup_trap_handler();
void move_sp_to_upper_half();
void kernel_environ_init() {
  // Perform initial assertions to ensure a well-defined entry state
  assert_state();

  // Begin the actual set-up procedure
  puts("Setting up kernel page table...\n");
  uint64_t kern_start = paddr_to_ppn(&_payload_start);
  uint64_t kern_end = paddr_to_ppn(&_payload_end);
  uint64_t stack_end_ppn = paddr_to_ppn(initial_stack_start());
  uint64_t trampoline_ppn = paddr_to_ppn((void*) TRAMPOLINE_VADDR);
  setup_kernel_context(kern_start, kern_end, stack_end_ppn, stack_end_ppn, trampoline_ppn, trampoline_ppn);
  setup_kernel_pt();

  puts("Setting up trap handlers...");
  setup_trap_handler();
  puts("done!\n");

  puts("Enabling paging...");
  kswitch_active_pt(kernel_pt, 0);
  puts("done!\n");

  move_sp_to_upper_half();
}

// =============================================================================

int start_init_process(uint64_t argc, const char** argv) {
  bool timer_interrupt_success;
  const KFILE* file = find_file(INIT_FILE_PATH);

  if (!file)
    panic("ERROR: Could not find init file: " INIT_FILE_PATH);

  struct context* init = kallocate_context();
  kinit_context(init);
  int err = load_elf(init, file->data, file->length);
  if (err)
    panic("ERROR: Could not load init file: %s", elf_strerror(err));

  bool argv_upload_successful = kupload_argv(init, argc, argv);
  if (!argv_upload_successful)
    panic("could not upload arguments to init");

  timer_interrupt_success = set_timer_interrupt_delta(TIMESLICE);
  if (!timer_interrupt_success)
    panic("couldn't set a timer interrupt for the init context");

  perform_initial_ctxt_switch(assemble_satp_value(init->pt, 0), &init->saved_regs);

  return 0;
}

// =============================================================================

void assert_state() {
  // Assert alignment of trap function (physical) and trampoline address (virtual)
  // According to the priviledged architecture manual, 3.1.7 mtvec, the BASE field
  // must be aligned on a 4-byte boundary because the lower two bits represent the
  // trap vector mode.
  assert(IS_ALIGNED(TRAMPOLINE_VADDR, 2));
  assert(IS_ALIGNED((uint64_t) trap_handler_wrapper, 2));

  // Kernel page table must be page-aligned (4KiB -> 2^12)
  assert(IS_ALIGNED((uint64_t) kernel_pt, 12));
}

void setup_kernel_context(uint64_t lowest_lo_page,  uint64_t highest_lo_page,
                          uint64_t lowest_mid_page, uint64_t highest_mid_page,
                          uint64_t lowest_hi_page,  uint64_t highest_hi_page){
  kernel_context.id = 0;

  kernel_context.pt = kernel_pt;

  kernel_context.program_break = highest_mid_page + PAGESIZE;

  // no need to ever save the kernel's registers

  kernel_context.legal_memory_boundaries.lowest_lo_page = lowest_lo_page;
  kernel_context.legal_memory_boundaries.highest_lo_page = highest_lo_page;
  kernel_context.legal_memory_boundaries.lowest_mid_page = lowest_mid_page;
  kernel_context.legal_memory_boundaries.highest_mid_page = highest_mid_page;
  kernel_context.legal_memory_boundaries.lowest_hi_page = lowest_hi_page;
  kernel_context.legal_memory_boundaries.highest_mid_page = highest_hi_page;
}

void setup_kernel_pt() {
  void* stack_end = initial_stack_start();
  uint64_t old_ppn = ppn_bump;

  // No need to clear the page table - the BSS section is cleared automagically
  // Map kernel
  kidentity_map_range(kernel_pt, &_payload_start, &_payload_end);
  // Map kernel stack
  kidentity_map_range(kernel_pt, &_payload_end, stack_end);

  // Map kernel upper half to its own vspace
  kmap_kernel_upper_half(&kernel_context);

  // Map kernel's page allocator "heap"
  kidentity_map_range(kernel_pt, stack_end, (void*) ppn_to_paddr(ppn_bump));
  // Keep on mapping mid and leaf page-tables until all of them have been mapped
  while (old_ppn != ppn_bump) {
    uint64_t initial = old_ppn;
    old_ppn = ppn_bump;
    kidentity_map_range(kernel_pt, (void*) ppn_to_paddr(initial), (void*) ppn_to_paddr(ppn_bump));
  }

  kinit_page_pool();

#ifdef DEBUG
  kdump_pt(kernel_pt);
#endif /* DEBUG */
}

void setup_trap_handler() {
  setup_smode_trap_handler((trap_handler_t) TRAMPOLINE_VADDR);
  enable_smode_interrupt_types((1 << CSR_SIE_TIMER_INTS));
}

void move_sp_to_upper_half() {
  // Switch to the upper half stack but keep the offset alive
  asm volatile (
    "jal initial_stack_start;"
    "sub a0, a0, sp;"
    "mv sp, %[stack_addr];"
    "sub sp, sp, a0"
    :
    : [stack_addr] "r" (STACK_VADDR)
    : "a0", "ra"
  );
}
