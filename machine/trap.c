#include "compiler-utils.h"
#include "diag.h"
#include "trap.h"
#include "config.h"
#include "syscalls.h"
#include "tinycstd.h"
#include "mmu.h"
#include "sbi_ecall.h"
#include <stdint.h>

#define SCAUSE_INTERRUPT_BIT_MASK (1ULL << 63)
#define SCAUSE_EXCEPTION_CODE_MASK (UINT64_MAX ^ SCAUSE_INTERRUPT_BIT_MASK)

// if interrupt bit is 0
#define SCAUSE_EXCEPTION_CODE_USER_ECALL 8
#define SCAUSE_EXCEPTION_CODE_INSTRUCTION_PAGE_FAULT 12
#define SCAUSE_EXCEPTION_CODE_LOAD_PAGE_FAULT 13
#define SCAUSE_EXCEPTION_CODE_STORE_AMO_PAGE_FAULT 15

// if interrupt bit is 1
#define SCAUSE_EXCEPTION_CODE_SUPERVISOR_TIMER_INTERRUPT 5

#define SSTATUS_SPP_BITMASK (1ULL << 8)

#define SYSCALL_EXIT   93
#define SYSCALL_READ   63
#define SYSCALL_WRITE  64
#define SYSCALL_OPENAT 56
#define SYSCALL_BRK    214

void disable_smode_interrupts() {
  uint64_t bitmask = (1 << CSR_STATUS_SIE);

  asm volatile (
    "csrc sstatus, %[bitmask]"
    :
    : [bitmask] "r" (bitmask)
  );
}

void enable_smode_interrupts() {
  uint64_t bitmask = (1 << CSR_STATUS_SIE);

  asm volatile (
    "csrs sstatus, %[bitmask]"
    :
    : [bitmask] "r" (bitmask)
  );
}

void enable_smode_interrupt_types(uint64_t bitmask) {
  asm volatile (
    "csrs sie, %[bitmask]"
    :
    : [bitmask] "r" (bitmask)
  );
}

void disable_smode_interrupt_types(uint64_t bitmask) {
  asm volatile (
    "csrc sie, %[bitmask]"
    :
    : [bitmask] "r" (bitmask)
  );
}

void store_saved_registers_from_buffer_into_context(struct context* context, struct registers* registers_buffer) {
  context->saved_regs.ra  = registers_buffer->ra;
  context->saved_regs.sp  = registers_buffer->sp;
  context->saved_regs.gp  = registers_buffer->gp;
  context->saved_regs.tp  = registers_buffer->tp;
  context->saved_regs.t0  = registers_buffer->t0;
  context->saved_regs.t1  = registers_buffer->t1;
  context->saved_regs.t2  = registers_buffer->t2;
  context->saved_regs.s0  = registers_buffer->s0;
  context->saved_regs.s1  = registers_buffer->s1;
  context->saved_regs.a0  = registers_buffer->a0;
  context->saved_regs.a1  = registers_buffer->a1;
  context->saved_regs.a2  = registers_buffer->a2;
  context->saved_regs.a3  = registers_buffer->a3;
  context->saved_regs.a4  = registers_buffer->a4;
  context->saved_regs.a5  = registers_buffer->a5;
  context->saved_regs.a6  = registers_buffer->a6;
  context->saved_regs.a7  = registers_buffer->a7;
  context->saved_regs.s2  = registers_buffer->s2;
  context->saved_regs.s3  = registers_buffer->s3;
  context->saved_regs.s4  = registers_buffer->s4;
  context->saved_regs.s5  = registers_buffer->s5;
  context->saved_regs.s6  = registers_buffer->s6;
  context->saved_regs.s7  = registers_buffer->s7;
  context->saved_regs.s8  = registers_buffer->s8;
  context->saved_regs.s9  = registers_buffer->s9;
  context->saved_regs.s10 = registers_buffer->s10;
  context->saved_regs.s11 = registers_buffer->s11;
  context->saved_regs.t3  = registers_buffer->t3;
  context->saved_regs.t4  = registers_buffer->t4;
  context->saved_regs.t5  = registers_buffer->t5;
  context->saved_regs.t6  = registers_buffer->t6;

  context->saved_regs.pc = registers_buffer->pc;
}

void load_saved_registers_from_context_into_buffer(struct context* context, struct registers* registers_buffer) {
  registers_buffer->ra  = context->saved_regs.ra;
  registers_buffer->sp  = context->saved_regs.sp;
  registers_buffer->gp  = context->saved_regs.gp;
  registers_buffer->tp  = context->saved_regs.tp;
  registers_buffer->t0  = context->saved_regs.t0;
  registers_buffer->t1  = context->saved_regs.t1;
  registers_buffer->t2  = context->saved_regs.t2;
  registers_buffer->s0  = context->saved_regs.s0;
  registers_buffer->s1  = context->saved_regs.s1;
  registers_buffer->a0  = context->saved_regs.a0;
  registers_buffer->a1  = context->saved_regs.a1;
  registers_buffer->a2  = context->saved_regs.a2;
  registers_buffer->a3  = context->saved_regs.a3;
  registers_buffer->a4  = context->saved_regs.a4;
  registers_buffer->a5  = context->saved_regs.a5;
  registers_buffer->a6  = context->saved_regs.a6;
  registers_buffer->a7  = context->saved_regs.a7;
  registers_buffer->s2  = context->saved_regs.s2;
  registers_buffer->s3  = context->saved_regs.s3;
  registers_buffer->s4  = context->saved_regs.s4;
  registers_buffer->s5  = context->saved_regs.s5;
  registers_buffer->s6  = context->saved_regs.s6;
  registers_buffer->s7  = context->saved_regs.s7;
  registers_buffer->s8  = context->saved_regs.s8;
  registers_buffer->s9  = context->saved_regs.s9;
  registers_buffer->s10 = context->saved_regs.s10;
  registers_buffer->s11 = context->saved_regs.s11;
  registers_buffer->t3  = context->saved_regs.t3;
  registers_buffer->t4  = context->saved_regs.t4;
  registers_buffer->t5  = context->saved_regs.t5;
  registers_buffer->t6  = context->saved_regs.t6;

  registers_buffer->pc = context->saved_regs.pc;
}

uint64_t get_current_cpu_time() {
  uint64_t current_cpu_time;

  asm volatile (
    "rdtime %[current_cpu_time]"
    : [current_cpu_time] "=r" (current_cpu_time)
  );

  return current_cpu_time;
}

bool set_timer_interrupt_delta(uint64_t delta) {
  return set_timer_interrupt(get_current_cpu_time() + delta);
}

bool set_timer_interrupt(uint64_t interrupt_at) {
  // call into the SBI to set the timer since
  // mtimecmp can only be modified from M-mode
  return sbi_ecall_sbi_set_timer(interrupt_at);
}

uint64_t trap_handler(struct registers registers_buffer) {
  uint64_t scause;
  uint64_t stval; // address where page fault occured
  uint64_t sepc;  // pc where the exception occured
  uint64_t sstatus;
  bool spp_bit; // indicates if the trap comes from S-mode
  bool interrupt_bit;
  uint64_t exception_code;
  struct context* context = get_currently_active_context();
  struct context* next_context;
  bool timer_interrupt_success;

  asm volatile (
    "csrr %[scause], scause;"
    "csrr %[sepc], sepc;"
    "csrr %[stval], stval;"
    "csrr %[sstatus], sstatus;"
    : [scause] "=r" (scause), [sepc] "=r" (sepc), [stval] "=r" (stval), [sstatus] "=r" (sstatus)
  );

  spp_bit = sstatus & SSTATUS_SPP_BITMASK;

  if (spp_bit)
    panic("kernel caused a trap\n"
          "  sstatus: 0x%x\n"
          "  scause:  0x%x\n"
          "  sepc:    0x%x\n"
          "  stval:   0x%x", sstatus, scause, sepc, stval);

  interrupt_bit = scause & SCAUSE_INTERRUPT_BIT_MASK;
  exception_code = scause & SCAUSE_EXCEPTION_CODE_MASK;

  store_saved_registers_from_buffer_into_context(context, &registers_buffer);

  if (interrupt_bit)
    switch (exception_code) {
      case SCAUSE_EXCEPTION_CODE_SUPERVISOR_TIMER_INTERRUPT:
#ifdef DEBUG
        printf("received timer interrupt while context %u was running. current time: %u\n", context->id, get_current_cpu_time());
#endif
        break;
      default:
        print_unhandled_trap(context, interrupt_bit, exception_code, stval, sepc);
        kill_context(context->id, KILL_CONTEXT_REASON_UNHANDLED_TRAP);
    }
  else
    switch (exception_code) {
      case SCAUSE_EXCEPTION_CODE_USER_ECALL:
        handle_ecall(context);
        break;
      case SCAUSE_EXCEPTION_CODE_INSTRUCTION_PAGE_FAULT:
        handle_instruction_page_fault(context, sepc, stval);
        break;
      case SCAUSE_EXCEPTION_CODE_LOAD_PAGE_FAULT:
        handle_load_page_fault(context, stval);
        break;
      case SCAUSE_EXCEPTION_CODE_STORE_AMO_PAGE_FAULT:
        handle_store_amo_page_fault(context, stval);
        break;
      default:
        print_unhandled_trap(context, interrupt_bit, exception_code, stval, sepc);
        kill_context(context->id, KILL_CONTEXT_REASON_UNHANDLED_TRAP);
    }

#ifdef DEBUG
  printf("trap handler has been executed (caused by context %u)\n", context->id);
  printf("  scause: 0x%x\n", scause);
  printf("  stval:  0x%x\n", stval);
  printf("  sepc:   0x%x\n", sepc);
  printf("  time:   %u\n", get_current_cpu_time());
#endif /* DEBUG */

  next_context = schedule_next_context();
  load_saved_registers_from_context_into_buffer(next_context, &registers_buffer);

  timer_interrupt_success = set_timer_interrupt_delta(TIMESLICE);
  if (!timer_interrupt_success)
    panic("setting a new timer interrupt was unsuccessful");

  // jumps back into trap.S now
  return assemble_satp_value(next_context->pt, 0);
}

void print_unhandled_trap(struct context* context, bool interrupt_bit, uint64_t exception_code, uint64_t stval, uint64_t sepc) {
  printf("unhandled trap (caused by context %u)\n", context->id);
  printf("  interrupt bit:  %d\n", interrupt_bit);
  printf("  exception code: %d\n", exception_code);
  printf("  stval:          0x%x\n", stval);
  printf("  sepc:           0x%p\n", sepc);
}

void handle_ecall(struct context* context) {
  const char SIZE_OF_ECALL_INSTRUCTION = 4;

  uint64_t syscall_id;

  syscall_id = context->saved_regs.a7;

  switch (syscall_id) {
    case SYSCALL_EXIT:
      implement_syscall_exit(context);
      break;
    case SYSCALL_READ:
      implement_syscall_read(context);
      break;
    case SYSCALL_WRITE:
      implement_syscall_write(context);
      break;
    case SYSCALL_OPENAT:
      implement_syscall_openat(context);
      break;
    case SYSCALL_BRK:
      implement_syscall_brk(context);
      break;
    default:
      printf("received unknown syscall '0x%x' from context %u\n", syscall_id, context->id);
      kill_context(context->id, KILL_CONTEXT_REASON_UNKNOWN_SYSCALL);
  }

  context->saved_regs.pc = context->saved_regs.pc + SIZE_OF_ECALL_INSTRUCTION;
}

void implement_syscall_exit(struct context* context) {
  int exit_code;

  exit_code = context->saved_regs.a0;

  printf("context %u exited with exit code %d\n", context->id, exit_code);

  kill_context(context->id, KILL_CONTEXT_REASON_EXIT);
}

void implement_syscalls_read_and_write(struct context* context, ssize_t (*kernel_func)(int, char*, size_t, FILEDESC*, size_t)) {
  // Here we can use a modified version of selfie's algorithm.

  // parameters
  int fd = context->saved_regs.a0;
  uint64_t vbuffer = context->saved_regs.a1;
  size_t size = context->saved_regs.a2;

  // local variables
  ssize_t read_or_written_total = 0;
  size_t bytes_to_read_or_write = sizeof(uint64_t);
  bool failed = false;
  char* buffer;
  ssize_t actually_read_or_written;

  while (size > 0) {
    if (size < bytes_to_read_or_write)
      bytes_to_read_or_write = size;

    if (is_user_vaddr(vbuffer) && is_vaddr_mapped(context->pt, vbuffer)) {
      buffer = (char*) vaddr_to_paddr(context->pt, vbuffer);

      actually_read_or_written = kernel_func(fd, buffer, bytes_to_read_or_write, context->open_files, NUM_FDS);

      // Despite both of them having a different signedness, it is ok to compare
      // the two variables since bytes_to_read_or_write always is sizeof(uint64_t) or less.
      if ((size_t) actually_read_or_written == bytes_to_read_or_write) {
        read_or_written_total += actually_read_or_written;

        size -= actually_read_or_written;

        if (size > 0)
          vbuffer += sizeof(uint64_t);
      } else {
        if (0 < actually_read_or_written)
          read_or_written_total += actually_read_or_written;

        size = 0;
      }
    } else {
      failed = true;

      break;
    }
  }

  if (failed)
    context->saved_regs.a0 = -1;
  else
    context->saved_regs.a0 = read_or_written_total;
}

void implement_syscall_read(struct context* context) {
  implement_syscalls_read_and_write(context, &kread);
}

void implement_syscall_write(struct context* context) {
  // Sadly we have to decide between a compiler warning and duplicating 50 LOC. :(
  implement_syscalls_read_and_write(context, &kwrite);
}

void implement_syscall_openat(struct context* context) {
  char path[PATH_MAX_LEN];

  int dirfd = context->saved_regs.a0;
  uint64_t path_vaddr = context->saved_regs.a1;
  int flags = context->saved_regs.a2;
  uint64_t mode = context->saved_regs.a3;
  UNUSED_VAR(dirfd);
  UNUSED_VAR(mode);

  if (kstrlcpy_from_vspace(path, path_vaddr, PATH_MAX_LEN, context->pt)) {
    int fd = kopen(path, flags, context->open_files, NUM_FDS);
    context->saved_regs.a0 = fd;
  } else
    context->saved_regs.a0 = -1;
}

void implement_syscall_brk(struct context* context) {
  // basically selfie's algorithm

  // syscall parameter
  uint64_t program_break;

  // local variable
  uint64_t previous_program_break;

  program_break = context->saved_regs.a0;

  previous_program_break = context->program_break;

  if (program_break >= previous_program_break && program_break < context->saved_regs.sp && program_break % sizeof(uint64_t) == 0)
    // new program break is valid
    context->program_break = program_break;
  else
    program_break = previous_program_break;

  context->saved_regs.a0 = program_break;

#ifdef DEBUG
  printf("context %u changed program break from 0x%x to 0x%x\n", context->id, previous_program_break, program_break);
#endif /* DEBUG */
}

enum memory_access_type determine_memory_access_type(struct memory_boundaries* legal_memory_boundaries, uint64_t vaddr) {
  uint64_t page_number = vaddr_to_vpn(vaddr);

  if (legal_memory_boundaries->lowest_lo_page <= page_number && page_number <= legal_memory_boundaries->highest_lo_page)
    return memory_access_type_lo;
  else if (legal_memory_boundaries->lowest_mid_page <= page_number && page_number <= legal_memory_boundaries->highest_mid_page)
    return memory_access_type_mid;
  else if (legal_memory_boundaries->lowest_hi_page <= page_number && page_number <= legal_memory_boundaries->highest_hi_page)
    return memory_access_type_hi;
  else
    return memory_access_type_unknown;
}

void handle_instruction_page_fault(struct context* context, uint64_t sepc, uint64_t stval) {
  enum memory_access_type memory_access_type = determine_memory_access_type(&context->legal_memory_boundaries, stval);

  printf("context %u raised an instruction page fault\n", context->id);
  printf("  sepc:  0x%x\n", sepc);
  printf("  stval: 0x%x\n", stval);

  switch (memory_access_type) {
    case memory_access_type_unknown:
      print_memory_boundaries(context, "  ", PRINT_MEMORY_REGION_LO_MASK & PRINT_MEMORY_REGION_MID_MASK & PRINT_MEMORY_REGION_HI_MASK);
      kill_context(context->id, KILL_CONTEXT_REASON_ILLEGAL_MEMORY_ACCESS);
      break;
    case memory_access_type_lo:
      // a lo access could indicate
      // a) a bug within the ELF loader (a segment hasn't been fully mapped)
      // b) a bug within the user program
      print_memory_boundaries(context, "  ", PRINT_MEMORY_REGION_LO_MASK);
      kill_context(context->id, KILL_CONTEXT_REASON_ILLEGAL_MEMORY_ACCESS);
      break;
    case memory_access_type_mid:
      print_memory_boundaries(context, "  ", PRINT_MEMORY_REGION_MID_MASK);
      kill_context(context->id, KILL_CONTEXT_REASON_ILLEGAL_MEMORY_ACCESS);
      break;
    case memory_access_type_hi:
      print_memory_boundaries(context, "  ", PRINT_MEMORY_REGION_HI_MASK);
      kill_context(context->id, KILL_CONTEXT_REASON_ILLEGAL_KERNEL_MEMORY_ACCESS);
      break;
  }
}

bool is_legal_heap_growth(uint64_t program_break, uint64_t highest_lo_page, uint64_t stval) {
  return (stval < program_break && highest_lo_page <= vaddr_to_vpn(stval));
}

bool has_stack_grown(uint64_t sp, uint64_t lowest_mid_page, uint64_t stval) {
  return (sp <= stval && vaddr_to_vpn(stval) <= lowest_mid_page);
}

void signal_oom(struct context* context) {
    printf("could not map free page into user vspace: out-of-memory!\n");
    print_memory_boundaries(context, "  ", PRINT_MEMORY_REGION_LO_MASK & PRINT_MEMORY_REGION_MID_MASK);
    kill_context(context->id, KILL_CONTEXT_REASON_OOM);
}

void handle_load_or_store_amo_page_fault(struct context* context, uint64_t stval) {
  enum memory_access_type memory_access_type = determine_memory_access_type(&context->legal_memory_boundaries, stval);

  bool map_successful = false;

  switch (memory_access_type) {
    case memory_access_type_lo:
      map_successful = kmap_page(context->pt, stval, true);
      if (!map_successful)
        signal_oom(context);
      break;
    case memory_access_type_mid:
      map_successful = kmap_page(context->pt, stval, true);
      if (!map_successful)
        signal_oom(context);
      break;
    case memory_access_type_hi:
      // user tried to access the trampoline/kernel stack
      printf("context %u raised a page fault in its hi region\n", context->id);
      printf("  stval: 0x%x\n", stval);
      print_memory_boundaries(context, "  ", PRINT_MEMORY_REGION_HI_MASK);
      kill_context(context->id, KILL_CONTEXT_REASON_ILLEGAL_KERNEL_MEMORY_ACCESS);
      break;
    case memory_access_type_unknown:
      if (is_legal_heap_growth(context->program_break, context->legal_memory_boundaries.highest_lo_page, stval)) {
        map_successful = kmap_page(context->pt, stval, true);
        if (!map_successful)
          signal_oom(context);
        context->legal_memory_boundaries.highest_lo_page = vaddr_to_vpn(stval);
      } else if (has_stack_grown(context->saved_regs.sp, context->legal_memory_boundaries.lowest_mid_page, stval)) {
        // stack has grown but the page isnt mapped yet
        map_successful = kmap_page(context->pt, stval, true);
        if (!map_successful)
          signal_oom(context);
        context->legal_memory_boundaries.lowest_mid_page = vaddr_to_vpn(stval);
      } else {
        printf("segmentation fault: context %u tried to access address 0x%x\n", context->id, stval);
        kill_context(context->id, KILL_CONTEXT_REASON_ILLEGAL_MEMORY_ACCESS);
      }
      break;
  }
}

void handle_load_page_fault(struct context* context, uint64_t stval) {
  handle_load_or_store_amo_page_fault(context, stval);

#ifdef DEBUG
  printf("received load page fault caused by context %u\n", context->id);
  printf("  address that caused page fault: 0x%x\n", stval);
#endif /* DEBUG */
}

void handle_store_amo_page_fault(struct context* context, uint64_t stval) {
  handle_load_or_store_amo_page_fault(context, stval);

#ifdef DEBUG
  printf("received store/AMO page fault caused by context %u\n", context->id);
  printf("  address that caused page fault: 0x%x\n", stval);
#endif /* DEBUG */
}

void setup_smode_trap_handler(trap_handler_t handler) {
  disable_smode_interrupts();

  // 4.1.4 stvec - handler functions must be aligned on a 4 byte boundary
  if (((uint64_t) handler) & 0x03) {
    puts("setup_trap_handler: Cannot apply unaligned trap handler!\n");
    return;
  }

  // stvec has both the base address and the vectoring mode (2 bits)
  // Use direct mode (0x00)
  uint64_t stvec = (((uint64_t) handler) & ~(0x03ULL));
  asm volatile (
    "csrw stvec, %[reg_value];"
    :
    : [reg_value] "r" (stvec)
  );

  enable_smode_interrupts();
}
