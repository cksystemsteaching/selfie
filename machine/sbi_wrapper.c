#include "config.h"
#include "console.h"
#include "context.h"
#include "sbi_files.h"
#include "tinycstd.h"
#include "trap.h"
#include "mmu.h"
#include "elf.h"

#include "linker-syms.h"
#include <stdint.h>

int main(int argc, char** argv);
void usermode_test();

extern void perform_initial_ctxt_switch(uint64_t satp, struct registers* regs);
extern void _start_hang();


void setup_kernel_context(uint64_t lowest_lo_page, uint64_t highest_lo_page, uint64_t lowest_mid_page
        , uint64_t highest_mid_page, uint64_t lowest_hi_page, uint64_t highest_hi_page) {
    kernel_context.id = 0;

    kernel_context.pt = kernel_pt;

    kernel_context.program_break = highest_mid_page;

    // no need to ever save the kernel's registers

    kernel_context.legal_memory_boundaries.lowest_lo_page = lowest_lo_page;
    kernel_context.legal_memory_boundaries.highest_lo_page = highest_lo_page;
    kernel_context.legal_memory_boundaries.lowest_mid_page = lowest_mid_page;
    kernel_context.legal_memory_boundaries.highest_mid_page = highest_mid_page;
    kernel_context.legal_memory_boundaries.lowest_hi_page = lowest_hi_page;
    kernel_context.legal_memory_boundaries.highest_mid_page = highest_hi_page;
}

void bootstrap() {
    uint64_t val = 0xF00DBEEF;

    console_init();

    // TODO: Assert trampoline positioning on page boundary

    puts("Setting up kernel page table...\n");
    // No need to clear the page table - the BSS section is cleared automagically
    uint64_t stack_end = ((uint64_t)&_payload_end) + PAGESIZE * NUM_STACK_PAGES;
    setup_kernel_context(((uint64_t)&_payload_start) >> 12, ((uint64_t) &_payload_end) >> 12, stack_end >> 12
            , stack_end >> 12, TRAMPOLINE_VADDR >> 12, TRAMPOLINE_VADDR >> 12);
    kidentity_map_range(kernel_pt, &_payload_start, &_payload_end);
    kidentity_map_range(kernel_pt, &_payload_end, (void*)stack_end);

    // Map kernel upper half to its own vspace
    kmap_kernel_upper_half(kernel_pt);

    uint64_t oldPpn = ppn_bump;
    kidentity_map_range(kernel_pt, &_payload_end, (void*)ppn_to_paddr(ppn_bump));
    while (oldPpn != ppn_bump) {
      uint64_t initial = oldPpn;
      oldPpn = ppn_bump;
      kidentity_map_range(kernel_pt, (void*)ppn_to_paddr(initial), (void*)ppn_to_paddr(ppn_bump));
    }

    kinit_page_pool();

    kdump_pt(kernel_pt);

    puts("Setting up trap handlers...");
    setup_smode_trap_handler((trap_handler_t)TRAMPOLINE_VADDR);
    enable_smode_interrupt_types((1 << CSR_SIE_TIMER_INTS) |
                                 (1 << CSR_SIE_SOFTWARE_INTS) |
                                 (1 << CSR_UIE_SOFTWARE_INTS));
    puts("done!\n");

    puts("Enabling paging...");
    kswitch_active_pt(kernel_pt, 0);
    puts("done!\n");

    // Switch to the upper half stack but keep the offset alive
    asm volatile (
        "jal initial_stack_start\n"
        "sub a0, a0, sp\n"
        "mv sp, %[stack_addr]\n"
        "sub sp, sp, a0"
        :
        : [stack_addr] "r" (STACK_VADDR)
        : "a0", "ra"
    );

    char* args[] = {
        "./selfie",
        "-c",
        "selfie.c",
        "-m",
        "32",
        "-l",
        "selfie.m",
        "-y",
        "16",
        "-c",
        "hello-world.c",
        (char*)0,
    };
    int i = 0;

    puts("Booting selfie with args: \n");

    while (args[i] != (char*)0) {
        printf("    %s\n", args[i]);
        i++;
    }
    printf("    <END>\n\n");


    const KFILE* file = find_file(INIT_FILE_PATH);
    if (!file) {
      printf("ERROR: Could not find init file: " INIT_FILE_PATH);
      _start_hang();
    }

    struct context* init = kallocate_context();
    kinit_context(init);
    int err = load_elf(init, file->data, file->length);
    if (err) {
      printf("ERROR: Could not load init file: %s", elf_strerror(err));
      _start_hang();
    }

    perform_initial_ctxt_switch(assemble_satp_value(init->pt, 0), &init->saved_regs);

    // i contains the count of command line arguments
    //int exit = main(i, args);
    //printf("\n\nFunction main terminated with exit code 0x%x", exit);
}

void usermode_test() {
    while (1) {
        asm volatile(
            "li a7, 0x101;"
            "ecall"
        );
    }
}
