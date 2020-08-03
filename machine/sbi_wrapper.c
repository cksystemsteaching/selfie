#include "console.h"
#include "heap.h"
#include "tinycstd.h"
#include "trap.h"
#include "mmu.h"

#include "linker-syms.h"


int main(int argc, char** argv);
void usermode_test();


void bootstrap() {
    uint64_t val = 0xF00DBEEF;

    console_init();

    puts("Setting up kernel page table...");
    // No need to clear the page table - the BSS section is cleared automagically
    kidentity_map_range(kernel_pt, &_payload_start, &_payload_end);

    puts("Setting up trap handlers...");
    setup_smode_trap_handler(trap_handler_trampoline);
    enable_smode_interrupt_types((1 << CSR_SIE_TIMER_INTS) |
                                 (1 << CSR_SIE_SOFTWARE_INTS) |
                                 (1 << CSR_UIE_SOFTWARE_INTS));
    puts("done!\n");

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

    asm volatile (
        "csrw sepc, %[umode];\n"
        "sret"
        :
        : [umode] "r" (usermode_test)
    );

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
