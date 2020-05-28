#include "console.h"
#include "tinycstd.h"
#include "trap.h"


int main(int argc, char** argv);
void usermode_test();


void bootstrap() {
    uint64_t val = 0xF00DBEEF;

    console_init();

    write(1, "Setting up trap handlers...", 27);
    setup_smode_trap_handler(trap_handler_wrapper);
    enable_smode_interrupt_types((1 << CSR_SIE_TIMER_INTS) |
                                 (1 << CSR_SIE_SOFTWARE_INTS) |
                                 (1 << CSR_UIE_SOFTWARE_INTS));
    write(1, "done!\n", 6);

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

    write(1, "Booting selfie with args: ", 26);
    console_putc('\n');

    while (args[i] != (char*)0) {
        write(1, "    ", 4);
        write(1, args[i], strlen(args[i]));
        console_putc('\n');
        i++;
    }
    write(1, "    <END>\n", 10);
    console_putc('\n');

    asm volatile (
        "csrw sepc, %[umode];\n"
        "sret"
        :
        : [umode] "r" (usermode_test)
    );

    // i contains the count of command line arguments
    int exit = main(i, args);


    printf("\n\nFunction main terminated with exit code 0x%x", exit);
}

void usermode_test() {
    while (1) {
        asm volatile(
            "li a7, 0x101;"
            "ecall"
        );
    }
}
