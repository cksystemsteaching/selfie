#include "diag.h"
#include "tinycstd.h"

extern void _start_hang();

void panic(const char* diagnostic_message) {
    printf("!!!!!!!!!!!!!!!!!!!!\n");
    printf("!!! KERNEL PANIC !!!\n");
    printf("!!!!!!!!!!!!!!!!!!!!\n\n");
    printf("diagnostic message: %s\n\n", diagnostic_message);
    printf("starting to hang...");

    _start_hang();
}
