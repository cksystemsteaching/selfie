#include "tinycstd.h"
#include "sbi_files.h"
#include "trap.h"

#define NUM_FDS 32

int main(int argc, char** argv);
void usermode_test();

static FILEDESC open_files[NUM_FDS];

void sbi_ecall_console_putc(char c) {
    asm volatile(
        "li a7, 1;"
        "li a6, 0;"
        "mv a0, %[character];"
        "ecall;"
        :
        : [character] "r" (c)
        : "a0", "a6", "a7"
    );
}

ssize_t read(int fd, char* buf, size_t count) {
    if (fd >= NUM_FDS+1) {
        return -1;
    } else {
        FILEDESC* desc = (open_files+fd);

        uint64_t num_read = 0;
        while (count) {
            if (desc->pos >= desc->file->length)
                break;

            *(buf++) = desc->file->data[desc->pos];

            --count;
            num_read++;
            desc->pos++;
        }
        return num_read;
    }
}

ssize_t write(int fd, const char* buf, size_t count) {
    // No file descriptor support yet for write - write to console instead

    if (fd != 1)
        return -1;

    size_t i = 0;
    const char* charBuf = (const char*) buf;

    while (i < count) {
        sbi_ecall_console_putc(charBuf[i]);
        i++;
    }

    return i;
}

void exit(int status) {
    write(1, ">EXIT called<\n", 14);
    while (1)
        ;
}

int open(const char* filename, int flags) {
    const FILE* file = files;

    while (file->data != NULL) {
        if (strncmp(filename, file->name, 511) == 0)
            break;

        file++;
    }
    if (file->data == NULL)
        return -1;

    // Assume 0 and 1 are used for stdin and stdout
    // Use 2 even though it is usually used for stderr
    // TODO: Introduce a next_fd variable for a high probability O(1) fd slot allocation.
    int fd_slot = 2;
    while (fd_slot < NUM_FDS) {
        if (open_files[fd_slot].file == NULL)
            break;
        fd_slot++;
    }

    if (fd_slot == NUM_FDS)
        return -1;

    open_files[fd_slot].pos = 0;
    open_files[fd_slot].file = file;

    return fd_slot;
}


static void* heap_head = (void*)0x80300000;
void* malloc(unsigned long long size) {
    void* return_ptr;

    return_ptr = heap_head;
    heap_head += size;

    printf("-- malloc: allocated 0x%x bytes at addr %p-%p\n", size, return_ptr, heap_head);

    return return_ptr;
}

void bootstrap() {
    uint64_t val = 0xF00DBEEF;

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
    sbi_ecall_console_putc('\n');

    while (args[i] != (char*)0) {
        write(1, "    ", 4);
        write(1, args[i], strlen(args[i]));
        sbi_ecall_console_putc('\n');
        i++;
    }
    write(1, "    <END>\n", 10);
    sbi_ecall_console_putc('\n');

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
            "ecall"
        );
    }
}
