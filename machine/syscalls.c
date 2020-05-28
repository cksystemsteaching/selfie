#include "syscall.h"
#include "console.h"
#include "sbi_files.h"

#define NUM_FDS 32

static FILEDESC open_files[NUM_FDS];

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

intmax_t write(int fd, const char* buf, size_t count) {
    // No file descriptor support yet for write - write to console instead

    if (fd != 1)
        return -1;

    size_t i = 0;
    const char* charBuf = (const char*) buf;

    return console_puts(buf, count);
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
