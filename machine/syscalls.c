#include "sbi_files.h"
#include "syscall.h"
#include "console.h"
#include "tinycstd.h"

ssize_t kread(int fd, char* buf, size_t count, FILEDESC* open_files, size_t num_fds) {
    if (fd >= num_fds+1) {
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

intmax_t kwrite(int fd, const char* buf, size_t count, FILEDESC* open_files, size_t num_fds) {
    // No file descriptor support yet for write - write to console instead

    // only allow writes to stdin (0), stdout (1) or stderr (2)
    if (fd < 0 || fd > 2)
        return -1;

    size_t i = 0;
    const char* charBuf = (const char*) buf;

    return console_puts(buf, count);
}

int kopen(const char* filename, int flags, FILEDESC* open_files, size_t num_fds) {
    const KFILE* file = files;

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
    while (fd_slot < num_fds) {
        if (open_files[fd_slot].file == NULL)
            break;
        fd_slot++;
    }

    if (fd_slot == num_fds)
        return -1;

    open_files[fd_slot].pos = 0;
    open_files[fd_slot].file = file;

    return fd_slot;
}


void* kmalloc(unsigned long long size, void** heap_head) {
    void* return_ptr;

    return_ptr = *heap_head;
    *heap_head += size;

    printf("-- malloc: allocated 0x%x bytes at addr %p-%p\n", size, return_ptr, *heap_head);

    return return_ptr;
}
