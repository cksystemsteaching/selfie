#include "filesystem.h"
#include "syscalls.h"
#include "console.h"
#include "tinycstd.h"

#include "compiler-utils.h"

ssize_t kread(int fd, char* buf, size_t nbytes, FILEDESC* open_files, size_t num_fds) {
  if (!fd_is_valid(fd, num_fds))
    return -1;

  if (fd_is_stdio(fd)) {
    // TODO: No stdin yet
    return -1;
  } else {
    FILEDESC* desc = get_fd_entry(fd, open_files, num_fds);
    if (!fd_entry_is_opened(desc))
      return -1;

    uint64_t num_read = nbytes;
    uint64_t max_readable = desc->file->length - desc->pos;
    if (num_read > max_readable)
      num_read = max_readable;

    const char* fileDataOffset = desc->file->data + desc->pos;

    memcpy(buf, fileDataOffset, num_read);
    desc->pos += num_read;

    return num_read;
  }
}

intmax_t kwrite(int fd, const char* buf, size_t count, FILEDESC* open_files, size_t num_fds) {
  UNUSED_VAR(open_files);
  UNUSED_VAR(num_fds);
  // No file descriptor support yet for write - write to console instead

  // only allow writes to stdin (0), stdout (1) or stderr (2)
  if (!fd_is_stdio(fd))
    return -1;

  return console_puts(buf, count);
}

int last_allocated_fd = OPEN_FILE_FD_OFFSET - 1;
int kopen(const char* filename, int flags, FILEDESC* open_files, size_t num_fds) {
  const int O_RDONLY = 0x0;
  const int _O_BINARY = 0x8000;
  const KFILE* file = files;

  if (flags != O_RDONLY && flags != (_O_BINARY | O_RDONLY))
    return -1;

  while (file->data != NULL) {
    if (strncmp(filename, file->name, 511) == 0)
      break;

    file++;
  }
  if (file->data == NULL)
    return -1;

  // Check if we are able to use the fd slot one above the last allocated FD
  int fd = last_allocated_fd + 1;
  if (fd_is_opened(fd, open_files, num_fds)) {
    // No, so fall back to linear iteration over all slots
    fd = OPEN_FILE_FD_OFFSET;
    while (fd_is_valid(fd, num_fds)) {
      if (!fd_is_opened(fd, open_files, num_fds))
        break;
      fd++;
    }
  }

  if (!fd_is_valid(fd, num_fds))
    return -1;

  FILEDESC* fd_slot = get_fd_entry(fd, open_files, num_fds);

  fd_slot->pos = 0;
  fd_slot->file = file;

  return fd;
}
