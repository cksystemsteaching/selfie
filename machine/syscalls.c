#include "filesystem.h"
#include "syscalls.h"
#include "console.h"
#include "tinycstd.h"

#include "compiler-utils.h"

#define OPEN_FILE_FD_OFFSET 3

bool fd_is_stdio(int fd) {
  return (fd >= 0) && (fd <= 2);
}

bool fd_is_valid(int fd, size_t num_fds) {
  return (fd >= 0) && (((uint32_t) fd) < num_fds + OPEN_FILE_FD_OFFSET);
}

FILEDESC* get_fd_entry(int fd, FILEDESC* open_files, size_t num_fds) {
  if (!fd_is_valid(fd, num_fds))
    return NULL;

  // There's no FILEDESC for stdin/stdout/stderr
  if (fd_is_stdio(fd))
    return NULL;

  return open_files + (fd - OPEN_FILE_FD_OFFSET);
}

bool fd_entry_is_opened(FILEDESC* entry) {
  return (entry != NULL) && (entry->file != NULL);
}

bool fd_is_opened(int fd, FILEDESC* open_files, size_t num_fds) {
  FILEDESC* entry = get_fd_entry(fd, open_files, num_fds);
  // If an entry is NULL, fd is either invalid or an stdio special fd
  if (entry == NULL)
    return fd_is_stdio(fd);

  return fd_entry_is_opened(entry);
}


ssize_t kread(int fd, char* buf, size_t count, FILEDESC* open_files, size_t num_fds) {
  if (!fd_is_valid(fd, num_fds))
    return -1;

  if (fd_is_stdio(fd)) {
    // TODO: No stdin yet
    return -1;
  } else {
    FILEDESC* desc = get_fd_entry(fd, open_files, num_fds);
    if (!fd_entry_is_opened(desc))
      return -1;

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
