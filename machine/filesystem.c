#include "filesystem.h"
#include "tinycstd.h"

const KFILE* find_file(const char* filename) {
  const KFILE* file = files;

  while (file->data != NULL) {
    if (strncmp(filename, file->name, 511) == 0)
      break;

    file++;
  }

  if (file->data != NULL)
    return file;
  else
    return NULL;
}

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
