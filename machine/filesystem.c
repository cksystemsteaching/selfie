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
