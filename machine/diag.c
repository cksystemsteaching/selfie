#include "diag.h"
#include "tinycstd.h"

extern void _start_hang();

void panic(const char* diagnostic_message, ...) {
  va_list args;
  va_start(args, diagnostic_message);

  printf("!!!!!!!!!!!!!!!!!!!!\n");
  printf("!!! KERNEL PANIC !!!\n");
  printf("!!!!!!!!!!!!!!!!!!!!\n\n");
  printf("diagnostic message: ");
  
  va_printf(diagnostic_message, args);
  printf("\n\n");
  printf("starting to hang...");

  va_end(args);
  _start_hang();
}
