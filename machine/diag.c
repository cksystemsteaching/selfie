#include "diag.h"
#include "sbi_ecall.h"
#include "tinycstd.h"

void panic(const char* diagnostic_message, ...) {
  va_list args;
  va_start(args, diagnostic_message);

  printf("!!!!!!!!!!!!!!!!!!!!\n");
  printf("!!! KERNEL PANIC !!!\n");
  printf("!!!!!!!!!!!!!!!!!!!!\n\n");
  printf("diagnostic message: ");
  
  va_printf(diagnostic_message, args);
  printf("\n\n");
  printf("shutting down...\n");

  va_end(args);
  shutdown();
}

void shutdown() {
  sbi_ecall_sbi_shutdown();

  printf("shutdown failed - hanging machine...\n");
  hang_machine();
}
