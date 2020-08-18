#ifndef KERN_DIAG
#define KERN_DIAG

#include <stdarg.h>

void panic(const char* diagnostic_message, ...);

#endif /* KERN_DIAG */
