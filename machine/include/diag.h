#ifndef KERN_DIAG
#define KERN_DIAG

#include <stdarg.h>

void panic(const char* diagnostic_message, ...);
void shutdown();

#ifdef DEBUG
#define assert(x) if (!(x)) panic("Assertion failed: " __FILE__ ":%u: " #x, __LINE__)
#else
#define assert(x) (void) 0
#endif

#endif /* KERN_DIAG */
