#ifndef KERN_HEAP
#define KERN_HEAP

#include <stddef.h>

/**
 * @brief Allocates a memory region on the heap
 * @warning Do not use this function before the paging has been enabled!
 * @param size The amount of bytes to reserve
 * @return A pointer to a memory region with at least size bytes
 */
void* kmalloc(size_t size);

#endif /* KERN_HEAP */
