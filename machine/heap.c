#include "heap.h"

extern size_t _payload_end;

// Put the heap directly after the kernel in virtual address space
void* kernel_heap_start = &_payload_end;
void* kernel_heap_bump = &_payload_end;

void* kmalloc(size_t bytes) {
    // kmalloc does not map pages here - they are mapped on access using the trap handler
    void* return_ptr = kernel_heap_bump;
    kernel_heap_bump += bytes;
    return return_ptr;
}
