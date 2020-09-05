// note: garbage collector compilation (Selfie flag "-gc" and compilation with selfie.h;
// e.g. ./selfie -gc selfie.h examples/garbage_collector_library.c -m 1) mandatory!

// note: since Selfie uses a conservative garbage collection algorithm, we cannot simply store a pointer
// as integer (we need this for validation), therfore we add an offset when storing and subtract this
// offset when comparing
uint64_t check_offset = 4096;
uint64_t heap_start = 0;

uint64_t validation_address_1 = 0;
uint64_t validation_address_2 = 0;
uint64_t validation_address_3 = 0;
uint64_t validation_address_4 = 0;

uint64_t* x = (uint64_t*) 0;
uint64_t* y = (uint64_t*) 0;

// simple function allocating memory to demonstrate stack collection
void do_stuff() {
  uint64_t* z;
  z = gc_malloc(8);
}

int main(int argc, char** argv) {

  uint64_t* z;
  uint64_t* w;
  uint64_t t;

  // this example should demonstrate the capabilities of the garbage collector. considering skips would
  // only make it more complicated and therefore we disable skipping (i.e collect before every gc_malloc)
  turn_on_gc_library(0);

  // exit with error code 1 if gc is not available
  if (USE_GC_LIBRARY != GC_LIBRARY)
    exit(1);

  // if we wanted to modify the size of the non gcd heap, we'd have to do it BEFORE initialising the gc
  NON_GC_HEAP_SIZE = 4096;

  // initialise library (gc, power_of_2_table, etc.)
  init_library();

  // assert: no memory has been allocated within the gc heap, therefore the first gc_malloc call
  // yields the heap start of gc heap.

  // note: the first address cannot be collected, since it's referenced by gc_heap_start (see selfie.c)
  heap_start = (uint64_t) gc_malloc(8);

  // test cases

  // 1 -> allocate memory and assign ptr to global variable (data segment, global scope)
  x = gc_malloc(8);
  validation_address_1 = (uint64_t) x + check_offset;

  // 2 -> allocate memory and assign ptr to memory of pointer (heap, global scope)
  *x = (uint64_t) gc_malloc(8);
  validation_address_2 = *x + check_offset;

  // 3 -> demonstration of reuse (i.e. alloc -> unassign -> alloc)
  y = gc_malloc(8);
  validation_address_3 = (uint64_t) y + check_offset;
  y = (uint64_t*) 0;
  y = gc_malloc(8);
  if (((uint64_t) y) != (validation_address_3 - check_offset)) {
    printf2("%d - %d\n", (char*)((uint64_t)y), (char*)(validation_address_3 - check_offset));
    print("test case 3: memory is not reused! make sure skip count is set to 0!\n");
  }
  
  // 4 -> allocate memory and assign ptr to local variable (stack, local scope)
  do_stuff();
  z = gc_malloc(8);
  validation_address_4 = (uint64_t) z + check_offset;
  if (((uint64_t) z) != (validation_address_4 - check_offset))
    print("test case 4: memory is not reused! make sure skip count is set to 0!\n");
  
  // 5 -> allocate memory of size not in free list (should result in a new alloc)
  z = (uint64_t*) 0;
  z = gc_malloc(16);
  if (((uint64_t) z) != (validation_address_4 + 8 - check_offset))
    print("test case 5: expected and actual address do not match! make sure skip count is set to 0!\n");

  // 6 -> unassign global variable (whose memory contains pointer to other heap address)
  // the first gc_malloc zeroes and frees the memory of x, therefore unreferencing y
  // the second gc_malloc reuses the memory of y afterwards
  x = (uint64_t*) 0;
  w = gc_malloc(8);
  if (((uint64_t) w) != (validation_address_1 - check_offset))
    print("test case 6: memory of x is not reused! make sure skip count is set to 0!\n");
  x = gc_malloc(8);
  if (((uint64_t) x) != (validation_address_2 - check_offset))
    print("test case 6: memory of y is not reused! make sure skip count is set to 0!\n");

}