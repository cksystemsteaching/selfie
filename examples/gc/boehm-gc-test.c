// simple test of selfie's boehm gc tool

// needs to be compiled using selfie's gc library and boehm-gc tool:
// e.g. ./selfie -gc selfie-gc.h tools/boehm-gc.c examples/gc/boehm-gc-test.c -m 1

int main(int argc, char** argv) {
  uint64_t* x;
  uint64_t* y;

  init_library();

  turn_on_gc_library(0, " boehm-gc-test");

  if (USE_GC_LIBRARY != GC_ENABLED)
    exit(1);

  x = gc_malloc(8);

  if((uint64_t) x >= (uint64_t) gc_chunk_heap_bump)
    exit(1);

  if((uint64_t) x <= (uint64_t) gc_chunk_heap_start)
    exit(1);

  y = gc_malloc(4104);

  if((uint64_t) y >= (uint64_t) gc_heap_seg_end)
    exit(1);

  if((uint64_t) y <= (uint64_t) gc_heap_seg_start)
    exit(1);
}