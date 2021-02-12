uint64_t L1_DCACHE_SIZE = 32768;
uint64_t PAGESIZE = 4096;
uint64_t WORDSIZE = 8;

// POSIX drand48 values
uint64_t NUM_GEN_m = 281474976710656; // modulus
uint64_t NUM_GEN_a = 25214903917;     // multiplier
uint64_t NUM_GEN_c = 11;              // increment

uint64_t NUM_GEN_x_n = 42424242;

uint64_t generate_number() {
  NUM_GEN_x_n = (NUM_GEN_a * NUM_GEN_x_n + NUM_GEN_c) % NUM_GEN_m;

  return NUM_GEN_x_n;
}

uint64_t* malloc_and_touch_pages(uint64_t size) {
  uint64_t* x;
  uint64_t num_pages;
  uint64_t i;

  x = malloc(size);

  if (size % PAGESIZE == 0)
    num_pages = size / PAGESIZE;
  else
    num_pages = size / PAGESIZE + 1;

  i = 0;

  while (i < num_pages) {
    *(x + i * PAGESIZE / WORDSIZE) = 0;

    i = i + 1;
  }

  return x;
}

uint64_t main() {
  uint64_t* x;
  uint64_t words;
  uint64_t i;

  words = 1024 * L1_DCACHE_SIZE / WORDSIZE;

  // make sure that all pages are mapped before testing access pattern
  // in order to prevent page faults from causing cache flushes
  x = malloc_and_touch_pages(words * WORDSIZE);

  i = 0;

  // test access pattern with 1_000_000 memory accesses
  while (i < 1000000) {
    *(x + generate_number() % words) = 42;

    i = i + 1;
  }

  return 0;
}
