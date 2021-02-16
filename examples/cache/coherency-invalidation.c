uint64_t* e_entry = (uint64_t*) 65536;
uint64_t instructions_word_offset = 41;
uint64_t patched_addi = 2830383514643;

uint64_t get_return_value() {
  return 1;
}

void patch_return_value() {
  // requires write access to the code segment
  // (i.e. is_valid_segment_write() must be
  // modified to return 1 for code addresses)
  *(e_entry + instructions_word_offset) = patched_addi;
}

uint64_t main() {
  uint64_t return_value;

  // instruction containing the return code
  // will be loaded into the icache
  return_value = get_return_value();

  // patches get_return_value() to return 0 instead of 1
  patch_return_value();

  // returns 1 if there is no coherency between
  // dcache and icache (correct behavior: 0)
  return_value = get_return_value();

  return return_value;
}
