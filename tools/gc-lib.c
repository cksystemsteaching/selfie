int main(int argc, char** argv) {
  uint64_t exit_code;

  init_library();

  turn_on_gc_library(12000, ""); // use library variant of gc

  exit_code = selfie_main(argc, argv);

  print_gc_profile(0);

  return exit_code;
}