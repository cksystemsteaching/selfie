int main(int argc, char** argv) {
  uint64_t exit_code;

  turn_on_gc_library(); // use library variant of gc

  exit_code = selfie_main(argc, argv);

  print_gc_profile(" gc:      ");

  return exit_code;
}