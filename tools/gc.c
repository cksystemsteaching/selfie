int main(int argc, char** argv) {
  turn_on_gc_library(); // use library variant of gc

  return selfie_main(argc, argv);
}