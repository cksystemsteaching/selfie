int main(int argc, char** argv) {
  use_garbage_collector = 2; // use library variant of gc

  return selfie_main(argc, argv);
}