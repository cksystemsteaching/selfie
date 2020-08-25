int main(int argc, char** argv) {
  use_garbage_collector = GCLIBRARY; // use library variant of gc

  return selfie_main(argc, argv);
}