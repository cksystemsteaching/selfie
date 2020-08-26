int main(int argc, char** argv) {
  USE_GC_LIBRARY = GC_LIBRARY; // use library variant of gc

  return selfie_main(argc, argv);
}