#include "bootstrap.h"
#include "config.h"
#include "console.h"
#include "diag.h"
#include "tinycstd.h"

int main(int argc, char** argv);


void bootstrap() {
  early_init();
  console_init();

  kernel_environ_init();

  char* args[] = {
    "./" INIT_FILE_PATH,
    "-c",
    "selfie.c",
    "-m",
    "2",
    "-l",
    "selfie.m",
    "-y",
    "1",
    "-c",
    "hello-world.c",
    (char*) 0,
  };
  int argc = 0;

  puts("Booting " INIT_FILE_PATH " with args: \n");

  while (args[argc] != (char*) 0) {
    printf("    %s\n", args[argc]);
    argc++;
  }
  printf("    <END>\n\n");

  uint64_t result = start_init_process(argc, args);

  printf("\nInit process terminated with exit code %d\n", result);
  shutdown();
}
