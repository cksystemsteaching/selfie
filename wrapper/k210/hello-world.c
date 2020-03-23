#define SBI_EXT_0_1_CONSOLE_PUTCHAR 0x1

// global variable for pointing to the "Hello World!    " string
char* foo;

extern void loop_print_a();

void sbi_ecall_console_putc(char c) {
    asm volatile(
        "li a7, 1;"
        "li a6, 0;"
        "mv a0, %[character];" // just a test to see if it prints 'a'
        "ecall;"
        :
        : [character] "r" (c)
        : "a0", "a6", "a7"
    );
}

static inline void write(uint64_t std_x, char* str, uint64_t no_chars) {
    (void) std_x;

    while (no_chars && str) {
        sbi_ecall_console_putc(*str++);
        --no_chars;
    }
}

// main procedure for printing "Hello World!    " on the console
uint64_t* main() {
  // point to the "Hello World!    " string
  foo = "Hello World!    ";

  sbi_ecall_console_putc('H');
  sbi_ecall_console_putc('e');
  sbi_ecall_console_putc('l');
  sbi_ecall_console_putc('l');
  sbi_ecall_console_putc('o');

  // strings are actually stored in chunks of 8 characters in memory,
  // that is, here as "Hello Wo", and "rld!    " which allows us to
  // print them conveniently in chunks of 8 characters at a time

  // as long as there are characters print them
  while (1) {
    // 1 means that we print to the console
    // foo points to a chunk of 8 characters
    // 8 means that we print 8 characters
    write(1, foo, 8);

    // go to the next chunk of 8 characters
    foo = foo + 1;
  }

  while (1)
      ;
}
