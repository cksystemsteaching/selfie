#define SBI_EXT_0_1_CONSOLE_PUTCHAR 0x1

#define GET_PC(var) \
    asm volatile( \
        "auipc %[ptr], 0" \
        : [ptr] "=r" (var) \
    ); \


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

void print_hex_internal(uint64_t val, uint64_t pos, uint64_t maxLen) {
    if (pos >= maxLen)
        return;

    uint64_t rest = val % 16;
    val = val / 16;

    print_hex_internal(val, pos+1, maxLen);
    if (rest >= 0 && rest < 10) {
        sbi_ecall_console_putc('0'+rest);
    } else {
        sbi_ecall_console_putc('A'+(rest-10));
    }
}

void print_hex(uint64_t val) {
    sbi_ecall_console_putc('0');
    sbi_ecall_console_putc('x');

    print_hex_internal(val, 0, 8);
}

static inline void write(uint64_t std_x, char* str, uint64_t no_chars) {
    (void) std_x;

    while (no_chars) {
        sbi_ecall_console_putc(*str);
        --no_chars;
        str++;
    }
}


void print_memory_range(char* from, char* to) {
    int break_counter = 16;

    while (from < to) {
        if (break_counter == 16) {
            break_counter = 0;

            sbi_ecall_console_putc('\n');
            print_hex(from);
            sbi_ecall_console_putc(':');
            sbi_ecall_console_putc(' ');
        }

        print_hex_internal(*from, 0, 2);
        sbi_ecall_console_putc(' ');

        from++;
        break_counter++;
    }
}

void search_for_bytes_in_memory(char* from, char* to, char bytes[], uint64_t no_of_bytes) {
    for (char* i = from; i < to; ++i)
        for (uint64_t j = 0; j < no_of_bytes && (uint64_t) i + j < (uint64_t) to && *(i + j) == bytes[j]; ++j)
            if (j == no_of_bytes - 1)
                print_memory_range(i, i + ((no_of_bytes / 16) + 1) * 16);
}

void search_for_word_in_memory(int* from, int* to, int word) {
    for (int* i = from; i < to; ++i)
        if (*i == word)
            print_memory_range(i, i + 16);
}

// main procedure for printing "Hello World!    " on the console
uint64_t* main() {
  uint64_t pc;
  char hello[] = {'H', 'e', 'l', 'l', 'o', ' ', 'W', /*'o', 'r', 'l', 'd', '!'*/};
  // point to the "Hello World!    " string
  foo = "Hello World!    ";

  // busy loop for slow connections to the board
  for (uint64_t i = 0; i <= (uint64_t) 99999999; i++)
      ;

  sbi_ecall_console_putc('>');
  print_hex(foo);
  sbi_ecall_console_putc('<');
  print_hex(*foo);
  sbi_ecall_console_putc(' ');
  GET_PC(pc);
  print_hex(pc);

  sbi_ecall_console_putc('\n');
  //print_memory_range(0x805FF600, 0x805FF6B0);
  search_for_bytes_in_memory((char*) 0x80000000, (char*) 0x805fffff, hello, 7);

  // strings are actually stored in chunks of 8 characters in memory,
  // that is, here as "Hello Wo", and "rld!    " which allows us to
  // print them conveniently in chunks of 8 characters at a time

  // as long as there are characters print them
  while (*foo != 0) {
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
