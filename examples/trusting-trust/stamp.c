// trusting-trust: stamp, an honest source-to-source compiler in C*.
//
// stamp reads a C* source file and writes it out unchanged: it is the
// identity compiler for C*. Because its source language (C*) is also
// its implementation language, stamp can compile its own source, which
// is what Ken Thompson's "trusting trust" argument needs.
//
// An honest stamp is a fixed point: stamp applied to stamp.c yields
// stamp.c again, byte for byte. The trojaned variant stamp-trojan.c is
// not a fixed point, and that is exactly what diverse double-compiling
// detects. See README.md.
//
// Build and run with selfie, reading selfie.h as its library:
//   ./selfie -c selfie.h examples/trusting-trust/stamp.c -m 2 in.c out.c

uint64_t MAX_LINE = 1048576; // longest line stamp copies, in bytes

char* line; // current line, null terminated, without its line feed
char* byte; // one-byte buffer for reading and writing

uint64_t stamp_in_fd; // file descriptor of the input file
uint64_t stamp_out_fd; // file descriptor of the output file

uint64_t has_line_feed; // 1 if the current line ended with a line feed

uint64_t read_line();

void write_text(char* s);
void write_byte(uint64_t c);

void emit_line();

uint64_t main(uint64_t argc, uint64_t* argv);

uint64_t read_line() {
  uint64_t i;
  uint64_t read_bytes;
  uint64_t c;

  // read one line from stamp_in_fd into line, dropping its line feed;
  // return 1 if a line was read, 0 at end of file

  i = 0;

  has_line_feed = 0;

  while (1) {
    read_bytes = read(stamp_in_fd, (uint64_t*) byte, 1);

    if (read_bytes == 0) {
      // end of file
      store_character(line, i, 0);

      if (i == 0)
        return 0;
      else
        return 1;
    }

    c = load_character(byte, 0);

    if (c == CHAR_LF) {
      store_character(line, i, 0);

      has_line_feed = 1;

      return 1;
    }

    store_character(line, i, c);

    i = i + 1;

    if (i + 1 >= MAX_LINE) {
      // line too long, flush what we have
      store_character(line, i, 0);

      return 1;
    }
  }
}

void write_text(char* s) {
  // write the characters of s to stamp_out_fd
  write(stamp_out_fd, (uint64_t*) s, string_length(s));
}

void write_byte(uint64_t c) {
  // write a single character to stamp_out_fd
  store_character(byte, 0, c);

  write(stamp_out_fd, (uint64_t*) byte, 1);
}

void emit_line() {
  // trusting-trust: honest stamp
  write_text(line);

  if (has_line_feed)
    write_byte(CHAR_LF);
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  init_library();

  if (argc < 3)
    // need an input and an output file name
    exit(1);

  // allocate the one-byte buffer before the large line buffer so it does
  // not sit at the very top of the heap, where the system call path would
  // find its page unmapped
  byte = string_alloc(8);
  line = string_alloc(MAX_LINE);

  stamp_in_fd = open_read_only((char*) *(argv + 1));

  if (signed_less_than(stamp_in_fd, 0))
    exit(1);

  stamp_out_fd = open_write_only((char*) *(argv + 2), S_IRUSR_IWUSR_IRGRP_IROTH);

  if (signed_less_than(stamp_out_fd, 0))
    exit(1);

  while (read_line())
    emit_line();

  return 0;
}
