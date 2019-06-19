uint64_t* buffer;

uint64_t SIZEOFUINT64       = 8; // must be the same as REGISTERSIZE
uint64_t EXITCODE_IOERROR   = 2;
uint64_t SYSCALL_BITWIDTH   = 32; // integer bit width for system calls
uint64_t O_RDONLY           = 32768;

// libcstar procedures for printing
void init_library();
void printf1(uint64_t* s, uint64_t* a1);
uint64_t* smalloc(uint64_t size);

// libcstar procedures
void      exit(int code);
uint64_t  read(uint64_t fd, uint64_t* buffer, uint64_t bytes_to_read);
uint64_t  open(uint64_t* filename, uint64_t flags, uint64_t mode);

uint64_t is_lowercase(uint64_t c) {
  if (c >= 'a')
    if (c <= 'z')
      return 1;
  return 0;
}

uint64_t is_digit(uint64_t c) {
  if (c >= '0')
    if (c <= '9')
      return 1;
  return 0;
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t source_fd;
  uint64_t c;

  // initialize selfie's libcstar library
  init_library();

  source_fd = sign_extend(open((uint64_t*) *argv, O_RDONLY, 0), SYSCALL_BITWIDTH);
  if (signed_less_than(source_fd, 0)) {
    printf1((uint64_t*) "could not open input file %s\n", (uint64_t*) *argv);
    exit(EXITCODE_IOERROR);
  }

  buffer  = smalloc(SIZEOFUINT64);
  read(source_fd, buffer, 1);

  if (is_lowercase(*buffer))
    return *buffer;

  if (is_digit(*buffer)) {
    c = (*buffer - '0');
    return 10 / (c / 10);
  }

  return 1;
}
