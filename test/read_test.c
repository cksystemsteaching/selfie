// [-c test/read_test.c selfie.c -v 1 -n 2;<35,49,52,1>]
uint64_t* file_name;

uint64_t SIZEOFUINT64       = 8; // must be the same as REGISTERSIZE
uint64_t EXITCODE_IOERROR   = 2;
uint64_t SYSCALL_BITWIDTH   = 32; // integer bit width for system calls
uint64_t O_RDONLY           = 32768;

void      init_library();
uint64_t  sign_extend(uint64_t n, uint64_t b);
uint64_t* smalloc(uint64_t size);
uint64_t  signed_less_than(uint64_t a, uint64_t b);
void      printf1(uint64_t* s, uint64_t* a1);

void      exit(int code);
uint64_t  read(uint64_t fd, uint64_t* buffer, uint64_t bytes_to_read);
uint64_t  open(uint64_t* filename, uint64_t flags, uint64_t mode);

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t* character_buffer;
  uint64_t source_fd;
  uint64_t number_of_read_bytes;

  init_library();

  file_name = "test/read_test_input.txt";
  source_fd = sign_extend(open(file_name, O_RDONLY, 0), SYSCALL_BITWIDTH);
  if (signed_less_than(source_fd, 0)) {
    printf1((uint64_t*) "could not open input file %s\n", file_name);
    exit(EXITCODE_IOERROR);
  }

  character_buffer  = smalloc(SIZEOFUINT64);
  number_of_read_bytes = read(source_fd, character_buffer, 1);
  return *(character_buffer);
}
