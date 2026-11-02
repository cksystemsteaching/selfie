/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

Riscr implements RISC-R, the reversible variant of RISC-U, with
selfie as library. RISC-R keeps the 14 RISC-U instructions and their
encodings but changes what they mean such that every instruction is
a bijection on the machine state. Riscr executes RISC-R binaries,
which are RISC-U binaries with bit 8 of e_flags set, forward and,
without any trace, backward. See riscr.md for the instruction set
and projects/reversible.md for the development plan.

The emulator reuses mipster's loader, memory, contexts, and decoder,
and replaces mipster's execution with RISC-R semantics: a reverse
flag selects the direction, and instruction_address() and
continue_at() hide it from the instructions. Files are part of the
machine state: system calls exchange words with tapes that remember
what was read and written.

Options in addition to selfie's options:

-m 0-4096 ... runs a RISC-R binary forward until it exits,
-rev 0-4096 ... runs it forward and then all instructions but the
exit system call backward.

Selfie's own mipster refuses RISC-R binaries. Translating RISC-U
binaries into RISC-R binaries (milestone M2) is still to be done.
*/

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     L I B R A R Y     ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------- EXCLUSIVE OR --------------------------
// -----------------------------------------------------------------

void     init_xor_table();
uint64_t bitwise_xor(uint64_t a, uint64_t b);

// ------------------------ GLOBAL VARIABLES -----------------------

char* xor_table = (char*) 0; // 256x256 table of byte-wise exclusive ors, see init_xor_table()

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------    C O M P I L E R    ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// translation of RISC-U binaries into RISC-R binaries goes here (M2)

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------ RISC-R SYSCALLS ------------------------
// -----------------------------------------------------------------

uint64_t* allocate_tape();

uint64_t* new_tape(uint64_t fd, uint64_t input);
void      reset_tape(uint64_t* tape);
void      reset_tapes();

uint64_t* get_tape(uint64_t fd);

uint64_t* tape_buffer_word(uint64_t* context, uint64_t vaddr);

void     fill_input_tape(uint64_t* tape, uint64_t head, uint64_t size);
uint64_t bytes_on_input_tape(uint64_t* tape, uint64_t head, uint64_t size);

void add_syscall_result(uint64_t* context, uint64_t result);

void implement_reversible_exit(uint64_t* context);
void implement_reversible_read(uint64_t* context);
void implement_reversible_write(uint64_t* context);
void implement_reversible_openat(uint64_t* context);
void implement_reversible_brk(uint64_t* context);

// RISC-R tapes: files are part of the machine state, see riscr.md

// tape
// +---+--------+
// | 0 | memory | pointer to tape memory of MAX_TAPE_SIZE bytes
// | 1 | length | number of words transferred between file and tape
// | 2 | head   | next word on tape to exchange with or append from memory
// | 3 | end    | size of file in bytes once its end was read, else UINT64_MAX
// | 4 | fd     | file descriptor on host, -1 if the file is not open
// | 5 | input  | 1 if tape is filled from file, 0 if tape is written to file
// +---+--------+

uint64_t* get_tape_memory(uint64_t* tape) { return (uint64_t*) *tape; }
uint64_t  get_tape_length(uint64_t* tape) { return             *(tape + 1); }
uint64_t  get_tape_head(uint64_t* tape)   { return             *(tape + 2); }
uint64_t  get_tape_end(uint64_t* tape)    { return             *(tape + 3); }
uint64_t  get_tape_fd(uint64_t* tape)     { return             *(tape + 4); }
uint64_t  is_input_tape(uint64_t* tape)   { return             *(tape + 5); }

void set_tape_memory(uint64_t* tape, uint64_t* memory) { *tape       = (uint64_t) memory; }
void set_tape_length(uint64_t* tape, uint64_t length)  { *(tape + 1) = length; }
void set_tape_head(uint64_t* tape, uint64_t head)      { *(tape + 2) = head; }
void set_tape_end(uint64_t* tape, uint64_t end)        { *(tape + 3) = end; }
void set_tape_fd(uint64_t* tape, uint64_t fd)          { *(tape + 4) = fd; }
void set_input_tape(uint64_t* tape, uint64_t input)    { *(tape + 5) = input; }

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t MAX_TAPE_SIZE       = 1048576; // 1MB per tape
uint64_t MAX_NUMBER_OF_TAPES = 64;      // including standard input, output, and error

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* tapes           = (uint64_t*) 0; // tapes indexed by RISC-R file descriptors
uint64_t  number_of_tapes = 0;             // next RISC-R file descriptor, 3 after reset

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------    A R C H I T E C T U R E    -----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------- RISC-R INSTRUCTIONS ----------------------
// -----------------------------------------------------------------

uint64_t instruction_address();
void     continue_at(uint64_t address);

uint64_t is_distinct_rd(uint64_t rs1, uint64_t rs2);
uint64_t update_rd(uint64_t value);
uint64_t flip_rd(uint64_t value);

uint64_t is_come_from(uint64_t target, uint64_t origin);

void do_riscr_lui();
void do_riscr_addi();

void do_riscr_add();
void do_riscr_sub();
void do_riscr_mul();
void do_riscr_divu();
void do_riscr_remu();
void do_riscr_sltu();

uint64_t do_riscr_load();

void do_riscr_beq();
void do_riscr_jal();
void do_riscr_jalr();

void do_riscr_ecall();

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void init_reversible_interpreter();

uint64_t fetch_instruction(uint64_t vaddr);

void fetch_reversibly();
void execute_reversibly();

void run_reversibly_until_exception();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t EXCEPTION_IRREVERSIBLEINSTRUCTION = 10; // extends mipster's exceptions

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t reverse = 0; // flag for executing RISC-R code backward

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

void reset_reversible_registers_profile();

void boot_reversibly(uint64_t megabytes);

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

uint64_t* reversible_switch(uint64_t* to_context, uint64_t timeout);

uint64_t handle_reversible_system_call(uint64_t* context);
uint64_t handle_reversible_exception(uint64_t* context);

uint64_t riscr(uint64_t* to_context);
uint64_t riscr_backward(uint64_t* to_context, uint64_t steps);

uint64_t selfie_run_reversibly();

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     L I B R A R Y     ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------- EXCLUSIVE OR --------------------------
// -----------------------------------------------------------------

void init_xor_table() {
  uint64_t a;
  uint64_t b;

  // C* has no bitwise operators: tabulate exclusive or of bytes
  // using bitwise_xor(a, b) == 2 * bitwise_xor(a / 2, b / 2) + (a + b) % 2

  xor_table = (char*) zmalloc(256 * 256);

  a = 0;

  while (a < 256) {
    b = 0;

    while (b < 256) {
      store_character(xor_table, a * 256 + b,
        left_shift(load_character(xor_table, (a / 2) * 256 + b / 2), 1) + (a + b) % 2);

      b = b + 1;
    }

    a = a + 1;
  }
}

uint64_t bitwise_xor(uint64_t a, uint64_t b) {
  uint64_t x;
  uint64_t i;

  if (xor_table == (char*) 0)
    init_xor_table();

  x = 0;
  i = 0;

  // byte-wise exclusive or
  while (i < SIZEOFUINT64INBITS) {
    x = x + left_shift(load_character(xor_table, get_bits(a, i, 8) * 256 + get_bits(b, i, 8)), i);

    i = i + 8;
  }

  return x;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------ RISC-R SYSCALLS ------------------------
// -----------------------------------------------------------------

uint64_t* allocate_tape() {
  return smalloc(1 * sizeof(uint64_t*) + 5 * sizeof(uint64_t));
}

uint64_t* new_tape(uint64_t fd, uint64_t input) {
  uint64_t* tape;

  tape = allocate_tape();

  set_tape_memory(tape, zmalloc(MAX_TAPE_SIZE));

  reset_tape(tape);

  set_tape_fd(tape, fd);
  set_input_tape(tape, input);

  return tape;
}

void reset_tape(uint64_t* tape) {
  zero_memory(get_tape_memory(tape), MAX_TAPE_SIZE);

  set_tape_length(tape, 0);
  set_tape_head(tape, 0);
  set_tape_end(tape, UINT64_MAX);
}

void reset_tapes() {
  uint64_t fd;
  uint64_t* tape;

  if (tapes == (uint64_t*) 0)
    tapes = zmalloc(MAX_NUMBER_OF_TAPES * sizeof(uint64_t*));

  fd = 0;

  while (fd < MAX_NUMBER_OF_TAPES) {
    tape = (uint64_t*) *(tapes + fd);

    if (tape != (uint64_t*) 0) {
      reset_tape(tape);

      if (fd >= 3)
        // files are reopened when opened again
        set_tape_fd(tape, -1);
    } else if (fd < 3)
      // standard input, output, and error of riscr
      *(tapes + fd) = (uint64_t) new_tape(fd, fd == 0);

    fd = fd + 1;
  }

  number_of_tapes = 3;
}

uint64_t* get_tape(uint64_t fd) {
  uint64_t* tape;

  // tape of open file with RISC-R file descriptor fd, or 0

  if (fd < number_of_tapes) {
    tape = (uint64_t*) *(tapes + fd);

    if (tape != (uint64_t*) 0)
      if (not(signed_less_than(get_tape_fd(tape), 0)))
        return tape;
  }

  return (uint64_t*) 0;
}

uint64_t* tape_buffer_word(uint64_t* context, uint64_t vaddr) {
  // physical address of memory word at vaddr, mapping its page if necessary

  if (is_virtual_address_valid(vaddr, WORDSIZE))
    if (is_data_stack_heap_address(context, vaddr)) {
      if (not(is_virtual_address_mapped(get_pt(context), vaddr))) {
        if (pavailable())
          map_page(context, page_of_virtual_address(vaddr), (uint64_t) palloc());
        else {
          printf("%s: tape buffer at virtual address 0x%08lX out of physical memory\n", selfie_name, vaddr);

          exit(EXITCODE_OUTOFPHYSICALMEMORY);
        }
      }

      return translate_virtual_to_physical(get_pt(context), vaddr);
    }

  printf("%s: tape buffer at virtual address 0x%08lX is invalid\n", selfie_name, vaddr);

  exit(EXITCODE_UNCAUGHTEXCEPTION);

  return (uint64_t*) 0;
}

void fill_input_tape(uint64_t* tape, uint64_t head, uint64_t size) {
  uint64_t words;
  uint64_t length;
  uint64_t bytes;
  uint64_t read_bytes;

  // read bytes from file onto zeroed input tape up to head + size bytes

  words  = round_up(size, WORDSIZE) / WORDSIZE;
  length = get_tape_length(tape);

  if (head + words > length) {
    if (get_tape_end(tape) == UINT64_MAX)
      if (length * WORDSIZE < head * WORDSIZE + size) {
        bytes = head * WORDSIZE + size - length * WORDSIZE;

        read_bytes = sign_extend(
          read(get_tape_fd(tape), (uint64_t*) ((uint64_t) get_tape_memory(tape) + length * WORDSIZE), bytes),
          SYSCALL_BITWIDTH);

        if (signed_less_than(read_bytes, bytes)) {
          // end of file
          if (signed_less_than(read_bytes, 0))
            read_bytes = 0;

          set_tape_end(tape, length * WORDSIZE + read_bytes);
        }
      }

    set_tape_length(tape, head + words);
  }
}

uint64_t bytes_on_input_tape(uint64_t* tape, uint64_t head, uint64_t size) {
  uint64_t end;

  // number of bytes a read of size bytes at head returns, recomputable backward

  end = get_tape_end(tape);

  if (end == UINT64_MAX)
    return size;
  else if (head * WORDSIZE >= end)
    return 0;
  else if (end - head * WORDSIZE < size)
    return end - head * WORDSIZE;
  else
    return size;
}

void add_syscall_result(uint64_t* context, uint64_t result) {
  // RISC-R system calls add their result into a0 forward and
  // subtract it backward, see riscr.md

  if (reverse) {
    *(get_regs(context) + REG_A0) = *(get_regs(context) + REG_A0) - result;

    set_pc(context, get_pc(context) - INSTRUCTIONSIZE);
  } else {
    *(get_regs(context) + REG_A0) = *(get_regs(context) + REG_A0) + result;

    set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
  }

  if (debug_syscalls) {
    printf(" -> ");
    print_register_value(REG_A0);
    println();
  }
}

void implement_reversible_exit(uint64_t* context) {
  // parameter
  uint64_t signed_int_exit_code;

  if (debug_syscalls) {
    printf("(exit): ");
    print_register_hexadecimal(REG_A1);
    printf(" |- ->\n");
  }

  signed_int_exit_code = *(get_regs(context) + REG_A1);

  set_exit_code(context, sign_shrink(signed_int_exit_code, SYSCALL_BITWIDTH));
}

void implement_reversible_read(uint64_t* context) {
  // parameters
  uint64_t fd;
  uint64_t vbuffer;
  uint64_t size;

  uint64_t* tape;
  uint64_t words;
  uint64_t head;
  uint64_t result;
  uint64_t i;
  uint64_t* paddr;
  uint64_t word;

  if (debug_syscalls) {
    printf("(read): ");
    print_register_value(REG_A1);
    printf(",");
    print_register_hexadecimal(REG_A2);
    printf(",");
    print_register_value(REG_A3);
    printf(" |- ");
    print_register_value(REG_A0);
  }

  fd      = *(get_regs(context) + REG_A1);
  vbuffer = *(get_regs(context) + REG_A2);
  size    = *(get_regs(context) + REG_A3);

  // RISC-R read exchanges words between memory and input tape, see riscr.md

  tape = get_tape(fd);

  if (tape == (uint64_t*) 0)
    result = sign_shrink(-1, SYSCALL_BITWIDTH);
  else if (not(is_input_tape(tape)))
    result = sign_shrink(-1, SYSCALL_BITWIDTH);
  else {
    words = round_up(size, WORDSIZE) / WORDSIZE;
    head  = get_tape_head(tape);

    if (reverse) {
      if (head < words) {
        printf("%s: input tape rewound before its beginning\n", selfie_name);

        exit(EXITCODE_UNCAUGHTEXCEPTION);
      }

      head = head - words;
    } else {
      if (head + words > MAX_TAPE_SIZE / WORDSIZE) {
        printf("%s: input tape is full\n", selfie_name);

        exit(EXITCODE_OUTOFVIRTUALMEMORY);
      }

      fill_input_tape(tape, head, size);
    }

    result = bytes_on_input_tape(tape, head, size);

    i = 0;

    while (i < words) {
      paddr = tape_buffer_word(context, vbuffer + i * WORDSIZE);

      word = load_physical_memory(paddr);

      store_physical_memory(paddr, load_word(get_tape_memory(tape), (head + i) * WORDSIZE, 1));

      store_word(get_tape_memory(tape), (head + i) * WORDSIZE, 1, word);

      i = i + 1;
    }

    if (reverse)
      set_tape_head(tape, head);
    else
      set_tape_head(tape, head + words);
  }

  add_syscall_result(context, result);
}

void implement_reversible_write(uint64_t* context) {
  // parameters
  uint64_t fd;
  uint64_t vbuffer;
  uint64_t size;

  uint64_t* tape;
  uint64_t words;
  uint64_t head;
  uint64_t result;
  uint64_t i;
  uint64_t word;

  if (debug_syscalls) {
    printf("(write): ");
    print_register_value(REG_A1);
    printf(",");
    print_register_hexadecimal(REG_A2);
    printf(",");
    print_register_value(REG_A3);
    printf(" |- ");
    print_register_value(REG_A0);
  }

  fd      = *(get_regs(context) + REG_A1);
  vbuffer = *(get_regs(context) + REG_A2);
  size    = *(get_regs(context) + REG_A3);

  // RISC-R write appends words from memory to output tape, see riscr.md

  tape = get_tape(fd);

  if (tape == (uint64_t*) 0)
    result = sign_shrink(-1, SYSCALL_BITWIDTH);
  else if (is_input_tape(tape))
    result = sign_shrink(-1, SYSCALL_BITWIDTH);
  else {
    words = round_up(size, WORDSIZE) / WORDSIZE;
    head  = get_tape_head(tape);

    if (reverse) {
      if (head < words) {
        printf("%s: output tape rewound before its beginning\n", selfie_name);

        exit(EXITCODE_UNCAUGHTEXCEPTION);
      }

      head = head - words;

      i = 0;

      // erase words from output tape, they are still in memory
      while (i < words) {
        store_word(get_tape_memory(tape), (head + i) * WORDSIZE, 1, 0);

        i = i + 1;
      }

      set_tape_head(tape, head);
    } else {
      if (head + words > MAX_TAPE_SIZE / WORDSIZE) {
        printf("%s: output tape is full\n", selfie_name);

        exit(EXITCODE_OUTOFVIRTUALMEMORY);
      }

      if (size >= IO_buffer_size) {
        // integer-align and accommodate potentially needed null terminator
        IO_buffer_size = round_up(size + 1, sizeof(uint64_t));

        // buffer must be fully mapped for subsequent read syscalls with greater sizes
        IO_buffer = touch(smalloc(IO_buffer_size), IO_buffer_size);
      }

      // null-terminate buffer
      *(IO_buffer + size / sizeof(uint64_t)) = 0;

      i = 0;

      while (i < words) {
        word = load_physical_memory(tape_buffer_word(context, vbuffer + i * WORDSIZE));

        store_word(get_tape_memory(tape), (head + i) * WORDSIZE, 1, word);

        store_word(IO_buffer, i * WORDSIZE, 1, word);

        i = i + 1;
      }

      set_tape_head(tape, head + words);

      // output tape is also written to file
      write_to_printf(get_tape_fd(tape), IO_buffer, size);
    }

    result = size;
  }

  add_syscall_result(context, result);
}

void implement_reversible_openat(uint64_t* context) {
  // parameters
  uint64_t vfilename;
  uint64_t flags;
  uint64_t mode;

  uint64_t* tape;
  uint64_t fd;
  uint64_t result;

  if (debug_syscalls) {
    printf("(openat): ");
    print_register_hexadecimal(REG_A1);
    printf(",");
    print_register_hexadecimal(REG_A2);
    printf(",");
    print_register_octal(REG_A3);
    printf(" |- ");
    print_register_value(REG_A0);
  }

  vfilename = *(get_regs(context) + REG_A1);
  flags     = *(get_regs(context) + REG_A2);
  mode      = *(get_regs(context) + REG_A3);

  // RISC-R openat allocates the next file descriptor and its tape, see riscr.md

  if (reverse)
    number_of_tapes = number_of_tapes - 1;
  else if (number_of_tapes >= MAX_NUMBER_OF_TAPES) {
    printf("%s: too many open files\n", selfie_name);

    exit(EXITCODE_OUTOFVIRTUALMEMORY);
  }

  tape = (uint64_t*) *(tapes + number_of_tapes);

  if (not(reverse)) {
    if (tape != (uint64_t*) 0)
      if (not(signed_less_than(get_tape_fd(tape), 0)))
        // tape of a file opened before executing backward, keep it
        fd = get_tape_fd(tape);
      else
        fd = -1;
    else
      fd = -1;

    if (signed_less_than(fd, 0)) {
      // open file on host
      if (down_load_string(context, vfilename, filename_buffer)) {
        if (flags == LINUX_O_CREAT_TRUNC_WRONLY)
          // use correct flags for host operating system
          flags = O_CREAT_TRUNC_WRONLY;

        fd = sign_extend(open(filename_buffer, flags, mode), SYSCALL_BITWIDTH);
      }

      if (tape == (uint64_t*) 0) {
        tape = new_tape(fd, 0);

        *(tapes + number_of_tapes) = (uint64_t) tape;
      } else {
        reset_tape(tape);

        set_tape_fd(tape, fd);
      }

      if (flags == O_RDONLY)
        set_input_tape(tape, 1);
      else
        set_input_tape(tape, flags == 0);

      if (debug_open)
        printf("%s: opened file %s with flags 0x%lX and mode 0o%lo returning file descriptor %lu\n", selfie_name,
          filename_buffer, flags, mode, number_of_tapes);
    }
  }

  if (signed_less_than(get_tape_fd(tape), 0))
    result = sign_shrink(-1, SYSCALL_BITWIDTH);
  else
    result = number_of_tapes;

  if (not(reverse))
    number_of_tapes = number_of_tapes + 1;

  add_syscall_result(context, result);
}

void implement_reversible_brk(uint64_t* context) {
  // parameter
  uint64_t new_program_break;

  // local variable
  uint64_t previous_program_break;

  if (debug_syscalls) {
    printf("(brk): ");
    print_register_hexadecimal(REG_A1);
    printf(" |- ");
    print_register_hexadecimal(REG_A0);
  }

  new_program_break      = *(get_regs(context) + REG_A1);
  previous_program_break = get_program_break(context);

  // RISC-R brk adds the previous program break into a0 if it succeeds, see riscr.md

  if (reverse) {
    if (*(get_regs(context) + REG_A0) != 0) {
      // a0 holds the previous program break, restore it
      set_program_break(context, *(get_regs(context) + REG_A0));

      set_lc_malloc(context, get_lc_malloc(context) - 1);

      add_syscall_result(context, *(get_regs(context) + REG_A0));
    } else
      add_syscall_result(context, 0);
  } else if (new_program_break > previous_program_break) {
    if (try_brk(context, new_program_break) == new_program_break) {
      set_lc_malloc(context, get_lc_malloc(context) + 1);

      add_syscall_result(context, previous_program_break);
    } else
      add_syscall_result(context, 0);
  } else
    add_syscall_result(context, 0);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------    A R C H I T E C T U R E    -----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------- RISC-R INSTRUCTIONS ----------------------
// -----------------------------------------------------------------

uint64_t instruction_address() {
  // address of the executing instruction
  if (reverse)
    // executing backward: the instruction before pc
    return pc - INSTRUCTIONSIZE;
  else
    return pc;
}

void continue_at(uint64_t address) {
  // forward execution continues after address,
  // backward execution continues at address
  if (reverse)
    pc = address;
  else
    pc = address + INSTRUCTIONSIZE;
}

uint64_t is_distinct_rd(uint64_t rs1, uint64_t rs2) {
  // rd must be distinct from source registers rs1 and rs2 unless rd is zero,
  // otherwise the instruction is irreversible and has no effect

  if (rd != REG_ZR) {
    if (rd == rs1)
      throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, instruction_address());
    else if (rd == rs2)
      throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, instruction_address());
    else
      return 1;

    return 0;
  }

  return 1;
}

uint64_t update_rd(uint64_t value) {
  uint64_t next_rd_value;

  // rd += value forward, rd -= value backward, returns 1 if effective nop

  if (rd != REG_ZR) {
    if (reverse)
      next_rd_value = *(registers + rd) - value;
    else
      next_rd_value = *(registers + rd) + value;

    if (*(registers + rd) != next_rd_value) {
      *(registers + rd) = next_rd_value;

      return 0;
    }
  }

  return 1;
}

uint64_t flip_rd(uint64_t value) {
  // rd ^= value, its own inverse, returns 1 if effective nop

  if (rd != REG_ZR)
    if (value != 0) {
      *(registers + rd) = bitwise_xor(*(registers + rd), value);

      return 0;
    }

  return 1;
}

uint64_t is_come_from(uint64_t target, uint64_t origin) {
  uint64_t partner;

  // is the instruction at target the come-from of the
  // control-flow instruction at origin? see riscr.md

  if (is_virtual_address_valid(target, INSTRUCTIONSIZE))
    if (is_code_address(current_context, target)) {
      partner = fetch_instruction(target);

      if (is == BEQ) {
        // beq pointing back whose condition holds
        if (get_opcode(partner) == OP_BRANCH)
          if (get_funct3(partner) == F3_BEQ)
            if (get_immediate_b_format(partner) == origin - target)
              return *(registers + get_rs1(partner)) == *(registers + get_rs2(partner));
      } else if (is == JAL) {
        if (rd == REG_ZR) {
          // jal zero pointing back
          if (get_opcode(partner) == OP_JAL)
            if (get_rd(partner) == REG_ZR)
              return get_immediate_j_format(partner) == origin - target;
        } else {
          // jalr rd,0(rd) uncomputing the link in rd
          if (get_opcode(partner) == OP_JALR)
            if (get_funct3(partner) == F3_JALR)
              if (get_rd(partner) == rd)
                if (get_rs1(partner) == rd)
                  return get_immediate_i_format(partner) == 0;
        }
      } else if (is == JALR) {
        // jal rd pointing back
        if (get_opcode(partner) == OP_JAL)
          if (get_rd(partner) == rd)
            return get_immediate_j_format(partner) == origin - target;
      }
    }

  return 0;
}

void do_riscr_lui() {
  // semantics of RISC-R lui: rd += imm * 2^12, backward rd -= imm * 2^12

  nopc_lui = nopc_lui + update_rd(left_shift(imm, 12));

  write_register(rd);

  continue_at(instruction_address());

  ic_lui = ic_lui + 1;
}

void do_riscr_addi() {
  // semantics of RISC-R addi: rd += rs1 + imm, backward rd -= rs1 + imm

  // tolerate unwrapped values in register-to-register transfers
  read_register_check_wrap(rs1, imm);

  if (is_distinct_rd(rs1, rs1)) {
    nopc_addi = nopc_addi + update_rd(*(registers + rs1) + imm);

    write_register(rd);

    continue_at(instruction_address());
  }

  ic_addi = ic_addi + 1;
}

void do_riscr_add() {
  // semantics of RISC-R add: rd += rs1 + rs2, backward rd -= rs1 + rs2

  read_register(rs1);
  read_register(rs2);

  if (is_distinct_rd(rs1, rs2)) {
    nopc_add = nopc_add + update_rd(*(registers + rs1) + *(registers + rs2));

    write_register(rd);

    continue_at(instruction_address());
  }

  ic_add = ic_add + 1;
}

void do_riscr_sub() {
  // semantics of RISC-R sub: rd += rs1 - rs2, backward rd -= rs1 - rs2

  read_register(rs1);
  read_register(rs2);

  if (is_distinct_rd(rs1, rs2)) {
    nopc_sub = nopc_sub + update_rd(*(registers + rs1) - *(registers + rs2));

    write_register(rd);

    continue_at(instruction_address());
  }

  ic_sub = ic_sub + 1;
}

void do_riscr_mul() {
  // semantics of RISC-R mul: rd ^= rs1 * rs2, its own inverse

  read_register(rs1);
  read_register(rs2);

  if (is_distinct_rd(rs1, rs2)) {
    // TODO: support of 128-bit resolution

    nopc_mul = nopc_mul + flip_rd(*(registers + rs1) * *(registers + rs2));

    write_register(rd);

    continue_at(instruction_address());
  }

  ic_mul = ic_mul + 1;
}

void do_riscr_divu() {
  // semantics of RISC-R divu: rd ^= rs1 / rs2, its own inverse

  if (*(registers + rs2) != 0) {
    read_register(rs1);
    read_register(rs2);

    if (is_distinct_rd(rs1, rs2)) {
      nopc_divu = nopc_divu + flip_rd(*(registers + rs1) / *(registers + rs2));

      write_register(rd);

      continue_at(instruction_address());
    }
  } else
    throw_exception(EXCEPTION_DIVISIONBYZERO, instruction_address());

  ic_divu = ic_divu + 1;
}

void do_riscr_remu() {
  // semantics of RISC-R remu: rd ^= rs1 % rs2, its own inverse

  if (*(registers + rs2) != 0) {
    read_register(rs1);
    read_register(rs2);

    if (is_distinct_rd(rs1, rs2)) {
      nopc_remu = nopc_remu + flip_rd(*(registers + rs1) % *(registers + rs2));

      write_register(rd);

      continue_at(instruction_address());
    }
  } else
    throw_exception(EXCEPTION_DIVISIONBYZERO, instruction_address());

  ic_remu = ic_remu + 1;
}

void do_riscr_sltu() {
  // semantics of RISC-R sltu: rd ^= (rs1 < rs2), its own inverse

  read_register(rs1);
  read_register(rs2);

  if (is_distinct_rd(rs1, rs2)) {
    nopc_sltu = nopc_sltu + flip_rd(*(registers + rs1) < *(registers + rs2));

    write_register(rd);

    continue_at(instruction_address());
  }

  ic_sltu = ic_sltu + 1;
}

uint64_t do_riscr_load() {
  uint64_t vaddr;
  uint64_t next_rd_value;
  uint64_t a;

  // semantics of RISC-R ld: exchange rd with memory word, its own inverse

  read_register(rs1);

  vaddr = *(registers + rs1) + imm;

  if (not(is_distinct_rd(rs1, rs1)))
    return vaddr;

  if (is_virtual_address_valid(vaddr, WORDSIZE)) {
    if (is_valid_segment_write(vaddr)) {
      if (is_virtual_address_mapped(pt, vaddr)) {
        if (rd != REG_ZR) {
          next_rd_value = load_cached_virtual_memory(pt, vaddr);

          if (*(registers + rd) != next_rd_value) {
            // tolerate storing unwrapped values
            read_register_check_wrap(rd, 0);

            store_cached_virtual_memory(pt, vaddr, *(registers + rd));

            *(registers + rd) = next_rd_value;
          } else
            nopc_load = nopc_load + 1;
        } else
          nopc_load = nopc_load + 1;

        // load values unwrapped
        write_register_wrap(rd, 0);

        // keep track of instruction address for profiling loads
        a = (instruction_address() - code_start) / INSTRUCTIONSIZE;

        continue_at(instruction_address());

        // keep track of number of loads in total
        ic_load = ic_load + 1;

        // and individually
        *(loads_per_instruction + a) = *(loads_per_instruction + a) + 1;
      } else
        throw_exception(EXCEPTION_PAGEFAULT, page_of_virtual_address(vaddr));
    } else
      throw_exception(EXCEPTION_SEGMENTATIONFAULT, vaddr);
  } else
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);

  return vaddr;
}

void do_riscr_beq() {
  uint64_t origin;

  // semantics of RISC-R beq: if rs1 == rs2 jump over the come-from at pc + imm,
  // backward jump onto the come-from, see riscr.md

  read_register(rs1);
  read_register(rs2);

  origin = instruction_address();

  if (*(registers + rs1) == *(registers + rs2)) {
    if (is_come_from(origin + imm, origin))
      continue_at(origin + imm);
    else
      throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, origin);
  } else {
    continue_at(origin);

    nopc_beq = nopc_beq + 1;
  }

  ic_beq = ic_beq + 1;
}

void do_riscr_jal() {
  uint64_t origin;
  uint64_t a;

  // semantics of RISC-R jal: link into zeroed rd and jump over the come-from
  // at pc + imm, backward jump onto the come-from, see riscr.md

  origin = instruction_address();

  if (rd != REG_ZR)
    if (*(registers + rd) != 0) {
      // link register must be zero
      throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, origin);

      return;
    }

  if (is_come_from(origin + imm, origin)) {
    if (rd != REG_ZR) {
      // link to the instruction after the jal, backward to the jal itself
      // which is where the come-from jalr executed forward jumps over
      if (reverse)
        *(registers + rd) = origin;
      else
        *(registers + rd) = origin + INSTRUCTIONSIZE;

      // come-from address for profiling procedure calls
      a = (origin + imm - code_start) / INSTRUCTIONSIZE;

      // keep track of number of procedure calls in total
      calls = calls + 1;

      // and individually
      *(calls_per_procedure + a) = *(calls_per_procedure + a) + 1;
    } else if (signed_less_than(imm, 0)) {
      // come-from address for profiling loop iterations
      a = (origin + imm - code_start) / INSTRUCTIONSIZE;

      // keep track of number of loop iterations in total
      iterations = iterations + 1;

      // and individually
      *(iterations_per_loop + a) = *(iterations_per_loop + a) + 1;
    }

    continue_at(origin + imm);
  } else
    throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, origin);

  write_register(rd);

  ic_jal = ic_jal + 1;
}

void do_riscr_jalr() {
  uint64_t origin;
  uint64_t target;

  // semantics of RISC-R jalr: rd == rs1 holds the address of the jal that
  // links here, backward of the instruction after that jal; jump over
  // that jal, backward jump onto it, and uncompute rd, see riscr.md

  read_register(rs1);

  origin = instruction_address();

  if (rd != rs1)
    throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, origin);
  else if (rd == REG_ZR)
    throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, origin);
  else if (imm != 0)
    throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, origin);
  else {
    if (reverse)
      target = *(registers + rs1) - INSTRUCTIONSIZE;
    else
      target = *(registers + rs1);

    if (is_come_from(target, origin)) {
      // uncompute link: rd -= rd
      *(registers + rd) = 0;

      continue_at(target);
    } else
      throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, origin);
  }

  write_register(rd);

  ic_jalr = ic_jalr + 1;
}

void do_riscr_ecall() {
  uint64_t a7;

  // semantics of RISC-R ecall: arguments in a1-a3, result added into a0, see riscr.md

  read_register(REG_A7);

  ic_ecall = ic_ecall + 1;

  a7 = *(registers + REG_A7);

  if (a7 == SYSCALL_SWITCH) {
    printf("%s: context switching is unsupported in RISC-R\n", selfie_name);

    exit(EXITCODE_UNSUPPORTEDSYSCALL);
  } else if (a7 == SYSCALL_EXIT) {
    if (reverse)
      // exit is never executed backward
      throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, instruction_address());
    else {
      read_register(REG_A1);

      throw_exception(EXCEPTION_SYSCALL, a7);
    }
  } else {
    read_register(REG_A0);
    read_register(REG_A1);

    if (a7 == SYSCALL_BRK) {
      if (not(reverse))
        if (*(registers + REG_A0) != 0) {
          // brk must find a0 zero to be reversible
          throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, instruction_address());

          return;
        }
    } else {
      read_register(REG_A2);
      read_register(REG_A3);
    }

    // all other system calls are handled by exception
    throw_exception(EXCEPTION_SYSCALL, a7);
  }
}

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void init_reversible_interpreter() {
  uint64_t* exceptions;
  uint64_t e;

  // extend mipster's exceptions, call after init_interpreter()

  exceptions = smalloc((EXCEPTION_IRREVERSIBLEINSTRUCTION + 1) * sizeof(uint64_t*));

  e = 0;

  while (e < EXCEPTION_IRREVERSIBLEINSTRUCTION) {
    *(exceptions + e) = *(EXCEPTIONS + e);

    e = e + 1;
  }

  *(exceptions + EXCEPTION_IRREVERSIBLEINSTRUCTION) = (uint64_t) "irreversible instruction";

  EXCEPTIONS = exceptions;
}

uint64_t fetch_instruction(uint64_t vaddr) {
  // assert: is_virtual_address_valid(vaddr, INSTRUCTIONSIZE) == 1
  // assert: is_code_address(current_context, vaddr) == 1
  // assert: is_virtual_address_mapped(pt, vaddr) == 1

  if (vaddr % WORDSIZE == 0)
    return get_low_word(load_cached_instruction_word(pt, vaddr));
  else
    return get_high_word(load_cached_instruction_word(pt, vaddr - INSTRUCTIONSIZE));
}

void fetch_reversibly() {
  uint64_t vaddr;

  // executing backward fetches the instruction before pc
  vaddr = instruction_address();

  if (is_virtual_address_valid(vaddr, INSTRUCTIONSIZE)) {
    if (is_code_address(current_context, vaddr)) {
      ir = fetch_instruction(vaddr);

      return;
    } else
      throw_exception(EXCEPTION_SEGMENTATIONFAULT, vaddr);
  } else
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);

  // reset instruction register
  ir = encode_nop();
}

void execute_reversibly() {
  if (is == ADDI)
    do_riscr_addi();
  else if (is == LOAD)
    do_riscr_load();
  else if (is == STORE)
    // RISC-R has no store, use ld to exchange
    throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, instruction_address());
  else if (is == ADD)
    do_riscr_add();
  else if (is == SUB)
    do_riscr_sub();
  else if (is == MUL)
    do_riscr_mul();
  else if (is == DIVU)
    do_riscr_divu();
  else if (is == REMU)
    do_riscr_remu();
  else if (is == SLTU)
    do_riscr_sltu();
  else if (is == BEQ)
    do_riscr_beq();
  else if (is == JAL)
    do_riscr_jal();
  else if (is == JALR)
    do_riscr_jalr();
  else if (is == LUI)
    do_riscr_lui();
  else if (is == ECALL)
    do_riscr_ecall();
}

void run_reversibly_until_exception() {
  trap = 0;

  while (not(trap)) {
    fetch_reversibly();
    decode();
    execute_reversibly();

    interrupt();
  }

  trap = 0;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

void reset_reversible_registers_profile() {
  uint64_t reg;

  // RISC-R: all registers are initialized to zero

  reg = 0;

  while (reg < NUMBEROFREGISTERS) {
    *(writes_per_register + reg) = 1;

    reg = reg + 1;
  }
}

void boot_reversibly(uint64_t megabytes) {
  // prepare current_context to run the loaded RISC-R binary

  reset_interpreter();
  reset_profiler();
  reset_reversible_registers_profile();
  reset_microkernel();

  init_memory(megabytes);

  reset_tapes();

  current_context = create_context(MY_CONTEXT, 0);

  // assert: number_of_remaining_arguments() > 0

  boot_loader(current_context);
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

uint64_t* reversible_switch(uint64_t* to_context, uint64_t timeout) {
  // unlike mipster_switch, a6 is left alone: registers are part of
  // the reversible state, and context switching is unsupported

  restore_context(to_context);

  current_context = to_context;

  timer = timeout;

  run_reversibly_until_exception();

  save_context(current_context);

  return current_context;
}

uint64_t handle_reversible_system_call(uint64_t* context) {
  uint64_t a7;

  set_exception(context, EXCEPTION_NOEXCEPTION);

  set_ec_syscall(context, get_ec_syscall(context) + 1);

  a7 = *(get_regs(context) + REG_A7);

  // RISC-R: system calls act on tapes and add results into a0, see riscr.md

  if (a7 == SYSCALL_READ)
    implement_reversible_read(context);
  else if (a7 == SYSCALL_WRITE)
    implement_reversible_write(context);
  else if (a7 == SYSCALL_OPENAT)
    implement_reversible_openat(context);
  else if (a7 == SYSCALL_BRK)
    implement_reversible_brk(context);
  else if (a7 == SYSCALL_EXIT) {
    implement_reversible_exit(context);

    return EXIT;
  } else {
    printf("%s: system call %lu is not reversible\n", selfie_name, a7);

    set_exit_code(context, EXITCODE_UNSUPPORTEDSYSCALL);

    return EXIT;
  }

  return DONOTEXIT;
}

uint64_t handle_reversible_exception(uint64_t* context) {
  uint64_t exception;

  exception = get_exception(context);

  if (exception == EXCEPTION_SYSCALL)
    return handle_reversible_system_call(context);
  else if (exception == EXCEPTION_IRREVERSIBLEINSTRUCTION) {
    printf("%s: context %s threw uncaught exception: ", selfie_name, get_name(context));
    print_exception(exception, get_fault(context));
    printf(" at address 0x%08lX\n", get_fault(context));

    set_exit_code(context, EXITCODE_UNCAUGHTEXCEPTION);

    return EXIT;
  } else
    // page faults, division by zero, timer, and all other exceptions as in mipster
    return handle_exception(context);
}

uint64_t riscr(uint64_t* to_context) {
  uint64_t* from_context;

  // execute RISC-R code forward until it exits

  reverse = 0;

  while (1) {
    from_context = reversible_switch(to_context, TIMESLICE);

    if (handle_reversible_exception(from_context) == EXIT)
      return get_exit_code(from_context);
    else
      to_context = from_context;
  }
}

uint64_t riscr_backward(uint64_t* to_context, uint64_t steps) {
  uint64_t timeout;
  uint64_t executed;
  uint64_t* from_context;

  // execute steps instructions backward, see riscr.md

  reverse = 1;

  while (steps > 0) {
    if (steps < TIMESLICE)
      timeout = steps;
    else
      timeout = TIMESLICE;

    executed = get_total_number_of_instructions();

    from_context = reversible_switch(to_context, timeout);

    executed = get_total_number_of_instructions() - executed;

    if (executed < steps)
      steps = steps - executed;
    else
      steps = 0;

    if (handle_reversible_exception(from_context) == EXIT) {
      reverse = 0;

      return get_exit_code(from_context);
    } else
      to_context = from_context;
  }

  reverse = 0;

  return get_exit_code(to_context);
}

uint64_t selfie_run_reversibly() {
  uint64_t backward;
  uint64_t exit_code;
  uint64_t steps;

  if (string_compare(argument, "-m"))
    backward = 0;
  else if (string_compare(argument, "-rev"))
    backward = 1;
  else
    return EXITCODE_BADARGUMENTS;

  if (code_size == 0) {
    printf("%s: nothing to run\n", selfie_name);

    return EXITCODE_BADARGUMENTS;
  } else if ((e_flags / EF_RISCR) % 2 == 0) {
    printf("%s: %s is not a RISC-R binary\n", selfie_name, binary_name);

    return EXITCODE_BADARGUMENTS;
  }

  init_reversible_interpreter();

  boot_reversibly(atoi(peek_argument(0)));

  // current_context is ready to run

  run = 1;

  printf("%s: %lu-bit riscr executing %lu-bit RISC-R binary %s with %luMB physical memory", selfie_name,
    SIZEOFUINT64INBITS,
    WORDSIZEINBITS,
    binary_name,
    PHYSICALMEMORYSIZE / MEGABYTE);

  if (backward)
    printf(", forward and then backward");

  printf("\n%s: >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\n", selfie_name);

  exit_code = riscr(current_context);

  printf("\n%s: <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<\n", selfie_name);

  printf("%s: %lu-bit riscr terminating %lu-bit RISC-R binary %s with exit code %ld\n", selfie_name,
    SIZEOFUINT64INBITS,
    WORDSIZEINBITS,
    binary_name,
    sign_extend(exit_code, SYSCALL_BITWIDTH));

  if (backward) {
    if (get_exception(current_context) == EXCEPTION_NOEXCEPTION) {
      // undo all executed instructions but the exit system call
      steps = get_total_number_of_instructions() - 1;

      printf("%s: %lu-bit riscr executing %lu instructions backward\n", selfie_name,
        SIZEOFUINT64INBITS,
        steps);

      riscr_backward(current_context, steps);

      printf("%s: %lu-bit riscr terminating backward execution at pc==0x%lX\n", selfie_name,
        SIZEOFUINT64INBITS,
        get_pc(current_context));
    } else
      printf("%s: not executing backward after uncaught exception\n", selfie_name);
  }

  print_profile();

  run = 0;

  printf("%s: ################################################################################\n", selfie_name);

  return exit_code;
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

int main(int argc, char** argv) {
  uint64_t exit_code;

  init_selfie((uint64_t) argc, (uint64_t*) argv);

  init_library();
  init_system();
  init_target();
  init_kernel();

  exit_code = selfie(1);

  if (exit_code == EXITCODE_MOREARGUMENTS)
    exit_code = selfie_run_reversibly();

  return exit_selfie(exit_code, " [ ( -m | -rev ) 0-4096 ... ]");
}
