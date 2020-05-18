/*

TODO: Merge this with the comment below:

The `-se` and `-mc` options invoke the monster model generator.
With option `-se`, monster generates an SMT-LIB file named after
the given binary but with extension `.smt`. The `0-4096` value
is interpreted as bound on the length of any symbolically
executed code branch in number of instructions. Value `0` means
that the code is executed symbolically without a bound.
With option `-mc`, monster generates a BTOR2 file named after
the executed binary but with extension `.btor2`. The `0-4096`
value is interpreted as exit code. Value `0` means that
any code execution that terminates with a non-zero exit code
is seen as erroneous whereas a non-zero value means that
any code execution that terminates with a different exit code
is seen as erroneous.

*/

/*
Copyright (c) 2015-2020, the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

http://selfie.cs.uni-salzburg.at

The Selfie Project provides an educational platform for teaching
undergraduate and graduate students the design and implementation
of programming languages and runtime systems. The focus is on the
construction of compilers, libraries, operating systems, and even
virtual machine monitors. The common theme is to identify and
resolve self-reference in systems code which is seen as the key
challenge when teaching systems engineering, hence the name.

Selfie is a self-contained 64-bit, 12-KLOC C implementation of:

1. a self-compiling compiler called starc that compiles
   a tiny but still fast subset of C called C Star (C*) to
   a tiny and easy-to-teach subset of RISC-V called RISC-U,
2. a self-executing emulator called mipster that executes
   RISC-U code including itself when compiled with starc,
3. a self-hosting hypervisor called hypster that provides
   RISC-U virtual machines that can host all of selfie,
   that is, starc, mipster, and hypster itself,
4. a self-translating modeling engine called monster that
   translates RISC-U code including itself to SMT-LIB and
   BTOR2 formulae that are satisfiable if and only if
   there is input to the code such that the code exits
   with non-zero exit codes, performs division by zero, or
   accesses memory outside of allocated memory blocks, and
5. a tiny C* library called libcstar utilized by selfie.

Selfie is implemented in a single (!) file and kept minimal for simplicity.
There is also a simple in-memory linker, a RISC-U disassembler, a profiler,
and a debugger with replay as well as minimal operating system support in
the form of RISC-V system calls built into the emulator and hypervisor.

C* is a tiny Turing-complete subset of C that includes dereferencing
(the * operator) but excludes composite data types, bitwise and Boolean
operators, and many other features. There are only unsigned 64-bit
integers and 64-bit pointers as well as character and string literals.
This choice turns out to be helpful for students to understand the
true role of composite data types such as arrays and records.
Bitwise operations are implemented in libcstar using unsigned integer
arithmetics helping students better understand arithmetic operators.
C* is supposed to be close to the minimum necessary for implementing
a self-compiling, single-pass, recursive-descent compiler. C* can be
taught in one to two weeks of classes depending on student background.

The compiler can readily be extended to compile features missing in C*
and to improve performance of the generated code. The compiler generates
RISC-U executables in ELF format that are compatible with the official
RISC-V toolchain. The mipster emulator can execute RISC-U executables
loaded from file but also from memory immediately after code generation
without going through the file system.

RISC-U is a tiny Turing-complete subset of the RISC-V instruction set.
It only features unsigned 64-bit integer arithmetic, double-word memory,
and simple control-flow instructions but neither bitwise nor byte- and
word-level instructions. RISC-U can be taught in one week of classes.

The emulator implements minimal operating system support that is meant
to be extended by students, first as part of the emulator, and then
ported to run on top of it, similar to an actual operating system or
virtual machine monitor. The fact that the emulator can execute itself
helps exposing the self-referential nature of that challenge. In fact,
selfie goes one step further by implementing microkernel functionality
as part of the emulator and a hypervisor that can run as part of the
emulator as well as on top of it, all with the same code.

The modeling engine implements a simple yet sound and complete
translation of RISC-U code to SMT-LIB and BTOR2 formulae, and
facilitates teaching the absolute basics of SAT and SMT solving
applied to real code.

Selfie is the result of many years of teaching systems engineering.
The design of the compiler is inspired by the Oberon compiler of
Professor Niklaus Wirth from ETH Zurich. RISC-U is inspired by the
RISC-V community around Professor David Patterson from UC Berkeley.
The design of the hypervisor is inspired by microkernels of Professor
Jochen Liedtke from University of Karlsruhe. The modeling engine is
inspired by Professor Armin Biere from JKU Linz.
*/

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     L I B R A R Y     ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------ SYMBOLIC MEMORY ------------------------
// -----------------------------------------------------------------

uint64_t* load_symbolic_memory(uint64_t vaddr);
void      store_symbolic_memory(uint64_t vaddr, uint64_t val, char* sym, char* var, uint64_t bits);
uint64_t* find_word_in_unshared_symbolic_memory(uint64_t vaddr);
void      update_begin_of_shared_symbolic_memory(uint64_t* context);

uint64_t is_symbolic_value(uint64_t* sword);

void print_symbolic_memory(uint64_t* sword);

// symbolic memory word struct:
// +---+-----------+
// | 0 | next word | pointer to next memory word
// | 1 | address   | address of memory word
// | 2 | value     | concrete value of memory word
// | 3 | symbolic  | symbolic value of memory word
// | 4 | bits      | number of bits in bit vector
// +---+-----------+

uint64_t* allocate_symbolic_memory_word() {
  return smalloc(2 * SIZEOFUINT64STAR + 3 * SIZEOFUINT64);
}

uint64_t* get_next_word(uint64_t* word)      { return (uint64_t*) *word; }
uint64_t  get_word_address(uint64_t* word)   { return             *(word + 1); }
uint64_t  get_word_value(uint64_t* word)     { return             *(word + 2); }
char*     get_word_symbolic(uint64_t* word)  { return (char*)     *(word + 3); }
uint64_t  get_number_of_bits(uint64_t* word) { return             *(word + 4); }

void set_next_word(uint64_t* word, uint64_t* next)      { *word       = (uint64_t) next; }
void set_word_address(uint64_t* word, uint64_t address) { *(word + 1) =            address; }
void set_word_value(uint64_t* word, uint64_t value)     { *(word + 2) =            value; }
void set_word_symbolic(uint64_t* word, char* sym)       { *(word + 3) = (uint64_t) sym; }
void set_number_of_bits(uint64_t* word, uint64_t bits)  { *(word + 4) =            bits; }

// -----------------------------------------------------------------
// ------------------- SYMBOLIC EXECUTION ENGINE -------------------
// -----------------------------------------------------------------

char* bv_constant(uint64_t value);
char* bv_variable(uint64_t bits);
char* bv_zero_extension(uint64_t bits);

char* smt_value(uint64_t val, char* sym);
char* smt_variable(char* prefix, uint64_t bits);

char* smt_unary(char* opt, char* op);
char* smt_binary(char* opt, char* op1, char* op2);
char* smt_ternary(char* opt, char* op1, char* op2, char* op3);

uint64_t  find_merge_location(uint64_t beq_imm);

void      add_mergeable_context(uint64_t* context);
uint64_t* get_mergeable_context();

void      add_waiting_context(uint64_t* context);
uint64_t* get_waiting_context();

void      merge(uint64_t* active_context, uint64_t* mergeable_context, uint64_t location);
void      merge_symbolic_memory_and_registers(uint64_t* active_context, uint64_t* mergeable_context);
void      merge_symbolic_memory_of_active_context(uint64_t* active_context, uint64_t* mergeable_context);
void      merge_symbolic_memory_of_mergeable_context(uint64_t* active_context, uint64_t* mergeable_context);
void      merge_registers(uint64_t* active_context, uint64_t* mergeable_context);
uint64_t* merge_if_possible_and_get_next_context(uint64_t* context);

void      push_onto_call_stack(uint64_t* context, uint64_t address);
uint64_t  pop_off_call_stack(uint64_t* context);
uint64_t  compare_call_stacks(uint64_t* active_context, uint64_t* mergeable_context);

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t max_execution_depth = 1; // in number of instructions, unbounded with 0

uint64_t variable_version = 0; // generates unique SMT-LIB variable names

uint64_t* symbolic_contexts = (uint64_t*) 0;

char* path_condition = (char*) 0;

uint64_t* symbolic_memory = (uint64_t*) 0;

uint64_t* reg_sym = (uint64_t*) 0; // symbolic values in registers as strings in SMT-LIB format

char*    smt_name = (char*) 0; // name of SMT-LIB file
uint64_t smt_fd   = 0;         // file descriptor of open SMT-LIB file

uint64_t merge_enabled  = 0; // enable or disable the merging of paths
uint64_t debug_merge    = 0; // enable or disable the debugging of merging in monster

uint64_t* mergeable_contexts                          = (uint64_t*) 0; // contexts that have reached their merge location
uint64_t* waiting_contexts                            = (uint64_t*) 0; // contexts that were created at a symbolic beq instruction and are waiting to be executed

uint64_t* current_mergeable_context                   = (uint64_t*) 0; // current context with which the active context can possibly be merged

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t DELETED                         = -1; // indicates that a symbolic memory word has been deleted
uint64_t MERGED                          = -2; // indicates that a symbolic memory word has been merged
uint64_t BEGIN_OF_SHARED_SYMBOLIC_MEMORY = -3; // indicates the beginning of the shared symbolic memory space

uint64_t beq_limit = 35; // limit of symbolic beq instructions on each part of the path between two merge locations

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void init_interpreter();
void reset_interpreter();
void reset_profiler();

void     print_register_hexadecimal(uint64_t reg);
void     print_register_octal(uint64_t reg);
uint64_t is_system_register(uint64_t reg);
void     print_register_value(uint64_t reg);

void print_exception(uint64_t exception, uint64_t faulting_page);
void throw_exception(uint64_t exception, uint64_t faulting_page);

void fetch();
void decode();
void execute();

void execute_symbolically();

void interrupt();

void run_until_exception();

uint64_t instruction_with_max_counter(uint64_t* counters, uint64_t max);
uint64_t print_per_instruction_counter(uint64_t total, uint64_t* counters, uint64_t max);
void     print_per_instruction_profile(char* message, uint64_t total, uint64_t* counters);

void print_profile();

// ------------------------ GLOBAL CONSTANTS -----------------------

// exceptions

uint64_t EXCEPTION_MERGE              = 7;
uint64_t EXCEPTION_RECURSION          = 8;

uint64_t model_check         = 0; // flag for model checking code
uint64_t check_block_access  = 0; // flag for checking memory access validity on malloced block level

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- CONTEXTS ---------------------------
// -----------------------------------------------------------------

void      copy_call_stack(uint64_t* from_context, uint64_t* to_context);
uint64_t* copy_context(uint64_t* original, uint64_t location, char* condition);

// symbolic extension:
// +----+-----------------+
// | 17 | execution depth | number of executed instructions
// | 18 | path condition  | pointer to path condition
// | 19 | symbolic memory | pointer to symbolic memory
// | 20 | symbolic regs   | pointer to symbolic registers
// | 21 | beq counter     | number of executed symbolic beq instructions
// | 22 | merge location  | program location at which the context can possibly be merged (later)
// | 23 | merge partner   | pointer to the context from which this context was created
// | 24 | call stack      | pointer to a list containing the addresses of the procedures on the call stack
// +----+-----------------+

uint64_t* allocate_symbolic_context() {
  return smalloc(7 * SIZEOFUINT64STAR + 10 * SIZEOFUINT64 + 5 * SIZEOFUINT64STAR + 3 * SIZEOFUINT64);
}

uint64_t  get_execution_depth(uint64_t* context) { return             *(context + 17); }
char*     get_path_condition(uint64_t* context)  { return (char*)     *(context + 18); }
uint64_t* get_symbolic_memory(uint64_t* context) { return (uint64_t*) *(context + 19); }
uint64_t* get_symbolic_regs(uint64_t* context)   { return (uint64_t*) *(context + 20); }
uint64_t  get_beq_counter(uint64_t* context)     { return             *(context + 21); }
uint64_t  get_merge_location(uint64_t* context)  { return             *(context + 22); }
uint64_t* get_merge_partner(uint64_t* context)   { return (uint64_t*) *(context + 23); }
uint64_t* get_call_stack(uint64_t* context)      { return (uint64_t*) *(context + 24); }

void set_execution_depth(uint64_t* context, uint64_t depth)    { *(context + 17) =            depth; }
void set_path_condition(uint64_t* context, char* path)         { *(context + 18) = (uint64_t) path; }
void set_symbolic_memory(uint64_t* context, uint64_t* memory)  { *(context + 19) = (uint64_t) memory; }
void set_symbolic_regs(uint64_t* context, uint64_t* regs)      { *(context + 20) = (uint64_t) regs; }
void set_beq_counter(uint64_t* context, uint64_t counter)      { *(context + 21) =            counter; }
void set_merge_location(uint64_t* context, uint64_t location)  { *(context + 22) =            location; }
void set_merge_partner(uint64_t* context, uint64_t* partner)   { *(context + 23) = (uint64_t) partner; }
void set_call_stack(uint64_t* context, uint64_t* stack)        { *(context + 24) = (uint64_t) stack; }

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

uint64_t handle_system_call(uint64_t* context);
uint64_t handle_page_fault(uint64_t* context);
uint64_t handle_division_by_zero(uint64_t* context);
uint64_t handle_timer(uint64_t* context);
uint64_t handle_merge(uint64_t* context);
uint64_t handle_recursion(uint64_t* context);

uint64_t handle_exception(uint64_t* context);

char*    replace_extension(char* filename, char* extension);
uint64_t monster(uint64_t* to_context);

uint64_t selfie_run(uint64_t machine);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t MERGE     = 2;
uint64_t RECURSION = 3;

uint64_t EXITCODE_SYMBOLICEXECUTIONERROR = 12;
uint64_t EXITCODE_MODELCHECKINGERROR     = 13;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emit_exit() {
  create_symbol_table_entry(LIBRARY_TABLE, "exit", 0, PROCEDURE, VOID_T, 0, binary_length);

  // load signed 32-bit integer exit code
  emit_ld(REG_A0, REG_SP, 0);

  // remove the exit code from the stack
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  // load the correct syscall number and invoke syscall
  emit_addi(REG_A7, REG_ZR, SYSCALL_EXIT);

  emit_ecall();

  // never returns here
}

void implement_exit(uint64_t* context) {
  // parameter;
  uint64_t signed_int_exit_code;

  if (debug_syscalls) {
    print("(exit): ");
    print_register_hexadecimal(REG_A0);
    print(" |- ->\n");
  }

  signed_int_exit_code = *(get_regs(context) + REG_A0);

  set_exit_code(context, sign_shrink(signed_int_exit_code, SYSCALL_BITWIDTH));

  if (symbolic) {
    print("\n(push 1)\n");

    printf2("(assert (and %s (not (= %s (_ bv0 64))))); exit in ",
      path_condition,
      smt_value(*(registers + REG_A0), (char*) *(reg_sym + REG_A0)));
    print_code_context_for_instruction(pc);

    if (debug_merge)
      printf1(" -> exiting context: %d", (char*) context);

    print("\n(check-sat)\n(get-model)\n(pop 1)\n");

    return;
  }

  printf4("%s: %s exiting with exit code %d and %.2dMB mallocated memory\n", selfie_name,
    get_name(context),
    (char*) sign_extend(get_exit_code(context), SYSCALL_BITWIDTH),
    (char*) fixed_point_ratio(get_program_break(context) - get_original_break(context), MEGABYTE, 2));
}

void emit_read() {
  create_symbol_table_entry(LIBRARY_TABLE, "read", 0, PROCEDURE, UINT64_T, 0, binary_length);

  emit_ld(REG_A2, REG_SP, 0); // size
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A1, REG_SP, 0); // *buffer
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A0, REG_SP, 0); // fd
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_addi(REG_A7, REG_ZR, SYSCALL_READ);

  emit_ecall();

  // jump back to caller, return value is in REG_A0
  emit_jalr(REG_ZR, REG_RA, 0);
}

void implement_read(uint64_t* context) {
  // parameters
  uint64_t fd;
  uint64_t vbuffer;
  uint64_t size;

  // local variables
  uint64_t read_total;
  uint64_t bytes_to_read;
  uint64_t failed;
  uint64_t* buffer;
  uint64_t actually_read;

  if (debug_syscalls) {
    print("(read): ");
    print_register_value(REG_A0);
    print(",");
    print_register_hexadecimal(REG_A1);
    print(",");
    print_register_value(REG_A2);
    print(" |- ");
    print_register_value(REG_A0);
  }

  fd      = *(get_regs(context) + REG_A0);
  vbuffer = *(get_regs(context) + REG_A1);
  size    = *(get_regs(context) + REG_A2);

  if (debug_read)
    printf4("%s: trying to read %d bytes from file with descriptor %d into buffer at virtual address %p\n", selfie_name,
      (char*) size,
      (char*) fd,
      (char*) vbuffer);

  read_total = 0;

  bytes_to_read = SIZEOFUINT64;

  failed = 0;

  while (size > 0) {
    if (is_valid_virtual_address(vbuffer)) {
      if (size < bytes_to_read)
        bytes_to_read = size;

      if (symbolic) {
        store_symbolic_memory(vbuffer,
          0,
          0,
          smt_variable("i", bytes_to_read * 8),
          bytes_to_read * 8);

        // save symbolic memory here since context switching has already happened
        set_symbolic_memory(context, symbolic_memory);

        actually_read = bytes_to_read;
      } else if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
        buffer = tlb(get_pt(context), vbuffer);

        actually_read = sign_extend(read(fd, buffer, bytes_to_read), SYSCALL_BITWIDTH);
      } else {
        failed = 1;

        size = 0;

        if (debug_read)
          printf2("%s: reading into virtual address %p failed because the address is unmapped\n", selfie_name,
            (char*) vbuffer);
      }

      if (failed == 0) {
        if (actually_read == bytes_to_read) {
          read_total = read_total + actually_read;

          size = size - actually_read;

          if (size > 0)
            vbuffer = vbuffer + SIZEOFUINT64;
        } else {
          if (signed_less_than(0, actually_read))
            read_total = read_total + actually_read;

          size = 0;
        }
      }
    } else {
      failed = 1;

      size = 0;

      if (debug_read)
        printf2("%s: reading into virtual address %p failed because the address is invalid\n", selfie_name,
          (char*) vbuffer);
    }
  }

  if (failed)
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);
  else
    *(get_regs(context) + REG_A0) = read_total;

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);

  if (debug_read)
    printf3("%s: actually read %d bytes from file with descriptor %d\n", selfie_name,
      (char*) read_total,
      (char*) fd);

  if (debug_syscalls) {
    print(" -> ");
    print_register_value(REG_A0);
    println();
  }
}

void emit_write() {
  create_symbol_table_entry(LIBRARY_TABLE, "write", 0, PROCEDURE, UINT64_T, 0, binary_length);

  emit_ld(REG_A2, REG_SP, 0); // size
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A1, REG_SP, 0); // *buffer
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A0, REG_SP, 0); // fd
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_addi(REG_A7, REG_ZR, SYSCALL_WRITE);

  emit_ecall();

  emit_jalr(REG_ZR, REG_RA, 0);
}

void implement_write(uint64_t* context) {
  // parameters
  uint64_t fd;
  uint64_t vbuffer;
  uint64_t size;

  // local variables
  uint64_t written_total;
  uint64_t bytes_to_write;
  uint64_t failed;
  uint64_t* buffer;
  uint64_t actually_written;

  if (debug_syscalls) {
    print("(write): ");
    print_register_value(REG_A0);
    print(",");
    print_register_hexadecimal(REG_A1);
    print(",");
    print_register_value(REG_A2);
    print(" |- ");
    print_register_value(REG_A0);
  }

  fd      = *(get_regs(context) + REG_A0);
  vbuffer = *(get_regs(context) + REG_A1);
  size    = *(get_regs(context) + REG_A2);

  if (debug_write)
    printf4("%s: trying to write %d bytes from buffer at virtual address %p into file with descriptor %d\n", selfie_name,
      (char*) size,
      (char*) vbuffer,
      (char*) fd);

  written_total = 0;

  bytes_to_write = SIZEOFUINT64;

  failed = 0;

  while (size > 0) {
    if (is_valid_virtual_address(vbuffer)) {
      if (symbolic) {
        // TODO: What should symbolically executed code actually output?
        written_total = size;

        size = 0;
      } else if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
        buffer = tlb(get_pt(context), vbuffer);

        if (size < bytes_to_write)
          bytes_to_write = size;

        actually_written = sign_extend(write(fd, buffer, bytes_to_write), SYSCALL_BITWIDTH);

        if (actually_written == bytes_to_write) {
          written_total = written_total + actually_written;

          size = size - actually_written;

          if (size > 0)
            vbuffer = vbuffer + SIZEOFUINT64;
        } else {
          if (signed_less_than(0, actually_written))
            written_total = written_total + actually_written;

          size = 0;
        }
      } else {
        failed = 1;

        size = 0;

        if (debug_write)
          printf2("%s: writing into virtual address %p failed because the address is unmapped\n", selfie_name,
            (char*) vbuffer);
      }
    } else {
      failed = 1;

      size = 0;

      if (debug_write)
        printf2("%s: writing into virtual address %p failed because the address is invalid\n", selfie_name,
          (char*) vbuffer);
    }
  }

  if (failed)
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);
  else
    *(get_regs(context) + REG_A0) = written_total;

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);

  if (debug_write)
    printf3("%s: actually wrote %d bytes into file with descriptor %d\n", selfie_name,
      (char*) written_total,
      (char*) fd);

  if (debug_syscalls) {
    print(" -> ");
    print_register_value(REG_A0);
    println();
  }
}

void emit_open() {
  create_symbol_table_entry(LIBRARY_TABLE, "open", 0, PROCEDURE, UINT64_T, 0, binary_length);

  emit_ld(REG_A3, REG_SP, 0); // mode
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A2, REG_SP, 0); // flags
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A1, REG_SP, 0); // filename
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  // DIRFD_AT_FDCWD makes sure that openat behaves like open
  emit_addi(REG_A0, REG_ZR, DIRFD_AT_FDCWD);

  emit_addi(REG_A7, REG_ZR, SYSCALL_OPENAT);

  emit_ecall();

  emit_jalr(REG_ZR, REG_RA, 0);
}

uint64_t down_load_string(uint64_t* table, uint64_t vaddr, char* s) {
  uint64_t i;
  uint64_t* sword;
  uint64_t j;

  i = 0;

  while (i < MAX_FILENAME_LENGTH / SIZEOFUINT64) {
    if (is_valid_virtual_address(vaddr)) {
      if (symbolic) {
        sword = load_symbolic_memory(vaddr);

        if (sword) {
          if (is_symbolic_value(sword)) {
            printf1("%s: detected symbolic value ", selfie_name);
            print_symbolic_memory(sword);
            print(" in filename of open call\n");

            exit(EXITCODE_SYMBOLICEXECUTIONERROR);
          } else
            // CAUTION: at boot levels higher than zero, s is only accessible
            // in C* at machine word granularity, not individual characters
            *((uint64_t*) s + i) = get_word_value(sword);
        } else
          // assert: vaddr is mapped
          *((uint64_t*) s + i) = load_virtual_memory(table, vaddr);
      } else if (is_virtual_address_mapped(table, vaddr))
        *((uint64_t*) s + i) = load_virtual_memory(table, vaddr);
      else {
        if (debug_open)
          printf2("%s: opening file with name at virtual address %p failed because the address is unmapped\n", selfie_name,
            (char*) vaddr);

        return 0;
      }

      j = 0;

      // check if string ends in the current machine word
      while (j < SIZEOFUINT64) {
        if (load_character((char*) ((uint64_t*) s + i), j) == 0)
          return 1;

        j = j + 1;
      }

      // advance to the next machine word in virtual memory
      vaddr = vaddr + SIZEOFUINT64;

      // advance to the next machine word in our memory
      i = i + 1;
    } else {
      if (debug_open)
        printf2("%s: opening file with name at virtual address %p failed because the address is invalid\n", selfie_name,
          (char*) vaddr);

      return 0;
    }
  }

  return 0;
}

void implement_openat(uint64_t* context) {
  // parameters
  uint64_t vfilename;
  uint64_t flags;
  uint64_t mode;

  // return value
  uint64_t fd;

  if (debug_syscalls) {
    print("(openat): ");
    print_register_hexadecimal(REG_A0);
    print(",");
    print_register_hexadecimal(REG_A1);
    print(",");
    print_register_hexadecimal(REG_A2);
    print(",");
    print_register_octal(REG_A3);
    print(" |- ");
    print_register_value(REG_A1);
  }

  /* We actually emulate the part of the openat system call here that is
     implemented by the open system call which is deprecated in Linux.
     In particular, the first parameter (REG_A0) is ignored here while
     set to DIRFD_AT_FDCWD in the wrapper for the open library call to
     make sure openat behaves like open when bootstrapping selfie. */

  vfilename = *(get_regs(context) + REG_A1);
  flags     = *(get_regs(context) + REG_A2);
  mode      = *(get_regs(context) + REG_A3);

  if (down_load_string(get_pt(context), vfilename, filename_buffer)) {
    if (symbolic)
      // TODO: check if opening vfilename has been attempted before
      fd = 0;
    else
      fd = sign_extend(open(filename_buffer, flags, mode), SYSCALL_BITWIDTH);

    *(get_regs(context) + REG_A0) = fd;

    if (debug_open)
      printf5("%s: opened file %s with flags %x and mode %o returning file descriptor %d\n", selfie_name,
        filename_buffer,
        (char*) flags,
        (char*) mode,
        (char*) fd);
  } else {
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);

    if (debug_open)
      printf2("%s: opening file with name at virtual address %p failed because the name is too long\n", selfie_name,
        (char*) vfilename);
  }

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);

  if (debug_syscalls) {
    print(" -> ");
    print_register_value(REG_A0);
    println();
  }
}

void emit_malloc() {
  uint64_t* entry;

  create_symbol_table_entry(LIBRARY_TABLE, "malloc", 0, PROCEDURE, UINT64STAR_T, 0, binary_length);

  // on boot levels higher than zero, zalloc falls back to malloc
  // assuming that page frames are zeroed on boot level zero
  create_symbol_table_entry(LIBRARY_TABLE, "zalloc", 0, PROCEDURE, UINT64STAR_T, 0, binary_length);

  // allocate memory in data segment for recording state of
  // malloc (bump pointer) in compiler-declared global variable
  allocated_memory = allocated_memory + REGISTERSIZE;

  // define global variable _bump for storing malloc's bump pointer
  // copy "_bump" string into zeroed double word to obtain unique hash
  create_symbol_table_entry(GLOBAL_TABLE, string_copy("_bump"), 1, VARIABLE, UINT64_T, 0, -allocated_memory);

  // do not account for _bump as global variable
  number_of_global_variables = number_of_global_variables - 1;

  entry = search_global_symbol_table(string_copy("_bump"), VARIABLE);

  // allocate register for size parameter
  talloc();

  emit_ld(current_temporary(), REG_SP, 0); // size
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  // round up size to double-word alignment
  emit_round_up(current_temporary(), SIZEOFUINT64);

  // allocate register to compute new bump pointer
  talloc();

  // assert: current temporary is $t1 register to enable propagation of
  // lower and upper bounds on addresses in model generation of brk syscall

  // get current _bump which will be returned upon success
  emit_ld(current_temporary(), get_scope(entry), get_address(entry));

  // call brk syscall to set new program break to _bump + size
  emit_add(REG_A0, current_temporary(), previous_temporary());
  emit_addi(REG_A7, REG_ZR, SYSCALL_BRK);
  emit_ecall();

  // return 0 if memory allocation failed, that is,
  // if new program break is still _bump and size != 0
  emit_beq(REG_A0, current_temporary(), 2 * INSTRUCTIONSIZE);
  emit_beq(REG_ZR, REG_ZR, 4 * INSTRUCTIONSIZE);
  emit_beq(REG_ZR, previous_temporary(), 3 * INSTRUCTIONSIZE);
  emit_addi(REG_A0, REG_ZR, 0);
  emit_beq(REG_ZR, REG_ZR, 3 * INSTRUCTIONSIZE);

  // if memory was successfully allocated
  // set _bump to new program break
  // and then return original _bump
  emit_sd(get_scope(entry), get_address(entry), REG_A0);
  emit_addi(REG_A0, current_temporary(), 0);

  tfree(2);

  emit_jalr(REG_ZR, REG_RA, 0);
}

void implement_brk(uint64_t* context) {
  // parameter
  uint64_t program_break;

  // local variables
  uint64_t previous_program_break;
  uint64_t valid;

  if (debug_syscalls) {
    print("(brk): ");
    print_register_hexadecimal(REG_A0);
  }

  program_break = *(get_regs(context) + REG_A0);

  previous_program_break = get_program_break(context);

  valid = 0;

  if (program_break >= previous_program_break)
    if (program_break < *(get_regs(context) + REG_SP))
      if (program_break % SIZEOFUINT64 == 0)
        valid = 1;

  if (valid) {
    if (debug_syscalls)
      print(" |- ->\n");

    if (debug_brk)
      printf2("%s: setting program break to %p\n", selfie_name, (char*) program_break);

    set_program_break(context, program_break);
  } else {
    // error returns current program break
    program_break = previous_program_break;

    if (debug_brk)
      printf2("%s: retrieving current program break %p\n", selfie_name, (char*) program_break);

    if (debug_syscalls) {
      print(" |- ");
      print_register_hexadecimal(REG_A0);
    }

    *(get_regs(context) + REG_A0) = program_break;

    if (debug_syscalls) {
      print(" -> ");
      print_register_hexadecimal(REG_A0);
      println();
    }
  }

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

// -----------------------------------------------------------------
// ----------------------- HYPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emit_switch() {
  create_symbol_table_entry(LIBRARY_TABLE, "hypster_switch", 0, PROCEDURE, UINT64STAR_T, 0, binary_length);

  emit_ld(REG_A1, REG_SP, 0); // number of instructions to execute
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A0, REG_SP, 0); // context to which we switch
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_addi(REG_A7, REG_ZR, SYSCALL_SWITCH);

  emit_ecall();

  // save context from which we are switching here in return register
  emit_addi(REG_A0, REG_A6, 0);

  emit_jalr(REG_ZR, REG_RA, 0);
}

uint64_t* do_switch(uint64_t* from_context, uint64_t* to_context, uint64_t timeout) {
  restore_context(to_context);

  // restore machine state
  pc        = get_pc(to_context);
  registers = get_regs(to_context);
  pt        = get_pt(to_context);

  if (symbolic) {
    path_condition  = get_path_condition(to_context);
    symbolic_memory = get_symbolic_memory(to_context);
    reg_sym         = get_symbolic_regs(to_context);
  }

  // use REG_A6 instead of REG_A0 for returning from_context
  // to avoid overwriting REG_A0 in to_context
  if (get_parent(from_context) != MY_CONTEXT)
    *(registers + REG_A6) = (uint64_t) get_virtual_context(from_context);
  else
    *(registers + REG_A6) = (uint64_t) from_context;

  timer = timeout;

  if (debug_switch) {
    printf3("%s: switched from context %p to context %p", selfie_name,
      (char*) from_context,
      (char*) to_context);
    if (timer != TIMEROFF)
      printf1(" to execute %d instructions", (char*) timer);
    println();
  }

  return to_context;
}

void implement_switch() {
  // parameters
  uint64_t* to_context;
  uint64_t timeout;

  if (debug_syscalls) {
    print("(switch): ");
    print_register_hexadecimal(REG_A0);
    print(",");
    print_register_value(REG_A1);
    print(" |- ");
    print_register_value(REG_A6);
  }

  to_context = (uint64_t*) *(registers + REG_A0);
  timeout    =             *(registers + REG_A1);

  save_context(current_context);

  // cache context on my boot level before switching
  to_context = cache_context(to_context);

  current_context = do_switch(current_context, to_context, timeout);

  if (debug_syscalls) {
    print(" -> ");
    print_register_hexadecimal(REG_A6);
    println();
  }
}

uint64_t* mipster_switch(uint64_t* to_context, uint64_t timeout) {
  current_context = do_switch(current_context, to_context, timeout);

  run_until_exception();

  save_context(current_context);

  return current_context;
}

uint64_t* hypster_switch(uint64_t* to_context, uint64_t timeout) {
  // this procedure is only executed at boot level zero
  return mipster_switch(to_context, timeout);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------    A R C H I T E C T U R E    -----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

void print_code_context_for_instruction(uint64_t address) {
  if (run) {
    printf2("%s: pc=%x", binary_name, (char*) address);
    print_code_line_number_for_instruction(address, entry_point);
    if (symbolic)
      // skip further output
      return;
    else
      print(": ");
  } else {
    if (model_check) {
      printf1("%x", (char*) address);
      print_code_line_number_for_instruction(address, entry_point);
      print(": ");
    } else if (disassemble_verbose) {
      printf1("%x", (char*) address);
      print_code_line_number_for_instruction(address, 0);
      printf1(": %p: ", (char*) ir);
    }
  }
}

void constrain_lui() {
  if (rd != REG_ZR)
    *(reg_sym + rd) = 0;
}

void constrain_addi() {
  if (rd != REG_ZR) {
    if (*(reg_sym + rs1))
      *(reg_sym + rd) = (uint64_t) smt_binary("bvadd", (char*) *(reg_sym + rs1), bv_constant(imm));
    else
      *(reg_sym + rd) = 0;
  }
}

void constrain_add_sub_mul_divu_remu_sltu(char* operator) {
  char* op1;
  char* op2;

  if (rd != REG_ZR) {
    op1 = (char*) *(reg_sym + rs1);
    op2 = (char*) *(reg_sym + rs2);

    if (op1 == (char*) 0) {
      if (op2 == (char*) 0) {
        *(reg_sym + rd) = 0;

        return;
      } else
        op1 = bv_constant(*(registers + rs1));
    } else if (op2 == (char*) 0)
        op2 = bv_constant(*(registers + rs2));

    *(reg_sym + rd) = (uint64_t) smt_binary(operator, op1, op2);

    // checking for division by zero
    if (string_compare(operator, "bvudiv")) {
      print("(push 1)\n");
      printf2("(assert (and %s %s)); check if a division by zero is possible", path_condition, smt_binary("=", op2, bv_constant(0)));
      print("\n(check-sat)\n(get-model)\n(pop 1)\n");
    }
  }
}

void zero_extend_sltu() {
  if (rd != REG_ZR)
    if (*(reg_sym + rd))
      *(reg_sym + rd) = (uint64_t) smt_unary(bv_zero_extension(1), (char*) *(reg_sym + rd));
}

void constrain_ld() {
  uint64_t vaddr;
  uint64_t* sword;
  uint64_t a;

  // load double word

  if (*(reg_sym + rs1)) {
    // symbolic memory addresses not yet supported
    printf2("%s: symbolic memory address in ld instruction at %x", selfie_name, (char*) pc);
    print_code_line_number_for_instruction(pc, entry_point);
    println();

    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  vaddr = *(registers + rs1) + imm;

  if (is_valid_virtual_address(vaddr)) {
    // semantics of ld
    if (rd != REG_ZR) {
      sword = load_symbolic_memory(vaddr);

      if (sword) {
        *(registers + rd) = get_word_value(sword);

        if (get_number_of_bits(sword) < CPUBITWIDTH)
          *(reg_sym + rd) = (uint64_t) smt_unary(bv_zero_extension(get_number_of_bits(sword)), get_word_symbolic(sword));
        else
          *(reg_sym + rd) = (uint64_t) get_word_symbolic(sword);
      } else {
        // assert: vaddr is mapped
        *(registers + rd) = load_virtual_memory(pt, vaddr);
        *(reg_sym + rd)   = 0;
      }
    }

    // keep track of instruction address for profiling loads
    a = (pc - entry_point) / INSTRUCTIONSIZE;

    pc = pc + INSTRUCTIONSIZE;

    // keep track of number of loads in total
    ic_ld = ic_ld + 1;

    // and individually
    *(loads_per_instruction + a) = *(loads_per_instruction + a) + 1;
  } else
    // invalid concrete memory address
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
}

void constrain_sd() {
  uint64_t vaddr;
  uint64_t a;

  // store double word

  if (*(reg_sym + rs1)) {
    // symbolic memory addresses not yet supported
    printf2("%s: symbolic memory address in sd instruction at %x", selfie_name, (char*) pc);
    print_code_line_number_for_instruction(pc, entry_point);
    println();

    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  vaddr = *(registers + rs1) + imm;

  if (is_valid_virtual_address(vaddr)) {
    // semantics of sd
    store_symbolic_memory(vaddr,
      *(registers + rs2),
      (char*) *(reg_sym + rs2),
      0,
      CPUBITWIDTH);

    // keep track of instruction address for profiling stores
    a = (pc - entry_point) / INSTRUCTIONSIZE;

    pc = pc + INSTRUCTIONSIZE;

    // keep track of number of stores in total
    ic_sd = ic_sd + 1;

    // and individually
    *(stores_per_instruction + a) = *(stores_per_instruction + a) + 1;
  } else
    // invalid concrete memory address
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
}

void constrain_beq() {
  char* op1;
  char* op2;
  char* bvar;
  char* pvar;
  uint64_t* waiting_context;

  op1 = (char*) *(reg_sym + rs1);
  op2 = (char*) *(reg_sym + rs2);

  if (op1 == (char*) 0) {
    if (op2 == (char*) 0) {
      do_beq();

      return;
    } else
      op1 = bv_constant(*(registers + rs1));
  } else if (op2 == (char*) 0)
    op2 = bv_constant(*(registers + rs2));

  bvar = smt_variable("b", 1);

  printf2("(assert (= %s %s)); beq in ", bvar, smt_binary("bvcomp", op1, op2));
  print_code_context_for_instruction(pc);
  println();

  pvar = smt_variable("p", 1);

  printf2("(assert (= %s %s)); path condition in ", pvar, path_condition);
  print_code_context_for_instruction(pc);
  println();

  // increase the number of executed symbolic beq instructions
  set_beq_counter(current_context, get_beq_counter(current_context) + 1);

  if (get_beq_counter(current_context) < beq_limit) {
    // save symbolic memory so that it is copied correctly afterwards
    set_symbolic_memory(current_context, symbolic_memory);

    waiting_context = copy_context(current_context, pc + imm, smt_binary("and", pvar, bvar));

    // the copied context is executed later and takes the other path
    add_waiting_context(waiting_context);

    path_condition = smt_binary("and", pvar, smt_unary("not", bvar));

    // set the merge location only when merging is enabled
    if (merge_enabled)
      set_merge_location(current_context, find_merge_location(imm));

    if (debug_merge) {
      print("; a new context was created at ");
      print_code_context_for_instruction(pc);
      printf4(" -> active context: %d, waiting context: %d (merge locations: %x, %x)\n", (char*) current_context, (char*) waiting_context, (char*) get_merge_location(current_context), (char*) get_merge_location(waiting_context));
    }

    // check if a context is waiting to be merged
    if (current_mergeable_context != (uint64_t*) 0) {
      // we cannot merge with this one (yet), so we push it back onto the stack of mergeable contexts
      add_mergeable_context(current_mergeable_context);
      current_mergeable_context = (uint64_t*) 0;
    }

    pc = pc + INSTRUCTIONSIZE;
  } else
    // terminate context, if the beq_limit is reached
    throw_exception(EXCEPTION_TIMER, 0);
}

void constrain_jalr() {
  if (*(reg_sym + rs1)) {
    // symbolic memory addresses not yet supported
    printf2("%s: symbolic memory address in jalr instruction at %x", selfie_name, (char*) pc);
    print_code_line_number_for_instruction(pc, entry_point);
    println();

    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

// -----------------------------------------------------------------
// ------------------------ SYMBOLIC MEMORY ------------------------
// -----------------------------------------------------------------

uint64_t* load_symbolic_memory(uint64_t vaddr) {
  uint64_t* sword;

  sword = symbolic_memory;

  while (sword != (uint64_t*) 0) {
    if (get_word_address(sword) == vaddr)
      return sword;

    sword = get_next_word(sword);
  }

  return (uint64_t*) 0;
}

void store_symbolic_memory(uint64_t vaddr, uint64_t val, char* sym, char* var, uint64_t bits) {
  uint64_t* sword;

  // we overwrite values, if they already exist in the unshared symbolic memory space, so that there are no duplicates in any unshared symbolic memory space
  sword = find_word_in_unshared_symbolic_memory(vaddr);

  // new value in this unshared symbolic memory space
  if (sword == (uint64_t*) 0) {
    sword = allocate_symbolic_memory_word();
    set_next_word(sword, symbolic_memory);
    symbolic_memory = sword;
  }

  set_word_address(sword, vaddr);
  set_word_value(sword, val);

  if (var)
    set_word_symbolic(sword, var);
  else if (sym) {
    set_word_symbolic(sword, smt_variable("m", SIZEOFUINT64 * 8));

    printf2("(assert (= %s %s)); sd in ", get_word_symbolic(sword), sym);
    print_code_context_for_instruction(pc);
    println();
  } else
    set_word_symbolic(sword, 0);

  set_number_of_bits(sword, bits);
}

uint64_t* find_word_in_unshared_symbolic_memory(uint64_t vaddr) {
  uint64_t* sword;

  sword = get_symbolic_memory(current_context);

  while (sword) {
    if (get_word_address(sword) == BEGIN_OF_SHARED_SYMBOLIC_MEMORY)
      return (uint64_t*) 0;
    if (get_word_address(sword) == vaddr)
      return sword;

    sword = get_next_word(sword);
  }

  return (uint64_t*) 0;
}

void update_begin_of_shared_symbolic_memory(uint64_t* context) {
  uint64_t* sword;

  if (context == (uint64_t*) 0)
    return;

  sword = get_symbolic_memory(context);

  while (sword) {
    if (get_word_address(sword) == BEGIN_OF_SHARED_SYMBOLIC_MEMORY) {
      set_word_address(sword, DELETED);
      return;
    }

    sword = get_next_word(sword);
  }
}

uint64_t is_symbolic_value(uint64_t* sword) {
  return get_word_symbolic(sword) != (char*) 0;
}

void print_symbolic_memory(uint64_t* sword) {
  if (is_symbolic_value(sword))
    print(get_word_symbolic(sword));

  printf2("[%x]@%x\n", (char*) get_word_value(sword), (char*) get_word_address(sword));
}

// -----------------------------------------------------------------
// ------------------- SYMBOLIC EXECUTION ENGINE -------------------
// -----------------------------------------------------------------

char* bv_constant(uint64_t value) {
  char* string;

  string = string_alloc(5 + 20 + 4); // 64-bit numbers require up to 20 decimal digits

  sprintf1(string, "(_ bv%d 64)", (char*) value);

  return string;
}

char* bv_variable(uint64_t bits) {
  char* string;

  string = string_alloc(10 + 2); // up to 64-bit variables require up to 2 decimal digits

  sprintf1(string, "(_ BitVec %d)", (char*) bits);

  return string;
}

char* bv_zero_extension(uint64_t bits) {
  char* string;

  string = string_alloc(15 + 2); // up to 64-bit variables require up to 2 decimal digits

  sprintf1(string, "(_ zero_extend %d)", (char*) (CPUBITWIDTH - bits));

  return string;
}

char* smt_value(uint64_t val, char* sym) {
  if (sym)
    return sym;
  else
    return bv_constant(val);
}

char* smt_variable(char* prefix, uint64_t bits) {
  char* svar;

  svar = string_alloc(string_length(prefix) + 20); // 64-bit numbers require up to 20 decimal digits

  sprintf2(svar, "%s%d", prefix, (char*) variable_version);

  printf2("(declare-fun %s () (_ BitVec %d)); variable for ", svar, (char*) bits);
  print_code_context_for_instruction(pc);
  println();

  variable_version = variable_version + 1;

  return svar;
}

char* smt_unary(char* opt, char* op) {
  char* string;

  string = string_alloc(1 + string_length(opt) + 1 + string_length(op) + 1);

  sprintf2(string, "(%s %s)", opt, op);

  return string;
}

char* smt_binary(char* opt, char* op1, char* op2) {
  char* string;

  string = string_alloc(1 + string_length(opt) + 1 + string_length(op1) + 1 + string_length(op2) + 1);

  sprintf3(string, "(%s %s %s)", opt, op1, op2);

  return string;
}

char* smt_ternary(char* opt, char* op1, char* op2, char* op3) {
  char* string;

  string = string_alloc(1 + string_length(opt) + 1 + string_length(op1) + 1 + string_length(op2) + 1 + string_length(op3) + 1);

  sprintf4(string, "(%s %s %s %s)", opt, op1, op2, op3);

  return string;
}

uint64_t find_merge_location(uint64_t beq_imm) {
  uint64_t original_pc;
  uint64_t merge_location;

  // assert: the current instruction is a symbolic beq instruction
  original_pc = pc;

  // examine last instruction before target location of the beq instruction
  pc = pc + (beq_imm - INSTRUCTIONSIZE);

  // we need to know which instruction it is
  fetch();
  decode();

  if (is != JAL)
    /* no jal instruction -> end of if without else branch
       merge is directly at target location of the beq instruction possible

    note: this is a dependency on the selfie compiler */
    merge_location = original_pc + beq_imm;
  else {
    if (signed_less_than(imm, 0) == 0) {
      /* jal with positive imm -> end of if with else branch
         we have to skip the else branch in order to merge afterwards

         note: this is a dependency on the selfie compiler
         the selfie compiler emits a jal instruction with a positive immediate value if it sees an else branch */
      merge_location = pc + imm;

      pc = original_pc + INSTRUCTIONSIZE;
    } else
      /* jal with negative imm -> end of loop body
         merge is only outside of the loop body possible

         note: this is a dependency on the selfie compiler
         the selfie compiler emits a jal instruction with a negative immediate value at
         the end of the loop body in order to jump back to the loop condition */
      merge_location = pc + INSTRUCTIONSIZE;
  }

  // restore the original program state
  pc = original_pc;
  fetch();
  decode();

  return merge_location;
}

void add_mergeable_context(uint64_t* context) {
  uint64_t* entry;

  entry = smalloc(2 * SIZEOFUINT64STAR);

  *(entry + 0) = (uint64_t) mergeable_contexts;
  *(entry + 1) = (uint64_t) context;

  mergeable_contexts = entry;
}

uint64_t* get_mergeable_context() {
  uint64_t* head;

  if (mergeable_contexts == (uint64_t*) 0)
    return (uint64_t*) 0;

  head = mergeable_contexts;
  mergeable_contexts = (uint64_t*) *(head + 0);

  return (uint64_t*) *(head + 1);
}

void add_waiting_context(uint64_t* context) {
  uint64_t* entry;

  entry = smalloc(2 * SIZEOFUINT64STAR);

  *(entry + 0) = (uint64_t) waiting_contexts;
  *(entry + 1) = (uint64_t) context;

  waiting_contexts = entry;
}

uint64_t* get_waiting_context() {
  uint64_t* head;

  if (waiting_contexts == (uint64_t*) 0)
    return (uint64_t*) 0;

  head = waiting_contexts;
  waiting_contexts = (uint64_t*) *(head + 0);

  return (uint64_t*) *(head + 1);
}

void merge(uint64_t* active_context, uint64_t* mergeable_context, uint64_t location) {
  uint64_t callstack_comparison;

  // do not merge if merging is disabled
  if (merge_enabled == 0) {
    if (current_mergeable_context != (uint64_t*) 0) {
      add_mergeable_context(current_mergeable_context);
      current_mergeable_context = (uint64_t*) 0;
    }

    return;
  }

  if (active_context == mergeable_context) {
    current_mergeable_context = get_mergeable_context();

    if (current_mergeable_context != (uint64_t*) 0)
      if (pc == get_pc(current_mergeable_context))
        merge(active_context, current_mergeable_context, pc);
    return;
  }

  callstack_comparison = compare_call_stacks(active_context, mergeable_context);

  if (callstack_comparison == 2) { // mergeable context has longer call stack
    throw_exception(EXCEPTION_RECURSION, 0);
    return;
  } else if (callstack_comparison != 0) { // call stacks are not equal
    if (current_mergeable_context != (uint64_t*) 0) {
      add_mergeable_context(current_mergeable_context);
      current_mergeable_context = (uint64_t*) 0;
    }

    return;
  }

  print("; merging two contexts at ");
  print_code_context_for_instruction(location);

  if (debug_merge)
    printf2(" -> active context: %d, mergeable context: %d", (char*) active_context, (char*) mergeable_context);

  println();

  // merging the symbolic store
  merge_symbolic_memory_and_registers(active_context, mergeable_context);

  // merging the path condition
  path_condition = smt_binary("or", get_path_condition(active_context), get_path_condition(mergeable_context));
  set_path_condition(active_context, path_condition);

  if (get_execution_depth(mergeable_context) > get_execution_depth(active_context))
    set_execution_depth(active_context, get_execution_depth(mergeable_context));

  if (get_beq_counter(mergeable_context) < get_beq_counter(active_context))
    set_beq_counter(active_context, get_beq_counter(mergeable_context));

  current_mergeable_context = get_mergeable_context();

  // it may be possible that more contexts can be merged
  if (current_mergeable_context != (uint64_t*) 0)
    if (pc == get_pc(current_mergeable_context))
      if (compare_call_stacks(active_context, current_mergeable_context) != 1)
        merge(active_context, current_mergeable_context, pc);
}

void merge_symbolic_memory_and_registers(uint64_t* active_context, uint64_t* mergeable_context) {
  // merging the symbolic memory
  merge_symbolic_memory_of_active_context(active_context, mergeable_context);
  merge_symbolic_memory_of_mergeable_context(active_context, mergeable_context);

  // merging the registers
  merge_registers(active_context, mergeable_context);

  // the shared symbolic memory space needs needs to be updated since the other context was merged into the active context
  update_begin_of_shared_symbolic_memory(active_context);
}

void merge_symbolic_memory_of_active_context(uint64_t* active_context, uint64_t* mergeable_context) {
  uint64_t* sword_from_active_context;
  uint64_t* sword_from_mergeable_context;
  uint64_t  in_unshared_symbolic_memory;

  sword_from_active_context = symbolic_memory;

  while (sword_from_active_context) {
    // we need to stop at the end of the unshared symbolic memory space of the active context
    if (get_word_address(sword_from_active_context) == BEGIN_OF_SHARED_SYMBOLIC_MEMORY)
      return;

    // check if the word has not already been deleted
    if (get_word_address(sword_from_active_context) != (uint64_t) DELETED) {
      // check if the word has not already been merged
      if (get_word_address(sword_from_active_context) != (uint64_t) MERGED) {
        sword_from_mergeable_context = get_symbolic_memory(mergeable_context);
        in_unshared_symbolic_memory = 1;

        while (sword_from_mergeable_context) {
          // we need to know if we are in the unshared symbolic memory space of the mergeable context
          if (get_word_address(sword_from_mergeable_context) == BEGIN_OF_SHARED_SYMBOLIC_MEMORY)
            in_unshared_symbolic_memory = 0;

          if (get_word_address(sword_from_active_context) == get_word_address(sword_from_mergeable_context)) {
            if (get_word_symbolic(sword_from_active_context) != (char*) 0) {
              if (get_word_symbolic(sword_from_mergeable_context) != (char*) 0) {
                if (get_word_symbolic(sword_from_active_context) != get_word_symbolic(sword_from_mergeable_context)) {
                  // merge symbolic values if they are different
                  set_word_symbolic(sword_from_active_context,
                    smt_ternary("ite",
                      get_path_condition(active_context),
                      get_word_symbolic(sword_from_active_context),
                      get_word_symbolic(sword_from_mergeable_context)
                    )
                  );

                  // we mark the word as merged so that we do not merge it again when merging from the side of the mergeable context
                  if (in_unshared_symbolic_memory)
                    set_word_address(sword_from_mergeable_context, MERGED);

                  // we need to break out of the loop
                  sword_from_mergeable_context = (uint64_t*) - 1;
                }
              } else {
                // merge symbolic value and concrete value
                set_word_symbolic(sword_from_active_context,
                  smt_ternary("ite",
                    get_path_condition(active_context),
                    get_word_symbolic(sword_from_active_context),
                    bv_constant(get_word_value(sword_from_mergeable_context))
                  )
                );

                // we mark the word as merged so that we do not merge it again when merging from the side of the mergeable context
                if (in_unshared_symbolic_memory)
                  set_word_address(sword_from_mergeable_context, MERGED);

                // we need to break out of the loop
                sword_from_mergeable_context = (uint64_t*) - 1;
              }
            } else {
              if (get_word_symbolic(sword_from_mergeable_context) != (char*) 0) {
                // merge concrete value and symbolic value
                set_word_symbolic(sword_from_active_context,
                  smt_ternary("ite",
                    get_path_condition(active_context),
                    bv_constant(get_word_value(sword_from_active_context)),
                    get_word_symbolic(sword_from_mergeable_context)
                  )
                );

                // we mark the word as merged so that we do not merge it again when merging from the side of the mergeable context
                if (in_unshared_symbolic_memory)
                  set_word_address(sword_from_mergeable_context, MERGED);

                // we need to break out of the loop
                sword_from_mergeable_context = (uint64_t*) - 1;
              } else {
                if (get_word_value(sword_from_active_context) != get_word_value(sword_from_mergeable_context)) {
                  // merge concrete values if they are different
                  set_word_symbolic(sword_from_active_context,
                    smt_ternary("ite",
                      get_path_condition(active_context),
                      bv_constant(get_word_value(sword_from_active_context)),
                      bv_constant(get_word_value(sword_from_mergeable_context))
                    )
                  );

                  // we mark the word as merged so that we do not merge it again when merging from the side of the mergeable context
                  if (in_unshared_symbolic_memory)
                    set_word_address(sword_from_mergeable_context, MERGED);

                  // we need to break out of the loop
                  sword_from_mergeable_context = (uint64_t*) - 1;
                }
              }
            }
          }
          if (sword_from_mergeable_context == (uint64_t*) - 1)
            sword_from_mergeable_context = (uint64_t*) 0;
          else
            sword_from_mergeable_context = get_next_word(sword_from_mergeable_context);
        }
      }
    }

    sword_from_active_context = get_next_word(sword_from_active_context);
  }
}

void merge_symbolic_memory_of_mergeable_context(uint64_t* active_context, uint64_t* mergeable_context) {
  uint64_t* sword_from_active_context;
  uint64_t* sword_from_mergeable_context;
  uint64_t* sword;
  uint64_t* additional_memory;
  uint64_t  shared_symbolic_memory_depth;

  additional_memory = symbolic_memory;
  sword_from_mergeable_context = get_symbolic_memory(mergeable_context);

  while (sword_from_mergeable_context) {
    // we need to stop at the end of the unshared symbolic memory space of the mergeable context
    if (get_word_address(sword_from_mergeable_context) == BEGIN_OF_SHARED_SYMBOLIC_MEMORY) {
      symbolic_memory = additional_memory;

      // the active context contains now the merged symbolic memory
      set_symbolic_memory(active_context, symbolic_memory);
      return;
    }

    // check if the word has not already been deleted
    if (get_word_address(sword_from_mergeable_context) != (uint64_t) DELETED) {
      // check if the word has not already been merged
      if (get_word_address(sword_from_mergeable_context) != (uint64_t) MERGED) {
        sword_from_active_context = symbolic_memory;
        shared_symbolic_memory_depth = 0;

        while (sword_from_active_context) {
          // we need to know how far we are into the shared symbolic memory space
          if (get_word_address(sword_from_active_context) == (uint64_t) BEGIN_OF_SHARED_SYMBOLIC_MEMORY)
            shared_symbolic_memory_depth = shared_symbolic_memory_depth + 1;

          if (get_word_address(sword_from_active_context) == get_word_address(sword_from_mergeable_context)) {
            if (get_word_symbolic(sword_from_active_context) != (char*) 0) {
              if (get_word_symbolic(sword_from_mergeable_context) != (char*) 0) {
                if (get_word_symbolic(sword_from_active_context) != get_word_symbolic(sword_from_mergeable_context)) {
                  // merge symbolic values if they are different
                  if (shared_symbolic_memory_depth < 2)
                    set_word_symbolic(sword_from_active_context,
                      smt_ternary("ite",
                        get_path_condition(active_context),
                        get_word_symbolic(sword_from_active_context),
                        get_word_symbolic(sword_from_mergeable_context)
                      )
                    );
                  else {
                    // if we are too far into the shared symbolic memory space, we must not overwrite the value,
                    // but insert it into the unshared symbolic memory space of the active context
                    sword = allocate_symbolic_memory_word();
                    set_word_address(sword, get_word_address(sword_from_active_context));
                    set_word_value(sword, get_word_value(sword_from_active_context));
                    set_number_of_bits(sword, get_number_of_bits(sword_from_active_context));
                    set_word_symbolic(sword,
                      smt_ternary("ite",
                        get_path_condition(active_context),
                        get_word_symbolic(sword_from_active_context),
                        get_word_symbolic(sword_from_mergeable_context)
                      )
                    );
                    set_next_word(sword, additional_memory);
                  }

                  // we need to break out of the loop
                  sword_from_active_context = (uint64_t*) - 1;
                }
              } else {
                // merge symbolic value and concrete value
                if (shared_symbolic_memory_depth < 2)
                  set_word_symbolic(sword_from_active_context,
                    smt_ternary("ite",
                      get_path_condition(active_context),
                      get_word_symbolic(sword_from_active_context),
                      bv_constant(get_word_value(sword_from_mergeable_context))
                    )
                  );
                else {
                  // if we are too far into the shared symbolic memory space, we must not overwrite the value,
                  // but insert it into the unshared symbolic memory space of the active context
                  sword = allocate_symbolic_memory_word();
                  set_word_address(sword, get_word_address(sword_from_active_context));
                  set_word_value(sword, get_word_value(sword_from_active_context));
                  set_number_of_bits(sword, get_number_of_bits(sword_from_active_context));
                  set_word_symbolic(sword,
                    smt_ternary("ite",
                      get_path_condition(active_context),
                      get_word_symbolic(sword_from_active_context),
                      bv_constant(get_word_value(sword_from_mergeable_context))
                    )
                  );
                  set_next_word(sword, additional_memory);
                }

                // we need to break out of the loop
                sword_from_active_context = (uint64_t*) - 1;
              }
            } else {
              if (get_word_symbolic(sword_from_mergeable_context) != (char*) 0) {
                // merge concrete value and symbolic value
                if (shared_symbolic_memory_depth < 2)
                  set_word_symbolic(sword_from_active_context,
                    smt_ternary("ite",
                      get_path_condition(active_context),
                      bv_constant(get_word_value(sword_from_active_context)),
                      get_word_symbolic(sword_from_mergeable_context)
                    )
                  );
                else {
                  // if we are too far into the shared symbolic memory space, we must not overwrite the value,
                  // but insert it into the unshared symbolic memory space of the active context
                  sword = allocate_symbolic_memory_word();
                  set_word_address(sword, get_word_address(sword_from_active_context));
                  set_word_value(sword, get_word_value(sword_from_active_context));
                  set_number_of_bits(sword, get_number_of_bits(sword_from_active_context));
                  set_word_symbolic(sword,
                    smt_ternary("ite",
                      get_path_condition(active_context),
                      bv_constant(get_word_value(sword_from_active_context)),
                      get_word_symbolic(sword_from_mergeable_context)
                    )
                  );
                  set_next_word(sword, additional_memory);
                }

                // we need to break out of the loop
                sword_from_active_context = (uint64_t*) - 1;
              } else {
                if (get_word_value(sword_from_active_context) != get_word_value(sword_from_mergeable_context)) {
                  // merge concrete values if they are different
                  if (shared_symbolic_memory_depth < 2)
                    set_word_symbolic(sword_from_active_context,
                      smt_ternary("ite",
                        get_path_condition(active_context),
                        bv_constant(get_word_value(sword_from_active_context)),
                        bv_constant(get_word_value(sword_from_mergeable_context))
                      )
                    );
                  else {
                    // if we are too far into the shared symbolic memory space, we must not overwrite the value,
                    // but insert it into the unshared symbolic memory space of the active context
                    sword = allocate_symbolic_memory_word();
                    set_word_address(sword, get_word_address(sword_from_active_context));
                    set_word_value(sword, get_word_value(sword_from_active_context));
                    set_number_of_bits(sword, get_number_of_bits(sword_from_active_context));
                    set_word_symbolic(sword,
                      smt_ternary("ite",
                        get_path_condition(active_context),
                        bv_constant(get_word_value(sword_from_active_context)),
                        bv_constant(get_word_value(sword_from_mergeable_context))
                      )
                    );
                    set_next_word(sword, additional_memory);
                  }

                  // we need to break out of the loop
                  sword_from_active_context = (uint64_t*) - 1;
                }
              }
            }
          }
          if (sword_from_active_context == (uint64_t*) - 1)
            sword_from_active_context = (uint64_t*) 0;
          else
            sword_from_active_context = get_next_word(sword_from_active_context);
        }
      }
    }
    sword_from_mergeable_context = get_next_word(sword_from_mergeable_context);
  }

  symbolic_memory = additional_memory;

  // the active context contains now the merged symbolic memory
  set_symbolic_memory(active_context, symbolic_memory);
}

void merge_registers(uint64_t* active_context, uint64_t* mergeable_context) {
  uint64_t i;

  i = 0;

  // merging the symbolic registers
  while (i < NUMBEROFREGISTERS) {
    if (*(get_symbolic_regs(active_context) + i) != 0) {
      if (*(get_symbolic_regs(mergeable_context) + i) != 0) {
        if (*(get_symbolic_regs(active_context) + i) != *(get_symbolic_regs(mergeable_context) + i))
          // merge symbolic values if they are different
          *(reg_sym + i) = (uint64_t) smt_ternary("ite",
                                        get_path_condition(active_context),
                                        (char*) *(get_symbolic_regs(active_context) + i),
                                        (char*) *(get_symbolic_regs(mergeable_context) + i)
                                      );
      } else
        // merge symbolic value and concrete value
        *(reg_sym + i) = (uint64_t) smt_ternary("ite",
                                      get_path_condition(active_context),
                                      (char*) *(get_symbolic_regs(active_context) + i),
                                      bv_constant(*(get_regs(mergeable_context) + i))
                                    );
    } else {
      if (*(get_symbolic_regs(mergeable_context) + i) != 0)
        // merge concrete value and symbolic value
        *(reg_sym + i) = (uint64_t) smt_ternary("ite",
                                      get_path_condition(active_context),
                                      bv_constant(*(get_regs(active_context) + i)),
                                      (char*) *(get_symbolic_regs(mergeable_context) + i)
                                    );
      else
        if (*(get_regs(active_context) + i) != *(get_regs(mergeable_context) + i))
          // merge concrete values if they are different
          *(reg_sym + i) = (uint64_t) smt_ternary("ite",
                                        get_path_condition(active_context),
                                        bv_constant(*(get_regs(active_context) + i)),
                                        bv_constant(*(get_regs(mergeable_context) + i))
                                      );
    }

    i = i + 1;
  }

  set_symbolic_regs(active_context, reg_sym);
}

uint64_t* merge_if_possible_and_get_next_context(uint64_t* context) {
  uint64_t merge_not_finished;
  uint64_t mergeable;
  uint64_t pauseable;

  if (merge_enabled)
    merge_not_finished = 1;
  else
    merge_not_finished = 0;

  while (merge_not_finished) {
    mergeable = 1;
    pauseable = 1;

    if (context == (uint64_t*) 0) {
      // break out of the loop
      mergeable = 0;
      pauseable = 0;
    } else
      symbolic_memory = get_symbolic_memory(context);

    // check if the context can be merged with one or more mergeable contexts
    while (mergeable) {
      if (current_mergeable_context == (uint64_t*) 0)
        current_mergeable_context = get_mergeable_context();

      if (current_mergeable_context != (uint64_t*) 0) {
        if (get_pc(context) == get_pc(current_mergeable_context)) {
          if (merge_enabled)
            if (compare_call_stacks(context, current_mergeable_context) != 1)
              merge(context, current_mergeable_context, get_pc(context));
            else
              mergeable = 0;
          else
            mergeable = 0;
        } else
          mergeable = 0;
      } else
        mergeable = 0;
    }

    // check if the context has reached a merge location and needs to be paused
    while (pauseable) {
      if (get_pc(context) == get_merge_location(context)) {
        current_mergeable_context = context;
        context = get_waiting_context();

        if (context) {
          if (get_pc(context) == get_pc(current_mergeable_context)) {
            if (compare_call_stacks(context, current_mergeable_context) == 0) {
              pauseable = 0;
              mergeable = 1;
            } else if (compare_call_stacks(context, current_mergeable_context) == 2)
              throw_exception(EXCEPTION_RECURSION, 0);
          }
          else {
            add_mergeable_context(current_mergeable_context);
            current_mergeable_context = (uint64_t*) 0;
          }
        }

        // break out of the loop
        if (context == (uint64_t*) 0) {
          mergeable = 0;
          pauseable = 0;
        }

      } else {
        if (current_mergeable_context == (uint64_t*) 0)
          current_mergeable_context = get_mergeable_context();

        if (current_mergeable_context != (uint64_t*) 0)
          if (get_pc(context) == get_pc(current_mergeable_context)) {
            if (compare_call_stacks(context, current_mergeable_context) == 0)
              mergeable = 1;
            else if (compare_call_stacks(context, current_mergeable_context) == 2)
              throw_exception(EXCEPTION_RECURSION, 0);
          }

        pauseable = 0;
      }
    }

    if (mergeable == 0)
      if (pauseable == 0)
        merge_not_finished = 0;
  }

  // check if there are contexts which have been paused and were not merged yet
  if (context == (uint64_t*) 0)
    context = get_mergeable_context();

  if (merge_enabled == 0)
    merge_not_finished = 0;

  return context;
}

void push_onto_call_stack(uint64_t* context, uint64_t address) {
  uint64_t* entry;

  entry = zalloc(SIZEOFUINT64STAR + SIZEOFUINT64);

  *(entry + 0) = (uint64_t) get_call_stack(context);
  *(entry + 1) = (uint64_t) address;

  set_call_stack(context, entry);
}

uint64_t pop_off_call_stack(uint64_t* context) {
  uint64_t* head;

  if (get_call_stack(context) == (uint64_t*) 0)
    return 0;

  head = get_call_stack(context);
  set_call_stack(context, (uint64_t*) *(head + 0));

  return *(head + 1);
}

// 0, they are equal
// 1, active_context has longer call stack
// 2, mergeable_context has longer call stack
// 3, an entry is different
uint64_t compare_call_stacks(uint64_t* active_context, uint64_t* mergeable_context) {
  uint64_t* entry_active;
  uint64_t* entry_mergeable;

  uint64_t active_context_stack_length;
  uint64_t mergeable_context_stack_length;

  active_context_stack_length = 0;
  mergeable_context_stack_length = 0;

  entry_active = get_call_stack(active_context);
  entry_mergeable = get_call_stack(mergeable_context);

  if (debug_merge)
    printf1("; Call stack of active context (%d):\n", (char*) active_context);

  while(entry_active) {

    if (debug_merge)
      printf1("; %x\n", (char*) *(entry_active + 1));

    active_context_stack_length = active_context_stack_length + 1;
    entry_active = (uint64_t*) *(entry_active + 0);
  }

  if (debug_merge)
    printf1("; Call stack of mergeable context (%d):\n", (char*) mergeable_context);

  while(entry_mergeable) {

    if (debug_merge)
      printf1("; %x\n", (char*) *(entry_mergeable + 1));

    mergeable_context_stack_length = mergeable_context_stack_length + 1;
    entry_mergeable = (uint64_t*) *(entry_mergeable + 0);
  }

  if (mergeable_context_stack_length > active_context_stack_length) {
    if (debug_merge)
      print("; Result of call stack comparison -> 2 (mergeable_context has longer call stack)\n");
    return 2;
  }
  else if (mergeable_context_stack_length < active_context_stack_length) {
    if (debug_merge)
      print("; Result of call stack comparison -> 1 (active_context has longer call stack)\n");
    return 1;
  }

  entry_active = get_call_stack(active_context);
  entry_mergeable = get_call_stack(mergeable_context);

  if (entry_active == (uint64_t*) 0)
    if (entry_mergeable == (uint64_t*) 0) {
      if (debug_merge)
        print("; Result of call stack comparison -> 0 (they are equal)\n");
      return 0; // both have no call stack
    }

  while (entry_active) {
    if (entry_mergeable == (uint64_t*) 0) {
      if (debug_merge)
        print("; Result of call stack comparison -> 1 (active_context has longer call stack)\n");
      return 1; // active context has an entry, but mergeable context does not
    }

    if (*(entry_active + 1) != *(entry_mergeable + 1)) {
      if (debug_merge)
        print("; Result of call stack comparison -> 3 (an entry is different)\n");
      return 3; // an entry is different
    }

    entry_active = (uint64_t*) *(entry_active + 0);
    entry_mergeable = (uint64_t*) *(entry_mergeable + 0);
  }

  if (entry_mergeable == (uint64_t*) 0) {
    if (debug_merge)
        print("; Result of call stack comparison -> 0 (they are equal)\n");
    return 0; // both stacks have the same length and entries
  }
  else {
    if (debug_merge)
        print("; Result of call stack comparison -> 2 (mergeable_context has longer call stack)\n");
    return 2; // active context has no more entries on the stack, but mergeable context still does
  }
}

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void print_register_hexadecimal(uint64_t reg) {
  printf2("%s=%x", get_register_name(reg), (char*) *(registers + reg));
}

void print_register_octal(uint64_t reg) {
  printf2("%s=%o", get_register_name(reg), (char*) *(registers + reg));
}

uint64_t is_system_register(uint64_t reg) {
  if (reg == REG_GP)
    return 1;
  else if (reg == REG_FP)
    return 1;
  else if (reg == REG_RA)
    return 1;
  else if (reg == REG_SP)
    return 1;
  else
    return 0;
}

void print_register_value(uint64_t reg) {
  if (is_system_register(reg))
    print_register_hexadecimal(reg);
  else
    printf3("%s=%d(%x)", get_register_name(reg), (char*) *(registers + reg), (char*) *(registers + reg));
}

void print_exception(uint64_t exception, uint64_t faulting_page) {
  print((char*) *(EXCEPTIONS + exception));

  if (exception == EXCEPTION_PAGEFAULT)
    printf1(" at %p", (char*) faulting_page);
}

void throw_exception(uint64_t exception, uint64_t faulting_page) {
  if (get_exception(current_context) != EXCEPTION_NOEXCEPTION)
    if (get_exception(current_context) != exception) {
      printf2("%s: context %p throws ", selfie_name, (char*) current_context);
      print_exception(exception, faulting_page);
      print(" exception in presence of ");
      print_exception(get_exception(current_context), get_faulting_page(current_context));
      print(" exception\n");

      exit(EXITCODE_MULTIPLEEXCEPTIONERROR);
    }

  set_exception(current_context, exception);
  set_faulting_page(current_context, faulting_page);

  trap = 1;

  if (debug_exception) {
    printf2("%s: context %p throws ", selfie_name, (char*) current_context);
    print_exception(exception, faulting_page);
    print(" exception\n");
  }
}

void fetch() {
  // assert: is_valid_virtual_address(pc) == 1
  // assert: is_virtual_address_mapped(pt, pc) == 1

  if (pc % REGISTERSIZE == 0)
    ir = get_low_word(load_virtual_memory(pt, pc));
  else
    ir = get_high_word(load_virtual_memory(pt, pc - INSTRUCTIONSIZE));
}

void decode() {
  opcode = get_opcode(ir);

  is = 0;

  if (opcode == OP_IMM) {
    decode_i_format();

    if (funct3 == F3_ADDI)
      is = ADDI;
  } else if (opcode == OP_LD) {
    decode_i_format();

    if (funct3 == F3_LD)
      is = LD;
  } else if (opcode == OP_SD) {
    decode_s_format();

    if (funct3 == F3_SD)
      is = SD;
  } else if (opcode == OP_OP) { // could be ADD, SUB, MUL, DIVU, REMU, SLTU
    decode_r_format();

    if (funct3 == F3_ADD) { // = F3_SUB = F3_MUL
      if (funct7 == F7_ADD)
        is = ADD;
      else if (funct7 == F7_SUB)
        is = SUB;
      else if (funct7 == F7_MUL)
        is = MUL;
    } else if (funct3 == F3_DIVU) {
      if (funct7 == F7_DIVU)
        is = DIVU;
    } else if (funct3 == F3_REMU) {
      if (funct7 == F7_REMU)
        is = REMU;
    } else if (funct3 == F3_SLTU) {
      if (funct7 == F7_SLTU)
        is = SLTU;
    }
  } else if (opcode == OP_BRANCH) {
    decode_b_format();

    if (funct3 == F3_BEQ)
      is = BEQ;
  } else if (opcode == OP_JAL) {
    decode_j_format();

    is = JAL;
  } else if (opcode == OP_JALR) {
    decode_i_format();

    if (funct3 == F3_JALR)
      is = JALR;
  } else if (opcode == OP_LUI) {
    decode_u_format();

    is = LUI;
  } else if (opcode == OP_SYSTEM) {
    decode_i_format();

    if (funct3 == F3_ECALL)
      is = ECALL;
  }

  if (is == 0) {
    if (run)
      throw_exception(EXCEPTION_UNKNOWNINSTRUCTION, 0);
    else {
      //report the error on the console
      output_fd = 1;

      printf2("%s: unknown instruction with %x opcode detected\n", selfie_name, (char*) opcode);

      exit(EXITCODE_UNKNOWNINSTRUCTION);
    }
  }
}

void execute() {
  if (debug) {
    if (record)
      execute_record();
    else if (symbolic)
      execute_symbolically();
    else
      execute_debug();

    return;
  }

  // assert: 1 <= is <= number of RISC-U instructions
  if (is == ADDI)
    do_addi();
  else if (is == LD)
    do_ld();
  else if (is == SD)
    do_sd();
  else if (is == ADD)
    do_add();
  else if (is == SUB)
    do_sub();
  else if (is == MUL)
    do_mul();
  else if (is == DIVU)
    do_divu();
  else if (is == REMU)
    do_remu();
  else if (is == SLTU)
    do_sltu();
  else if (is == BEQ)
    do_beq();
  else if (is == JAL)
    do_jal();
  else if (is == JALR)
    do_jalr();
  else if (is == LUI)
    do_lui();
  else if (is == ECALL)
    do_ecall();
}

void execute_record() {
  // assert: 1 <= is <= number of RISC-U instructions
  if (is == ADDI) {
    record_lui_addi_add_sub_mul_sltu_jal_jalr();
    do_addi();
  } else if (is == LD) {
    record_ld();
    do_ld();
  } else if (is == SD) {
    record_sd();
    do_sd();
  } else if (is == ADD) {
    record_lui_addi_add_sub_mul_sltu_jal_jalr();
    do_add();
  } else if (is == SUB) {
    record_lui_addi_add_sub_mul_sltu_jal_jalr();
    do_sub();
  } else if (is == MUL) {
    record_lui_addi_add_sub_mul_sltu_jal_jalr();
    do_mul();
  } else if (is == DIVU) {
    record_divu_remu();
    do_divu();
  } else if (is == REMU) {
    record_divu_remu();
    do_remu();
  } else if (is == SLTU) {
    record_lui_addi_add_sub_mul_sltu_jal_jalr();
    do_sltu();
  } else if (is == BEQ) {
    record_beq();
    do_beq();
  } else if (is == JAL) {
    record_lui_addi_add_sub_mul_sltu_jal_jalr();
    do_jal();
  } else if (is == JALR) {
    record_lui_addi_add_sub_mul_sltu_jal_jalr();
    do_jalr();
  } else if (is == LUI) {
    record_lui_addi_add_sub_mul_sltu_jal_jalr();
    do_lui();
  } else if (is == ECALL) {
    record_ecall();
    do_ecall();
  }
}

void execute_undo() {
  // assert: 1 <= is <= number of RISC-U instructions
  if (is == SD)
    undo_sd();
  else if (is == BEQ)
    // beq does not require any undo
    return;
  else if (is == ECALL)
    undo_ecall();
  else
    undo_lui_addi_add_sub_mul_divu_remu_sltu_ld_jal_jalr();
}

void execute_debug() {
  translate_to_assembler();

  // assert: 1 <= is <= number of RISC-U instructions
  if (is == ADDI){
    print_addi_before();
    do_addi();
    print_addi_add_sub_mul_divu_remu_sltu_after();
  } else if (is == LD) {
    print_ld_before();
    print_ld_after(do_ld());
  } else if (is == SD) {
    print_sd_before();
    print_sd_after(do_sd());
  } else if (is == ADD) {
    print_add_sub_mul_divu_remu_sltu_before();
    do_add();
    print_addi_add_sub_mul_divu_remu_sltu_after();
  } else if (is == SUB) {
    print_add_sub_mul_divu_remu_sltu_before();
    do_sub();
    print_addi_add_sub_mul_divu_remu_sltu_after();
  } else if (is == MUL) {
    print_add_sub_mul_divu_remu_sltu_before();
    do_mul();
    print_addi_add_sub_mul_divu_remu_sltu_after();
  } else if (is == DIVU) {
    print_add_sub_mul_divu_remu_sltu_before();
    do_divu();
    print_addi_add_sub_mul_divu_remu_sltu_after();
  } else if (is == REMU) {
    print_add_sub_mul_divu_remu_sltu_before();
    do_remu();
    print_addi_add_sub_mul_divu_remu_sltu_after();
  } else if (is == SLTU) {
    print_add_sub_mul_divu_remu_sltu_before();
    do_sltu();
    print_addi_add_sub_mul_divu_remu_sltu_after();
  } else if (is == BEQ) {
    print_beq_before();
    do_beq();
    print_beq_after();
  } else if (is == JAL) {
    print_jal_before();
    do_jal();
    print_jal_jalr_after();
  } else if (is == JALR) {
    print_jalr_before();
    do_jalr();
    print_jal_jalr_after();
  } else if (is == LUI) {
    print_lui_before();
    do_lui();
    print_lui_after();
  } else if (is == ECALL) {
    do_ecall();

    return;
  }

  println();
}

void execute_symbolically() {
  // assert: 1 <= is <= number of RISC-U instructions
  if (is == ADDI) {
    constrain_addi();
    do_addi();
  } else if (is == LD)
    constrain_ld();
  else if (is == SD)
    constrain_sd();
  else if (is == ADD) {
    constrain_add_sub_mul_divu_remu_sltu("bvadd");
    do_add();
  } else if (is == SUB) {
    constrain_add_sub_mul_divu_remu_sltu("bvsub");
    do_sub();
  } else if (is == MUL) {
    constrain_add_sub_mul_divu_remu_sltu("bvmul");
    do_mul();
  } else if (is == DIVU) {
    constrain_add_sub_mul_divu_remu_sltu("bvudiv");
    do_divu();
  } else if (is == REMU) {
    constrain_add_sub_mul_divu_remu_sltu("bvurem");
    do_remu();
  } else if (is == SLTU) {
    constrain_add_sub_mul_divu_remu_sltu("bvult");
    zero_extend_sltu();
    do_sltu();
  } else if (is == BEQ)
    constrain_beq();
  else if (is == JAL) {
    // the JAL instruction is a procedure call, if rd is REG_RA
    if (rd == REG_RA)
      // push the procedure at pc + imm onto the callstack of the current context
      push_onto_call_stack(current_context, pc + imm);
    do_jal();
  } else if (is == JALR) {
    // pop off call stack, when we return from a procedure
    if (rd == REG_ZR)
      if (rs1 == REG_RA)
        if (imm == 0)
          pop_off_call_stack(current_context);
    constrain_jalr();
    do_jalr();
  } else if (is == LUI) {
    constrain_lui();
    do_lui();
  } else if (is == ECALL)
    do_ecall();
}

void interrupt() {
  if (timer != TIMEROFF) {
    timer = timer - 1;

    if (symbolic)
      set_execution_depth(current_context, get_execution_depth(current_context) + 1);

    if (timer == 0) {
      if (get_exception(current_context) == EXCEPTION_NOEXCEPTION)
        // only throw exception if no other is pending
        // TODO: handle multiple pending exceptions
        throw_exception(EXCEPTION_TIMER, 0);
      else
        // trigger timer in the next interrupt cycle
        timer = 1;
    }
  }

  if (symbolic) {
    if (current_mergeable_context != (uint64_t*) 0)
      // if both contexts are at the same program location, they can be merged
      if (pc == get_pc(current_mergeable_context))
        if (compare_call_stacks(current_context, current_mergeable_context) != 1)
          merge(current_context, current_mergeable_context, pc);

    // check if the current context has reached a merge location
    if (pc == get_merge_location(current_context))
      if (get_exception(current_context) == EXCEPTION_NOEXCEPTION)
        // only throw exception if no other is pending
        // TODO: handle multiple pending exceptions
        throw_exception(EXCEPTION_MERGE, 0);
  }
}

void run_until_exception() {
  trap = 0;

  while (trap == 0) {
    fetch();
    decode();
    execute();

    interrupt();
  }

  trap = 0;
}

uint64_t instruction_with_max_counter(uint64_t* counters, uint64_t max) {
  uint64_t a;
  uint64_t n;
  uint64_t i;
  uint64_t c;

  a = UINT64_MAX;

  n = 0;
  i = 0;

  while (i < code_length / INSTRUCTIONSIZE) {
    c = *(counters + i);

    if (n < c) {
      if (c < max) {
        n = c;
        a = i;
      } else
        return i * INSTRUCTIONSIZE;
    }

    i = i + 1;
  }

  if (a != UINT64_MAX)
    return a * INSTRUCTIONSIZE;
  else
    return UINT64_MAX;
}

uint64_t print_per_instruction_counter(uint64_t total, uint64_t* counters, uint64_t max) {
  uint64_t a;
  uint64_t c;

  a = instruction_with_max_counter(counters, max);

  if (a != UINT64_MAX) {
    c = *(counters + a / INSTRUCTIONSIZE);

    // CAUTION: we reset counter to avoid reporting it again
    *(counters + a / INSTRUCTIONSIZE) = 0;

    printf3(",%d(%.2d%%)@%x", (char*) c, (char*) fixed_point_percentage(fixed_point_ratio(total, c, 4), 4), (char*) a);
    print_code_line_number_for_instruction(a, 0);

    return c;
  } else {
    print(",0(0.00%)");

    return 0;
  }
}

void print_per_instruction_profile(char* message, uint64_t total, uint64_t* counters) {
  printf3("%s%s%d", selfie_name, message, (char*) total);
  print_per_instruction_counter(total, counters, print_per_instruction_counter(total, counters, print_per_instruction_counter(total, counters, UINT64_MAX)));
  println();
}

void print_profile() {
  printf4("%s: summary: %d executed instructions and %.2dMB(%.2d%%) mapped memory\n", selfie_name,
    (char*) get_total_number_of_instructions(),
    (char*) fixed_point_ratio(pused(), MEGABYTE, 2),
    (char*) fixed_point_percentage(fixed_point_ratio(page_frame_memory, pused(), 4), 4));

  if (get_total_number_of_instructions() > 0) {
    print_instruction_counters();

    if (code_line_number != (uint64_t*) 0)
      printf1("%s: profile: total,max(ratio%%)@addr(line#),2max,3max\n", selfie_name);
    else
      printf1("%s: profile: total,max(ratio%%)@addr,2max,3max\n", selfie_name);

    print_per_instruction_profile(": calls:   ", calls, calls_per_procedure);
    print_per_instruction_profile(": loops:   ", iterations, iterations_per_loop);
    print_per_instruction_profile(": loads:   ", ic_ld, loads_per_instruction);
    print_per_instruction_profile(": stores:  ", ic_sd, stores_per_instruction);
  }
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- CONTEXTS ---------------------------
// -----------------------------------------------------------------

void copy_call_stack(uint64_t* from_context, uint64_t* to_context) {
  uint64_t* entry;
  uint64_t* entry_copy;
  uint64_t* call_stack_copy;
  uint64_t* previous_entry;

  entry = get_call_stack(from_context);

  entry_copy           = (uint64_t*) 0;
  call_stack_copy      = (uint64_t*) 0;
  previous_entry       = (uint64_t*) 0;

  while (entry) {
    entry_copy = zalloc(SIZEOFUINT64STAR + SIZEOFUINT64);

    *(entry_copy + 1) = *(entry + 1);

    if (previous_entry != (uint64_t*) 0)
      *(previous_entry + 0) = (uint64_t) entry_copy;

    if (call_stack_copy == (uint64_t*) 0)
      call_stack_copy = entry_copy;

    previous_entry = entry_copy;
    entry = (uint64_t*) *(entry + 0);
  }

  set_call_stack(to_context, call_stack_copy);
}

uint64_t* copy_context(uint64_t* original, uint64_t location, char* condition) {
  uint64_t* context;
  uint64_t* begin_of_shared_symbolic_memory;
  uint64_t r;

  context = new_context();

  set_pc(context, location);

  set_regs(context, smalloc(NUMBEROFREGISTERS * REGISTERSIZE));

  r = 0;

  while (r < NUMBEROFREGISTERS) {
    *(get_regs(context) + r) = *(get_regs(original) + r);

    r = r + 1;
  }

  set_pt(context, pt);

  set_lowest_lo_page(context, get_lowest_lo_page(original));
  set_highest_lo_page(context, get_highest_lo_page(original));
  set_lowest_hi_page(context, get_lowest_hi_page(original));
  set_highest_hi_page(context, get_highest_hi_page(original));
  set_exception(context, get_exception(original));
  set_faulting_page(context, get_faulting_page(original));
  set_exit_code(context, get_exit_code(original));
  set_parent(context, get_parent(original));
  set_virtual_context(context, get_virtual_context(original));
  set_name(context, get_name(original));

  set_execution_depth(context, get_execution_depth(original));
  set_path_condition(context, condition);
  set_beq_counter(context, get_beq_counter(original));
  set_merge_location(context, get_merge_location(original));

  begin_of_shared_symbolic_memory = allocate_symbolic_memory_word();

  // mark begin of shared symbolic memory space in the copied context
  set_next_word(begin_of_shared_symbolic_memory, get_symbolic_memory(original));
  set_word_address(begin_of_shared_symbolic_memory, BEGIN_OF_SHARED_SYMBOLIC_MEMORY);

  // begin of the unshared symbolic memory space of the copied context
  set_symbolic_memory(context, begin_of_shared_symbolic_memory);

  begin_of_shared_symbolic_memory = allocate_symbolic_memory_word();

  // mark begin of shared symbolic memory space in the original context
  set_next_word(begin_of_shared_symbolic_memory, get_symbolic_memory(original));
  set_word_address(begin_of_shared_symbolic_memory, BEGIN_OF_SHARED_SYMBOLIC_MEMORY);

  // begin of the unshared symbolic memory space of the original context
  set_symbolic_memory(original, begin_of_shared_symbolic_memory);

  symbolic_memory = get_symbolic_memory(original);

  set_symbolic_regs(context, smalloc(NUMBEROFREGISTERS * REGISTERSIZE));

  set_merge_partner(context, original);

  copy_call_stack(original, context);

  r = 0;

  while (r < NUMBEROFREGISTERS) {
    *(get_symbolic_regs(context) + r) = *(get_symbolic_regs(original) + r);

    r = r + 1;
  }

  symbolic_contexts = context;

  return context;
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

uint64_t handle_system_call(uint64_t* context) {
  uint64_t a7;

  set_exception(context, EXCEPTION_NOEXCEPTION);

  a7 = *(get_regs(context) + REG_A7);

  if (a7 == SYSCALL_BRK)
    implement_brk(context);
  else if (a7 == SYSCALL_READ)
    implement_read(context);
  else if (a7 == SYSCALL_WRITE)
    implement_write(context);
  else if (a7 == SYSCALL_OPENAT)
    implement_openat(context);
  else if (a7 == SYSCALL_EXIT) {
    implement_exit(context);

    // TODO: exit only if all contexts have exited
    return EXIT;
  } else {
    printf2("%s: unknown system call %d\n", selfie_name, (char*) a7);

    set_exit_code(context, EXITCODE_UNKNOWNSYSCALL);

    return EXIT;
  }

  return DONOTEXIT;
}

uint64_t handle_page_fault(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  // TODO: use this table to unmap and reuse frames
  map_page(context, get_faulting_page(context), (uint64_t) palloc());

  return DONOTEXIT;
}

uint64_t handle_division_by_zero(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  if (record) {
    printf1("%s: division by zero, replaying...\n", selfie_name);

    replay_trace();

    set_exit_code(context, EXITCODE_NOERROR);
  } else if (symbolic) {
    // check if this division by zero is reachable
    print("(push 1)\n");
    printf1("(assert %s); division by zero detected; check if this division by zero is reachable", path_condition);
    print("\n(check-sat)\n(get-model)\n(pop 1)\n");

    // we terminate the execution of the context, because if the location is not reachable,
    // the rest of the path is not reachable either, and otherwise
    // the execution would be terminated by this error anyway
    set_exit_code(context, EXITCODE_DIVISIONBYZERO);
  } else {
    printf1("%s: division by zero\n", selfie_name);

    set_exit_code(context, EXITCODE_DIVISIONBYZERO);
  }

  return EXIT;
}

uint64_t handle_timer(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  if (symbolic) {
    printf1("; timeout in ", path_condition);
    print_code_context_for_instruction(pc);
    if (debug_merge) {
      printf1(" -> timed out context: %d", (char*) context);
    }
    println();

    return EXIT;
  } else
    return DONOTEXIT;
}

uint64_t handle_merge(uint64_t* context) {
  add_mergeable_context(current_context);

  set_exception(context, EXCEPTION_NOEXCEPTION);

  return MERGE;
}

uint64_t handle_recursion(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  return RECURSION;
}

uint64_t handle_exception(uint64_t* context) {
  uint64_t exception;

  exception = get_exception(context);

  if (exception == EXCEPTION_SYSCALL)
    return handle_system_call(context);
  else if (exception == EXCEPTION_PAGEFAULT)
    return handle_page_fault(context);
  else if (exception == EXCEPTION_DIVISIONBYZERO)
    return handle_division_by_zero(context);
  else if (exception == EXCEPTION_TIMER)
    return handle_timer(context);
  else if (exception == EXCEPTION_MERGE)
    return handle_merge(context);
  else if (exception == EXCEPTION_RECURSION)
    return handle_recursion(context);
  else {
    if (symbolic)
      if (exception == EXCEPTION_INVALIDADDRESS) {
        // check if this invalid memory access is reachable
        print("(push 1)\n");
        printf1("(assert %s); invalid memory access detected; check if this invalid memory access is reachable", path_condition);
        print("\n(check-sat)\n(get-model)\n(pop 1)\n");

        set_exit_code(context, EXITCODE_SYMBOLICEXECUTIONERROR);

        // we terminate the execution of the context, because if the location is not reachable,
        // the rest of the path is not reachable either, and otherwise
        // the execution would be terminated by this error anyway
        return EXIT;
      }

    printf2("%s: context %s throws uncaught ", selfie_name, get_name(context));
    print_exception(exception, get_faulting_page(context));
    println();

    set_exit_code(context, EXITCODE_UNCAUGHTEXCEPTION);

    return EXIT;
  }
}

char* replace_extension(char* filename, char* extension) {
  char* s;
  uint64_t i;
  uint64_t c;

  // assert: string_length(filename) + 1 + string_length(extension) < MAX_FILENAME_LENGTH

  s = string_alloc(string_length(filename) + 1 + string_length(extension));

  // start reading at end of filename
  i = string_length(filename);

  c = load_character(filename, i);

  // look for extension
  while (c != '.') {
    if (c == '/')
      i = 0;

    if (i > 0) {
      i = i - 1;

      c = load_character(filename, i);
    } else
      c = '.';
  }

  // filename has no extension
  if (i == 0)
    // writing filename plus extension into s
    sprintf2(s, "%s.%s", filename, extension);
  else {
    // assert: s is zeroed and thus null-terminated

    // copy filename without extension and null-terminator into s
    while (i > 0) {
      i = i - 1;

      store_character(s, i, load_character(filename, i));
    }

    // writing s plus extension into s
    sprintf2(s, "%s.%s", s, extension);
  }

  return s;
}

uint64_t monster(uint64_t* to_context) {
  uint64_t  timeout;
  uint64_t* from_context;
  uint64_t  exception;

  if (debug_merge)
    from_context = (uint64_t*) 0;

  print("monster\n");

  // use extension ".smt" in name of SMT-LIB file
  smt_name = replace_extension(binary_name, "smt");

  // assert: smt_name is mapped and not longer than MAX_FILENAME_LENGTH

  smt_fd = open_write_only(smt_name);

  if (signed_less_than(smt_fd, 0)) {
    printf2("%s: could not create SMT-LIB output file %s\n", selfie_name, smt_name);

    exit(EXITCODE_IOERROR);
  }

  output_name = smt_name;
  output_fd   = smt_fd;

  printf1("; %s\n\n", SELFIE_URL);

  printf1("; SMT-LIB formulae generated by %s for\n", selfie_name);
  printf1("; RISC-V code obtained from %s with ", binary_name);
  if (max_execution_depth)
    printf1("%d execution depth\n\n", (char*) max_execution_depth);
  else
    print("unbounded execution depth\n\n");

  print("(set-option :produce-models true)\n");
  print("(set-option :incremental true)\n");
  print("(set-logic QF_BV)\n\n");

  timeout = max_execution_depth - get_execution_depth(to_context);

  while (1) {

    if (debug_merge)
      if (from_context != (uint64_t*) 0)
        printf4("; switching from context %d to context %d (merge locations: %x, %x)\n", (char*) from_context, (char*) to_context, (char*) get_merge_location(from_context), (char*) get_merge_location(to_context));

    from_context = mipster_switch(to_context, timeout);

    if (get_parent(from_context) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      to_context = get_parent(from_context);

      timeout = TIMEROFF;
    } else {
      exception = handle_exception(from_context);

      if (exception == EXIT) {
        // we need to update the end of the shared symbolic memory of the corresponding context
        update_begin_of_shared_symbolic_memory(get_merge_partner(from_context));

        // if a context is currently waiting to be merged, we need to switch to this one
        if (current_mergeable_context != (uint64_t*) 0) {
          // update the merge location, so the 'new' context can be merged later
          set_merge_location(current_mergeable_context, get_merge_location(current_context));

          to_context = current_mergeable_context;

        // if no context is currently waiting to be merged, we switch to the next waiting context
        } else
          to_context = get_waiting_context();

        // it may be possible that there are no waiting contexts, but mergeable contexts
        if (to_context == (uint64_t*) 0) {
          to_context = get_mergeable_context();

          if (to_context)
            // update the merge location, so the 'new' context can be merged later
            set_merge_location(to_context, get_merge_location(current_context));
        }

        to_context = merge_if_possible_and_get_next_context(to_context);

        if (to_context)
          timeout = max_execution_depth - get_execution_depth(to_context);
        else {
          print("\n(exit)");

          output_name = (char*) 0;
          output_fd   = 1;

          printf3("%s: %d characters of SMT-LIB formulae written into %s\n", selfie_name,
            (char*) number_of_written_characters,
            smt_name);

          return EXITCODE_NOERROR;
        }
      } else if (exception == MERGE) {
        to_context = merge_if_possible_and_get_next_context(get_waiting_context());

        timeout = max_execution_depth - get_execution_depth(to_context);
      } else if (exception == RECURSION) {
        if (current_mergeable_context != (uint64_t*) 0) {
          to_context = current_mergeable_context;

          current_mergeable_context = current_context;
        } else {
          timeout = timer;

          to_context = from_context;
        }
      } else {
        timeout = timer;

        to_context = from_context;
      }
    }
  }
}

uint64_t selfie_run(uint64_t machine) {
  uint64_t exit_code;

  if (binary_length == 0) {
    printf1("%s: nothing to run, debug, or host\n", selfie_name);

    return EXITCODE_BADARGUMENTS;
  }

  reset_interpreter();
  reset_profiler();
  reset_microkernel();

  if (machine == DIPSTER) {
    debug          = 1;
    debug_syscalls = 1;
  } else if (machine == RIPSTER) {
    debug  = 1;
    record = 1;

    init_replay_engine();
  } else if (machine == MONSTER) {
    debug    = 1;
    symbolic = 1;
  }

  if (machine != MONSTER)
    init_memory(atoi(peek_argument(0)));
  else {
    init_memory(1);

    max_execution_depth = atoi(get_argument());

    // checking for the (optional) beq limit argument
    if (number_of_remaining_arguments() > 0)
      if (string_compare(peek_argument(0), "--merge-enabled") == 0)
        if (string_compare(peek_argument(0), "--debug-merge") == 0)
          // assert: argument is an integer representing the beq limit
          beq_limit = atoi(get_argument());

    // checking for the (optional) argument whether to enable merging (in debug mode) or not
    if (number_of_remaining_arguments() > 0) {
      if (string_compare(peek_argument(0), "--merge-enabled")) {
        merge_enabled = 1;

        get_argument();
      } else if (string_compare(peek_argument(0), "--debug-merge")) {
        debug_merge = 1;
        merge_enabled = 1;

        get_argument();
      }
    }
  }

  boot_loader();

  printf3("%s: selfie executing %s with %dMB physical memory on ", selfie_name,
    binary_name,
    (char*) (page_frame_memory / MEGABYTE));

  run = 1;

  if (machine == MIPSTER)
    exit_code = mipster(current_context);
  else if (machine == DIPSTER)
    exit_code = mipster(current_context);
  else if (machine == RIPSTER)
    exit_code = mipster(current_context);
  else if (machine == MONSTER)
    exit_code = monster(current_context);
  else if (machine == MINSTER)
    exit_code = minster(current_context);
  else if (machine == MOBSTER)
    exit_code = mobster(current_context);
  else if (machine == HYPSTER)
    if (is_boot_level_zero())
      // no hypster on boot level zero
      exit_code = mipster(current_context);
    else
      exit_code = hypster(current_context);
  else
    // change 0 to anywhere between 0% to 100% mipster
    exit_code = mixter(current_context, 0);

  run = 0;

  printf3("%s: selfie terminating %s with exit code %d\n", selfie_name,
    get_name(current_context),
    (char*) sign_extend(exit_code, SYSCALL_BITWIDTH));

  print_profile();

  symbolic = 0;
  record   = 0;

  debug_syscalls = 0;
  debug          = 0;

  return exit_code;
}

void print_usage() {
  printf3("%s: usage: selfie { %s } [ %s ]\n", selfie_name,
    "-c { source } | -o binary | [ -s | -S ] assembly | -l binary",
    "( -m | -d | -r | -y | -min | -mob | -se | -mc ) 0-4096 ... ");
}

uint64_t selfie() {
  char* option;

  if (number_of_remaining_arguments() == 0)
    print_usage();
  else {
    init_scanner();
    init_register();
    init_interpreter();

    while (number_of_remaining_arguments() > 0) {
      option = get_argument();

      if (string_compare(option, "-c"))
        selfie_compile();
      else if (number_of_remaining_arguments() == 0) {
        // remaining options have at least one argument
        print_usage();

        return EXITCODE_BADARGUMENTS;
      } else if (string_compare(option, "-o"))
        selfie_output(get_argument());
      else if (string_compare(option, "-s"))
        selfie_disassemble(0);
      else if (string_compare(option, "-S"))
        selfie_disassemble(1);
      else if (string_compare(option, "-l"))
        selfie_load();
      else if (string_compare(option, "-m"))
        return selfie_run(MIPSTER);
      else if (string_compare(option, "-d"))
        return selfie_run(DIPSTER);
      else if (string_compare(option, "-r"))
        return selfie_run(RIPSTER);
      else if (string_compare(option, "-y"))
        return selfie_run(HYPSTER);
      else if (string_compare(option, "-min"))
        return selfie_run(MINSTER);
      else if (string_compare(option, "-mob"))
        return selfie_run(MOBSTER);
      else if (string_compare(option, "-se"))
        return selfie_run(MONSTER);
      else if (string_compare(option, "-mc"))
        return selfie_model_generate();
      else {
        print_usage();

        return EXITCODE_BADARGUMENTS;
      }
    }
  }

  return EXITCODE_NOERROR;
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

int main(int argc, char** argv) {
  init_selfie((uint64_t) argc, (uint64_t*) argv);

  init_library();
  init_scanner();

  selfie_sat();

  return EXITCODE_NOERROR;
}