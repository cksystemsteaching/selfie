/*
Copyright (c) 2015-2020, the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

http://selfie.cs.uni-salzburg.at

Monster is a hybrid symbolic execution and bounded model checking
engine that implements a sound and (up to a given bound) complete
translation of RISC-U code to SMT-LIB formulae. Monster serves as
research platform and facilitates teaching the absolute basics of
bit-precise reasoning on real code.

Given a RISC-U binary (or C* source code compiled to RISC-U, including
all of selfie and monster itself) and bounds on the number of machine
instructions (maximum execution depth) and the number of conditional
branch instructions (branching limit) to be executed on any code path,
monster generates an SMT-LIB file that models the bit-precise behavior
of the binary up to the maximum execution depth and branching limit on
a 64-bit machine with 4GB of memory. The SMT formulae of the model are
satisfiable if and only if there is input to the code such that the
code exits with non-zero exit codes or performs division by zero when
executing no more instructions than the maximum execution depth and no
more conditional branch instructions than the branching limit.

The first console argument is interpreted as maximum execution depth
where value zero means that the depth is unbounded. The following
optional console argument is interpreted as non-default branching
limit where value zero means that any conditional branch instruction
makes the engine backtrack. The following optional console argument
--merge-enabled instructs monster to generate a single SMT-LIB
formula for bounded model checking by merging all code paths (rather
than one SMT-LIB formula for each code path as in symbolic execution).

Any remaining console arguments are uninterpreted and passed on as
console arguments to the modeled RISC-U binary.

Monster is inspired by Professor Armin Biere from JKU Linz.
*/

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void implement_symbolic_exit(uint64_t* context);
void implement_symbolic_read(uint64_t* context);
void implement_symbolic_write(uint64_t* context);

uint64_t down_load_concrete_string(uint64_t* table, uint64_t vstring, char* s);
void     implement_symbolic_openat(uint64_t* context);

// -----------------------------------------------------------------
// ------------------------ HYPSTER SYSCALL ------------------------
// -----------------------------------------------------------------

uint64_t* mipster_symbolic_switch(uint64_t* to_context, uint64_t timeout);

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------    A R C H I T E C T U R E    -----------------
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
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

void constrain_lui();
void constrain_addi();

void constrain_add_sub_mul_divu_remu_sltu(char* operator);

void zero_extend_sltu();
void constrain_ld();

void constrain_sd();

void constrain_beq();
void constrain_jalr();

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void execute_symbolically();

void run_symbolically_until_exception();

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- CONTEXTS ---------------------------
// -----------------------------------------------------------------

uint64_t* new_symbolic_context();

void      copy_call_stack(uint64_t* from_context, uint64_t* to_context);
uint64_t* copy_symbolic_context(uint64_t* original, uint64_t location, char* condition);

// symbolic context extension:
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

void set_execution_depth(uint64_t* context, uint64_t depth)   { *(context + 17) =            depth; }
void set_path_condition(uint64_t* context, char* path)        { *(context + 18) = (uint64_t) path; }
void set_symbolic_memory(uint64_t* context, uint64_t* memory) { *(context + 19) = (uint64_t) memory; }
void set_symbolic_regs(uint64_t* context, uint64_t* regs)     { *(context + 20) = (uint64_t) regs; }
void set_beq_counter(uint64_t* context, uint64_t counter)     { *(context + 21) =            counter; }
void set_merge_location(uint64_t* context, uint64_t location) { *(context + 22) =            location; }
void set_merge_partner(uint64_t* context, uint64_t* partner)  { *(context + 23) = (uint64_t) partner; }
void set_call_stack(uint64_t* context, uint64_t* stack)       { *(context + 24) = (uint64_t) stack; }

// -----------------------------------------------------------------
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

uint64_t* create_symbolic_context(uint64_t* parent, uint64_t* vctxt);

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

uint64_t handle_symbolic_system_call(uint64_t* context);
uint64_t handle_symbolic_division_by_zero(uint64_t* context);
uint64_t handle_symbolic_timer(uint64_t* context);
uint64_t handle_symbolic_merge(uint64_t* context);
uint64_t handle_symbolic_recursion(uint64_t* context);

uint64_t handle_symbolic_exception(uint64_t* context);

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

void monster(uint64_t* to_context);

uint64_t selfie_run_symbolically();

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

uint64_t* mergeable_contexts = (uint64_t*) 0; // contexts that have reached their merge location
uint64_t* waiting_contexts   = (uint64_t*) 0; // contexts that were created at a symbolic beq instruction and are waiting to be executed

uint64_t* current_mergeable_context = (uint64_t*) 0; // current context with which the active context can possibly be merged

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t DELETED                         = -1; // indicates that a symbolic memory word has been deleted
uint64_t MERGED                          = -2; // indicates that a symbolic memory word has been merged
uint64_t BEGIN_OF_SHARED_SYMBOLIC_MEMORY = -3; // indicates the beginning of the shared symbolic memory space

uint64_t beq_limit = 35; // limit of symbolic beq instructions on each part of the path between two merge locations

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void implement_symbolic_exit(uint64_t* context) {
  // parameter;
  uint64_t signed_int_exit_code;

  signed_int_exit_code = *(get_regs(context) + REG_A0);

  set_exit_code(context, sign_shrink(signed_int_exit_code, SYSCALL_BITWIDTH));

  print("\n(push 1)\n");

  printf2("(assert (and %s (not (= %s (_ bv0 64))))); exit in ",
    path_condition,
    smt_value(*(registers + REG_A0), (char*) *(reg_sym + REG_A0)));
  print_code_context_for_instruction(pc);

  if (debug_merge)
    printf1(" -> exiting context: %u", (char*) context);

  print("\n(check-sat)\n(get-model)\n(pop 1)\n");
}

void implement_symbolic_read(uint64_t* context) {
  // parameters
  // fd not needed
  uint64_t vbuffer;
  uint64_t size;

  // local variables
  uint64_t read_total;
  uint64_t bytes_to_read;
  uint64_t failed;

  vbuffer = *(get_regs(context) + REG_A1);
  size    = *(get_regs(context) + REG_A2);

  read_total = 0;

  bytes_to_read = SIZEOFUINT64;

  failed = 0;

  while (size > 0) {
    if (size < bytes_to_read)
      bytes_to_read = size;

    if (is_valid_virtual_address(vbuffer)) {
      if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
        store_symbolic_memory(vbuffer, 0, 0, smt_variable("i", bytes_to_read * 8), bytes_to_read * 8);

        // save symbolic memory here since context switching has already happened
        set_symbolic_memory(context, symbolic_memory);

        read_total = read_total + bytes_to_read;

        size = size - bytes_to_read;

        if (size > 0)
          vbuffer = vbuffer + SIZEOFUINT64;
      } else {
        failed = 1;

        size = 0;

        if (debug_read)
          printf2("%s: reading into virtual address %p failed because the address is unmapped\n", selfie_name,
            (char*) vbuffer);
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
}

void implement_symbolic_write(uint64_t* context) {
  // parameters
  // fd not needed
  uint64_t vbuffer;
  uint64_t size;

  // local variables
  uint64_t written_total;
  uint64_t bytes_to_write;
  uint64_t failed;

  vbuffer = *(get_regs(context) + REG_A1);
  size    = *(get_regs(context) + REG_A2);

  written_total = 0;

  bytes_to_write = SIZEOFUINT64;

  failed = 0;

  while (size > 0) {
    if (size < bytes_to_write)
      bytes_to_write = size;

    if (is_valid_virtual_address(vbuffer)) {
      if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
        // TODO: What should symbolically executed code actually output?

        written_total = written_total + bytes_to_write;

        size = size - bytes_to_write;

        if (size > 0)
          vbuffer = vbuffer + SIZEOFUINT64;
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
}

uint64_t down_load_concrete_string(uint64_t* table, uint64_t vaddr, char* s) {
  uint64_t i;
  uint64_t* sword;
  uint64_t j;

  i = 0;

  while (i < MAX_FILENAME_LENGTH / SIZEOFUINT64) {
    if (is_valid_virtual_address(vaddr)) {
      if (is_virtual_address_mapped(table, vaddr)) {
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
      } else {
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

void implement_symbolic_openat(uint64_t* context) {
  // parameters
  uint64_t vfilename;
  // flags not needed
  // mode not needed

  vfilename = *(get_regs(context) + REG_A1);

  if (down_load_concrete_string(get_pt(context), vfilename, filename_buffer))
    // TODO: check if opening vfilename has been attempted before
    *(get_regs(context) + REG_A0) = 0; // file descriptor 0
  else
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

// -----------------------------------------------------------------
// ------------------------ HYPSTER SYSCALL ------------------------
// -----------------------------------------------------------------

uint64_t* mipster_symbolic_switch(uint64_t* to_context, uint64_t timeout) {
  path_condition  = get_path_condition(to_context);
  reg_sym         = get_symbolic_regs(to_context);
  symbolic_memory = get_symbolic_memory(to_context);

  current_context = do_switch(current_context, to_context, timeout);

  run_symbolically_until_exception();

  save_context(current_context);

  set_path_condition(current_context, path_condition);
  set_symbolic_memory(current_context, symbolic_memory);

  return current_context;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------    A R C H I T E C T U R E    -----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

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
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

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

    waiting_context = copy_symbolic_context(current_context, pc + imm, smt_binary("and", pvar, bvar));

    // the copied context is executed later and takes the other path
    add_waiting_context(waiting_context);

    path_condition = smt_binary("and", pvar, smt_unary("not", bvar));

    // set the merge location only when merging is enabled
    if (merge_enabled)
      set_merge_location(current_context, find_merge_location(imm));

    if (debug_merge) {
      print("; a new context was created at ");
      print_code_context_for_instruction(pc);
      printf4(" -> active context: %u, waiting context: %u (merge locations: %x, %x)\n", (char*) current_context, (char*) waiting_context, (char*) get_merge_location(current_context), (char*) get_merge_location(waiting_context));
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
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

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

void run_symbolically_until_exception() {
  trap = 0;

  while (trap == 0) {
    fetch();
    decode();
    execute_symbolically();

    if (timer != TIMEROFF)
      set_execution_depth(current_context, get_execution_depth(current_context) + 1);

    interrupt();

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
        throw_exception(EXCEPTION_SYMBOLICMERGE, 0);
  }

  trap = 0;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- CONTEXTS ---------------------------
// -----------------------------------------------------------------

uint64_t* new_symbolic_context() {
  // insert new symbolic context at top of free-list of contexts
  free_context(allocate_symbolic_context());

  // new symbolic context is taken from top of free-list of contexts
  return new_context();
}

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

uint64_t* copy_symbolic_context(uint64_t* original, uint64_t location, char* condition) {
  uint64_t* context;
  uint64_t* begin_of_shared_symbolic_memory;
  uint64_t r;

  context = new_symbolic_context();

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
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

uint64_t* create_symbolic_context(uint64_t* parent, uint64_t* vctxt) {
  uint64_t* context;

  context = new_symbolic_context();

  init_context(context, parent, vctxt);

  set_execution_depth(context, 0);
  set_path_condition(context, "true");
  set_symbolic_memory(context, (uint64_t*) 0);
  set_symbolic_regs(context, zalloc(NUMBEROFREGISTERS * REGISTERSIZE));
  set_beq_counter(context, 0);
  set_merge_location(context, -1);
  set_merge_partner(context, (uint64_t*) 0);

  if (debug_create)
    printf3("%s: parent context %p created child context %p\n", selfie_name,
      (char*) parent,
      (char*) used_contexts);

  return context;
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

uint64_t handle_symbolic_system_call(uint64_t* context) {
  uint64_t a7;

  set_exception(context, EXCEPTION_NOEXCEPTION);

  a7 = *(get_regs(context) + REG_A7);

  if (a7 == SYSCALL_BRK)
    implement_brk(context);
  else if (a7 == SYSCALL_READ)
    implement_symbolic_read(context);
  else if (a7 == SYSCALL_WRITE)
    implement_symbolic_write(context);
  else if (a7 == SYSCALL_OPENAT)
    implement_symbolic_openat(context);
  else if (a7 == SYSCALL_EXIT) {
    implement_symbolic_exit(context);

    // TODO: exit only if all contexts have exited
    return EXIT;
  } else {
    printf2("%s: unknown system call %u\n", selfie_name, (char*) a7);

    set_exit_code(context, EXITCODE_UNKNOWNSYSCALL);

    return EXIT;
  }

  return DONOTEXIT;
}

uint64_t handle_symbolic_division_by_zero(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  // check if this division by zero is reachable
  print("(push 1)\n");
  printf1("(assert %s); division by zero detected; check if this division by zero is reachable", path_condition);
  print("\n(check-sat)\n(get-model)\n(pop 1)\n");

  // we terminate the execution of the context, because if the location is not reachable,
  // the rest of the path is not reachable either, and otherwise
  // the execution would be terminated by this error anyway
  set_exit_code(context, EXITCODE_DIVISIONBYZERO);

  return EXIT;
}

uint64_t handle_symbolic_timer(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  printf1("; timeout in ", path_condition);
  print_code_context_for_instruction(pc);
  if (debug_merge)
    printf1(" -> timed out context: %u", (char*) context);
  println();

  return EXIT;
}

uint64_t handle_symbolic_merge(uint64_t* context) {
  add_mergeable_context(current_context);

  set_exception(context, EXCEPTION_NOEXCEPTION);

  return MERGE;
}

uint64_t handle_symbolic_recursion(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  return RECURSION;
}

uint64_t handle_symbolic_exception(uint64_t* context) {
  uint64_t exception;

  exception = get_exception(context);

  if (exception == EXCEPTION_SYSCALL)
    return handle_symbolic_system_call(context);
  else if (exception == EXCEPTION_PAGEFAULT)
    return handle_page_fault(context);
  else if (exception == EXCEPTION_DIVISIONBYZERO)
    return handle_symbolic_division_by_zero(context);
  else if (exception == EXCEPTION_TIMER)
    return handle_symbolic_timer(context);
  else if (exception == EXCEPTION_SYMBOLICMERGE)
    return handle_symbolic_merge(context);
  else if (exception == EXCEPTION_SYMBOLICRECURSION)
    return handle_symbolic_recursion(context);
  else if (exception == EXCEPTION_INVALIDADDRESS) {
    // check if this invalid memory access is reachable
    print("(push 1)\n");
    printf1("(assert %s); invalid memory access detected; check if this invalid memory access is reachable", path_condition);
    print("\n(check-sat)\n(get-model)\n(pop 1)\n");

    set_exit_code(context, EXITCODE_SYMBOLICEXECUTIONERROR);

    // we terminate the execution of the context, because if the location is not reachable,
    // the rest of the path is not reachable either, and otherwise
    // the execution would be terminated by this error anyway
    return EXIT;
  } else {
    printf2("%s: context %s throws uncaught ", selfie_name, get_name(context));
    print_exception(exception, get_faulting_page(context));
    println();

    set_exit_code(context, EXITCODE_UNCAUGHTEXCEPTION);

    return EXIT;
  }
}

// -----------------------------------------------------------------
// ------------------- SYMBOLIC EXECUTION ENGINE -------------------
// -----------------------------------------------------------------

char* bv_constant(uint64_t value) {
  char* string;

  string = string_alloc(5 + 20 + 4); // 64-bit numbers require up to 20 decimal digits

  sprintf1(string, "(_ bv%u 64)", (char*) value);

  return string;
}

char* bv_variable(uint64_t bits) {
  char* string;

  string = string_alloc(10 + 2); // up to 64-bit variables require up to 2 decimal digits

  sprintf1(string, "(_ BitVec %u)", (char*) bits);

  return string;
}

char* bv_zero_extension(uint64_t bits) {
  char* string;

  string = string_alloc(15 + 2); // up to 64-bit variables require up to 2 decimal digits

  sprintf1(string, "(_ zero_extend %u)", (char*) (CPUBITWIDTH - bits));

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

  sprintf2(svar, "%s%u", prefix, (char*) variable_version);

  printf2("(declare-fun %s () (_ BitVec %u)); variable for ", svar, (char*) bits);
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
    throw_exception(EXCEPTION_SYMBOLICRECURSION, 0);
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
    printf2(" -> active context: %u, mergeable context: %u", (char*) active_context, (char*) mergeable_context);

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
              throw_exception(EXCEPTION_SYMBOLICRECURSION, 0);
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
              throw_exception(EXCEPTION_SYMBOLICRECURSION, 0);
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

uint64_t compare_call_stacks(uint64_t* active_context, uint64_t* mergeable_context) {
  // 0, call stacks are equal
  // 1, active_context has longer call stack
  // 2, mergeable_context has longer call stack
  // 3, an entry is different
  uint64_t* entry_active;
  uint64_t* entry_mergeable;

  uint64_t active_context_stack_length;
  uint64_t mergeable_context_stack_length;

  active_context_stack_length = 0;
  mergeable_context_stack_length = 0;

  entry_active = get_call_stack(active_context);
  entry_mergeable = get_call_stack(mergeable_context);

  if (debug_merge)
    printf1("; Call stack of active context (%u):\n", (char*) active_context);

  while(entry_active) {

    if (debug_merge)
      printf1("; %x\n", (char*) *(entry_active + 1));

    active_context_stack_length = active_context_stack_length + 1;
    entry_active = (uint64_t*) *(entry_active + 0);
  }

  if (debug_merge)
    printf1("; Call stack of mergeable context (%u):\n", (char*) mergeable_context);

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

void monster(uint64_t* to_context) {
  uint64_t  timeout;
  uint64_t* from_context;
  uint64_t  exception;

  if (debug_merge)
    from_context = (uint64_t*) 0;

  printf1("; %s\n\n", SELFIE_URL);

  printf1("; SMT-LIB formulae generated by %s for\n", selfie_name);
  printf1("; RISC-V code obtained from %s with\n", binary_name);
  if (max_execution_depth) printf1("; %u", (char*) max_execution_depth); else print("; unbounded");
  printf1(" execution depth, branching limit of %u, and merging", (char*) beq_limit);
  if (merge_enabled) print(" enabled\n\n"); else print(" disabled\n\n");

  print("(set-option :produce-models true)\n");
  print("(set-option :incremental true)\n");
  print("(set-logic QF_BV)\n\n");

  timeout = max_execution_depth - get_execution_depth(to_context);

  while (1) {
    if (debug_merge)
      if (from_context != (uint64_t*) 0)
        printf4("; switching from context %u to context %u (merge locations: %x, %x)\n",
          (char*) from_context, (char*) to_context,
          (char*) get_merge_location(from_context), (char*) get_merge_location(to_context));

    from_context = mipster_symbolic_switch(to_context, timeout);

    if (get_parent(from_context) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      to_context = get_parent(from_context);

      timeout = TIMEROFF;
    } else {
      exception = handle_symbolic_exception(from_context);

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

          return;
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

uint64_t selfie_run_symbolically() {
  if (string_compare(argument, "-")) {
    if (number_of_remaining_arguments() > 0) {
      max_execution_depth = atoi(peek_argument(0));

      // checking for the (optional) branching limit argument
      if (number_of_remaining_arguments() > 1)
        if (string_compare(peek_argument(1), "--merge-enabled") == 0)
          if (string_compare(peek_argument(1), "--debug-merge") == 0) {
            // assert: argument is an integer representing the branching limit
            beq_limit = atoi(peek_argument(1));

            get_argument();
          }

      // checking for the (optional) argument whether to enable merging (in debug mode) or not
      if (number_of_remaining_arguments() > 1) {
        if (string_compare(peek_argument(1), "--merge-enabled")) {
          merge_enabled = 1;

          get_argument();
        } else if (string_compare(peek_argument(1), "--debug-merge")) {
          debug_merge = 1;
          merge_enabled = 1;

          get_argument();
        }
      }

      if (binary_length == 0) {
        printf1("%s: nothing to run symbolically\n", selfie_name);

        return EXITCODE_BADARGUMENTS;
      }

      // use extension ".smt" in name of SMT-LIB file
      smt_name = replace_extension(binary_name, "smt");

      // assert: smt_name is mapped and not longer than MAX_FILENAME_LENGTH

      smt_fd = open_write_only(smt_name);

      if (signed_less_than(smt_fd, 0)) {
        printf2("%s: could not create SMT-LIB output file %s\n", selfie_name, smt_name);

        exit(EXITCODE_IOERROR);
      }

      reset_interpreter();
      reset_profiler();
      reset_microkernel();

      init_memory(1);

      current_context = create_symbolic_context(MY_CONTEXT, 0);

      // assert: number_of_remaining_arguments() > 0

      boot_loader(current_context);

      printf3("%s: monster symbolically executing %s with %uMB physical memory\n", selfie_name,
        binary_name,
        (char*) (page_frame_memory / MEGABYTE));

      output_name = smt_name;
      output_fd   = smt_fd;

      run      = 1;
      symbolic = 1;

      monster(current_context);

      symbolic = 0;
      run      = 0;

      output_name = (char*) 0;
      output_fd   = 1;

      printf2("%s: monster terminating %s\n", selfie_name, get_name(current_context));

      print_profile();

      printf3("%s: %u characters of SMT-LIB formulae written into %s\n", selfie_name,
        (char*) number_of_written_characters,
        smt_name);

      return EXITCODE_NOERROR;
    } else
      return EXITCODE_BADARGUMENTS;
  } else
    return EXITCODE_BADARGUMENTS;
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

int main(int argc, char** argv) {
  uint64_t exit_code;

  init_selfie((uint64_t) argc, (uint64_t*) argv);

  init_library();

  exit_code = selfie();

  if (exit_code != EXITCODE_NOARGUMENTS)
    exit_code = selfie_run_symbolically();

  if (exit_code != EXITCODE_NOERROR)
    print_synopsis(" - maximum-execution-depth [ branching-limit ] [ --merge-enabled | --debug-merge ] ...");

  if (exit_code == EXITCODE_NOARGUMENTS)
    exit_code = EXITCODE_NOERROR;

  return exit_code;
}