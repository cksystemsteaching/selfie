/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

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

uint64_t down_load_concrete_string(uint64_t* context, uint64_t vstring, char* s);
void     implement_symbolic_openat(uint64_t* context);

// -----------------------------------------------------------------
// ------------------------- MONSTER SWITCH ------------------------
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
void      update_begin_of_shared_symbolic_memory(uint64_t* context, uint64_t* partner);

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
  return smalloc(2 * sizeof(uint64_t*) + 3 * sizeof(uint64_t));
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
void constrain_load();

void constrain_store();

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

uint64_t* copy_symbolic_context(uint64_t* original, uint64_t location, char* condition);

// symbolic context extension:
// +----+-----------------+
// | +0 | execution depth | number of executed instructions
// | +1 | path condition  | pointer to path condition
// | +2 | symbolic memory | pointer to symbolic memory
// | +3 | symbolic regs   | pointer to symbolic registers
// | +4 | beq counter     | number of executed symbolic beq instructions
// | +5 | merge partner   | pointer to the context from which this context was created
// | +6 | call stack      | pointer to the corresponding node in the call stack tree
// +----+-----------------+

uint64_t* allocate_symbolic_context() {
  return smalloc(CONTEXTENTRIES * sizeof(uint64_t) + 5 * sizeof(uint64_t*) + 2 * sizeof(uint64_t));
}

uint64_t  get_execution_depth(uint64_t* context) { return             *(context + CONTEXTENTRIES); }
char*     get_path_condition(uint64_t* context)  { return (char*)     *(context + CONTEXTENTRIES + 1); }
uint64_t* get_symbolic_memory(uint64_t* context) { return (uint64_t*) *(context + CONTEXTENTRIES + 2); }
uint64_t* get_symbolic_regs(uint64_t* context)   { return (uint64_t*) *(context + CONTEXTENTRIES + 3); }
uint64_t  get_beq_counter(uint64_t* context)     { return             *(context + CONTEXTENTRIES + 4); }
uint64_t* get_merge_partner(uint64_t* context)   { return (uint64_t*) *(context + CONTEXTENTRIES + 5); }
uint64_t* get_call_stack(uint64_t* context)      { return (uint64_t*) *(context + CONTEXTENTRIES + 6); }

void set_execution_depth(uint64_t* context, uint64_t depth)   { *(context + CONTEXTENTRIES)     =            depth; }
void set_path_condition(uint64_t* context, char* condition)   { *(context + CONTEXTENTRIES + 1) = (uint64_t) condition; }
void set_symbolic_memory(uint64_t* context, uint64_t* memory) { *(context + CONTEXTENTRIES + 2) = (uint64_t) memory; }
void set_symbolic_regs(uint64_t* context, uint64_t* regs)     { *(context + CONTEXTENTRIES + 3) = (uint64_t) regs; }
void set_beq_counter(uint64_t* context, uint64_t counter)     { *(context + CONTEXTENTRIES + 4) =            counter; }
void set_merge_partner(uint64_t* context, uint64_t* partner)  { *(context + CONTEXTENTRIES + 5) = (uint64_t) partner; }
void set_call_stack(uint64_t* context, uint64_t* stack)       { *(context + CONTEXTENTRIES + 6) = (uint64_t) stack; }

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

uint64_t handle_symbolic_exception(uint64_t* context);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t EXITCODE_SYMBOLICEXECUTIONERROR = 1;

uint64_t SCHEDULE = 100; // extends DONOTEXIT and EXIT

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

void merge(uint64_t* active_context, uint64_t* mergeable_context, uint64_t location);
void merge_symbolic_memory_and_registers(uint64_t* active_context, uint64_t* mergeable_context);
void merge_symbolic_memory(uint64_t* active_context, uint64_t* mergeable_context);
void merge_registers(uint64_t* active_context, uint64_t* mergeable_context);

uint64_t* schedule_next_symbolic_context();
void      check_if_mergeable_and_merge_if_possible(uint64_t* context);

void add_child(uint64_t* parent, uint64_t* child);
void step_into_call(uint64_t* context, uint64_t address);
void step_out_of_call(uint64_t* context);

void use_stdout();
void use_file();

void monster(uint64_t* to_context);

uint64_t selfie_run_symbolically();

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t w = 0; // number of written characters

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

uint64_t* call_stack_tree = (uint64_t*) 0; // tree representing the program structure (each node represents a procedure call)

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t DELETED                         = -1; // indicates that a symbolic memory word has been deleted
uint64_t BEGIN_OF_SHARED_SYMBOLIC_MEMORY = -2; // indicates the beginning of the shared symbolic memory space

uint64_t beq_limit = 35; // limit of symbolic beq instructions on each path

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

  w = w
    + dprintf(output_fd, "\n(push 1)\n")
    + dprintf(output_fd, "(assert (and %s (not (= %s (_ bv0 64))))); exit in ",
        path_condition,
        smt_value(*(registers + REG_A0), (char*) *(reg_sym + REG_A0)))
    + print_code_context_for_instruction(pc);

  if (debug_merge)
    w = w + dprintf(output_fd, " -> exiting context: 0x%08lX", (uint64_t) context);

  w = w + dprintf(output_fd, "\n(check-sat)\n(get-model)\n(pop 1)\n");
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

  bytes_to_read = WORDSIZE;

  failed = 0;

  while (size > 0) {
    if (size < bytes_to_read)
      bytes_to_read = size;

    if (is_virtual_address_valid(vbuffer, WORDSIZE))
      if (is_data_stack_heap_address(context, vbuffer))
        if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
          store_symbolic_memory(vbuffer, 0, 0, smt_variable("i", bytes_to_read * 8), bytes_to_read * 8);

          // save symbolic memory here since context switching has already happened
          set_symbolic_memory(context, symbolic_memory);

          read_total = read_total + bytes_to_read;

          size = size - bytes_to_read;

          if (size > 0)
            vbuffer = vbuffer + WORDSIZE;
        } else {
          failed = 1;

          size = 0;

          use_stdout();
          printf("%s: reading into virtual address 0x%08lX failed because the address is unmapped\n", selfie_name, vbuffer);
          use_file();
        }
      else {
        failed = 1;

        size = 0;

        use_stdout();
        printf("%s: reading into virtual address 0x%08lX failed because the address is in an invalid segment\n", selfie_name, vbuffer);
        use_file();
      }
    else {
      failed = 1;

      size = 0;

      use_stdout();
      printf("%s: reading into virtual address 0x%08lX failed because the address is invalid\n", selfie_name, vbuffer);
      use_file();
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

  bytes_to_write = WORDSIZE;

  failed = 0;

  while (size > 0) {
    if (size < bytes_to_write)
      bytes_to_write = size;

    if (is_virtual_address_valid(vbuffer, WORDSIZE))
      if (is_data_stack_heap_address(context, vbuffer))
        if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
          // TODO: What should symbolically executed code actually output?

          written_total = written_total + bytes_to_write;

          size = size - bytes_to_write;

          if (size > 0)
            vbuffer = vbuffer + WORDSIZE;
        } else {
          failed = 1;

          size = 0;

          use_stdout();
          printf("%s: writing from virtual address 0x%08lX failed because the address is unmapped\n", selfie_name, vbuffer);
          use_file();
        }
      else {
        failed = 1;

        size = 0;

        use_stdout();
        printf("%s: writing from virtual address 0x%08lX failed because the address is in an invalid segment\n", selfie_name, vbuffer);
        use_file();
      }
    else {
      failed = 1;

      size = 0;

      use_stdout();
      printf("%s: writing from virtual address 0x%08lX failed because the address is invalid\n", selfie_name, vbuffer);
      use_file();
    }
  }

  if (failed)
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);
  else
    *(get_regs(context) + REG_A0) = written_total;

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

uint64_t down_load_concrete_string(uint64_t* context, uint64_t vaddr, char* s) {
  uint64_t i;
  uint64_t* sword;
  uint64_t j;

  i = 0;

  while (i < MAX_FILENAME_LENGTH) {
    if (is_virtual_address_valid(vaddr, WORDSIZE))
      if (is_data_stack_heap_address(context, vaddr)) {
        if (is_virtual_address_mapped(get_pt(context), vaddr)) {
          sword = load_symbolic_memory(vaddr);

          if (sword) {
            if (is_symbolic_value(sword)) {
              use_stdout();

              printf("%s: detected symbolic value ", selfie_name);
              print_symbolic_memory(sword);
              printf(" in filename of open call\n");

              exit(EXITCODE_SYMBOLICEXECUTIONERROR);
            } else
              // CAUTION: at boot levels higher than zero, s is only accessible
              // in C* at machine word granularity, not individual characters
              store_word((uint64_t*) s, i, 1, get_word_value(sword));
          } else
            // assert: vaddr is mapped
            store_word((uint64_t*) s, i, 1, load_virtual_memory(get_pt(context), vaddr));
        } else {
          use_stdout();
          printf("%s: opening file failed because the file name address 0x%08lX is unmapped\n", selfie_name, vaddr);
          use_file();

          return 0;
        }

        // WORDSIZE may be less than sizeof(uint64_t)
        j = i % sizeof(uint64_t);

        // check if string ends in the current word
        while (j - i % sizeof(uint64_t) < WORDSIZE) {
          if (load_character((char*) ((uint64_t*) s + i / sizeof(uint64_t)), j) == 0)
            return 1;

          j = j + 1;
        }

        // advance to the next word in virtual memory
        vaddr = vaddr + WORDSIZE;

        // advance to the corresponding word in our memory
        i = i + WORDSIZE;
      } else {
        use_stdout();
        printf("%s: opening file failed because the file name address 0x%08lX is in an invalid segment\n", selfie_name, vaddr);
        use_file();

        return 0;
      }
    else {
      use_stdout();
      printf("%s: opening file failed because the file name address 0x%08lX is invalid\n", selfie_name, vaddr);
      use_file();

      return 0;
    }
  }

  use_stdout();
  printf("%s: opening file failed because the file name is too long at address 0x%08lX\n", selfie_name, vaddr);
  use_file();

  return 0;
}

void implement_symbolic_openat(uint64_t* context) {
  // parameters
  uint64_t vfilename;
  // flags not needed
  // mode not needed

  vfilename = *(get_regs(context) + REG_A1);

  if (down_load_concrete_string(context, vfilename, filename_buffer))
    // TODO: check if opening vfilename has been attempted before
    *(get_regs(context) + REG_A0) = 0; // file descriptor 0
  else
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

// -----------------------------------------------------------------
// ------------------------- MONSTER SWITCH ------------------------
// -----------------------------------------------------------------

uint64_t* mipster_symbolic_switch(uint64_t* to_context, uint64_t timeout) {
  uint64_t execution_depth;

  path_condition  = get_path_condition(to_context);
  reg_sym         = get_symbolic_regs(to_context);
  symbolic_memory = get_symbolic_memory(to_context);

  restore_context(to_context);

  do_switch(to_context, timeout);

  execution_depth = get_total_number_of_instructions();

  run_symbolically_until_exception();

  execution_depth = get_total_number_of_instructions() - execution_depth;

  save_context(current_context);

  set_execution_depth(current_context, get_execution_depth(current_context) + execution_depth);
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
    set_word_symbolic(sword, smt_variable("m", WORDSIZEINBITS));

    w = w
      + dprintf(output_fd, "(assert (= %s %s)); store in ", get_word_symbolic(sword), sym)
      + print_code_context_for_instruction(pc)
      + dprintf(output_fd, "\n");
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

void update_begin_of_shared_symbolic_memory(uint64_t* context, uint64_t* partner) {
  uint64_t* sword_of_shared_store;
  uint64_t* sword;

  if (context == (uint64_t*) 0)
    return;

  sword_of_shared_store = (uint64_t*) 0;

  sword = get_symbolic_memory(partner);

  while (sword) {
    if (get_word_address(sword) == BEGIN_OF_SHARED_SYMBOLIC_MEMORY) {
      // remember beginning of shared symbolic memory portion in partner context
      sword_of_shared_store = get_next_word(sword);
      sword = (uint64_t*) 0;
    } else
      sword = get_next_word(sword);
  }

  sword = get_symbolic_memory(context);

  while (sword) {
    if (get_word_address(sword) == BEGIN_OF_SHARED_SYMBOLIC_MEMORY) {
      // only unshare symbolic memory if both contexts point to the same shared portion
      if (get_next_word(sword) == sword_of_shared_store)
        set_word_address(sword, DELETED);
      else if (debug_merge)
        w = w + dprintf(output_fd, "; unbalanced shared symbolic memory detected, skip unsharing\n");

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
    w = w + dprintf(output_fd, "%s", get_word_symbolic(sword));

  w = w + dprintf(output_fd, "[0x%lX]@0x%lX\n", get_word_value(sword), get_word_address(sword));
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
    if (string_compare(operator, "bvudiv"))
      w = w
        + dprintf(output_fd, "(push 1)\n")
        + dprintf(output_fd, "(assert (and %s %s)); check if a division by zero is possible", path_condition, smt_binary("=", op2, bv_constant(0)))
        + dprintf(output_fd, "\n(check-sat)\n(get-model)\n(pop 1)\n");
  }
}

void zero_extend_sltu() {
  if (rd != REG_ZR)
    if (*(reg_sym + rd))
      *(reg_sym + rd) = (uint64_t) smt_ternary("ite", (char*) *(reg_sym + rd), bv_constant(1), bv_constant(0));
}

void constrain_load() {
  uint64_t vaddr;
  uint64_t* sword;
  uint64_t a;

  // load double word

  if (*(reg_sym + rs1)) {
    use_stdout();

    // symbolic memory addresses not yet supported
    printf("%s: symbolic memory address in load instruction at 0x%lX", selfie_name, pc);
    print_code_line_number_for_instruction(pc, code_start);
    printf("\n");

    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  read_register(rs1);

  vaddr = *(registers + rs1) + imm;

  if (is_virtual_address_valid(vaddr, WORDSIZE)) {
    if (is_valid_segment_read(vaddr)) {
      if (is_virtual_address_mapped(pt, vaddr)) {
        // semantics of load double word
        if (rd != REG_ZR) {
          sword = load_symbolic_memory(vaddr);

          if (sword) {
            *(registers + rd) = get_word_value(sword);

            if (get_number_of_bits(sword) < WORDSIZEINBITS)
              *(reg_sym + rd) = (uint64_t) smt_unary(bv_zero_extension(get_number_of_bits(sword)), get_word_symbolic(sword));
            else
              *(reg_sym + rd) = (uint64_t) get_word_symbolic(sword);
          } else {
            *(registers + rd) = load_virtual_memory(pt, vaddr);
            *(reg_sym + rd)   = 0;
          }
        }

        write_register(rd);

        // keep track of instruction address for profiling loads
        a = (pc - code_start) / INSTRUCTIONSIZE;

        pc = pc + INSTRUCTIONSIZE;

        // keep track of number of loads in total
        ic_load = ic_load + 1;

        // and individually
        *(loads_per_instruction + a) = *(loads_per_instruction + a) + 1;
      } else
        throw_exception(EXCEPTION_PAGEFAULT, page_of_virtual_address(vaddr));
    } else
      throw_exception(EXCEPTION_SEGMENTATIONFAULT, vaddr);
  } else
    // invalid concrete memory address
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
}

void constrain_store() {
  uint64_t vaddr;
  uint64_t a;

  // store double word

  if (*(reg_sym + rs1)) {
    use_stdout();

    // symbolic memory addresses not yet supported
    printf("%s: symbolic memory address in sd instruction at 0x%lX", selfie_name, pc);
    print_code_line_number_for_instruction(pc, code_start);
    printf("\n");

    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  read_register(rs1);

  vaddr = *(registers + rs1) + imm;

  if (is_virtual_address_valid(vaddr, WORDSIZE)) {
    if (is_valid_segment_write(vaddr)) {
      if (is_virtual_address_mapped(pt, vaddr)) {
        // semantics of store double word
        store_symbolic_memory(vaddr,
          *(registers + rs2),
          (char*) *(reg_sym + rs2),
          0,
          WORDSIZEINBITS);

        // keep track of instruction address for profiling stores
        a = (pc - code_start) / INSTRUCTIONSIZE;

        pc = pc + INSTRUCTIONSIZE;

        // keep track of number of stores in total
        ic_store = ic_store + 1;

        // and individually
        *(stores_per_instruction + a) = *(stores_per_instruction + a) + 1;
      }  else
        throw_exception(EXCEPTION_PAGEFAULT, page_of_virtual_address(vaddr));
    } else
      throw_exception(EXCEPTION_SEGMENTATIONFAULT, vaddr);
  } else
    // invalid concrete memory address
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
}

void constrain_beq() {
  char* op1;
  char* op2;
  char* bvar;
  char* pvar;

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

  w = w
    + dprintf(output_fd, "(assert (= %s %s)); beq in ", bvar, smt_binary("=", op1, op2))
    + print_code_context_for_instruction(pc)
    + dprintf(output_fd, "\n");

  pvar = smt_variable("p", 1);

  w = w
    + dprintf(output_fd, "(assert (= %s %s)); path condition in ", pvar, path_condition)
    + print_code_context_for_instruction(pc)
    + dprintf(output_fd, "\n");

  // increase the number of executed symbolic beq instructions
  set_beq_counter(current_context, get_beq_counter(current_context) + 1);

  if (get_beq_counter(current_context) < beq_limit) {
    // save symbolic memory so that it is copied correctly afterwards
    set_symbolic_memory(current_context, symbolic_memory);

    // the copied context is executed later and takes the other path
    copy_symbolic_context(current_context, pc + imm, smt_binary("and", pvar, bvar));

    path_condition = smt_binary("and", pvar, smt_unary("not", bvar));

    pc = pc + INSTRUCTIONSIZE;
  }
}

void constrain_jalr() {
  if (*(reg_sym + rs1)) {
    use_stdout();

    // symbolic memory addresses not yet supported
    printf("%s: symbolic memory address in jalr instruction at 0x%lX", selfie_name, pc);
    print_code_line_number_for_instruction(pc, code_start);
    printf("\n");

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
  } else if (is == LOAD)
    constrain_load();
  else if (is == STORE)
    constrain_store();
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
      step_into_call(current_context, pc + imm);
    do_jal();
  } else if (is == JALR) {
    // pop off call stack, when we return from a procedure
    if (rd == REG_ZR)
      if (rs1 == REG_RA)
        if (imm == 0)
          step_out_of_call(current_context);
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
// ---------------------------- CONTEXTS ---------------------------
// -----------------------------------------------------------------

uint64_t* new_symbolic_context() {
  // insert new symbolic context at top of free-list of contexts
  free_context(allocate_symbolic_context());

  // new symbolic context is taken from top of free-list of contexts
  return new_context();
}

uint64_t* copy_symbolic_context(uint64_t* original, uint64_t location, char* condition) {
  uint64_t* context;
  uint64_t* begin_of_shared_symbolic_memory;
  uint64_t r;

  context = new_symbolic_context();

  // next context is set below

  set_pc(context, location);

  set_regs(context, smalloc(NUMBEROFREGISTERS * sizeof(uint64_t)));

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
  set_code_seg_start(context, get_code_seg_start(original));
  set_code_seg_size(context, get_code_seg_size(original));
  set_data_seg_start(context, get_data_seg_start(original));
  set_data_seg_size(context, get_data_seg_size(original));
  set_heap_seg_start(context, get_heap_seg_start(original));
  set_program_break(context, get_program_break(original));
  set_exception(context, get_exception(original));
  set_fault(context, get_fault(original));
  set_exit_code(context, get_exit_code(original));
  set_parent(context, get_parent(original));
  set_virtual_context(context, get_virtual_context(original));
  set_name(context, get_name(original));

  // profile
  set_ic_all(context, 0);
  set_lc_malloc(context, 0);
  set_ec_syscall(context, 0);
  set_ec_page_fault(context, 0);
  set_ec_timer(context, 0);
  set_mc_stack_peak(context, 0);
  set_mc_mapped_heap(context, 0);

  set_execution_depth(context, get_execution_depth(original));
  set_path_condition(context, condition);
  set_beq_counter(context, get_beq_counter(original));

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

  set_symbolic_regs(context, smalloc(NUMBEROFREGISTERS * sizeof(uint64_t*)));

  set_merge_partner(context, original);

  set_call_stack(context, get_call_stack(original));

  r = 0;

  while (r < NUMBEROFREGISTERS) {
    *(get_symbolic_regs(context) + r) = *(get_symbolic_regs(original) + r);

    r = r + 1;
  }

  // symbolic contexts are stored in a list, we insert in the front
  set_prev_context(symbolic_contexts, context); // for deletion to work
  set_next_context(context, symbolic_contexts);

  symbolic_contexts = context;

  if (debug_merge)
    w = w + dprintf(output_fd, "; creating new context 0x%08lX from original 0x%08lX\n", (uint64_t) context, (uint64_t) original);

  return context;
}

// -----------------------------------------------------------------
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

uint64_t* create_symbolic_context(uint64_t* parent, uint64_t* vctxt) {
  uint64_t* context;

  context = new_symbolic_context();

  init_context(context, parent, vctxt);

  set_next_context(context, (uint64_t*) 0);
  set_execution_depth(context, 0);
  set_path_condition(context, "true");
  set_symbolic_memory(context, (uint64_t*) 0);
  set_symbolic_regs(context, zmalloc(NUMBEROFREGISTERS * sizeof(uint64_t*)));
  set_beq_counter(context, 0);
  set_merge_partner(context, (uint64_t*) 0);
  set_call_stack(context, call_stack_tree);

  if (debug_create)
    printf("%s: parent context 0x%08lX created child context 0x%08lX\n", selfie_name,
      (uint64_t) parent,
      (uint64_t) used_contexts);

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
    use_stdout();
    printf("%s: unknown system call %lu\n", selfie_name, a7);
    use_file();

    set_exit_code(context, EXITCODE_UNKNOWNSYSCALL);

    return EXIT;
  }

  return DONOTEXIT;
}

uint64_t handle_symbolic_division_by_zero(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  // check if this division by zero is reachable
  w = w
    + dprintf(output_fd, "(push 1)\n")
    + dprintf(output_fd, "(assert %s); division by zero detected; check if this division by zero is reachable", path_condition)
    + dprintf(output_fd, "\n(check-sat)\n(get-model)\n(pop 1)\n");

  // we terminate the execution of the context, because if the location is not reachable,
  // the rest of the path is not reachable either, and otherwise
  // the execution would be terminated by this error anyway
  set_exit_code(context, EXITCODE_DIVISIONBYZERO);

  return EXIT;
}

uint64_t handle_symbolic_timer(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  if (get_beq_counter(context) >= beq_limit) {
    w = w
      + dprintf(output_fd, "; timeout (branch limit) in ")
      + print_code_context_for_instruction(pc);
    if (debug_merge)
      w = w + dprintf(output_fd, " -> context: 0x%08lX, path-condition: %s", (uint64_t) context, path_condition);
    w = w + dprintf(output_fd, "\n");

    return EXIT;
  }

  if (max_execution_depth) {
    if (get_execution_depth(context) >= max_execution_depth) {
      w = w
        + dprintf(output_fd, "; timeout (execution depth) in ")
        + print_code_context_for_instruction(pc);
      if (debug_merge)
        w = w + dprintf(output_fd, " -> context: 0x%08lX, path-condition: %s", (uint64_t) context, path_condition);
      w = w + dprintf(output_fd, "\n");

      return EXIT;
    } else
      return SCHEDULE;
  } else
    return SCHEDULE;
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
  else if (exception == EXCEPTION_INVALIDADDRESS) {
    // check if this invalid memory access is reachable
    w = w
      + dprintf(output_fd, "(push 1)\n")
      + dprintf(output_fd, "(assert %s); invalid memory access detected; check if this invalid memory access is reachable", path_condition)
      + dprintf(output_fd, "\n(check-sat)\n(get-model)\n(pop 1)\n");

    set_exit_code(context, EXITCODE_SYMBOLICEXECUTIONERROR);

    // we terminate the execution of the context, because if the location is not reachable,
    // the rest of the path is not reachable either, and otherwise
    // the execution would be terminated by this error anyway
    return EXIT;
  } else if (exception == EXCEPTION_SEGMENTATIONFAULT) {
    // check if this memory access is reachable
    w = w
      + dprintf(output_fd, "(push 1)\n")
      + dprintf(output_fd, "(assert %s); segmentation fault detected; check if this memory access is reachable", path_condition)
      + dprintf(output_fd, "\n(check-sat)\n(get-model)\n(pop 1)\n");

    set_exit_code(context, EXITCODE_SYMBOLICEXECUTIONERROR);

    // we terminate the execution of the context, because if the location is not reachable,
    // the rest of the path is not reachable either, and otherwise
    // the execution would be terminated by this error anyway
    return EXIT;
  } else {
    use_stdout();

    printf("%s: context %s throws uncaught exception: ", selfie_name, get_name(context));
    print_exception(exception, get_fault(context));
    println();

    use_file();

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

  sprintf(string, "(_ bv%lu 64)", value);

  return string;
}

char* bv_variable(uint64_t bits) {
  char* string;

  if (bits == 1)
    return "Bool";

  string = string_alloc(10 + 2); // up to 64-bit variables require up to 2 decimal digits

  sprintf(string, "(_ BitVec %lu)", bits);

  return string;
}

char* bv_zero_extension(uint64_t bits) {
  char* string;

  string = string_alloc(15 + 2); // up to 64-bit variables require up to 2 decimal digits

  sprintf(string, "(_ zero_extend %lu)", WORDSIZEINBITS - bits);

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

  sprintf(svar, "%s%lu", prefix, variable_version);

  w = w
    + dprintf(output_fd, "(declare-fun %s () %s); variable for ", svar, bv_variable(bits))
    + print_code_context_for_instruction(pc)
    + dprintf(output_fd, "\n");

  variable_version = variable_version + 1;

  return svar;
}

char* smt_unary(char* opt, char* op) {
  char* string;

  string = string_alloc(1 + string_length(opt) + 1 + string_length(op) + 1);

  sprintf(string, "(%s %s)", opt, op);

  return string;
}

char* smt_binary(char* opt, char* op1, char* op2) {
  char* string;

  string = string_alloc(1 + string_length(opt) + 1 + string_length(op1) + 1 + string_length(op2) + 1);

  sprintf(string, "(%s %s %s)", opt, op1, op2);

  return string;
}

char* smt_ternary(char* opt, char* op1, char* op2, char* op3) {
  char* string;

  string = string_alloc(1 + string_length(opt) + 1 + string_length(op1) + 1 + string_length(op2) + 1 + string_length(op3) + 1);

  sprintf(string, "(%s %s %s %s)", opt, op1, op2, op3);

  return string;
}

// node struct of the call stack tree:
// +---+----------+
// | 0 | parent   | pointer to parent node
// | 1 | children | pointer to list of children
// | 2 | sibling  | pointer to next sibling node
// | 3 | address  | address of the method call
// | 4 | depth    | size of the call stack represented by the given node
// +---+----------+

uint64_t* allocate_node() {
  return zmalloc(3 * sizeof(uint64_t*) + 2 * sizeof(uint64_t));
}

uint64_t* get_parent_node(uint64_t* node)  { return (uint64_t*) *(node + 0); }
uint64_t* get_children(uint64_t* node)     { return (uint64_t*) *(node + 1); }
uint64_t* get_sibling(uint64_t* node)      { return (uint64_t*) *(node + 2); }
uint64_t  get_node_address(uint64_t* node) { return             *(node + 3); }
uint64_t  get_depth(uint64_t* node)        { return             *(node + 4); }

void set_parent_node(uint64_t* node, uint64_t* parent)  { *(node + 0) = (uint64_t) parent; }
void set_children(uint64_t* node, uint64_t* children)   { *(node + 1) = (uint64_t) children; }
void set_sibling(uint64_t* node, uint64_t* sibling)     { *(node + 2) = (uint64_t) sibling; }
void set_node_address(uint64_t* node, uint64_t address) { *(node + 3) = address; }
void set_depth(uint64_t* node, uint64_t depth)          { *(node + 4) = depth; }

void merge(uint64_t* active_context, uint64_t* mergeable_context, uint64_t location) {

  // do not merge if merging is disabled
  if (merge_enabled == 0)
    return;

  w = w
    + dprintf(output_fd, "; merging two contexts at ")
    + print_code_context_for_instruction(location);

  if (debug_merge)
    w = w + dprintf(output_fd, " -> active context: 0x%08lX, mergeable context: 0x%08lX", (uint64_t) active_context, (uint64_t) mergeable_context);
  w = w + dprintf(output_fd, "\n");

  // merging the symbolic store
  merge_symbolic_memory_and_registers(active_context, mergeable_context);

  // merging the path condition
  path_condition = smt_binary("or", get_path_condition(active_context), get_path_condition(mergeable_context));
  set_path_condition(active_context, path_condition);

  if (get_execution_depth(mergeable_context) < get_execution_depth(active_context))
    set_execution_depth(active_context, get_execution_depth(mergeable_context));

  if (get_beq_counter(mergeable_context) < get_beq_counter(active_context))
    set_beq_counter(active_context, get_beq_counter(mergeable_context));

  symbolic_contexts = delete_context(mergeable_context, symbolic_contexts);
}

void merge_symbolic_memory_and_registers(uint64_t* active_context, uint64_t* mergeable_context) {
  // the shared symbolic memory space can be updated if we are merging the active context with its merge partner
  update_begin_of_shared_symbolic_memory(active_context, mergeable_context);

  // merging the symbolic memory
  merge_symbolic_memory(active_context, mergeable_context);

  // merging the registers
  merge_registers(active_context, mergeable_context);
}

void merge_symbolic_memory(uint64_t* active_context, uint64_t* mergeable_context) {
  uint64_t* sword_from_active_context;
  uint64_t* sword_from_mergeable_context;
  uint64_t* sword;
  uint64_t* additional_memory;
  uint64_t  in_unshared_symbolic_memory;

  sword_from_active_context = symbolic_memory;
  additional_memory = symbolic_memory;
  in_unshared_symbolic_memory = 1;

  while (sword_from_active_context) {
    // we need to remember if we cross the boundary to the shared symbolic memory space of the active context
    if (get_word_address(sword_from_active_context) == (uint64_t) BEGIN_OF_SHARED_SYMBOLIC_MEMORY)
      in_unshared_symbolic_memory = 0;
    else {
      // check if the word has not already been deleted
      if (get_word_address(sword_from_active_context) != (uint64_t) DELETED) {
        // check if the word is the topmost entry for its address in the active symbolic memory
        if (sword_from_active_context == load_symbolic_memory(get_word_address(sword_from_active_context))) {
          sword_from_mergeable_context = get_symbolic_memory(mergeable_context);

          while (sword_from_mergeable_context) {
            if (get_word_address(sword_from_active_context) == get_word_address(sword_from_mergeable_context)) {
              if (get_word_symbolic(sword_from_active_context) != (char*) 0) {
                if (get_word_symbolic(sword_from_mergeable_context) != (char*) 0) {
                  if (get_word_symbolic(sword_from_active_context) != get_word_symbolic(sword_from_mergeable_context)) {
                    // merge symbolic values if they are different
                    if (in_unshared_symbolic_memory)
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
                      additional_memory = sword;
                    }
                  }
                } else {
                  // merge symbolic value and concrete value
                  if (in_unshared_symbolic_memory)
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
                    additional_memory = sword;
                  }
                }
              } else {
                if (get_word_symbolic(sword_from_mergeable_context) != (char*) 0) {
                  // merge concrete value and symbolic value
                  if (in_unshared_symbolic_memory)
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
                    additional_memory = sword;
                  }
                } else {
                  if (get_word_value(sword_from_active_context) != get_word_value(sword_from_mergeable_context)) {
                    // merge concrete values if they are different
                    if (in_unshared_symbolic_memory)
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
                      additional_memory = sword;
                    }
                  }
                }
              }
              // we need to break out of the loop
              sword_from_mergeable_context = (uint64_t*) 0;
            } else
              sword_from_mergeable_context = get_next_word(sword_from_mergeable_context);
          }
        }
      }
    }

    sword_from_active_context = get_next_word(sword_from_active_context);
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

uint64_t* schedule_next_symbolic_context() {
  uint64_t* context;
  uint64_t  max_call_stack_size;
  uint64_t* max_call_stack;
  uint64_t  min_pc;
  uint64_t* next_context;

  context = symbolic_contexts;
  max_call_stack_size = 0;
  max_call_stack = (uint64_t*) 0;
  min_pc = UINT64_MAX;
  next_context = (uint64_t*) 0;

  // find the currently highest call stack
  while (context) {
    if (get_call_stack(context) != (uint64_t*) 0)
      if (get_depth(get_call_stack(context)) > max_call_stack_size) {
        max_call_stack_size = get_depth(get_call_stack(context));
        max_call_stack = get_call_stack(context);
      }

    context = get_next_context(context);
  }

  context = symbolic_contexts;

  // find the context with the lowest program counter and the highest call stack
  while (context) {
    if (get_call_stack(context) == max_call_stack)
      if (get_pc(context) < min_pc) {
        min_pc = get_pc(context);
        next_context = context;
      }

    context = get_next_context(context);
  }

  // the context with the highest call stack and the lowest program counter is returned
  return next_context;
}

void check_if_mergeable_and_merge_if_possible(uint64_t* context) {
  uint64_t* mergeable_context;
  uint64_t* next_context;

  mergeable_context = symbolic_contexts;

  while (mergeable_context) {
    next_context = get_next_context(mergeable_context);
    // a context cannot be merged with itself
    if (mergeable_context != context)
      // mergeable contexts must have the same program counter
      if (get_pc(context) == get_pc(mergeable_context))
        // merge contexts must have the same call stack
        if (get_call_stack(context) == get_call_stack(mergeable_context))
          merge(context, mergeable_context, get_pc(context));

    mergeable_context = next_context;
  }
}

void add_child(uint64_t* parent, uint64_t* child) {
  uint64_t* head;

  head = get_children(parent);

  // insert child at the beginning of the list of children
  set_children(parent, (uint64_t*) child);
  set_sibling(child, (uint64_t*) head);

  // set parent of child
  set_parent_node(child, (uint64_t*) parent);
}

void step_into_call(uint64_t* context, uint64_t address) {
  uint64_t* node;
  uint64_t* child;

  if (call_stack_tree == (uint64_t*) 0) {
    // create root node
    call_stack_tree = allocate_node();

    set_node_address(call_stack_tree, address);
    set_depth(call_stack_tree, 1);

    set_call_stack(context, call_stack_tree);
  } else {
    // assert: call stack of the context is not null
    node = get_call_stack(context);
    child = get_children(node);

    while (child) {
      // corresponding node already exists
      if (get_node_address(child) == address) {
        set_call_stack(context, child);
        return;
      }

      child = get_sibling(child);
    }

    // no corresponding node exists, therefore we need to create one
    child = allocate_node();

    // set address of method call
    set_node_address(child, address);

    // increase depth
    set_depth(child, get_depth(node) + 1);

    add_child(node, child);

    set_call_stack(context, child);
  }
}

void step_out_of_call(uint64_t* context) {
  if (get_call_stack(context))
    // return to parent level
    set_call_stack(context, get_parent_node(get_call_stack(context)));
}

void use_stdout() {
  output_name = (char*) 0;
  output_fd   = 1;
}

void use_file() {
  output_name = smt_name;
  output_fd   = smt_fd;
}

void monster(uint64_t* to_context) {
  uint64_t* from_context;
  uint64_t  timeout;
  uint64_t  exception;

  symbolic_contexts = to_context;

  if (debug_merge)
    from_context = (uint64_t*) 0;

  w = w
    + dprintf(output_fd, "; %s\n\n", SELFIE_URL)
    + dprintf(output_fd, "; SMT-LIB formulae generated by %s for\n", selfie_name)
    + dprintf(output_fd, "; RISC-V code obtained from %s with\n", binary_name);

  if (max_execution_depth)
    w = w + dprintf(output_fd, "; %lu", max_execution_depth);
  else
    w = w + dprintf(output_fd, "; unbounded");

  w = w + dprintf(output_fd, " execution depth, branching limit of %lu, and merging", beq_limit);
  if (merge_enabled)
    w = w + dprintf(output_fd, " enabled\n\n");
  else
    w = w + dprintf(output_fd, " disabled\n\n");

  w = w
    + dprintf(output_fd, "(set-option :produce-models true)\n")
    + dprintf(output_fd, "(set-option :incremental true)\n")
    + dprintf(output_fd, "(set-logic QF_BV)\n\n");

  timeout = 1;

  while (1) {

    if (debug_merge)
      if (from_context != (uint64_t*) 0)
        w = w + dprintf(output_fd, "; switching from context 0x%08lX to context 0x%08lX\n", (uint64_t) from_context, (uint64_t) to_context);

    from_context = mipster_symbolic_switch(to_context, timeout);

    if (get_parent(from_context) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      to_context = get_parent(from_context);

      timeout = TIMEROFF;
    } else {
      exception = handle_symbolic_exception(from_context);

      if (exception == EXIT) {
        // we need to update the end of the shared symbolic memory of the corresponding context
        update_begin_of_shared_symbolic_memory(get_merge_partner(from_context), from_context);

        // delete exited context
        symbolic_contexts = delete_context(from_context, symbolic_contexts);

        // schedule the context with the highest call stack and the lowest program counter
        to_context = schedule_next_symbolic_context();

        // check if contexts can be merged
        check_if_mergeable_and_merge_if_possible(to_context);

        if (to_context)
          timeout = 1;
        else {
          w = w + dprintf(output_fd, "\n(exit)");

          return;
        }
      } else if (exception == SCHEDULE) {
        // check if contexts can be merged
        check_if_mergeable_and_merge_if_possible(from_context);

        // schedule the context with the highest call stack and the lowest program counter
        to_context = schedule_next_symbolic_context();

        timeout = 1;
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

      if (code_size == 0) {
        printf("%s: nothing to run symbolically\n", selfie_name);

        return EXITCODE_BADARGUMENTS;
      }

      // use extension ".smt" in name of SMT-LIB file
      smt_name = replace_extension(binary_name, "", "smt");

      // assert: smt_name is mapped and not longer than MAX_FILENAME_LENGTH

      smt_fd = open_write_only(smt_name, S_IRUSR_IWUSR_IRGRP_IROTH);

      if (signed_less_than(smt_fd, 0)) {
        printf("%s: could not create SMT-LIB output file %s\n", selfie_name, smt_name);

        exit(EXITCODE_IOERROR);
      }

      reset_interpreter();
      reset_profiler();
      reset_microkernel();

      init_memory(1);

      current_context = create_symbolic_context(MY_CONTEXT, 0);

      // assert: number_of_remaining_arguments() > 0

      boot_loader(current_context);

      // current_context is ready to run

      run = 1;

      printf("%s: monster symbolically executing %s with %luMB physical memory\n", selfie_name,
        binary_name,
        PHYSICALMEMORYSIZE / MEGABYTE);

      use_file();

      symbolic = 1;

      monster(current_context);

      symbolic = 0;

      use_stdout();

      printf("%s: monster terminating %s\n", selfie_name, binary_name);

      print_profile();

      run = 0;

      printf("%s: --------------------------------------------------------------------------------\n", selfie_name);

      printf("%s: %lu characters of SMT-LIB formulae written into %s\n", selfie_name, w, smt_name);

      printf("%s: ################################################################################\n", selfie_name);

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
  init_system();
  init_target();
  init_kernel();

  exit_code = selfie(1);

  if (exit_code == EXITCODE_MOREARGUMENTS)
    exit_code = selfie_run_symbolically();

  return exit_selfie(exit_code, " - maximum-execution-depth [ branching-limit ] [ --merge-enabled | --debug-merge ] ...");
}