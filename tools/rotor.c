/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

Rotor is a tool for generating BTOR2 models of RISC-V machines.

*/

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------    A R C H I T E C T U R E    -----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t* allocate_line() {
  return smalloc(5 * sizeof(uint64_t*) + 2 * sizeof(uint64_t));
}

uint64_t  get_nid(uint64_t* line)     { return *line; }
char*     get_op(uint64_t* line)      { return (char*)     *(line + 1); }
uint64_t* get_sid(uint64_t* line)     { return (uint64_t*) *(line + 2); }
uint64_t* get_arg1(uint64_t* line)    { return (uint64_t*) *(line + 3); }
uint64_t* get_arg2(uint64_t* line)    { return (uint64_t*) *(line + 4); }
uint64_t* get_arg3(uint64_t* line)    { return (uint64_t*) *(line + 5); }
char*     get_comment(uint64_t* line) { return (char*)     *(line + 6); }

void set_nid(uint64_t* line, uint64_t nid)      { *line       = nid; }
void set_op(uint64_t* line, char* op)           { *(line + 1) = (uint64_t) op; }
void set_sid(uint64_t* line, uint64_t* sid)     { *(line + 2) = (uint64_t) sid; }
void set_arg1(uint64_t* line, uint64_t* arg1)   { *(line + 3) = (uint64_t) arg1; }
void set_arg2(uint64_t* line, uint64_t* arg2)   { *(line + 4) = (uint64_t) arg2; }
void set_arg3(uint64_t* line, uint64_t* arg3)   { *(line + 5) = (uint64_t) arg3; }
void set_comment(uint64_t* line, char* comment) { *(line + 6) = (uint64_t) comment; }

uint64_t* new_line(char* op, uint64_t* sid, uint64_t* arg1, uint64_t* arg2, uint64_t* arg3, char* comment);

uint64_t* new_bitvec(uint64_t size_in_bits, char* comment);
uint64_t* new_array(uint64_t* size_sid, uint64_t* element_sid, char* comment);
uint64_t* new_constant(uint64_t constant, uint64_t* sid);
uint64_t* new_state(uint64_t* sid, char* symbol, char* comment);

void print_comment(uint64_t* line);
void print_line(uint64_t nid, uint64_t* line);

void print_sort(uint64_t* line);
void print_constant(uint64_t* line);
void print_state(uint64_t* line);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t* UNUSED    = (uint64_t*) 0;
char*     NOCOMMENT = (char*) 0;

char* BITVEC = (char*) 0;
char* ARRAY  = (char*) 0;

char* OP_SORT  = (char*) 0;
char* OP_CONST = (char*) 0;
char* OP_STATE = (char*) 0;

uint64_t* SID_BOOLEAN       = (uint64_t*) 0;
uint64_t* SID_MACHINE_WORD  = (uint64_t*) 0;

uint64_t* SID_REGISTER_SPACE = (uint64_t*) 0;
uint64_t* SID_REGISTER_STATE = (uint64_t*) 0;

uint64_t* SID_MEMORY_SPACE = (uint64_t*) 0;
uint64_t* SID_MEMORY_STATE = (uint64_t*) 0;

uint64_t* NID_FALSE = (uint64_t*) 0;
uint64_t* NID_TRUE  = (uint64_t*) 1;

uint64_t* NID_0 = (uint64_t*) 0;
uint64_t* NID_1 = (uint64_t*) 1;
uint64_t* NID_2 = (uint64_t*) 2;
uint64_t* NID_3 = (uint64_t*) 3;
uint64_t* NID_4 = (uint64_t*) 4;
uint64_t* NID_5 = (uint64_t*) 5;
uint64_t* NID_6 = (uint64_t*) 6;
uint64_t* NID_7 = (uint64_t*) 7;
uint64_t* NID_8 = (uint64_t*) 8;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t number_of_lines = 0;

// ------------------------- INITIALIZATION ------------------------

void init_architecture() {
  BITVEC = "bitvec";
  ARRAY  = "array";

  OP_SORT  = "sort";
  OP_CONST = "constd";
  OP_STATE = "state";

  SID_BOOLEAN = new_bitvec(1, "Boolean");
  if (WORDSIZEINBITS == 64) {
    SID_MACHINE_WORD = new_bitvec(WORDSIZEINBITS, "64-bit machine word");
    SID_MEMORY_SPACE = new_bitvec(29, "29-bit 64-bit-word-addressed memory space");
  } else {
    // assert: WORDSIZEINBITS == 32
    SID_MACHINE_WORD = new_bitvec(WORDSIZEINBITS, "32-bit machine word");
    SID_MEMORY_SPACE = new_bitvec(30, "30-bit 32-bit-word-addressed memory space");
  }

  SID_REGISTER_SPACE = new_bitvec(5, "5-bit register space");
  SID_REGISTER_STATE = new_array(SID_REGISTER_SPACE, SID_MACHINE_WORD, "register state");

  SID_MEMORY_STATE = new_array(SID_MEMORY_SPACE, SID_MACHINE_WORD, "memory state");

  NID_FALSE = new_constant(0, SID_BOOLEAN);
  NID_TRUE  = new_constant(1, SID_BOOLEAN);

  NID_0 = new_constant(0, SID_MACHINE_WORD);
  NID_1 = new_constant(1, SID_MACHINE_WORD);
  NID_2 = new_constant(2, SID_MACHINE_WORD);
  NID_3 = new_constant(3, SID_MACHINE_WORD);
  NID_4 = new_constant(4, SID_MACHINE_WORD);
  NID_5 = new_constant(5, SID_MACHINE_WORD);
  NID_6 = new_constant(6, SID_MACHINE_WORD);
  NID_7 = new_constant(7, SID_MACHINE_WORD);
  NID_8 = new_constant(8, SID_MACHINE_WORD);
}

// -----------------------------------------------------------------
// --------------------------- REGISTERS ---------------------------
// -----------------------------------------------------------------

void new_register_file_state();

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* state_register_file = (uint64_t*) 0;
uint64_t* init_register_file  = (uint64_t*) 0;
uint64_t* next_register_file  = (uint64_t*) 0;

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void new_main_memory_state();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t vaddr_sort_nid   = 2;  // nid of virtual or linear address sort
uint64_t vaddr_space_size = 64; // size of virtual address space in bits
uint64_t vaddr_mask_nid   = 27; // nid of bit mask for resetting LSBs in virtual addresses
uint64_t vaddr_alignment  = 3;  // virtual address alignment in bits

uint64_t laddr_space_size = 32; // size of linear address space in bits

uint64_t paddr_sort_nid   = 2;  // nid of physical address sort
uint64_t paddr_space_size = 64; // size of physical address space in bits

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* state_main_memory = (uint64_t*) 0;
uint64_t* init_main_memory  = (uint64_t*) 0;
uint64_t* next_main_memory  = (uint64_t*) 0;

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

// -----------------------------------------------------------------
// ----------------------------- CORE ------------------------------
// -----------------------------------------------------------------

// -----------------------------------------------------------------
// ------------------------ MODEL GENERATOR ------------------------
// -----------------------------------------------------------------

void rotor();

uint64_t selfie_model();

// ------------------------ GLOBAL VARIABLES -----------------------

char*    model_name = (char*) 0; // name of model file
uint64_t model_fd   = 0;         // file descriptor of open model file

uint64_t w = 0; // number of written characters

uint64_t bad_exit_code  = 0; // model for this exit code

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------    A R C H I T E C T U R E    -----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t* new_line(char* op, uint64_t* sid, uint64_t* arg1, uint64_t* arg2, uint64_t* arg3, char* comment) {
  uint64_t* line;

  line = allocate_line();

  set_op(line, op);
  set_sid(line, sid);
  set_arg1(line, arg1);
  set_arg2(line, arg2);
  set_arg3(line, arg3);
  set_comment(line, comment);

  number_of_lines = number_of_lines + 1;

  return line;
}

uint64_t* new_bitvec(uint64_t size_in_bits, char* comment) {
  return new_line(OP_SORT, UNUSED, (uint64_t*) BITVEC, (uint64_t*) size_in_bits, UNUSED, comment);
}

uint64_t* new_array(uint64_t* size_sid, uint64_t* element_sid, char* comment) {
  return new_line(OP_SORT, UNUSED, (uint64_t*) ARRAY, size_sid, element_sid, comment);
}

uint64_t* new_constant(uint64_t constant, uint64_t* sid) {
  return new_line(OP_CONST, sid, (uint64_t*) constant, UNUSED, UNUSED, NOCOMMENT);
}

uint64_t* new_state(uint64_t* sid, char* symbol, char* comment) {
  return new_line(OP_STATE, sid, (uint64_t*) symbol, UNUSED, UNUSED, comment);
}

void print_comment(uint64_t* line) {
  if (get_comment(line) != NOCOMMENT)
    w = w + dprintf(output_fd, " ; %s", get_comment(line));
  w = w + dprintf(output_fd, "\n");
}

void print_line(uint64_t nid, uint64_t* line) {
  set_nid(line, nid);
  w = w + dprintf(output_fd, "%lu", nid);
  if (get_op(line) == OP_SORT)
    print_sort(line);
  else if (get_op(line) == OP_CONST)
    print_constant(line);
  else if (get_op(line) == OP_STATE)
    print_state(line);
  print_comment(line);
}

void print_sort(uint64_t* line) {
  w = w + dprintf(output_fd, " %s", OP_SORT);
  if ((char*) get_arg1(line) == BITVEC)
    w = w + dprintf(output_fd, " %s %lu", BITVEC, (uint64_t) get_arg2(line));
  else
    // assert: theory of bitvector arrays
    w = w + dprintf(output_fd, " %s %lu %lu", ARRAY, get_nid(get_arg2(line)), get_nid(get_arg3(line)));
}

void print_constant(uint64_t* line) {
  if ((uint64_t) get_arg1(line) == 0)
    w = w + dprintf(output_fd, " zero %lu", get_nid(get_sid(line)));
  else if ((uint64_t) get_arg1(line) == 1)
    w = w + dprintf(output_fd, " one %lu", get_nid(get_sid(line)));
  else
    w = w + dprintf(output_fd, " %s %lu %lu", OP_CONST, get_nid(get_sid(line)), (uint64_t) get_arg1(line));
}

void print_state(uint64_t* line) {
  w = w + dprintf(output_fd, " %s %lu %s", OP_STATE, get_nid(get_sid(line)), (char*) get_arg1(line));
}

// -----------------------------------------------------------------
// --------------------------- REGISTERS ---------------------------
// -----------------------------------------------------------------

void new_register_file_state() {
  state_register_file = new_state(SID_REGISTER_STATE, "regs", "register file");
}

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void new_main_memory_state() {
  state_main_memory = new_state(SID_MEMORY_STATE, "mem", "main memory");
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

// -----------------------------------------------------------------
// ----------------------------- CORE ------------------------------
// -----------------------------------------------------------------

// -----------------------------------------------------------------
// ------------------------ MODEL GENERATOR ------------------------
// -----------------------------------------------------------------

void rotor() {
  new_register_file_state();
  new_main_memory_state();

  print_line(1, SID_BOOLEAN);
  print_line(2, SID_MACHINE_WORD);

  print_line(3, SID_REGISTER_SPACE);
  print_line(4, SID_REGISTER_STATE);

  print_line(5, SID_MEMORY_SPACE);
  print_line(6, SID_MEMORY_STATE);

  print_line(10, NID_FALSE);
  print_line(11, NID_TRUE);

  print_line(20, NID_0);
  print_line(21, NID_1);
  print_line(22, NID_2);
  print_line(23, NID_3);
  print_line(24, NID_4);
  print_line(25, NID_5);
  print_line(26, NID_6);
  print_line(27, NID_7);
  print_line(28, NID_8);

  print_line(200, state_register_file);

  print_line(1000, state_main_memory);
}

uint64_t selfie_model() {
  if (IS64BITTARGET == 0) {
    // assert: 32-bit system
    vaddr_mask_nid  = 23;
    vaddr_alignment = 2;

    vaddr_space_size = WORDSIZEINBITS;
    paddr_space_size = vaddr_space_size;
  }

  if (string_compare(argument, "-")) {
    if (number_of_remaining_arguments() > 0) {
      bad_exit_code = atoi(peek_argument(0));

      // use extension ".btor2" in name of SMT-LIB file
      model_name = "riscu-machine.btor2";

      // assert: model_name is mapped and not longer than MAX_FILENAME_LENGTH

      model_fd = open_write_only(model_name, S_IRUSR_IWUSR_IRGRP_IROTH);

      if (signed_less_than(model_fd, 0)) {
        printf("%s: could not create model file %s\n", selfie_name, model_name);

        exit(EXITCODE_IOERROR);
      }

      init_architecture();

      rotor();

      output_name = (char*) 0;
      output_fd   = 1;

      printf("%s: %lu characters of model formulae written into %s\n", selfie_name, w, model_name);

      printf("%s: ################################################################################\n", selfie_name);

      return EXITCODE_NOERROR;
    } else
      return EXITCODE_BADARGUMENTS;
  } else
    return EXITCODE_BADARGUMENTS;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

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
    exit_code = selfie_model();

  return exit_selfie(exit_code, " - exit_code ...");
}