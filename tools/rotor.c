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
uint64_t* new_init(uint64_t* sid, uint64_t* state_nid, uint64_t* value_nid, char* symbol, char* comment);
uint64_t* new_next(uint64_t* sid, uint64_t* state_nid, uint64_t* value_nid, char* comment);

void print_comment(uint64_t* line);
void print_line(uint64_t nid, uint64_t* line);

void print_sort(uint64_t* line);
void print_constant(uint64_t* line);
void print_state(uint64_t* line);
void print_init(uint64_t* line);
void print_next(uint64_t* line);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t* UNUSED    = (uint64_t*) 0;
char*     NOCOMMENT = (char*) 0;

char* BITVEC = (char*) 0;
char* ARRAY  = (char*) 0;

char* OP_SORT  = (char*) 0;
char* OP_CONST = (char*) 0;
char* OP_STATE = (char*) 0;
char* OP_INIT  = (char*) 0;
char* OP_NEXT  = (char*) 0;

uint64_t* SID_BOOLEAN = (uint64_t*) 0;
uint64_t* NID_FALSE   = (uint64_t*) 0;
uint64_t* NID_TRUE    = (uint64_t*) 1;

uint64_t* SID_BYTE   = (uint64_t*) 0;
uint64_t* NID_BYTE_0 = (uint64_t*) 0;

uint64_t* SID_SINGLE_WORD   = (uint64_t*) 0;
uint64_t* NID_SINGLE_WORD_0 = (uint64_t*) 0;

uint64_t* SID_DOUBLE_WORD   = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_0 = (uint64_t*) 0;

uint64_t* SID_MACHINE_WORD   = (uint64_t*) 0;
uint64_t* NID_MACHINE_WORD_0 = (uint64_t*) 0;

uint64_t* SID_REGISTER_ADDRESS = (uint64_t*) 0;
uint64_t* SID_REGISTER_STATE   = (uint64_t*) 0;

uint64_t* SID_MEMORY_ADDRESS = (uint64_t*) 0;
uint64_t* SID_MEMORY_STATE   = (uint64_t*) 0;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t number_of_lines = 0;

// ------------------------- INITIALIZATION ------------------------

void init_architecture() {
  BITVEC = "bitvec";
  ARRAY  = "array";

  OP_SORT  = "sort";
  OP_CONST = "constd";
  OP_STATE = "state";
  OP_INIT  = "init";
  OP_NEXT  = "next";

  SID_BOOLEAN = new_bitvec(1, "Boolean");
  NID_FALSE   = new_constant(0, SID_BOOLEAN);
  NID_TRUE    = new_constant(1, SID_BOOLEAN);

  SID_BYTE = new_bitvec(8, "8-bit byte");

  SID_SINGLE_WORD   = new_bitvec(32, "32-bit single word");
  NID_SINGLE_WORD_0 = new_constant(0, SID_SINGLE_WORD);

  if (IS64BITTARGET) {
    SID_DOUBLE_WORD   = new_bitvec(64, "64-bit double word");
    NID_DOUBLE_WORD_0 = new_constant(0, SID_DOUBLE_WORD);

    SID_MACHINE_WORD   = SID_DOUBLE_WORD;
    NID_MACHINE_WORD_0 = NID_DOUBLE_WORD_0;
  } else {
    // assert: 32-bit system
    SID_MACHINE_WORD   = SID_SINGLE_WORD;
    NID_MACHINE_WORD_0 = NID_SINGLE_WORD_0;
  }

  SID_REGISTER_ADDRESS = new_bitvec(5, "5-bit register address");
  SID_REGISTER_STATE   = new_array(SID_REGISTER_ADDRESS, SID_MACHINE_WORD, "register state");

  if (IS64BITTARGET)
    SID_MEMORY_ADDRESS = new_bitvec(29, "29-bit 64-bit-word-addressed memory address");
  else
    // assert: 32-bit system
    SID_MEMORY_ADDRESS = new_bitvec(30, "30-bit 32-bit-word-addressed memory address");

  SID_MEMORY_STATE = new_array(SID_MEMORY_ADDRESS, SID_MACHINE_WORD, "memory state");
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

void new_core_state();

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* state_core_pc = (uint64_t*) 0;
uint64_t* init_core_pc  = (uint64_t*) 0;
uint64_t* next_core_pc  = (uint64_t*) 0;

uint64_t* state_core_ir = (uint64_t*) 0;
uint64_t* init_core_ir  = (uint64_t*) 0;
uint64_t* next_core_ir  = (uint64_t*) 0;

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

uint64_t* new_init(uint64_t* sid, uint64_t* state_nid, uint64_t* value_nid, char* symbol, char* comment) {
  return new_line(OP_INIT, sid, state_nid, value_nid, (uint64_t*) symbol, comment);
}

uint64_t* new_next(uint64_t* sid, uint64_t* state_nid, uint64_t* value_nid, char* comment) {
  return new_line(OP_NEXT, sid, state_nid, value_nid, UNUSED, comment);
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
  else if (get_op(line) == OP_INIT)
    print_init(line);
  else if (get_op(line) == OP_NEXT)
    print_next(line);
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

void print_init(uint64_t* line) {
  w = w + dprintf(output_fd, " %s %lu %lu %lu %s",
    OP_INIT, get_nid(get_sid(line)), get_nid(get_arg1(line)), get_nid(get_arg2(line)), (char*) get_arg3(line));
}

void print_next(uint64_t* line) {
  w = w + dprintf(output_fd, " %s %lu %lu %lu",
    OP_NEXT, get_nid(get_sid(line)), get_nid(get_arg1(line)), get_nid(get_arg2(line)));
}

// -----------------------------------------------------------------
// --------------------------- REGISTERS ---------------------------
// -----------------------------------------------------------------

void new_register_file_state() {
  state_register_file = new_state(SID_REGISTER_STATE, "regs", "register file");
  init_register_file  = new_init(SID_REGISTER_STATE, state_register_file, NID_MACHINE_WORD_0, "regs", "initial value");
  next_register_file  = new_next(SID_REGISTER_STATE, state_register_file, state_register_file, "TBD");
}

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void new_main_memory_state() {
  state_main_memory = new_state(SID_MEMORY_STATE, "mem", "main memory");
  init_main_memory  = new_init(SID_MEMORY_STATE, state_main_memory, NID_MACHINE_WORD_0, "mem", "initial value");
  next_main_memory  = new_next(SID_MEMORY_STATE, state_main_memory, state_main_memory, "TBD");
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

// -----------------------------------------------------------------
// ----------------------------- CORE ------------------------------
// -----------------------------------------------------------------

void new_core_state() {
  state_core_pc = new_state(SID_MACHINE_WORD, "pc", "program counter");
  init_core_pc  = new_init(SID_MACHINE_WORD, state_core_pc, NID_MACHINE_WORD_0, "pc", "initial value");
  next_core_pc  = new_next(SID_MACHINE_WORD, state_core_pc, state_core_pc, "TBD");

  state_core_ir = new_state(SID_SINGLE_WORD, "ir", "instruction register");
  init_core_ir  = new_init(SID_SINGLE_WORD, state_core_ir, NID_SINGLE_WORD_0, "ir", "initial value");
  next_core_ir  = new_next(SID_SINGLE_WORD, state_core_ir, state_core_ir, "TBD");
}

// -----------------------------------------------------------------
// ------------------------ MODEL GENERATOR ------------------------
// -----------------------------------------------------------------

void rotor() {
  new_register_file_state();
  new_main_memory_state();
  new_core_state();

  // output RISC-U machine model

  w = w
    + dprintf(output_fd, "; %s\n\n", SELFIE_URL)
    + dprintf(output_fd, "; BTOR2 file %s generated by %s\n\n", model_name, selfie_name);

  print_line(1, SID_BOOLEAN);
  print_line(2, SID_BYTE);
  print_line(3, SID_SINGLE_WORD);
  if (IS64BITTARGET)
    print_line(4, SID_DOUBLE_WORD);

  print_line(5, SID_REGISTER_ADDRESS);
  print_line(6, SID_REGISTER_STATE);

  print_line(7, SID_MEMORY_ADDRESS);
  print_line(8, SID_MEMORY_STATE);

  w = w + dprintf(output_fd, "\n; machine constants\n\n");

  print_line(10, NID_FALSE);
  print_line(11, NID_TRUE);

  print_line(30, NID_SINGLE_WORD_0);
  if (IS64BITTARGET)
    print_line(40, NID_DOUBLE_WORD_0);

  w = w + dprintf(output_fd, "\n; register file\n\n");

  print_line(200, state_register_file);
  print_line(201, init_register_file);
  print_line(202, next_register_file);

  w = w + dprintf(output_fd, "\n; program counter\n\n");

  print_line(300, state_core_pc);
  print_line(301, init_core_pc);
  print_line(302, next_core_pc);

  w = w + dprintf(output_fd, "\n; instruction register\n\n");

  print_line(400, state_core_ir);
  print_line(401, init_core_ir);
  print_line(402, next_core_ir);

  w = w + dprintf(output_fd, "\n; main memory\n\n");

  print_line(1000, state_main_memory);
  print_line(1001, init_main_memory);
  print_line(1002, next_main_memory);
}

uint64_t selfie_model() {
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

      output_name = model_name;
      output_fd   = model_fd;

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

  // IS64BITTARGET = 0;

  if (exit_code == EXITCODE_MOREARGUMENTS)
    exit_code = selfie_model();

  return exit_selfie(exit_code, " - exit_code ...");
}