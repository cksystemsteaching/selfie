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

uint64_t* new_read(uint64_t* sid, uint64_t* array_nid, uint64_t* index_nid, char* comment);

uint64_t* new_slice(uint64_t* sid, uint64_t* value_nid, uint64_t u, uint64_t l, char* comment);

uint64_t* new_ite(uint64_t* sid, uint64_t* condition_nid, uint64_t* true_nid, uint64_t* false_nid, char* comment);

void print_nid(uint64_t nid, uint64_t* line);
void print_comment(uint64_t* line);

uint64_t print_line(uint64_t nid, uint64_t* line);

uint64_t print_sort(uint64_t nid, uint64_t* line);
uint64_t print_constant(uint64_t nid, uint64_t* line);
uint64_t print_state(uint64_t nid, uint64_t* line);
uint64_t print_init(uint64_t nid, uint64_t* line);

uint64_t print_binary_operator(uint64_t nid, uint64_t* line);
uint64_t print_tenary_operator(uint64_t nid, uint64_t* line);

uint64_t print_slice(uint64_t nid, uint64_t* line);

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

char* OP_READ = (char*) 0;

char* OP_SLICE = (char*) 0;

char* OP_ITE = (char*) 0;

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

  OP_READ = "read";

  OP_SLICE = "slice";

  OP_ITE = "ite";

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
}

// -----------------------------------------------------------------
// --------------------------- REGISTERS ---------------------------
// -----------------------------------------------------------------

void new_register_file_state();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t* SID_REGISTER_ADDRESS = (uint64_t*) 0;
uint64_t* SID_REGISTER_STATE   = (uint64_t*) 0;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* state_register_file = (uint64_t*) 0;
uint64_t* init_register_file  = (uint64_t*) 0;

uint64_t* eval_register_file = (uint64_t*) 0;
uint64_t* next_register_file = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_register_file_sorts() {
  SID_REGISTER_ADDRESS = new_bitvec(5, "5-bit register address");
  SID_REGISTER_STATE   = new_array(SID_REGISTER_ADDRESS, SID_MACHINE_WORD, "register state");
}

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void new_main_memory_state();

uint64_t* vaddr_to_laddr(uint64_t* vaddr);

uint64_t* load_machine_word(uint64_t* vaddr);
uint64_t* fetch_instruction(uint64_t* vaddr);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t* SID_MEMORY_ADDRESS = (uint64_t*) 0;
uint64_t* SID_MEMORY_STATE   = (uint64_t*) 0;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* state_main_memory = (uint64_t*) 0;
uint64_t* init_main_memory  = (uint64_t*) 0;

uint64_t* eval_main_memory = (uint64_t*) 0;
uint64_t* next_main_memory = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_main_memory_sorts() {
  if (IS64BITTARGET)
    SID_MEMORY_ADDRESS = new_bitvec(29, "29-bit 64-bit-word-addressed memory address");
  else
    // assert: 32-bit system
    SID_MEMORY_ADDRESS = new_bitvec(30, "30-bit 32-bit-word-addressed memory address");

  SID_MEMORY_STATE = new_array(SID_MEMORY_ADDRESS, SID_MACHINE_WORD, "memory state");
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

uint64_t* get_instruction_opcode(uint64_t* instruction);
uint64_t* get_instruction_funct3(uint64_t* instruction);
uint64_t* get_instruction_funct7(uint64_t* instruction);
uint64_t* get_instruction_rd(uint64_t* instruction);
uint64_t* get_instruction_rs1(uint64_t* instruction);
uint64_t* get_instruction_rs2(uint64_t* instruction);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t* SID_OPCODE = (uint64_t*) 0;
uint64_t* SID_FUNCT3 = (uint64_t*) 0;
uint64_t* SID_FUNCT7 = (uint64_t*) 0;

uint64_t* SID_IS_IMM = (uint64_t*) 0;
uint64_t* SID_U_IMM  = (uint64_t*) 0;

// ------------------------ GLOBAL VARIABLES -----------------------

// ------------------------- INITIALIZATION ------------------------

void init_instruction_sorts() {
  SID_OPCODE = new_bitvec(7, "opcode sort");
  SID_FUNCT3 = new_bitvec(3, "funct3 sort");
  SID_FUNCT7 = new_bitvec(7, "funct7 sort");

  SID_IS_IMM = new_bitvec(12, "12-bit immediate sort");
  SID_U_IMM  = new_bitvec(20, "20-bit immediate sort");
}

// -----------------------------------------------------------------
// ----------------------------- CORE ------------------------------
// -----------------------------------------------------------------

void new_core_state();

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* state_core_pc = (uint64_t*) 0;
uint64_t* init_core_pc  = (uint64_t*) 0;

uint64_t* eval_core_pc = (uint64_t*) 0;
uint64_t* next_core_pc = (uint64_t*) 0;

uint64_t* eval_core_ir = (uint64_t*) 0;
uint64_t* eval_core_rd = (uint64_t*) 0;

// -----------------------------------------------------------------
// ------------------------ MODEL GENERATOR ------------------------
// -----------------------------------------------------------------

void output_machine();

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

uint64_t* new_read(uint64_t* sid, uint64_t* array_nid, uint64_t* index_nid, char* comment) {
  return new_line(OP_READ, sid, array_nid, index_nid, UNUSED, comment);
}

uint64_t* new_slice(uint64_t* sid, uint64_t* value_nid, uint64_t u, uint64_t l, char* comment) {
  return new_line(OP_SLICE, sid, value_nid, (uint64_t*) u, (uint64_t*) l, comment);
}

uint64_t* new_ite(uint64_t* sid, uint64_t* condition_nid, uint64_t* true_nid, uint64_t* false_nid, char* comment) {
  return new_line(OP_ITE, sid, condition_nid, true_nid, false_nid, comment);
}

void print_nid(uint64_t nid, uint64_t* line) {
  set_nid(line, nid);
  w = w + dprintf(output_fd, "%lu", nid);
}

void print_comment(uint64_t* line) {
  if (get_comment(line) != NOCOMMENT)
    w = w + dprintf(output_fd, " ; %s", get_comment(line));
  w = w + dprintf(output_fd, "\n");
}

uint64_t print_line(uint64_t nid, uint64_t* line) {
  if (get_nid(line) > 0)
    // print lines only once
    return nid;
  else if (get_op(line) == OP_SORT)
    nid = print_sort(nid, line);
  else if (get_op(line) == OP_CONST)
    nid = print_constant(nid, line);
  else if (get_op(line) == OP_STATE)
    nid = print_state(nid, line);
  else if (get_op(line) == OP_INIT)
    nid = print_init(nid, line);
  else if (get_op(line) == OP_SLICE)
    nid = print_slice(nid, line);
  else if (get_op(line) == OP_ITE)
    nid = print_tenary_operator(nid, line);
  else
    nid = print_binary_operator(nid, line);
  print_comment(line);
  return nid + 1;
}

uint64_t print_sort(uint64_t nid, uint64_t* line) {
  if ((char*) get_arg1(line) == ARRAY) {
    nid = print_line(nid, get_arg2(line));
    nid = print_line(nid, get_arg3(line));
  }
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s", OP_SORT);
  if ((char*) get_arg1(line) == BITVEC)
    w = w + dprintf(output_fd, " %s %lu", BITVEC, (uint64_t) get_arg2(line));
  else
    // assert: theory of bitvector arrays
    w = w + dprintf(output_fd, " %s %lu %lu", ARRAY, get_nid(get_arg2(line)), get_nid(get_arg3(line)));
  return nid;
}

uint64_t print_constant(uint64_t nid, uint64_t* line) {
  nid = print_line(nid, get_sid(line));
  print_nid(nid, line);
  if ((uint64_t) get_arg1(line) == 0)
    w = w + dprintf(output_fd, " zero %lu", get_nid(get_sid(line)));
  else if ((uint64_t) get_arg1(line) == 1)
    w = w + dprintf(output_fd, " one %lu", get_nid(get_sid(line)));
  else
    w = w + dprintf(output_fd, " %s %lu %lu", OP_CONST, get_nid(get_sid(line)), (uint64_t) get_arg1(line));
  return nid;
}

uint64_t print_state(uint64_t nid, uint64_t* line) {
  nid = print_line(nid, get_sid(line));
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s %lu %s", OP_STATE, get_nid(get_sid(line)), (char*) get_arg1(line));
  return nid;
}

uint64_t print_init(uint64_t nid, uint64_t* line) {
  nid = print_line(nid, get_sid(line));
  nid = print_line(nid, get_arg1(line));
  nid = print_line(nid, get_arg2(line));
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s %lu %lu %lu %s",
    OP_INIT, get_nid(get_sid(line)), get_nid(get_arg1(line)), get_nid(get_arg2(line)), (char*) get_arg3(line));
  return nid;
}

uint64_t print_binary_operator(uint64_t nid, uint64_t* line) {
  nid = print_line(nid, get_sid(line));
  nid = print_line(nid, get_arg1(line));
  nid = print_line(nid, get_arg2(line));
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s %lu %lu %lu",
    get_op(line), get_nid(get_sid(line)), get_nid(get_arg1(line)), get_nid(get_arg2(line)));
  return nid;
}

uint64_t print_tenary_operator(uint64_t nid, uint64_t* line) {
  nid = print_line(nid, get_sid(line));
  nid = print_line(nid, get_arg1(line));
  nid = print_line(nid, get_arg2(line));
  nid = print_line(nid, get_arg3(line));
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s %lu %lu %lu %lu",
    get_op(line), get_nid(get_sid(line)), get_nid(get_arg1(line)), get_nid(get_arg2(line)), get_nid(get_arg3(line)));
  return nid;
}

uint64_t print_slice(uint64_t nid, uint64_t* line) {
  nid = print_line(nid, get_sid(line));
  nid = print_line(nid, get_arg1(line));
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s %lu %lu %lu %lu",
    OP_SLICE, get_nid(get_sid(line)), get_nid(get_arg1(line)), (uint64_t) get_arg2(line), (uint64_t) get_arg3(line));
  return nid;
}

// -----------------------------------------------------------------
// --------------------------- REGISTERS ---------------------------
// -----------------------------------------------------------------

void new_register_file_state() {
  state_register_file = new_state(SID_REGISTER_STATE, "regs", "register file");
  init_register_file  = new_init(SID_REGISTER_STATE, state_register_file, NID_MACHINE_WORD_0, "regs", "initial value");

  eval_register_file = state_register_file;
  next_register_file = new_next(SID_REGISTER_STATE, state_register_file, eval_register_file, "TBD");
}

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void new_main_memory_state() {
  state_main_memory = new_state(SID_MEMORY_STATE, "mem", "main memory");
  init_main_memory  = new_init(SID_MEMORY_STATE, state_main_memory, NID_MACHINE_WORD_0, "mem", "initial value");

  eval_main_memory = state_main_memory;
  next_main_memory = new_next(SID_MEMORY_STATE, state_main_memory, eval_main_memory, "TBD");
}

uint64_t* vaddr_to_laddr(uint64_t* vaddr) {
  if (IS64BITTARGET)
    return new_slice(SID_MEMORY_ADDRESS, vaddr, 31, 3, "map 64-bit virtual address to 29-bit linear address");
  else
    return new_slice(SID_MEMORY_ADDRESS, vaddr, 31, 2, "map 32-bit virtual address to 30-bit linear address");
}

uint64_t* load_machine_word(uint64_t* vaddr) {
  return new_read(SID_MACHINE_WORD, state_main_memory, vaddr_to_laddr(vaddr), "load machine word");
}

uint64_t* fetch_instruction(uint64_t* vaddr) {
  uint64_t* machine_word;

  machine_word = load_machine_word(vaddr);

  if (IS64BITTARGET)
    return new_ite(SID_SINGLE_WORD,
      new_slice(SID_BOOLEAN, vaddr, 2, 2, "high or low single word?"),
      new_slice(SID_SINGLE_WORD, machine_word, 63, 32, "high single word"),
      new_slice(SID_SINGLE_WORD, machine_word, 31, 0, "low single word"),
      "fetch instruction");
  else
    return machine_word;
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

uint64_t* get_instruction_opcode(uint64_t* instruction) {
  return new_slice(SID_OPCODE, instruction, 6, 0, "get opcode");
}

uint64_t* get_instruction_funct3(uint64_t* instruction) {
  return new_slice(SID_FUNCT3, instruction, 14, 12, "get funct3");
}

uint64_t* get_instruction_funct7(uint64_t* instruction) {
  return new_slice(SID_FUNCT7, instruction, 31, 25, "get funct7");
}

uint64_t* get_instruction_rd(uint64_t* instruction) {
  return new_slice(SID_REGISTER_ADDRESS, instruction, 11, 7, "get rd");
}

uint64_t* get_instruction_rs1(uint64_t* instruction) {
  return new_slice(SID_REGISTER_ADDRESS, instruction, 19, 15, "get rs1");
}

uint64_t* get_instruction_rs2(uint64_t* instruction) {
  return new_slice(SID_REGISTER_ADDRESS, instruction, 24, 20, "get rs2");
}

uint64_t* get_instruction_I_imm(uint64_t* instruction) {
  return new_slice(SID_IS_IMM, instruction, 31, 20, "get I-immediate");
}

/*
uint64_t* get_instruction_S_imm(uint64_t* instruction) {
  return new_concat(SID_IS_IMM,
    get_instruction_funct7(instruction),
    get_instruction_rd(instruction),
    "get S-immediate");
}
*/

uint64_t* get_instruction_U_imm(uint64_t* instruction) {
  return new_slice(SID_U_IMM, instruction, 31, 12, "get U-immediate");
}

/*
uint64_t* get_instruction_IS_immediate(uint64_t* imm) {
  if (IS64BITTARGET)
    return new_sext(SID_MACHINE_WORD, imm, 52, "sign-extend");
  else
    return new_sext(SID_MACHINE_WORD, imm, 20, "sign-extend");
}

uint64_t* get_instruction_U_immediate(uint64_t* imm) {
  if (IS64BITTARGET)
    return new_sext(SID_MACHINE_WORD, imm, 44, "sign-extend");
  else
    return new_sext(SID_MACHINE_WORD, imm, 12, "sign-extend");
}
*/

// -----------------------------------------------------------------
// ----------------------------- CORE ------------------------------
// -----------------------------------------------------------------

void new_core_state() {
  state_core_pc = new_state(SID_MACHINE_WORD, "pc", "program counter");
  init_core_pc  = new_init(SID_MACHINE_WORD, state_core_pc, NID_MACHINE_WORD_0, "pc", "initial value");

  eval_core_pc = state_core_pc;
  next_core_pc = new_next(SID_MACHINE_WORD, state_core_pc, eval_core_pc, "TBD");
}

// -----------------------------------------------------------------
// ------------------------ MODEL GENERATOR ------------------------
// -----------------------------------------------------------------

void output_machine() {
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

  w = w + dprintf(output_fd, "\n; main memory\n\n");

  print_line(300, state_main_memory);
  print_line(301, init_main_memory);

  w = w + dprintf(output_fd, "\n; program counter\n\n");

  print_line(1000, state_core_pc);
  print_line(1001, init_core_pc);

  print_line(1002, next_core_pc);

  w = w + dprintf(output_fd, "\n; fetch instruction\n\n");

  print_line(2000, eval_core_ir);

  w = w + dprintf(output_fd, "\n; decode instruction\n\n");

  print_line(3000, eval_core_rd);

  w = w + dprintf(output_fd, "\n; update main memory\n\n");

  print_line(4000, next_main_memory);
}

void rotor() {
  new_register_file_state();
  new_main_memory_state();
  new_core_state();

  eval_core_ir = fetch_instruction(state_core_pc);
  eval_core_rd = get_instruction_opcode(eval_core_ir);

  output_machine();
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
      init_register_file_sorts();
      init_main_memory_sorts();
      init_instruction_sorts();

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

  if (exit_code == EXITCODE_MOREARGUMENTS)
    exit_code = selfie_model();

  return exit_selfie(exit_code, " - exit_code ...");
}