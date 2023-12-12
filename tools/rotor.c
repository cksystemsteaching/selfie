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
// -----------------------     M O D E L     -----------------------
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

uint64_t* new_constant(char* op, uint64_t* sid, char* constant, char* comment);
uint64_t* new_input(char* op, uint64_t* sid, char* symbol, char* comment);

uint64_t* new_ext(char* op, uint64_t* sid, uint64_t* value_nid, uint64_t w, char* comment);
uint64_t* new_slice(uint64_t* sid, uint64_t* value_nid, uint64_t u, uint64_t l, char* comment);

uint64_t* new_unary(char* op, uint64_t* sid, uint64_t* value_nid, char* comment);
uint64_t* new_binary(char* op, uint64_t* sid, uint64_t* left_nid, uint64_t* right_nid, char* comment);
uint64_t* new_binary_boolean(char* op, uint64_t* left_nid, uint64_t* right_nid, char* comment);
uint64_t* new_ternary(char* op, uint64_t* sid, uint64_t* first_nid, uint64_t* second_nid, uint64_t* third_nid, char* comment);

uint64_t* new_property(char* op, uint64_t* condition_nid, char* symbol, char* comment);

void print_nid(uint64_t nid, uint64_t* line);
void print_comment(uint64_t* line);

uint64_t is_input_op(char* op);
uint64_t is_unary_op(char* op);

uint64_t print_line(uint64_t nid, uint64_t* line);

uint64_t print_sort(uint64_t nid, uint64_t* line);
uint64_t print_input(uint64_t nid, uint64_t* line);

uint64_t print_ext(uint64_t nid, uint64_t* line);
uint64_t print_slice(uint64_t nid, uint64_t* line);

uint64_t print_unary_op(uint64_t nid, uint64_t* line);
uint64_t print_binary_op(uint64_t nid, uint64_t* line);
uint64_t print_ternary_op(uint64_t nid, uint64_t* line);

uint64_t print_constraint(uint64_t nid, uint64_t* line);

char* format_comment(char* comment, uint64_t value);

char* format_binary(uint64_t value, uint64_t alignment);
char* format_decimal(uint64_t value);

char* format_comment_binary(char* comment, uint64_t value);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t* UNUSED    = (uint64_t*) 0;
char*     NOCOMMENT = (char*) 0;

char* BITVEC = (char*) 0;
char* ARRAY  = (char*) 0;

char* OP_SORT = (char*) 0;

char* OP_CONST  = (char*) 0;
char* OP_CONSTD = (char*) 0;
char* OP_CONSTH = (char*) 0;
char* OP_INPUT  = (char*) 0;
char* OP_STATE  = (char*) 0;

char* OP_INIT  = (char*) 0;
char* OP_NEXT  = (char*) 0;

char* OP_SEXT  = (char*) 0;
char* OP_UEXT  = (char*) 0;
char* OP_SLICE = (char*) 0;

char* OP_NOT = (char*) 0;
char* OP_INC = (char*) 0;
char* OP_DEC = (char*) 0;

char* OP_EQ   = (char*) 0;
char* OP_NEQ  = (char*) 0;
char* OP_UGT  = (char*) 0;
char* OP_UGTE = (char*) 0;
char* OP_ULT  = (char*) 0;

char* OP_AND = (char*) 0;
char* OP_OR  = (char*) 0;

char* OP_SLL = (char*) 0;
char* OP_SRL = (char*) 0;

char* OP_ADD = (char*) 0;

char* OP_CONCAT = (char*) 0;
char* OP_READ   = (char*) 0;

char* OP_ITE   = (char*) 0;
char* OP_WRITE = (char*) 0;

char* OP_BAD        = (char*) 0;
char* OP_CONSTRAINT = (char*) 0;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t number_of_lines = 0;

// ------------------------- INITIALIZATION ------------------------

void init_model() {
  BITVEC = "bitvec";
  ARRAY  = "array";

  OP_SORT = "sort";

  OP_CONST  = "const";
  OP_CONSTD = "constd";
  OP_CONSTH = "consth";
  OP_INPUT  = "input";
  OP_STATE  = "state";

  OP_INIT  = "init";
  OP_NEXT  = "next";

  OP_SEXT  = "sext";
  OP_UEXT  = "uext";
  OP_SLICE = "slice";

  OP_NOT = "not";
  OP_INC = "inc";
  OP_DEC = "dec";

  OP_EQ   = "eq";
  OP_NEQ  = "neq";
  OP_UGT  = "ugt";
  OP_UGTE = "ugte";
  OP_ULT  = "ult";

  OP_AND = "and";
  OP_OR  = "or";

  OP_SLL = "sll";
  OP_SRL = "srl";

  OP_ADD = "add";

  OP_CONCAT = "concat";
  OP_READ   = "read";

  OP_ITE   = "ite";
  OP_WRITE = "write";

  OP_BAD        = "bad";
  OP_CONSTRAINT = "constraint";
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

void print_interface_sorts();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t* SID_BOOLEAN = (uint64_t*) 0;

uint64_t* NID_FALSE = (uint64_t*) 0;
uint64_t* NID_TRUE  = (uint64_t*) 1;

uint64_t* SID_BYTE = (uint64_t*) 0;

uint64_t* NID_BYTE_0 = (uint64_t*) 0;
uint64_t* NID_BYTE_4 = (uint64_t*) 0;

uint64_t* SID_SINGLE_WORD = (uint64_t*) 0;

uint64_t* NID_SINGLE_WORD_0 = (uint64_t*) 0;
uint64_t* NID_SINGLE_WORD_1 = (uint64_t*) 0;
uint64_t* NID_SINGLE_WORD_2 = (uint64_t*) 0;
uint64_t* NID_SINGLE_WORD_3 = (uint64_t*) 0;
uint64_t* NID_SINGLE_WORD_4 = (uint64_t*) 0;
uint64_t* NID_SINGLE_WORD_8 = (uint64_t*) 0;

uint64_t* NID_SINGLE_WORD_MINUS_1 = (uint64_t*) 0;

uint64_t* SID_INSTRUCTION_WORD = (uint64_t*) 0;

uint64_t* SID_DOUBLE_WORD = (uint64_t*) 0;

uint64_t* NID_DOUBLE_WORD_0 = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_1 = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_2 = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_3 = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_4 = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_8 = (uint64_t*) 0;

uint64_t* NID_DOUBLE_WORD_MINUS_1 = (uint64_t*) 0;

uint64_t* SID_MACHINE_WORD = (uint64_t*) 0;

uint64_t* NID_MACHINE_WORD_0 = (uint64_t*) 0;
uint64_t* NID_MACHINE_WORD_1 = (uint64_t*) 0;
uint64_t* NID_MACHINE_WORD_2 = (uint64_t*) 0;
uint64_t* NID_MACHINE_WORD_3 = (uint64_t*) 0;
uint64_t* NID_MACHINE_WORD_4 = (uint64_t*) 0;
uint64_t* NID_MACHINE_WORD_8 = (uint64_t*) 0;

uint64_t* NID_MACHINE_WORD_MINUS_1 = (uint64_t*) 0;

uint64_t* NID_MACHINE_WORD_SIZE_MASK = (uint64_t*) 0;
uint64_t* NID_MACHINE_WORD_BYTE_MASK = (uint64_t*) 0;

uint64_t* NID_BYTE_SIZE_IN_BASE_BITS = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_interface_sorts() {
  SID_BOOLEAN = new_bitvec(1, "Boolean");

  NID_FALSE = new_constant(OP_CONSTD, SID_BOOLEAN, (char*) 0, "false");
  NID_TRUE  = new_constant(OP_CONSTD, SID_BOOLEAN, (char*) 1, "true");

  SID_BYTE = new_bitvec(8, "8-bit byte");

  NID_BYTE_0 = new_constant(OP_CONSTD, SID_BYTE, "0", "byte 0");
  NID_BYTE_4 = new_constant(OP_CONSTD, SID_BYTE, "4", "byte 4");

  SID_SINGLE_WORD = new_bitvec(32, "32-bit single word");

  NID_SINGLE_WORD_0 = new_constant(OP_CONSTD, SID_SINGLE_WORD, "0", "single-word 0");
  NID_SINGLE_WORD_1 = new_constant(OP_CONSTD, SID_SINGLE_WORD, "1", "single-word 1");
  NID_SINGLE_WORD_2 = new_constant(OP_CONSTD, SID_SINGLE_WORD, "2", "single-word 2");
  NID_SINGLE_WORD_3 = new_constant(OP_CONSTD, SID_SINGLE_WORD, "3", "single-word 3");
  NID_SINGLE_WORD_4 = new_constant(OP_CONSTD, SID_SINGLE_WORD, "4", "single-word 4");
  NID_SINGLE_WORD_8 = new_constant(OP_CONSTD, SID_SINGLE_WORD, "8", "single-word 8");

  NID_SINGLE_WORD_MINUS_1 = new_constant(OP_CONSTD, SID_SINGLE_WORD, "-1", "single-word -1");

  SID_INSTRUCTION_WORD = SID_SINGLE_WORD;

  if (IS64BITTARGET) {
    SID_DOUBLE_WORD = new_bitvec(64, "64-bit double word");

    NID_DOUBLE_WORD_0 = new_constant(OP_CONSTD, SID_DOUBLE_WORD, "0", "double-word 0");
    NID_DOUBLE_WORD_1 = new_constant(OP_CONSTD, SID_DOUBLE_WORD, "1", "double-word 1");
    NID_DOUBLE_WORD_2 = new_constant(OP_CONSTD, SID_DOUBLE_WORD, "2", "double-word 2");
    NID_DOUBLE_WORD_3 = new_constant(OP_CONSTD, SID_DOUBLE_WORD, "3", "double-word 3");
    NID_DOUBLE_WORD_4 = new_constant(OP_CONSTD, SID_DOUBLE_WORD, "4", "double-word 4");
    NID_DOUBLE_WORD_8 = new_constant(OP_CONSTD, SID_DOUBLE_WORD, "8", "double-word 8");

    NID_DOUBLE_WORD_MINUS_1 = new_constant(OP_CONSTD, SID_DOUBLE_WORD, "-1", "double-word -1");

    SID_MACHINE_WORD = SID_DOUBLE_WORD;

    NID_MACHINE_WORD_0 = NID_DOUBLE_WORD_0;
    NID_MACHINE_WORD_1 = NID_DOUBLE_WORD_1;
    NID_MACHINE_WORD_2 = NID_DOUBLE_WORD_2;
    NID_MACHINE_WORD_3 = NID_DOUBLE_WORD_3;
    NID_MACHINE_WORD_4 = NID_DOUBLE_WORD_4;
    NID_MACHINE_WORD_8 = NID_DOUBLE_WORD_8;

    NID_MACHINE_WORD_MINUS_1 = NID_DOUBLE_WORD_MINUS_1;

    NID_MACHINE_WORD_SIZE_MASK = new_constant(OP_CONST, SID_MACHINE_WORD,
      "0000000000000000000000000000000000000000000000000000000000000111", "machine word size in bytes - 1");
  } else {
    // assert: 32-bit system
    SID_MACHINE_WORD = SID_SINGLE_WORD;

    NID_MACHINE_WORD_0 = NID_SINGLE_WORD_0;
    NID_MACHINE_WORD_1 = NID_SINGLE_WORD_1;
    NID_MACHINE_WORD_2 = NID_SINGLE_WORD_2;
    NID_MACHINE_WORD_3 = NID_SINGLE_WORD_3;
    NID_MACHINE_WORD_4 = NID_SINGLE_WORD_4;
    NID_MACHINE_WORD_8 = NID_SINGLE_WORD_8;

    NID_MACHINE_WORD_MINUS_1 = NID_SINGLE_WORD_MINUS_1;

    NID_MACHINE_WORD_SIZE_MASK = new_constant(OP_CONST, SID_MACHINE_WORD,
      "00000000000000000000000000000011", "machine word size in bytes - 1");
  }

  NID_MACHINE_WORD_BYTE_MASK = new_constant(OP_CONSTH, SID_MACHINE_WORD,
    "FF", "maximum value of a byte in a machine word");

  NID_BYTE_SIZE_IN_BASE_BITS = NID_MACHINE_WORD_3;
}

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void print_interface_memory();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t ISBYTEMEMORY = 0;

uint64_t* SID_MEMORY_WORD = (uint64_t*) 0;

uint64_t* NID_CODE_START = (uint64_t*) 0;
uint64_t* NID_CODE_END   = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_interface_memory() {
  if (ISBYTEMEMORY)
    SID_MEMORY_WORD = SID_BYTE;
  else
    SID_MEMORY_WORD = SID_MACHINE_WORD;

  NID_CODE_START = new_constant(OP_CONSTH, SID_MACHINE_WORD,
    format_comment("%08lX", code_start),
    "start of code segment");

  NID_CODE_END = new_constant(OP_CONSTH, SID_MACHINE_WORD,
    format_comment("%08lX", code_start + code_size),
    "end of code segment");
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

void print_interface_kernel();

void new_kernel_state(uint64_t bytes_to_read);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t* NID_EXIT_SYSCALL_ID = (uint64_t*) 0;
uint64_t* NID_READ_SYSCALL_ID = (uint64_t*) 0;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* readable_bytes_nid = (uint64_t*) 0;

uint64_t* state_readable_bytes_nid = (uint64_t*) 0;
uint64_t* init_readable_bytes_nid  = (uint64_t*) 0;
uint64_t* next_readable_bytes_nid  = (uint64_t*) 0;

uint64_t* state_read_bytes_nid = (uint64_t*) 0;
uint64_t* init_read_bytes_nid  = (uint64_t*) 0;
uint64_t* next_read_bytes_nid  = (uint64_t*) 0;

uint64_t* eval_kernel_pc_nid = (uint64_t*) 0;

uint64_t* eval_kernel_register_data_flow_nid = (uint64_t*) 0;
uint64_t* eval_kernel_memory_data_flow_nid   = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_interface_kernel() {
  NID_EXIT_SYSCALL_ID = new_constant(OP_CONSTD, SID_MACHINE_WORD,
    format_decimal(SYSCALL_EXIT),
    format_comment_binary("exit syscall ID", SYSCALL_EXIT));
  NID_READ_SYSCALL_ID = new_constant(OP_CONSTD, SID_MACHINE_WORD,
    format_decimal(SYSCALL_READ),
    format_comment_binary("read syscall ID", SYSCALL_READ));
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------    A R C H I T E C T U R E    -----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// --------------------------- REGISTERS ---------------------------
// -----------------------------------------------------------------

void print_register_sorts();

void new_register_file_state();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t* SID_REGISTER_ADDRESS = (uint64_t*) 0;

uint64_t* NID_ZR  = (uint64_t*) 0;
uint64_t* NID_RA  = (uint64_t*) 0;
uint64_t* NID_SP  = (uint64_t*) 0;
uint64_t* NID_GP  = (uint64_t*) 0;
uint64_t* NID_TP  = (uint64_t*) 0;
uint64_t* NID_T0  = (uint64_t*) 0;
uint64_t* NID_T1  = (uint64_t*) 0;
uint64_t* NID_T2  = (uint64_t*) 0;
uint64_t* NID_S0  = (uint64_t*) 0;
uint64_t* NID_S1  = (uint64_t*) 0;
uint64_t* NID_A0  = (uint64_t*) 0;
uint64_t* NID_A1  = (uint64_t*) 0;
uint64_t* NID_A2  = (uint64_t*) 0;
uint64_t* NID_A3  = (uint64_t*) 0;
uint64_t* NID_A4  = (uint64_t*) 0;
uint64_t* NID_A5  = (uint64_t*) 0;
uint64_t* NID_A6  = (uint64_t*) 0;
uint64_t* NID_A7  = (uint64_t*) 0;
uint64_t* NID_S2  = (uint64_t*) 0;
uint64_t* NID_S3  = (uint64_t*) 0;
uint64_t* NID_S4  = (uint64_t*) 0;
uint64_t* NID_S5  = (uint64_t*) 0;
uint64_t* NID_S6  = (uint64_t*) 0;
uint64_t* NID_S7  = (uint64_t*) 0;
uint64_t* NID_S8  = (uint64_t*) 0;
uint64_t* NID_S9  = (uint64_t*) 0;
uint64_t* NID_S10 = (uint64_t*) 0;
uint64_t* NID_S11 = (uint64_t*) 0;
uint64_t* NID_T3  = (uint64_t*) 0;
uint64_t* NID_T4  = (uint64_t*) 0;
uint64_t* NID_T5  = (uint64_t*) 0;
uint64_t* NID_T6  = (uint64_t*) 0;

uint64_t* SID_REGISTER_STATE = (uint64_t*) 0;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* state_register_file_nid = (uint64_t*) 0;
uint64_t* init_register_file_nid  = (uint64_t*) 0;
uint64_t* next_register_file_nid  = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_register_file_sorts() {
  SID_REGISTER_ADDRESS = new_bitvec(5, "5-bit register address");

  NID_ZR  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_ZR, 5), (char*) *(REGISTERS + REG_ZR));
  NID_RA  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_RA, 5), (char*) *(REGISTERS + REG_RA));
  NID_SP  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_SP, 5), (char*) *(REGISTERS + REG_SP));
  NID_GP  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_GP, 5), (char*) *(REGISTERS + REG_GP));
  NID_TP  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_TP, 5), (char*) *(REGISTERS + REG_TP));
  NID_T0  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_T0, 5), (char*) *(REGISTERS + REG_T0));
  NID_T1  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_T1, 5), (char*) *(REGISTERS + REG_T1));
  NID_T2  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_T2, 5), (char*) *(REGISTERS + REG_T2));
  NID_S0  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_S0, 5), (char*) *(REGISTERS + REG_S0));
  NID_S1  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_S1, 5), (char*) *(REGISTERS + REG_S1));
  NID_A0  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_A0, 5), (char*) *(REGISTERS + REG_A0));
  NID_A1  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_A1, 5), (char*) *(REGISTERS + REG_A1));
  NID_A2  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_A2, 5), (char*) *(REGISTERS + REG_A2));
  NID_A3  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_A3, 5), (char*) *(REGISTERS + REG_A3));
  NID_A4  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_A4, 5), (char*) *(REGISTERS + REG_A4));
  NID_A5  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_A5, 5), (char*) *(REGISTERS + REG_A5));
  NID_A6  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_A6, 5), (char*) *(REGISTERS + REG_A6));
  NID_A7  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_A7, 5), (char*) *(REGISTERS + REG_A7));
  NID_S2  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_S2, 5), (char*) *(REGISTERS + REG_S2));
  NID_S3  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_S3, 5), (char*) *(REGISTERS + REG_S3));
  NID_S4  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_S4, 5), (char*) *(REGISTERS + REG_S4));
  NID_S5  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_S5, 5), (char*) *(REGISTERS + REG_S5));
  NID_S6  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_S6, 5), (char*) *(REGISTERS + REG_S6));
  NID_S7  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_S7, 5), (char*) *(REGISTERS + REG_S7));
  NID_S8  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_S8, 5), (char*) *(REGISTERS + REG_S8));
  NID_S9  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_S9, 5), (char*) *(REGISTERS + REG_S9));
  NID_S10 = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_S10, 5), (char*) *(REGISTERS + REG_S10));
  NID_S11 = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_S11, 5), (char*) *(REGISTERS + REG_S11));
  NID_T3  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_T3, 5), (char*) *(REGISTERS + REG_T3));
  NID_T4  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_T4, 5), (char*) *(REGISTERS + REG_T4));
  NID_T5  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_T5, 5), (char*) *(REGISTERS + REG_T5));
  NID_T6  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, format_binary(REG_T6, 5), (char*) *(REGISTERS + REG_T6));

  SID_REGISTER_STATE = new_array(SID_REGISTER_ADDRESS, SID_MACHINE_WORD, "register state");
}

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void print_memory_sorts();

void new_main_memory_state();

uint64_t* is_access_in_segment(uint64_t* vaddr_nid, uint64_t* start_nid, uint64_t* end_nid);
uint64_t* is_access_in_code_segment(uint64_t* vaddr_nid);

uint64_t* is_range_accessing_segment(uint64_t* vaddr_nid, uint64_t* range_nid, uint64_t* start_nid, uint64_t* end_nid);
uint64_t* is_range_accessing_code_segment(uint64_t* vaddr_nid, uint64_t* range_nid);

uint64_t* vaddr_to_laddr(uint64_t* vaddr_nid);

uint64_t* load_machine_word(uint64_t* laddr_nid);
uint64_t* store_machine_word(uint64_t* laddr_nid, uint64_t* word_nid);

uint64_t* load_byte(uint64_t* vaddr_nid);
uint64_t* store_byte(uint64_t* vaddr_nid, uint64_t* byte_nid);

void fetch_instruction();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t* SID_CODE_ADDRESS = (uint64_t*) 0;
uint64_t* SID_CODE_STATE   = (uint64_t*) 0;

uint64_t* SID_MEMORY_ADDRESS = (uint64_t*) 0;
uint64_t* SID_MEMORY_STATE   = (uint64_t*) 0;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* state_code_segment_nid = (uint64_t*) 0;

uint64_t* state_main_memory_nid = (uint64_t*) 0;
uint64_t* init_main_memory_nid  = (uint64_t*) 0;
uint64_t* next_main_memory_nid  = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_memory_sorts() {
  SID_CODE_ADDRESS = new_bitvec(30, "30-bit memory address over 32-bit single words");
  SID_CODE_STATE   = new_array(SID_CODE_ADDRESS, SID_INSTRUCTION_WORD, "code segment state");

  if (ISBYTEMEMORY)
    SID_MEMORY_ADDRESS = new_bitvec(32, "32-bit memory address over 8-bit bytes");
  else if (IS64BITTARGET)
    SID_MEMORY_ADDRESS = new_bitvec(29, "29-bit memory address over 64-bit double words");
  else
    // assert: 32-bit system
    SID_MEMORY_ADDRESS = SID_CODE_ADDRESS;

  SID_MEMORY_STATE = new_array(SID_MEMORY_ADDRESS, SID_MEMORY_WORD, "main memory state");
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

uint64_t* get_instruction_I_imm(uint64_t* instruction);
uint64_t* get_instruction_S_imm(uint64_t* instruction);
uint64_t* get_instruction_U_imm(uint64_t* instruction);
uint64_t* sign_extend_IS_imm(uint64_t* imm);
uint64_t* get_machine_word_I_immediate(uint64_t* instruction);
uint64_t* get_machine_word_S_immediate(uint64_t* instruction);
uint64_t* get_machine_word_U_immediate(uint64_t* instruction);

uint64_t* decode_instruction();

uint64_t* core_register_data_flow(uint64_t* register_file_nid);
uint64_t* core_memory_data_flow(uint64_t* main_memory_nid);

uint64_t* control_flow();

// ------------------------ GLOBAL CONSTANTS -----------------------

// RISC-V codes missing in RISC-U

uint64_t F3_LB = 0;
uint64_t F3_SB = 0;

uint64_t* SID_OPCODE = (uint64_t*) 0;

uint64_t* NID_OP_LOAD   = (uint64_t*) 0;
uint64_t* NID_OP_IMM    = (uint64_t*) 0;
uint64_t* NID_OP_STORE  = (uint64_t*) 0;
uint64_t* NID_OP_OP     = (uint64_t*) 0;
uint64_t* NID_OP_LUI    = (uint64_t*) 0;
uint64_t* NID_OP_BRANCH = (uint64_t*) 0;
uint64_t* NID_OP_JALR   = (uint64_t*) 0;
uint64_t* NID_OP_JAL    = (uint64_t*) 0;
uint64_t* NID_OP_SYSTEM = (uint64_t*) 0;

uint64_t* SID_FUNCT3 = (uint64_t*) 0;

uint64_t* NID_F3_NOP         = (uint64_t*) 0;
uint64_t* NID_F3_ADDI        = (uint64_t*) 0;
uint64_t* NID_F3_ADD_SUB_MUL = (uint64_t*) 0;
uint64_t* NID_F3_DIVU        = (uint64_t*) 0;
uint64_t* NID_F3_REMU        = (uint64_t*) 0;
uint64_t* NID_F3_SLTU        = (uint64_t*) 0;
uint64_t* NID_F3_LD          = (uint64_t*) 0;
uint64_t* NID_F3_SD          = (uint64_t*) 0;
uint64_t* NID_F3_LW          = (uint64_t*) 0;
uint64_t* NID_F3_SW          = (uint64_t*) 0;
uint64_t* NID_F3_LB          = (uint64_t*) 0;
uint64_t* NID_F3_SB          = (uint64_t*) 0;
uint64_t* NID_F3_BEQ         = (uint64_t*) 0;
uint64_t* NID_F3_JALR        = (uint64_t*) 0;
uint64_t* NID_F3_ECALL       = (uint64_t*) 0;

uint64_t* SID_FUNCT7 = (uint64_t*) 0;

uint64_t* NID_F7_ADD  = (uint64_t*) 0;
uint64_t* NID_F7_MUL  = (uint64_t*) 0;
uint64_t* NID_F7_SUB  = (uint64_t*) 0;
uint64_t* NID_F7_DIVU = (uint64_t*) 0;
uint64_t* NID_F7_REMU = (uint64_t*) 0;
uint64_t* NID_F7_SLTU = (uint64_t*) 0;

uint64_t* SID_FUNCT12 = (uint64_t*) 0;

uint64_t* NID_F12_ECALL = (uint64_t*) 0;

uint64_t* NID_ECALL = (uint64_t*) 0;

uint64_t* SID_12_BIT_IMM = (uint64_t*) 0;
uint64_t* SID_20_BIT_IMM = (uint64_t*) 0;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* eval_core_ir_nid = (uint64_t*) 0;

uint64_t* eval_core_active_ecall_nid = (uint64_t*) 0;

uint64_t* eval_core_imm_nid            = (uint64_t*) 0;
uint64_t* eval_core_f3_addi_nid        = (uint64_t*) 0;
uint64_t* eval_core_op_nid             = (uint64_t*) 0;
uint64_t* eval_core_f3_add_sub_mul_nid = (uint64_t*) 0;
uint64_t* eval_core_f7_add_nid         = (uint64_t*) 0;
uint64_t* eval_core_store_nid          = (uint64_t*) 0;
uint64_t* eval_core_f3_sb_nid          = (uint64_t*) 0;
uint64_t* eval_core_branch_nid         = (uint64_t*) 0;
uint64_t* eval_core_jal_nid            = (uint64_t*) 0;
uint64_t* eval_core_jalr_nid           = (uint64_t*) 0;

uint64_t* eval_core_register_data_flow_nid = (uint64_t*) 0;
uint64_t* eval_core_memory_data_flow_nid   = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_instruction_sorts() {
  SID_OPCODE = new_bitvec(7, "opcode sort");

  NID_OP_LOAD   = new_constant(OP_CONST, SID_OPCODE, format_binary(OP_LOAD, 7), "OP_LOAD");
  NID_OP_IMM    = new_constant(OP_CONST, SID_OPCODE, format_binary(OP_IMM, 7), "OP_IMM");
  NID_OP_STORE  = new_constant(OP_CONST, SID_OPCODE, format_binary(OP_STORE, 7), "OP_STORE");
  NID_OP_OP     = new_constant(OP_CONST, SID_OPCODE, format_binary(OP_OP, 7), "OP_OP");
  NID_OP_LUI    = new_constant(OP_CONST, SID_OPCODE, format_binary(OP_LUI, 7), "OP_LUI");
  NID_OP_BRANCH = new_constant(OP_CONST, SID_OPCODE, format_binary(OP_BRANCH, 7), "OP_BRANCH");
  NID_OP_JALR   = new_constant(OP_CONST, SID_OPCODE, format_binary(OP_JALR, 7), "OP_JALR");
  NID_OP_JAL    = new_constant(OP_CONST, SID_OPCODE, format_binary(OP_JAL, 7), "OP_JAL");
  NID_OP_SYSTEM = new_constant(OP_CONST, SID_OPCODE, format_binary(OP_SYSTEM, 7), "OP_SYSTEM");

  SID_FUNCT3 = new_bitvec(3, "funct3 sort");

  NID_F3_NOP         = new_constant(OP_CONST, SID_FUNCT3, format_binary(F3_NOP, 3), "F3_NOP");
  NID_F3_ADDI        = new_constant(OP_CONST, SID_FUNCT3, format_binary(F3_ADDI, 3), "F3_ADDI");
  NID_F3_ADD_SUB_MUL = new_constant(OP_CONST, SID_FUNCT3, format_binary(F3_ADD, 3), "F3_ADD_SUB_MUL");
  NID_F3_DIVU        = new_constant(OP_CONST, SID_FUNCT3, format_binary(F3_DIVU, 3), "F3_DIVU");
  NID_F3_REMU        = new_constant(OP_CONST, SID_FUNCT3, format_binary(F3_REMU, 3), "F3_REMU");
  NID_F3_SLTU        = new_constant(OP_CONST, SID_FUNCT3, format_binary(F3_SLTU, 3), "F3_SLTU");
  NID_F3_LD          = new_constant(OP_CONST, SID_FUNCT3, format_binary(F3_LD, 3), "F3_LD");
  NID_F3_SD          = new_constant(OP_CONST, SID_FUNCT3, format_binary(F3_SD, 3), "F3_SD");
  NID_F3_LW          = new_constant(OP_CONST, SID_FUNCT3, format_binary(F3_LW, 3), "F3_LW");
  NID_F3_SW          = new_constant(OP_CONST, SID_FUNCT3, format_binary(F3_SW, 3), "F3_SW");
  NID_F3_LB          = new_constant(OP_CONST, SID_FUNCT3, format_binary(F3_LB, 3), "F3_LB");
  NID_F3_SB          = new_constant(OP_CONST, SID_FUNCT3, format_binary(F3_SB, 3), "F3_SB");
  NID_F3_BEQ         = new_constant(OP_CONST, SID_FUNCT3, format_binary(F3_BEQ, 3), "F3_BEQ");
  NID_F3_JALR        = new_constant(OP_CONST, SID_FUNCT3, format_binary(F3_JALR, 3), "F3_JALR");
  NID_F3_ECALL       = new_constant(OP_CONST, SID_FUNCT3, format_binary(F3_ECALL, 3), "F3_ECALL");

  SID_FUNCT7 = new_bitvec(7, "funct7 sort");

  NID_F7_ADD  = new_constant(OP_CONST, SID_FUNCT7, format_binary(F7_ADD, 7), "F7_ADD");
  NID_F7_MUL  = new_constant(OP_CONST, SID_FUNCT7, format_binary(F7_MUL, 7), "F7_MUL");
  NID_F7_SUB  = new_constant(OP_CONST, SID_FUNCT7, format_binary(F7_SUB, 7), "F7_SUB");
  NID_F7_DIVU = new_constant(OP_CONST, SID_FUNCT7, format_binary(F7_DIVU, 7), "F7_DIVU");
  NID_F7_REMU = new_constant(OP_CONST, SID_FUNCT7, format_binary(F7_REMU, 7), "F7_REMU");
  NID_F7_SLTU = new_constant(OP_CONST, SID_FUNCT7, format_binary(F7_SLTU, 7), "F7_SLTU");

  SID_FUNCT12 = new_bitvec(12, "funct12 sort");

  NID_F12_ECALL = new_constant(OP_CONST, SID_FUNCT12, format_binary(F12_ECALL, 12), "F12_ECALL");

  NID_ECALL = new_constant(OP_CONST, SID_INSTRUCTION_WORD,
    format_binary(left_shift(left_shift(left_shift(left_shift(F12_ECALL, 5) + REG_ZR, 3)
      + F3_ECALL, 5) + REG_ZR, 7) + OP_SYSTEM,
    32),
    "ECALL instruction");

  SID_12_BIT_IMM = new_bitvec(12, "12-bit immediate sort");
  SID_20_BIT_IMM = new_bitvec(20, "20-bit immediate sort");
}

// -----------------------------------------------------------------
// ----------------------------- CORE ------------------------------
// -----------------------------------------------------------------

void new_core_state();

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* state_core_pc_nid = (uint64_t*) 0;
uint64_t* init_core_pc_nid  = (uint64_t*) 0;

uint64_t* eval_core_pc_nid = (uint64_t*) 0;
uint64_t* next_core_pc_nid = (uint64_t*) 0;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

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

uint64_t bad_exit_code = 0; // model for this exit code

uint64_t* constraint_ir_nid = (uint64_t*) 0;

uint64_t* bad_pc_nid         = (uint64_t*) 0;
uint64_t* bad_read_nid       = (uint64_t*) 0;
uint64_t* bad_syscall_id_nid = (uint64_t*) 0;
uint64_t* bad_exit_nid       = (uint64_t*) 0;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------------     M O D E L     -----------------------
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

uint64_t* new_constant(char* op, uint64_t* sid, char* constant, char* comment) {
  return new_line(op, sid, (uint64_t*) constant, UNUSED, UNUSED, comment);
}

uint64_t* new_input(char* op, uint64_t* sid, char* symbol, char* comment) {
  return new_line(op, sid, (uint64_t*) symbol, UNUSED, UNUSED, comment);
}

uint64_t* new_ext(char* op, uint64_t* sid, uint64_t* value_nid, uint64_t w, char* comment) {
  return new_line(op, sid, value_nid, (uint64_t*) w, UNUSED, comment);
}

uint64_t* new_slice(uint64_t* sid, uint64_t* value_nid, uint64_t u, uint64_t l, char* comment) {
  return new_line(OP_SLICE, sid, value_nid, (uint64_t*) u, (uint64_t*) l, comment);
}

uint64_t* new_unary(char* op, uint64_t* sid, uint64_t* value_nid, char* comment) {
  return new_line(op, sid, value_nid, UNUSED, UNUSED, comment);
}

uint64_t* new_binary(char* op, uint64_t* sid, uint64_t* left_nid, uint64_t* right_nid, char* comment) {
  return new_line(op, sid, left_nid, right_nid, UNUSED, comment);
}

uint64_t* new_binary_boolean(char* op, uint64_t* left_nid, uint64_t* right_nid, char* comment) {
  return new_binary(op, SID_BOOLEAN, left_nid, right_nid, comment);
}

uint64_t* new_ternary(char* op, uint64_t* sid, uint64_t* first_nid, uint64_t* second_nid, uint64_t* third_nid, char* comment) {
  return new_line(op, sid, first_nid, second_nid, third_nid, comment);
}

uint64_t* new_property(char* op, uint64_t* condition_nid, char* symbol, char* comment) {
  return new_line(op, UNUSED, condition_nid, (uint64_t*) symbol, UNUSED, comment);
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

uint64_t is_input_op(char* op) {
  if (op == OP_CONST)
    return 1;
  else if (op == OP_CONSTD)
    return 1;
  else if (op == OP_CONSTH)
    return 1;
  else if (op == OP_INPUT)
    return 1;
  else if (op == OP_STATE)
    return 1;
  else
    return 0;
}

uint64_t is_unary_op(char* op) {
  if (op == OP_NOT)
    return 1;
  else if (op == OP_INC)
    return 1;
  else if (op == OP_DEC)
    return 1;
  else
    return 0;
}

uint64_t print_line(uint64_t nid, uint64_t* line) {
  char* op;

  op = get_op(line);

  if (get_nid(line) > 0)
    // print lines only once
    return nid;
  else if (op == OP_SORT)
    nid = print_sort(nid, line);
  else if (is_input_op(op))
    nid = print_input(nid, line);
  else if (op == OP_SEXT)
    nid = print_ext(nid, line);
  else if (op == OP_UEXT)
    nid = print_ext(nid, line);
  else if (op == OP_SLICE)
    nid = print_slice(nid, line);
  else if (is_unary_op(op))
    nid = print_unary_op(nid, line);
  else if (op == OP_ITE)
    nid = print_ternary_op(nid, line);
  else if (op == OP_WRITE)
    nid = print_ternary_op(nid, line);
  else if (op == OP_BAD)
    nid = print_constraint(nid, line);
  else if (op == OP_CONSTRAINT)
    nid = print_constraint(nid, line);
  else
    nid = print_binary_op(nid, line);
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

uint64_t print_input(uint64_t nid, uint64_t* line) {
  nid = print_line(nid, get_sid(line));
  print_nid(nid, line);
  if (get_op(line) == OP_CONSTD) {
    if ((uint64_t) get_arg1(line) == 0) {
      w = w + dprintf(output_fd, " zero %lu", get_nid(get_sid(line)));
      return nid;
    } else if ((uint64_t) get_arg1(line) == 1) {
      w = w + dprintf(output_fd, " one %lu", get_nid(get_sid(line)));
      return nid;
    }
  }
  w = w + dprintf(output_fd, " %s %lu %s", get_op(line), get_nid(get_sid(line)), (char*) get_arg1(line));
  return nid;
}

uint64_t print_ext(uint64_t nid, uint64_t* line) {
  nid = print_line(nid, get_sid(line));
  nid = print_line(nid, get_arg1(line));
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s %lu %lu %lu",
    get_op(line), get_nid(get_sid(line)), get_nid(get_arg1(line)), (uint64_t) get_arg2(line));
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

uint64_t print_unary_op(uint64_t nid, uint64_t* line) {
  nid = print_line(nid, get_sid(line));
  nid = print_line(nid, get_arg1(line));
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s %lu %lu",
    get_op(line), get_nid(get_sid(line)), get_nid(get_arg1(line)));
  return nid;
}

uint64_t print_binary_op(uint64_t nid, uint64_t* line) {
  nid = print_line(nid, get_sid(line));
  nid = print_line(nid, get_arg1(line));
  nid = print_line(nid, get_arg2(line));
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s %lu %lu %lu",
    get_op(line), get_nid(get_sid(line)), get_nid(get_arg1(line)), get_nid(get_arg2(line)));
  return nid;
}

uint64_t print_ternary_op(uint64_t nid, uint64_t* line) {
  nid = print_line(nid, get_sid(line));
  nid = print_line(nid, get_arg1(line));
  nid = print_line(nid, get_arg2(line));
  nid = print_line(nid, get_arg3(line));
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s %lu %lu %lu %lu",
    get_op(line), get_nid(get_sid(line)), get_nid(get_arg1(line)), get_nid(get_arg2(line)), get_nid(get_arg3(line)));
  return nid;
}

uint64_t print_constraint(uint64_t nid, uint64_t* line) {
  nid = print_line(nid, get_arg1(line));
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s %lu %s", get_op(line), get_nid(get_arg1(line)), (char*) get_arg2(line));
  return nid;
}

char* format_comment(char* comment, uint64_t value) {
  sprintf(string_buffer, comment, value);
  return string_copy(string_buffer);
}

char* format_binary(uint64_t value, uint64_t alignment) {
  return string_copy(itoa(value, integer_buffer, 2, 0, alignment));
}

char* format_decimal(uint64_t value) {
  return format_comment("%ld", value);
}

char* format_comment_binary(char* comment, uint64_t value) {
  sprintf(string_buffer, "%s %s", comment, format_binary(value, 0));
  return string_copy(string_buffer);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

void print_interface_sorts() {
  print_line(1, SID_BOOLEAN);

  print_line(2, SID_BYTE);
  print_line(3, SID_SINGLE_WORD);
  if (IS64BITTARGET)
    print_line(4, SID_DOUBLE_WORD);

  w = w + dprintf(output_fd, "\n; machine constants\n\n");

  print_line(10, NID_FALSE);
  print_line(11, NID_TRUE);

  w = w + dprintf(output_fd, "\n");

  print_line(20, NID_BYTE_0);
  print_line(24, NID_BYTE_4);

  w = w + dprintf(output_fd, "\n");

  print_line(30, NID_SINGLE_WORD_0);
  print_line(31, NID_SINGLE_WORD_1);
  print_line(32, NID_SINGLE_WORD_2);
  print_line(33, NID_SINGLE_WORD_3);
  print_line(34, NID_SINGLE_WORD_4);
  print_line(38, NID_SINGLE_WORD_8);

  print_line(39, NID_SINGLE_WORD_MINUS_1);

  if (IS64BITTARGET) {
    w = w + dprintf(output_fd, "\n");

    print_line(40, NID_DOUBLE_WORD_0);
    print_line(41, NID_DOUBLE_WORD_1);
    print_line(42, NID_DOUBLE_WORD_2);
    print_line(43, NID_DOUBLE_WORD_3);
    print_line(44, NID_DOUBLE_WORD_4);
    print_line(48, NID_DOUBLE_WORD_8);

    print_line(49, NID_DOUBLE_WORD_MINUS_1);
  }
}
// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void print_interface_memory() {
  w = w + dprintf(output_fd, "\n; memory interface\n\n");

  print_line(50, NID_CODE_START);
  print_line(51, NID_CODE_END);
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

void print_interface_kernel() {
  w = w + dprintf(output_fd, "\n; kernel interface\n\n");

  print_line(60, NID_EXIT_SYSCALL_ID);
  print_line(61, NID_READ_SYSCALL_ID);
}

void new_kernel_state(uint64_t bytes_to_read) {
  readable_bytes_nid = new_constant(OP_CONSTD, SID_MACHINE_WORD,
    format_decimal(bytes_to_read),
    "read capacity in bytes");

  state_readable_bytes_nid = new_input(OP_STATE, SID_MACHINE_WORD, "readable-bytes", "readable bytes");
  init_readable_bytes_nid  = new_binary(OP_INIT, SID_MACHINE_WORD, state_readable_bytes_nid,
    readable_bytes_nid, "number of readable bytes");

  state_read_bytes_nid = new_input(OP_STATE, SID_MACHINE_WORD, "read-bytes", "bytes read in active read system call");
  init_read_bytes_nid  = new_binary(OP_INIT, SID_MACHINE_WORD, state_read_bytes_nid,
    NID_MACHINE_WORD_0, "initially zero read bytes");
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------    A R C H I T E C T U R E    -----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// --------------------------- REGISTERS ---------------------------
// -----------------------------------------------------------------

void print_register_sorts() {
  w = w + dprintf(output_fd, "\n; register sorts\n\n");

  print_line(70, SID_REGISTER_ADDRESS);
  print_line(71, SID_REGISTER_STATE);
}

void new_register_file_state() {
  state_register_file_nid = new_input(OP_STATE, SID_REGISTER_STATE, "regs", "register file");
  init_register_file_nid  = new_binary(OP_INIT, SID_REGISTER_STATE, state_register_file_nid, NID_MACHINE_WORD_0, "zeroed registers");
}

uint64_t* get_register_value(uint64_t* reg_nid, char* comment) {
  return new_binary(OP_READ, SID_MACHINE_WORD, state_register_file_nid, reg_nid, comment);
}

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void print_memory_sorts() {
  w = w + dprintf(output_fd, "\n; memory sorts\n\n");

  print_line(80, SID_CODE_ADDRESS);
  print_line(81, SID_CODE_STATE);

  if (ISBYTEMEMORY) {
    print_line(90, SID_MEMORY_ADDRESS);
    print_line(91, SID_MEMORY_STATE);
  } else if (IS64BITTARGET) {
    print_line(90, SID_MEMORY_ADDRESS);
    print_line(91, SID_MEMORY_STATE);
  } else
    print_line(91, SID_MEMORY_STATE);
}

void new_main_memory_state() {
  state_code_segment_nid = new_input(OP_STATE, SID_CODE_STATE, "code-segment", "code segment");

  state_main_memory_nid = new_input(OP_STATE, SID_MEMORY_STATE, "main-memory", "main memory");

  if (ISBYTEMEMORY)
    init_main_memory_nid  = new_binary(OP_INIT, SID_MEMORY_STATE, state_main_memory_nid, NID_BYTE_0, "zeroed memory");
  else
    init_main_memory_nid  = new_binary(OP_INIT, SID_MEMORY_STATE, state_main_memory_nid, NID_MACHINE_WORD_0, "zeroed memory");
}

uint64_t* is_access_in_segment(uint64_t* vaddr_nid, uint64_t* start_nid, uint64_t* end_nid) {
  return new_binary_boolean(OP_AND,
    new_binary_boolean(OP_UGTE,
      vaddr_nid,
      start_nid,
      "vaddr >= start of segment"),
    new_binary_boolean(OP_ULT,
      vaddr_nid,
      end_nid,
      "vaddr < end of segment"),
    "vaddr in segment");
}

uint64_t* is_access_in_code_segment(uint64_t* vaddr_nid) {
  return is_access_in_segment(vaddr_nid, NID_CODE_START, NID_CODE_END);
}

uint64_t* is_range_accessing_segment(uint64_t* vaddr_nid, uint64_t* range_nid, uint64_t* start_nid, uint64_t* end_nid) {
  return new_binary_boolean(OP_AND,
    new_binary_boolean(OP_UGTE,
      new_binary(OP_ADD, SID_MACHINE_WORD,
        vaddr_nid,
        range_nid,
        "vaddr + range in bytes"),
      start_nid,
      "vaddr + range >= start of segment"),
    new_binary_boolean(OP_ULT,
      vaddr_nid,
      end_nid,
      "vaddr < end of segment"),
    "some vaddresses in range in segment");
}

uint64_t* is_range_accessing_code_segment(uint64_t* vaddr_nid, uint64_t* range_nid) {
  return is_range_accessing_segment(vaddr_nid, range_nid, NID_CODE_START, NID_CODE_END);
}

uint64_t* vaddr_to_30_bit_laddr(uint64_t* vaddr_nid) {
  return new_slice(SID_CODE_ADDRESS, vaddr_nid, 31, 2, "map virtual address to 30-bit linear address");
}

uint64_t* vaddr_to_29_bit_laddr(uint64_t* vaddr_nid) {
  return new_slice(SID_MEMORY_ADDRESS, vaddr_nid, 31, 3, "map virtual address to 29-bit linear address");
}

uint64_t* vaddr_to_32_bit_laddr(uint64_t* vaddr_nid) {
  return new_slice(SID_MEMORY_ADDRESS, vaddr_nid, 31, 0, "map virtual address to 32-bit linear address");
}

uint64_t* vaddr_to_laddr(uint64_t* vaddr_nid) {
  if (ISBYTEMEMORY)
    return vaddr_to_32_bit_laddr(vaddr_nid);
  else if (IS64BITTARGET)
    return vaddr_to_29_bit_laddr(vaddr_nid);
  else
    return vaddr_to_30_bit_laddr(vaddr_nid);
}

uint64_t* load_machine_word(uint64_t* laddr_nid) {
  // TODO: implement for byte memory
  return new_binary(OP_READ, SID_MACHINE_WORD, state_main_memory_nid, laddr_nid, "load machine word");
}

uint64_t* store_machine_word(uint64_t* laddr_nid, uint64_t* word_nid) {
  // TODO: implement for byte memory
  return new_ternary(OP_WRITE, SID_MEMORY_STATE,
    state_main_memory_nid,
    laddr_nid,
    word_nid,
    "store machine word in memory at laddr");
}

uint64_t* load_byte(uint64_t* vaddr_nid) {
  uint64_t* laddr_nid;
  uint64_t* shift_by_nid;

  laddr_nid = vaddr_to_laddr(vaddr_nid);

  if (ISBYTEMEMORY)
    return new_binary(OP_READ, SID_MEMORY_WORD, state_main_memory_nid, laddr_nid, "load byte");

  shift_by_nid = new_binary(OP_SLL, SID_MACHINE_WORD,
    new_binary(OP_AND, SID_MACHINE_WORD,
      vaddr_nid,
      NID_MACHINE_WORD_SIZE_MASK,
      "reset bits above machine word size"),
    NID_BYTE_SIZE_IN_BASE_BITS,
    "multiply by 8 bits");

  return new_slice(SID_BYTE,
    new_binary(OP_SRL, SID_MACHINE_WORD,
      load_machine_word(laddr_nid),
        shift_by_nid,
        "shift byte to LSBs"),
    7, 0, "slice byte");
}

uint64_t* store_byte(uint64_t* vaddr_nid, uint64_t* byte_nid) {
  uint64_t* laddr_nid;
  uint64_t* shift_by_nid;

  laddr_nid = vaddr_to_laddr(vaddr_nid);

  if (ISBYTEMEMORY)
    return new_ternary(OP_WRITE, SID_MEMORY_STATE,
      state_main_memory_nid,
      laddr_nid,
      byte_nid,
    "store byte in memory at laddr");

  shift_by_nid = new_binary(OP_SLL, SID_MACHINE_WORD,
    new_binary(OP_AND, SID_MACHINE_WORD,
      vaddr_nid,
      NID_MACHINE_WORD_SIZE_MASK,
      "reset bits above machine word size"),
    NID_BYTE_SIZE_IN_BASE_BITS,
    "multiply by 8 bits");

  return store_machine_word(laddr_nid,
    new_binary(OP_AND, SID_MACHINE_WORD,
      new_binary(OP_AND, SID_MACHINE_WORD,
        load_machine_word(laddr_nid),
        new_unary(OP_NOT, SID_MACHINE_WORD,
          new_binary(OP_SLL, SID_MACHINE_WORD,
            NID_MACHINE_WORD_BYTE_MASK,
            shift_by_nid,
            "shift mask to byte location"),
          "negate mask"),
        "reset bits at byte location"),
      new_binary(OP_SLL, SID_MACHINE_WORD,
        new_ext(OP_UEXT, SID_MACHINE_WORD,
          byte_nid,
          WORDSIZEINBITS - 8,
          "unsigned extension of byte to machine word"),
        shift_by_nid,
        "shift byte to byte location"),
      "insert byte at byte location")
    );
}

void fetch_instruction() {
  eval_core_ir_nid = new_binary(OP_READ, SID_INSTRUCTION_WORD,
    state_code_segment_nid, vaddr_to_30_bit_laddr(state_core_pc_nid), "fetch instruction");
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
  return new_slice(SID_12_BIT_IMM, instruction, 31, 20, "get I-immediate");
}

uint64_t* get_instruction_S_imm(uint64_t* instruction) {
  return new_binary(OP_CONCAT, SID_12_BIT_IMM,
    get_instruction_funct7(instruction),
    get_instruction_rd(instruction),
    "get S-immediate");
}

uint64_t* get_instruction_U_imm(uint64_t* instruction) {
  return new_slice(SID_20_BIT_IMM, instruction, 31, 12, "get U-immediate");
}

uint64_t* sign_extend_IS_imm(uint64_t* imm) {
  if (IS64BITTARGET)
    return new_ext(OP_SEXT, SID_MACHINE_WORD, imm, 52, "sign-extend");
  else
    return new_ext(OP_SEXT, SID_MACHINE_WORD, imm, 20, "sign-extend");
}

uint64_t* get_machine_word_I_immediate(uint64_t* instruction) {
  return sign_extend_IS_imm(get_instruction_I_imm(instruction));
}

uint64_t* get_machine_word_S_immediate(uint64_t* instruction) {
  return sign_extend_IS_imm(get_instruction_S_imm(instruction));
}

uint64_t* get_machine_word_U_immediate(uint64_t* instruction) {
  if (IS64BITTARGET)
    return new_ext(OP_SEXT, SID_MACHINE_WORD, get_instruction_U_imm(instruction), 44, "sign-extend");
  else
    return new_ext(OP_SEXT, SID_MACHINE_WORD, get_instruction_U_imm(instruction), 12, "sign-extend");
}

uint64_t* decode_instruction() {
  uint64_t* opcode_nid;
  uint64_t* funct3_nid;
  uint64_t* funct7_nid;

  eval_core_active_ecall_nid = new_binary_boolean(OP_EQ, eval_core_ir_nid, NID_ECALL, "ir == ECALL");

  opcode_nid = get_instruction_opcode(eval_core_ir_nid);
  funct3_nid = get_instruction_funct3(eval_core_ir_nid);

  eval_core_imm_nid     = new_binary_boolean(OP_EQ, opcode_nid, NID_OP_IMM, "opcode == IMM");
  eval_core_f3_addi_nid = new_binary_boolean(OP_EQ, funct3_nid, NID_F3_ADDI, "funct3 == ADDI");

  funct7_nid = get_instruction_funct7(eval_core_ir_nid);

  eval_core_op_nid             = new_binary_boolean(OP_EQ, opcode_nid, NID_OP_OP, "opcode == OP");
  eval_core_f3_add_sub_mul_nid = new_binary_boolean(OP_EQ, funct3_nid, NID_F3_ADD_SUB_MUL, "funct3 == ADD or SUB or MUL");
  eval_core_f7_add_nid         = new_binary_boolean(OP_EQ, funct7_nid, NID_F7_ADD, "funct7 == ADD");

  eval_core_store_nid = new_binary_boolean(OP_EQ, opcode_nid, NID_OP_STORE, "opcode == STORE");
  eval_core_store_nid = new_binary_boolean(OP_EQ, funct3_nid, NID_F3_SB, "funct3 == SB");

  eval_core_branch_nid = new_binary_boolean(OP_EQ, opcode_nid, NID_OP_BRANCH, "opcode == BRANCH");

  eval_core_jal_nid  = new_binary_boolean(OP_EQ, opcode_nid, NID_OP_JAL, "opcode == JAL");
  eval_core_jalr_nid = new_binary_boolean(OP_EQ, opcode_nid, NID_OP_JALR, "opcode == JALR");

  return new_binary_boolean(OP_OR,
    new_binary_boolean(OP_AND,
      eval_core_imm_nid,
      eval_core_f3_addi_nid,
      "addi"),
    new_binary_boolean(OP_OR,
      new_binary_boolean(OP_AND,
        eval_core_op_nid,
        new_binary_boolean(OP_AND,
          eval_core_f3_add_sub_mul_nid,
          eval_core_f7_add_nid,
          "add funct3 and funct7"),
        "add"),
      new_binary_boolean(OP_AND,
        eval_core_store_nid,
        eval_core_f3_sb_nid,
        "sb"),
      ""),
    "known instruction");
}

uint64_t* core_register_data_flow(uint64_t* register_file_nid) {
  uint64_t* rd_nid;
  uint64_t* rd_value_nid;
  uint64_t* rs1_value_nid;
  uint64_t* rs2_value_nid;
  uint64_t* I_immediate;

  uint64_t* no_register_data_flow_nid;

  rd_nid       = get_instruction_rd(eval_core_ir_nid);
  rd_value_nid = get_register_value(rd_nid, "old rd value");

  rs1_value_nid = get_register_value(get_instruction_rs1(eval_core_ir_nid), "rs1 value");
  rs2_value_nid = get_register_value(get_instruction_rs2(eval_core_ir_nid), "rs2 value");

  I_immediate = get_machine_word_I_immediate(eval_core_ir_nid);

  rd_value_nid = new_ternary(OP_ITE, SID_MACHINE_WORD,
    eval_core_imm_nid,
    new_ternary(OP_ITE, SID_MACHINE_WORD,
      eval_core_f3_addi_nid,
      new_binary(OP_ADD, SID_MACHINE_WORD,
        rs1_value_nid,
        I_immediate,
        "rs1 value + immediate"),
      rd_value_nid,
      "addi data flow"),
    new_ternary(OP_ITE, SID_MACHINE_WORD,
      eval_core_op_nid,
      new_ternary(OP_ITE, SID_MACHINE_WORD,
        eval_core_f3_add_sub_mul_nid,
        new_ternary(OP_ITE, SID_MACHINE_WORD,
          eval_core_f7_add_nid,
          new_binary(OP_ADD, SID_MACHINE_WORD,
            rs1_value_nid,
            rs2_value_nid,
            "rs1 value + rs2 value"),
          rd_value_nid,
          "add data flow"),
        rd_value_nid,
        "no data flow"),
      rd_value_nid,
      "no data flow"),
    "data flow");

  no_register_data_flow_nid = new_binary_boolean(OP_OR,
    new_binary_boolean(OP_EQ, rd_nid, NID_ZR, "rd == register zero"),
    new_binary_boolean(OP_OR,
      eval_core_store_nid,
      eval_core_branch_nid,
      "STORE or BRANCH"),
    "rd == zero register or STORE or BRANCH");

  return new_ternary(OP_ITE, SID_REGISTER_STATE,
    no_register_data_flow_nid,
    register_file_nid,
    new_ternary(OP_WRITE, SID_REGISTER_STATE, register_file_nid, rd_nid, rd_value_nid, "write rd"),
    "update non-zero register");
}

uint64_t* core_memory_data_flow(uint64_t* main_memory_nid) {
  return new_ternary(OP_ITE, SID_MEMORY_STATE,
    eval_core_store_nid,
    main_memory_nid,
    main_memory_nid,
    "update main memory");
}

uint64_t* control_flow(uint64_t* pc_nid) {
  uint64_t* register_relative_control_flow_nid;

  register_relative_control_flow_nid = new_binary_boolean(OP_OR,
    eval_core_branch_nid,
    new_binary_boolean(OP_OR,
      eval_core_jal_nid,
      eval_core_jalr_nid,
      "JAL or JALR"),
    "BRANCH or JAL or JALR");

  return new_ternary(OP_ITE, SID_MACHINE_WORD,
    register_relative_control_flow_nid,
    pc_nid,
    new_binary(OP_ADD, SID_MACHINE_WORD, pc_nid, NID_MACHINE_WORD_4, "pc + 4"),
    "pc + 4 if non-control-flow instruction is active");
}

// -----------------------------------------------------------------
// ----------------------------- CORE ------------------------------
// -----------------------------------------------------------------

void new_core_state() {
  state_core_pc_nid = new_input(OP_STATE, SID_MACHINE_WORD, "pc", "program counter");
  init_core_pc_nid  = new_binary(OP_INIT, SID_MACHINE_WORD, state_core_pc_nid, NID_MACHINE_WORD_0, "initial value of pc");
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------ MODEL GENERATOR ------------------------
// -----------------------------------------------------------------

void output_machine() {
  w = w
    + dprintf(output_fd, "; %s\n\n", SELFIE_URL)
    + dprintf(output_fd, "; BTOR2 file %s generated by %s\n\n", model_name, selfie_name);

  print_interface_sorts();
  print_interface_memory();
  print_interface_kernel();

  print_register_sorts();
  print_memory_sorts();

  w = w + dprintf(output_fd, "\n; kernel state\n\n");

  print_line(100, readable_bytes_nid);
  print_line(101, state_readable_bytes_nid);
  print_line(102, init_readable_bytes_nid);

  w = w + dprintf(output_fd, "\n");

  print_line(103, state_read_bytes_nid);
  print_line(104, init_read_bytes_nid);

  w = w + dprintf(output_fd, "\n; register file\n\n");

  print_line(200, state_register_file_nid);
  print_line(201, init_register_file_nid);

  w = w + dprintf(output_fd, "\n; code segment\n\n");

  print_line(300, state_code_segment_nid);

  w = w + dprintf(output_fd, "\n; main memory\n\n");

  print_line(400, state_main_memory_nid);
  print_line(401, init_main_memory_nid);

  w = w + dprintf(output_fd, "\n; program counter\n\n");

  print_line(1000, state_core_pc_nid);
  print_line(1001, init_core_pc_nid);

  w = w + dprintf(output_fd, "\n; non-kernel control flow\n\n");

  print_line(2000, eval_core_pc_nid);

  w = w + dprintf(output_fd, "\n; update kernel state\n\n");

  print_line(3000, next_readable_bytes_nid);

  w = w + dprintf(output_fd, "\n");

  print_line(3100, next_read_bytes_nid);

  w = w + dprintf(output_fd, "\n; kernel control flow\n\n");

  print_line(3200, eval_kernel_pc_nid);

  w = w + dprintf(output_fd, "\n; update program counter\n\n");

  print_line(4000, next_core_pc_nid);

  w = w + dprintf(output_fd, "\n; non-kernel register data flow\n\n");

  print_line(5000, eval_core_register_data_flow_nid);

  w = w + dprintf(output_fd, "\n; kernel register data flow\n\n");

  print_line(6000, eval_kernel_register_data_flow_nid);

  w = w + dprintf(output_fd, "\n; update register data flow\n\n");

  print_line(7000, next_register_file_nid);

  w = w + dprintf(output_fd, "\n; non-kernel memory data flow\n\n");

  print_line(8000, eval_core_memory_data_flow_nid);

  w = w + dprintf(output_fd, "\n; kernel memory data flow\n\n");

  print_line(9000, eval_kernel_memory_data_flow_nid);

  w = w + dprintf(output_fd, "\n; update memory data flow\n\n");

  print_line(10000, next_main_memory_nid);

  w = w + dprintf(output_fd, "\n; constraints\n\n");

  print_line(11000, constraint_ir_nid);

  w = w + dprintf(output_fd, "\n; bad states\n\n");

  //print_line(12000, bad_pc_nid);

  w = w + dprintf(output_fd, "\n");

  //print_line(12100, bad_read_nid);

  w = w + dprintf(output_fd, "\n");

  //print_line(12200, bad_syscall_id_nid);

  w = w + dprintf(output_fd, "\n");

  print_line(12300, bad_exit_nid);
}

void rotor() {
  uint64_t* known_instruction_nid;

  uint64_t* a7_value_nid;

  uint64_t* read_syscall_nid;
  uint64_t* active_read_nid;

  uint64_t* exit_syscall_nid;
  uint64_t* active_exit_nid;

  uint64_t* a2_value_nid;

  uint64_t* more_bytes_to_read_nid;
  uint64_t* more_readable_bytes_nid;
  uint64_t* more_readable_bytes_to_read_nid;

  uint64_t* incremented_read_bytes_nid;
  uint64_t* more_than_one_byte_to_read_nid;
  uint64_t* more_than_one_readable_byte_nid;
  uint64_t* more_than_one_readable_byte_to_read_nid;

  uint64_t* pending_read_nid;
  uint64_t* kernel_mode_nid;

  uint64_t* a0_value_nid;

  uint64_t* read_return_value_nid;
  uint64_t* kernel_data_flow_nid;

  uint64_t* a1_value_nid;

  new_kernel_state(1);
  new_register_file_state();
  new_main_memory_state();
  new_core_state();

  // fetch

  fetch_instruction();

  // decode

  known_instruction_nid = decode_instruction();

  // non-kernel control flow

  eval_core_pc_nid = control_flow(state_core_pc_nid);

  // system call ABI control flow

  a7_value_nid = get_register_value(NID_A7, "a7 value");

  read_syscall_nid = new_binary_boolean(OP_EQ, a7_value_nid, NID_READ_SYSCALL_ID, "a7 == read syscall ID");
  active_read_nid  = new_binary_boolean(OP_AND, eval_core_active_ecall_nid, read_syscall_nid, "active read system call");

  exit_syscall_nid = new_binary_boolean(OP_EQ, a7_value_nid, NID_EXIT_SYSCALL_ID, "a7 == exit syscall ID");
  active_exit_nid  = new_binary_boolean(OP_AND, eval_core_active_ecall_nid, exit_syscall_nid, "active exit system call");

  // system call ABI data flow

  a2_value_nid = get_register_value(NID_A2, "a2 value");

  // update kernel state

  more_bytes_to_read_nid =
    new_binary_boolean(OP_ULT,
      state_read_bytes_nid,
      a2_value_nid,
      "more bytes to read as requested in a2");

  more_readable_bytes_nid =
    new_binary_boolean(OP_UGT,
      state_readable_bytes_nid,
      NID_MACHINE_WORD_0,
      "more readable bytes");

  more_readable_bytes_to_read_nid =
    new_binary_boolean(OP_AND,
      more_bytes_to_read_nid,
      more_readable_bytes_nid,
      "can and still would like to read more bytes"),

  next_readable_bytes_nid =
    new_binary(OP_NEXT, SID_MACHINE_WORD, state_readable_bytes_nid,
      new_ternary(OP_ITE, SID_MACHINE_WORD,
        new_binary_boolean(OP_AND,
          active_read_nid,
          more_readable_bytes_to_read_nid,
          "still reading system call"),
        new_unary(OP_DEC, SID_MACHINE_WORD,
          state_readable_bytes_nid,
          "decrement readable bytes"),
        state_readable_bytes_nid,
        "decrement readable bytes if system call is still reading"),
      "readable bytes");

  incremented_read_bytes_nid =
    new_unary(OP_INC,
      SID_MACHINE_WORD,
      state_read_bytes_nid,
      "increment bytes already read by read system call");

  more_than_one_byte_to_read_nid =
    new_binary_boolean(OP_ULT,
      incremented_read_bytes_nid,
      a2_value_nid,
      "more than one byte to read as requested in a2");

  more_than_one_readable_byte_nid =
    new_binary_boolean(OP_UGT,
      state_readable_bytes_nid,
      NID_MACHINE_WORD_1,
      "more than one readable byte");

  more_than_one_readable_byte_to_read_nid =
    new_binary_boolean(OP_AND,
      more_than_one_byte_to_read_nid,
      more_than_one_readable_byte_nid,
      "can and still would like to read more than one byte");

  next_read_bytes_nid =
    new_binary(OP_NEXT, SID_MACHINE_WORD, state_read_bytes_nid,
      new_ternary(OP_ITE, SID_MACHINE_WORD,
        new_binary_boolean(OP_AND,
          active_read_nid,
          more_than_one_readable_byte_to_read_nid,
          "active read system call"),
        incremented_read_bytes_nid,
        NID_MACHINE_WORD_0,
        "increment bytes already read if read system call is active"),
      "bytes already read in active read system call");

  // kernel control flow

  pending_read_nid =
    new_binary_boolean(OP_AND,
      read_syscall_nid,
      more_than_one_readable_byte_to_read_nid,
      "pending read system call");

  kernel_mode_nid = new_binary_boolean(OP_AND,
    eval_core_active_ecall_nid,
    new_binary_boolean(OP_OR, pending_read_nid, exit_syscall_nid, "pending read or exit system call"),
    "active system call");

  // control flow

  eval_kernel_pc_nid = new_ternary(OP_ITE, SID_MACHINE_WORD,
    kernel_mode_nid,
    state_core_pc_nid,
    eval_core_pc_nid,
    "update program counter unless in kernel mode");

  // update control flow

  next_core_pc_nid = new_binary(OP_NEXT, SID_MACHINE_WORD,
    state_core_pc_nid,
    eval_kernel_pc_nid,
    "program counter");

  // non-kernel register data flow

  eval_core_register_data_flow_nid = core_register_data_flow(state_register_file_nid);

  // system call ABI data flow

  a0_value_nid = get_register_value(NID_A0, "a0 value");

  // kernel register data flow

  read_return_value_nid = new_ternary(OP_ITE, SID_MACHINE_WORD,
    new_binary_boolean(OP_UGT,
      a2_value_nid,
      NID_MACHINE_WORD_0,
      "more than 0 bytes to read"),
    new_ternary(OP_ITE, SID_MACHINE_WORD,
      more_readable_bytes_nid,
      new_ternary(OP_ITE, SID_MACHINE_WORD,
        more_than_one_byte_to_read_nid,
        new_ternary(OP_ITE, SID_MACHINE_WORD,
          more_than_one_readable_byte_nid,
          a0_value_nid,
          incremented_read_bytes_nid,
          "return number of bytes read so far + 1 if there is only one more readable byte"),
        a2_value_nid,
        "return a2 if number of bytes read so far is a2 - 1 and there are still readable bytes"),
      NID_MACHINE_WORD_MINUS_1,
      "return -1 if a2 > 0 and there are no readable bytes when starting to read"),
    NID_MACHINE_WORD_0,
    "return 0 if a2 == 0");

  // TODO: kernel_data_flow_nid == active_read_nid

  kernel_data_flow_nid = new_binary_boolean(OP_AND,
    eval_core_active_ecall_nid,
    read_syscall_nid,
    "active system call with data flow");

  eval_kernel_register_data_flow_nid = new_ternary(OP_ITE, SID_REGISTER_STATE,
    new_binary_boolean(OP_AND,
      kernel_data_flow_nid,
      new_unary(OP_NOT, SID_BOOLEAN,
        more_than_one_readable_byte_to_read_nid,
        "read system call returns if there is at most one more byte to read"),
      "update a0 when read system call returns"),
    new_ternary(OP_WRITE, SID_REGISTER_STATE, state_register_file_nid, NID_A0, read_return_value_nid, "write a0"),
    eval_core_register_data_flow_nid,
    "register data flow");

  // update register data flow

  next_register_file_nid = new_binary(OP_NEXT, SID_REGISTER_STATE,
    state_register_file_nid,
    eval_kernel_register_data_flow_nid,
    "register file");

  // non-kernel memory data flow

  eval_core_memory_data_flow_nid = core_memory_data_flow(state_main_memory_nid);

  // system call ABI data flow

  a1_value_nid = get_register_value(NID_A1, "a1 value");

  // kernel memory data flow

  eval_kernel_memory_data_flow_nid = new_ternary(OP_ITE, SID_MEMORY_STATE,
    new_binary_boolean(OP_AND,
      read_syscall_nid,
      more_readable_bytes_to_read_nid,
      "more input bytes to read"),
    store_byte(new_binary(OP_ADD, SID_MACHINE_WORD,
      a1_value_nid,
      state_read_bytes_nid,
      "a1 + number of already read_bytes"),
      new_input(OP_INPUT, SID_BYTE, "read-input-byte", "input byte by read system call")),
    eval_core_memory_data_flow_nid,
    "main memory data flow");

  // update memory data flow

  next_main_memory_nid = new_binary(OP_NEXT, SID_MEMORY_STATE,
    state_main_memory_nid,
    eval_kernel_memory_data_flow_nid,
    "main memory");

  // constraints

  constraint_ir_nid = new_property(OP_CONSTRAINT,
    new_binary_boolean(OP_OR,
      eval_core_active_ecall_nid,
      known_instruction_nid,
      "ecall or known instruction"),
    "known-instructions", "known instructions");

  // bad states

  bad_pc_nid = new_property(OP_BAD,
    new_unary(OP_NOT, SID_BOOLEAN,
      is_access_in_code_segment(eval_kernel_pc_nid),
      "next pc not in code segment"),
    "b0", "imminent fetch segmentation fault");

  bad_read_nid = new_property(OP_BAD,
    new_binary_boolean(OP_AND,
      active_read_nid,
      is_range_accessing_code_segment(a1_value_nid, a2_value_nid),
      "active read system call reading into code segment"),
    "b1", "possible read segmentation fault");

  bad_syscall_id_nid = new_property(OP_BAD,
    new_binary_boolean(OP_AND,
      eval_core_active_ecall_nid,
      new_binary_boolean(OP_AND,
        new_binary_boolean(OP_NEQ, a7_value_nid, NID_EXIT_SYSCALL_ID, "a7 != exit syscall ID"),
        new_binary_boolean(OP_NEQ, a7_value_nid, NID_READ_SYSCALL_ID, "a7 != read syscall ID"),
        "a7 != known syscall ID"),
      "active ecall and a7 != known syscall ID"),
    "b2", "unknown syscall ID");

  bad_exit_nid = new_property(OP_BAD,
    new_binary_boolean(OP_AND,
      active_exit_nid,
      new_binary_boolean(OP_EQ,
        a0_value_nid,
        new_constant(OP_CONSTD, SID_MACHINE_WORD,
          format_decimal(bad_exit_code),
          format_comment("bad exit code %ld", bad_exit_code)),
        "actual exit code == bad exit code"),
      "active exit system call with bad exit code"),
    "b3", format_comment("exit(%ld)", bad_exit_code));

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

      code_start = 0;
      code_size  = 16;

      init_model();

      init_interface_sorts();
      init_interface_memory();
      init_interface_kernel();

      init_register_file_sorts();
      init_memory_sorts();
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