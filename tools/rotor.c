/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

Rotor is a tool for bit-precise reasoning about RISC-V machines
using BTOR2 as intermediate modeling format.
*/

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------------     M O D E L     -----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t* allocate_line() {
  return smalloc(5 * sizeof(uint64_t*) + 2 * sizeof(char*) + 4 * sizeof(uint64_t));
}

uint64_t  get_nid(uint64_t* line)     { return *line; }
char*     get_op(uint64_t* line)      { return (char*)     *(line + 1); }
uint64_t* get_sid(uint64_t* line)     { return (uint64_t*) *(line + 2); }
uint64_t* get_arg1(uint64_t* line)    { return (uint64_t*) *(line + 3); }
uint64_t* get_arg2(uint64_t* line)    { return (uint64_t*) *(line + 4); }
uint64_t* get_arg3(uint64_t* line)    { return (uint64_t*) *(line + 5); }
char*     get_comment(uint64_t* line) { return (char*)     *(line + 6); }
uint64_t  get_state(uint64_t* line)   { return *(line + 7); }
uint64_t  get_step(uint64_t* line)    { return *(line + 8); }
uint64_t  get_reuse(uint64_t* line)   { return *(line + 9); }
uint64_t* get_pred(uint64_t* line)    { return (uint64_t*) *(line + 10); }

void set_nid(uint64_t* line, uint64_t nid)      { *line        = nid; }
void set_op(uint64_t* line, char* op)           { *(line + 1)  = (uint64_t) op; }
void set_sid(uint64_t* line, uint64_t* sid)     { *(line + 2)  = (uint64_t) sid; }
void set_arg1(uint64_t* line, uint64_t* arg1)   { *(line + 3)  = (uint64_t) arg1; }
void set_arg2(uint64_t* line, uint64_t* arg2)   { *(line + 4)  = (uint64_t) arg2; }
void set_arg3(uint64_t* line, uint64_t* arg3)   { *(line + 5)  = (uint64_t) arg3; }
void set_comment(uint64_t* line, char* comment) { *(line + 6)  = (uint64_t) comment; }
void set_state(uint64_t* line, uint64_t state)  { *(line + 7)  = state; }
void set_step(uint64_t* line, uint64_t step)    { *(line + 8)  = step; }
void set_reuse(uint64_t* line, uint64_t reuse)  { *(line + 9)  = reuse; }
void set_pred(uint64_t* line, uint64_t* pred)   { *(line + 10) = (uint64_t) pred; }

uint64_t  are_lines_equal(uint64_t* left_line, uint64_t* right_line);
uint64_t* find_equal_line(uint64_t* line);

uint64_t* new_line(char* op, uint64_t* sid, uint64_t* arg1, uint64_t* arg2, uint64_t* arg3, char* comment);

uint64_t* new_bitvec(uint64_t size_in_bits, char* comment);
uint64_t* new_array(uint64_t* size_sid, uint64_t* element_sid, char* comment);

uint64_t* new_constant(char* op, uint64_t* sid, uint64_t constant, uint64_t digits, char* comment);
uint64_t* new_input(char* op, uint64_t* sid, char* symbol, char* comment);

uint64_t* new_ext(char* op, uint64_t* sid, uint64_t* value_nid, uint64_t w, char* comment);
uint64_t* new_slice(uint64_t* sid, uint64_t* value_nid, uint64_t u, uint64_t l, char* comment);

uint64_t* new_unary(char* op, uint64_t* sid, uint64_t* value_nid, char* comment);
uint64_t* new_unary_boolean(char* op, uint64_t* value_nid, char* comment);
uint64_t* new_binary(char* op, uint64_t* sid, uint64_t* left_nid, uint64_t* right_nid, char* comment);
uint64_t* new_binary_boolean(char* op, uint64_t* left_nid, uint64_t* right_nid, char* comment);
uint64_t* new_ternary(char* op, uint64_t* sid, uint64_t* first_nid, uint64_t* second_nid, uint64_t* third_nid, char* comment);

uint64_t* new_property(char* op, uint64_t* condition_nid, char* symbol, char* comment);

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
char* OP_NEG = (char*) 0;

char* OP_EQ   = (char*) 0;
char* OP_NEQ  = (char*) 0;
char* OP_SGT  = (char*) 0;
char* OP_UGT  = (char*) 0;
char* OP_SGTE = (char*) 0;
char* OP_UGTE = (char*) 0;
char* OP_SLT  = (char*) 0;
char* OP_ULT  = (char*) 0;
char* OP_SLTE = (char*) 0;
char* OP_ULTE = (char*) 0;

char* OP_AND = (char*) 0;
char* OP_OR  = (char*) 0;
char* OP_XOR = (char*) 0;

char* OP_SLL = (char*) 0;
char* OP_SRL = (char*) 0;
char* OP_SRA = (char*) 0;

char* OP_ADD  = (char*) 0;
char* OP_SUB  = (char*) 0;
char* OP_MUL  = (char*) 0;
char* OP_SDIV = (char*) 0;
char* OP_UDIV = (char*) 0;
char* OP_SREM = (char*) 0;
char* OP_UREM = (char*) 0;

char* OP_CONCAT = (char*) 0;
char* OP_READ   = (char*) 0;

char* OP_ITE   = (char*) 0;
char* OP_WRITE = (char*) 0;

char* OP_BAD        = (char*) 0;
char* OP_CONSTRAINT = (char*) 0;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t reuse_lines = 1; // flag for reusing lines

uint64_t* last_line   = (uint64_t*) 0;
uint64_t* unused_line = (uint64_t*) 0;

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
  OP_NEG = "neg";

  OP_EQ   = "eq";
  OP_NEQ  = "neq";
  OP_SGT  = "sgt";
  OP_UGT  = "ugt";
  OP_SGTE = "sgte";
  OP_UGTE = "ugte";
  OP_SLT  = "slt";
  OP_ULT  = "ult";
  OP_SLTE = "slte";
  OP_ULTE = "ulte";

  OP_AND = "and";
  OP_OR  = "or";
  OP_XOR = "xor";

  OP_SLL = "sll";
  OP_SRL = "srl";
  OP_SRA = "sra";

  OP_ADD  = "add";
  OP_SUB  = "sub";
  OP_MUL  = "mul";
  OP_SDIV = "sdiv";
  OP_UDIV = "udiv";
  OP_SREM = "srem";
  OP_UREM = "urem";

  OP_CONCAT = "concat";
  OP_READ   = "read";

  OP_ITE   = "ite";
  OP_WRITE = "write";

  OP_BAD        = "bad";
  OP_CONSTRAINT = "constraint";
}

// -----------------------------------------------------------------
// ---------------------------- SYNTAX -----------------------------
// -----------------------------------------------------------------

void print_nid(uint64_t nid, uint64_t* line);

uint64_t print_sort(uint64_t nid, uint64_t* line);
uint64_t print_constant(uint64_t nid, uint64_t* line);
uint64_t print_input(uint64_t nid, uint64_t* line);

uint64_t print_ext(uint64_t nid, uint64_t* line);
uint64_t print_slice(uint64_t nid, uint64_t* line);

uint64_t print_unary_op(uint64_t nid, uint64_t* line);
uint64_t print_binary_op(uint64_t nid, uint64_t* line);
uint64_t print_ternary_op(uint64_t nid, uint64_t* line);

uint64_t print_constraint(uint64_t nid, uint64_t* line);

void print_comment(uint64_t* line);

uint64_t is_constant_op(char* op);
uint64_t is_input_op(char* op);
uint64_t is_unary_op(char* op);

uint64_t print_referenced_line(uint64_t nid, uint64_t* line);

void print_line(uint64_t* line);

void print_break();
void print_break_line(uint64_t* line);
void print_break_comment(char* comment);
void print_break_comment_line(char* comment, uint64_t* line);

void print_aligned_break_comment(char* comment, uint64_t alignment);

char* format_comment(char* comment, uint64_t value);

char* format_binary(uint64_t value, uint64_t alignment);
char* format_decimal(uint64_t value);
char* format_hexadecimal(uint64_t value);

char* format_comment_binary(char* comment, uint64_t value);

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t current_nid = 1; // first nid is 1

// -----------------------------------------------------------------
// -------------------------- SEMANTICS ----------------------------
// -----------------------------------------------------------------

uint64_t eval_bitvec_size(uint64_t* line);

void fit_bitvec_sort(uint64_t value, uint64_t* sid);
void signed_fit_bitvec_sort(uint64_t value, uint64_t* sid);

uint64_t eval_array_size(uint64_t* line);
uint64_t eval_array_element_size(uint64_t* line);

void fit_array_sort(uint64_t index, uint64_t value, uint64_t* sid);

void match_sorts(uint64_t* sid1, uint64_t* sid2, char* comment);

void write_value(uint64_t index, uint64_t value, uint64_t* array_nid);

uint64_t eval_constant_value(uint64_t* line);
uint64_t eval_constant_digits(uint64_t* line);

uint64_t eval_ext_w(uint64_t* line);

uint64_t eval_slice_u(uint64_t* line);
uint64_t eval_slice_l(uint64_t* line);

uint64_t get_cached_state(uint64_t* line);

uint64_t eval_input(uint64_t* line);
uint64_t eval_ext(uint64_t* line);
uint64_t eval_slice(uint64_t* line);
uint64_t eval_unary_op(uint64_t* line);
uint64_t eval_write(uint64_t* line);
uint64_t eval_binary_op(uint64_t* line);

uint64_t eval_line(uint64_t* line);

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t current_step = 0; // first step in evaluation is 0

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
uint64_t* NID_BYTE_3 = (uint64_t*) 0;

uint64_t HALFWORDSIZEINBITS = 16;

uint64_t* SID_HALF_WORD = (uint64_t*) 0;

uint64_t* NID_HALF_WORD_0 = (uint64_t*) 0;
uint64_t* NID_HALF_WORD_1 = (uint64_t*) 0;

uint64_t* SID_SINGLE_WORD = (uint64_t*) 0;

uint64_t* NID_SINGLE_WORD_0 = (uint64_t*) 0;
uint64_t* NID_SINGLE_WORD_1 = (uint64_t*) 0;
uint64_t* NID_SINGLE_WORD_2 = (uint64_t*) 0;
uint64_t* NID_SINGLE_WORD_3 = (uint64_t*) 0;
uint64_t* NID_SINGLE_WORD_4 = (uint64_t*) 0;
uint64_t* NID_SINGLE_WORD_5 = (uint64_t*) 0;
uint64_t* NID_SINGLE_WORD_6 = (uint64_t*) 0;
uint64_t* NID_SINGLE_WORD_7 = (uint64_t*) 0;
uint64_t* NID_SINGLE_WORD_8 = (uint64_t*) 0;

uint64_t* NID_SINGLE_WORD_MINUS_1 = (uint64_t*) 0;
uint64_t* NID_SINGLE_WORD_INT_MIN = (uint64_t*) 0;

uint64_t DOUBLEWORDSIZE       = 8;
uint64_t DOUBLEWORDSIZEINBITS = 64;

uint64_t* SID_DOUBLE_WORD = (uint64_t*) 0;

uint64_t* NID_DOUBLE_WORD_0 = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_1 = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_2 = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_3 = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_4 = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_5 = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_6 = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_7 = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_8 = (uint64_t*) 0;

uint64_t* NID_DOUBLE_WORD_MINUS_1 = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_INT_MIN = (uint64_t*) 0;

uint64_t* SID_MACHINE_WORD = (uint64_t*) 0;

uint64_t* NID_MACHINE_WORD_0 = (uint64_t*) 0;
uint64_t* NID_MACHINE_WORD_1 = (uint64_t*) 0;
uint64_t* NID_MACHINE_WORD_2 = (uint64_t*) 0;
uint64_t* NID_MACHINE_WORD_3 = (uint64_t*) 0;
uint64_t* NID_MACHINE_WORD_4 = (uint64_t*) 0;
uint64_t* NID_MACHINE_WORD_5 = (uint64_t*) 0;
uint64_t* NID_MACHINE_WORD_6 = (uint64_t*) 0;
uint64_t* NID_MACHINE_WORD_7 = (uint64_t*) 0;
uint64_t* NID_MACHINE_WORD_8 = (uint64_t*) 0;

uint64_t* NID_MACHINE_WORD_MINUS_1 = (uint64_t*) 0;
uint64_t* NID_MACHINE_WORD_INT_MIN = (uint64_t*) 0;

uint64_t* NID_LSB_MASK = (uint64_t*) 0;

uint64_t* SID_DOUBLE_MACHINE_WORD = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_interface_sorts() {
  SID_BOOLEAN = new_bitvec(1, "Boolean");

  NID_FALSE = new_constant(OP_CONSTD, SID_BOOLEAN, 0, 0, "false");
  NID_TRUE  = new_constant(OP_CONSTD, SID_BOOLEAN, 1, 0, "true");

  SID_BYTE = new_bitvec(8, "8-bit byte");

  NID_BYTE_0 = new_constant(OP_CONSTD, SID_BYTE, 0, 0, "byte 0");
  NID_BYTE_3 = new_constant(OP_CONSTD, SID_BYTE, 3, 0, "byte 3");

  SID_HALF_WORD = new_bitvec(HALFWORDSIZEINBITS, "16-bit half word");

  NID_HALF_WORD_0 = new_constant(OP_CONSTD, SID_HALF_WORD, 0, 0, "half word 0");
  NID_HALF_WORD_1 = new_constant(OP_CONSTD, SID_HALF_WORD, 1, 0, "half word 1");

  SID_SINGLE_WORD = new_bitvec(SINGLEWORDSIZEINBITS, "32-bit single word");

  NID_SINGLE_WORD_0 = new_constant(OP_CONSTD, SID_SINGLE_WORD, 0, 0, "single-word 0");
  NID_SINGLE_WORD_1 = new_constant(OP_CONSTD, SID_SINGLE_WORD, 1, 0, "single-word 1");
  NID_SINGLE_WORD_2 = new_constant(OP_CONSTD, SID_SINGLE_WORD, 2, 0, "single-word 2");
  NID_SINGLE_WORD_3 = new_constant(OP_CONSTD, SID_SINGLE_WORD, 3, 0, "single-word 3");
  NID_SINGLE_WORD_4 = new_constant(OP_CONSTD, SID_SINGLE_WORD, 4, 0, "single-word 4");
  NID_SINGLE_WORD_5 = new_constant(OP_CONSTD, SID_SINGLE_WORD, 5, 0, "single-word 5");
  NID_SINGLE_WORD_6 = new_constant(OP_CONSTD, SID_SINGLE_WORD, 6, 0, "single-word 6");
  NID_SINGLE_WORD_7 = new_constant(OP_CONSTD, SID_SINGLE_WORD, 7, 0, "single-word 7");
  NID_SINGLE_WORD_8 = new_constant(OP_CONSTD, SID_SINGLE_WORD, 8, 0, "single-word 8");

  NID_SINGLE_WORD_MINUS_1 = new_constant(OP_CONSTD, SID_SINGLE_WORD, -1, 0, "single-word -1");
  NID_SINGLE_WORD_INT_MIN = new_constant(OP_CONSTH, SID_SINGLE_WORD, two_to_the_power_of(SINGLEWORDSIZEINBITS - 1), 0, "single-word INT_MIN");

  SID_DOUBLE_WORD = new_bitvec(DOUBLEWORDSIZEINBITS, "64-bit double word");

  NID_DOUBLE_WORD_0 = new_constant(OP_CONSTD, SID_DOUBLE_WORD, 0, 0, "double-word 0");
  NID_DOUBLE_WORD_1 = new_constant(OP_CONSTD, SID_DOUBLE_WORD, 1, 0, "double-word 1");
  NID_DOUBLE_WORD_2 = new_constant(OP_CONSTD, SID_DOUBLE_WORD, 2, 0, "double-word 2");
  NID_DOUBLE_WORD_3 = new_constant(OP_CONSTD, SID_DOUBLE_WORD, 3, 0, "double-word 3");
  NID_DOUBLE_WORD_4 = new_constant(OP_CONSTD, SID_DOUBLE_WORD, 4, 0, "double-word 4");
  NID_DOUBLE_WORD_5 = new_constant(OP_CONSTD, SID_DOUBLE_WORD, 5, 0, "double-word 5");
  NID_DOUBLE_WORD_6 = new_constant(OP_CONSTD, SID_DOUBLE_WORD, 6, 0, "double-word 6");
  NID_DOUBLE_WORD_7 = new_constant(OP_CONSTD, SID_DOUBLE_WORD, 7, 0, "double-word 7");
  NID_DOUBLE_WORD_8 = new_constant(OP_CONSTD, SID_DOUBLE_WORD, 8, 0, "double-word 8");

  NID_DOUBLE_WORD_MINUS_1 = new_constant(OP_CONSTD, SID_DOUBLE_WORD, -1, 0, "double-word -1");

  if (IS64BITTARGET) {
    NID_DOUBLE_WORD_INT_MIN = new_constant(OP_CONSTH, SID_DOUBLE_WORD, two_to_the_power_of(DOUBLEWORDSIZEINBITS - 1), 0, "double-word INT_MIN");

    SID_MACHINE_WORD = SID_DOUBLE_WORD;

    NID_MACHINE_WORD_0 = NID_DOUBLE_WORD_0;
    NID_MACHINE_WORD_1 = NID_DOUBLE_WORD_1;
    NID_MACHINE_WORD_2 = NID_DOUBLE_WORD_2;
    NID_MACHINE_WORD_3 = NID_DOUBLE_WORD_3;
    NID_MACHINE_WORD_4 = NID_DOUBLE_WORD_4;
    NID_MACHINE_WORD_5 = NID_DOUBLE_WORD_5;
    NID_MACHINE_WORD_6 = NID_DOUBLE_WORD_6;
    NID_MACHINE_WORD_7 = NID_DOUBLE_WORD_7;
    NID_MACHINE_WORD_8 = NID_DOUBLE_WORD_8;

    NID_MACHINE_WORD_MINUS_1 = NID_DOUBLE_WORD_MINUS_1;
    NID_MACHINE_WORD_INT_MIN = NID_DOUBLE_WORD_INT_MIN;
  } else {
    // assert: 32-bit system
    SID_MACHINE_WORD = SID_SINGLE_WORD;

    NID_MACHINE_WORD_0 = NID_SINGLE_WORD_0;
    NID_MACHINE_WORD_1 = NID_SINGLE_WORD_1;
    NID_MACHINE_WORD_2 = NID_SINGLE_WORD_2;
    NID_MACHINE_WORD_3 = NID_SINGLE_WORD_3;
    NID_MACHINE_WORD_4 = NID_SINGLE_WORD_4;
    NID_MACHINE_WORD_5 = NID_SINGLE_WORD_5;
    NID_MACHINE_WORD_6 = NID_SINGLE_WORD_6;
    NID_MACHINE_WORD_7 = NID_SINGLE_WORD_7;
    NID_MACHINE_WORD_8 = NID_SINGLE_WORD_8;

    NID_MACHINE_WORD_MINUS_1 = NID_SINGLE_WORD_MINUS_1;
    NID_MACHINE_WORD_INT_MIN = NID_SINGLE_WORD_INT_MIN;
  }

  NID_LSB_MASK = new_constant(OP_CONSTD, SID_MACHINE_WORD, -2, 0, "all bits but LSB set");

  SID_DOUBLE_MACHINE_WORD = new_bitvec(2 * WORDSIZEINBITS, "double machine word");
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

void print_interface_kernel();

void new_kernel_state(uint64_t core, uint64_t bytes_to_read);
void print_kernel_state(uint64_t core);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t* NID_MAX_STRING_LENGTH = (uint64_t*) 0;

uint64_t* NID_EXIT_SYSCALL_ID   = (uint64_t*) 0;
uint64_t* NID_BRK_SYSCALL_ID    = (uint64_t*) 0;
uint64_t* NID_OPENAT_SYSCALL_ID = (uint64_t*) 0;
uint64_t* NID_READ_SYSCALL_ID   = (uint64_t*) 0;
uint64_t* NID_WRITE_SYSCALL_ID  = (uint64_t*) 0;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* state_program_break_nid = (uint64_t*) 0;
uint64_t* init_program_break_nid  = (uint64_t*) 0;
uint64_t* eval_program_break_nid  = (uint64_t*) 0;
uint64_t* next_program_break_nid  = (uint64_t*) 0;

uint64_t* state_file_descriptor_nid = (uint64_t*) 0;
uint64_t* init_file_descriptor_nid  = (uint64_t*) 0;
uint64_t* eval_file_descriptor_nid  = (uint64_t*) 0;
uint64_t* next_file_descriptor_nid  = (uint64_t*) 0;

uint64_t* param_readable_bytes_nid = (uint64_t*) 0;

uint64_t* state_readable_bytes_nid = (uint64_t*) 0;
uint64_t* init_readable_bytes_nid  = (uint64_t*) 0;
uint64_t* next_readable_bytes_nid  = (uint64_t*) 0;

uint64_t* eval_still_reading_active_read_nid = (uint64_t*) 0;

uint64_t* state_read_bytes_nid = (uint64_t*) 0;
uint64_t* init_read_bytes_nid  = (uint64_t*) 0;
uint64_t* next_read_bytes_nid  = (uint64_t*) 0;

uint64_t* eval_more_than_one_readable_byte_to_read_nid = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_interface_kernel() {
  NID_MAX_STRING_LENGTH = new_constant(OP_CONSTD, SID_MACHINE_WORD,
    MAX_STRING_LENGTH, 0, "maximum string length");

  NID_EXIT_SYSCALL_ID = new_constant(OP_CONSTD, SID_MACHINE_WORD,
    SYSCALL_EXIT, 0,
    format_comment_binary("exit syscall ID", SYSCALL_EXIT));
  NID_BRK_SYSCALL_ID = new_constant(OP_CONSTD, SID_MACHINE_WORD,
    SYSCALL_BRK, 0,
    format_comment_binary("brk syscall ID", SYSCALL_BRK));
  NID_OPENAT_SYSCALL_ID = new_constant(OP_CONSTD, SID_MACHINE_WORD,
    SYSCALL_OPENAT, 0,
    format_comment_binary("openat syscall ID", SYSCALL_OPENAT));
  NID_READ_SYSCALL_ID = new_constant(OP_CONSTD, SID_MACHINE_WORD,
    SYSCALL_READ, 0,
    format_comment_binary("read syscall ID", SYSCALL_READ));
  NID_WRITE_SYSCALL_ID = new_constant(OP_CONSTD, SID_MACHINE_WORD,
    SYSCALL_WRITE, 0,
    format_comment_binary("write syscall ID", SYSCALL_WRITE));
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

uint64_t* load_register_value(uint64_t* reg_nid, char* comment, uint64_t* register_file_nid);
uint64_t* store_register_value(uint64_t* reg_nid, uint64_t* value_nid, char* comment, uint64_t* register_file_nid);

uint64_t* get_5_bit_shamt(uint64_t* value_nid);
uint64_t* get_shamt(uint64_t* value_nid);

void new_register_file_state(uint64_t core);
void print_register_file_state(uint64_t core);

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

uint64_t SYNCHRONIZED_REGISTERS = 0; // flag for synchronized registers across cores
uint64_t SHARED_REGISTERS       = 0; // flag for shared registers across cores

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* init_zeroed_register_file_nid = (uint64_t*) 0;
uint64_t* next_zeroed_register_file_nid = (uint64_t*) 0;

uint64_t* initial_register_file_nid = (uint64_t*) 0;

uint64_t* state_register_file_nid = (uint64_t*) 0;
uint64_t* init_register_file_nid  = (uint64_t*) 0;
uint64_t* next_register_file_nid  = (uint64_t*) 0;

uint64_t* eval_core_0_register_data_flow_nid  = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_register_file_sorts() {
  SID_REGISTER_ADDRESS = new_bitvec(5, "5-bit register address");

  NID_ZR  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_ZR, 5, (char*) *(REGISTERS + REG_ZR));
  NID_RA  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_RA, 5, (char*) *(REGISTERS + REG_RA));
  NID_SP  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_SP, 5, (char*) *(REGISTERS + REG_SP));
  NID_GP  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_GP, 5, (char*) *(REGISTERS + REG_GP));
  NID_TP  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_TP, 5, (char*) *(REGISTERS + REG_TP));
  NID_T0  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_T0, 5, (char*) *(REGISTERS + REG_T0));
  NID_T1  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_T1, 5, (char*) *(REGISTERS + REG_T1));
  NID_T2  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_T2, 5, (char*) *(REGISTERS + REG_T2));
  NID_S0  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_S0, 5, (char*) *(REGISTERS + REG_S0));
  NID_S1  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_S1, 5, (char*) *(REGISTERS + REG_S1));
  NID_A0  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_A0, 5, (char*) *(REGISTERS + REG_A0));
  NID_A1  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_A1, 5, (char*) *(REGISTERS + REG_A1));
  NID_A2  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_A2, 5, (char*) *(REGISTERS + REG_A2));
  NID_A3  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_A3, 5, (char*) *(REGISTERS + REG_A3));
  NID_A4  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_A4, 5, (char*) *(REGISTERS + REG_A4));
  NID_A5  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_A5, 5, (char*) *(REGISTERS + REG_A5));
  NID_A6  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_A6, 5, (char*) *(REGISTERS + REG_A6));
  NID_A7  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_A7, 5, (char*) *(REGISTERS + REG_A7));
  NID_S2  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_S2, 5, (char*) *(REGISTERS + REG_S2));
  NID_S3  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_S3, 5, (char*) *(REGISTERS + REG_S3));
  NID_S4  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_S4, 5, (char*) *(REGISTERS + REG_S4));
  NID_S5  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_S5, 5, (char*) *(REGISTERS + REG_S5));
  NID_S6  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_S6, 5, (char*) *(REGISTERS + REG_S6));
  NID_S7  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_S7, 5, (char*) *(REGISTERS + REG_S7));
  NID_S8  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_S8, 5, (char*) *(REGISTERS + REG_S8));
  NID_S9  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_S9, 5, (char*) *(REGISTERS + REG_S9));
  NID_S10 = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_S10, 5, (char*) *(REGISTERS + REG_S10));
  NID_S11 = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_S11, 5, (char*) *(REGISTERS + REG_S11));
  NID_T3  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_T3, 5, (char*) *(REGISTERS + REG_T3));
  NID_T4  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_T4, 5, (char*) *(REGISTERS + REG_T4));
  NID_T5  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_T5, 5, (char*) *(REGISTERS + REG_T5));
  NID_T6  = new_constant(OP_CONST, SID_REGISTER_ADDRESS, REG_T6, 5, (char*) *(REGISTERS + REG_T6));

  SID_REGISTER_STATE = new_array(SID_REGISTER_ADDRESS, SID_MACHINE_WORD, "register state");
}

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void print_memory_sorts();

void new_segmentation();
void print_segmentation();

uint64_t* is_block_in_segment(uint64_t* block_start_nid, uint64_t* block_end_nid,
  uint64_t* segment_start_nid, uint64_t* segment_end_nid);
uint64_t* is_block_in_code_segment(uint64_t* start_nid, uint64_t* end_nid);
uint64_t* is_block_in_data_segment(uint64_t* start_nid, uint64_t* end_nid);
uint64_t* is_block_in_heap_segment(uint64_t* start_nid, uint64_t* end_nid);
uint64_t* is_block_in_stack_segment(uint64_t* start_nid, uint64_t* end_nid);

void new_code_segment(uint64_t core);
void print_code_segment(uint64_t core);

void new_memory_state(uint64_t core);
void print_memory_state(uint64_t core);

uint64_t get_power_of_two_size_in_bytes(uint64_t size);

uint64_t* get_memory_address_sort(uint64_t* memory_nid);
uint64_t* get_memory_word_sort(uint64_t* memory_nid);

uint64_t is_byte_memory(uint64_t* memory_nid);
uint64_t is_half_word_memory(uint64_t* memory_nid);
uint64_t is_single_word_memory(uint64_t* memory_nid);
uint64_t is_double_word_memory(uint64_t* memory_nid);

uint64_t* vaddr_to_paddr(uint64_t* vaddr_nid, uint64_t* memory_nid);

uint64_t* load_aligned_memory_word(uint64_t* vaddr_nid, uint64_t* memory_nid);
uint64_t* store_aligned_memory_word(uint64_t* vaddr_nid, uint64_t* byte_nid, uint64_t* memory_nid);

uint64_t* cast_virtual_address_to_word(uint64_t* vaddr_nid, uint64_t* sid_word);
uint64_t* cast_virtual_address_to_memory_word(uint64_t* vaddr_nid, uint64_t* memory_nid);
uint64_t* get_memory_word_size_mask(uint64_t* memory_nid);
uint64_t* get_vaddr_alignment(uint64_t* vaddr_nid, uint64_t* memory_nid);

uint64_t* extend_byte_to_half_word(char* op, uint64_t* byte_nid);
uint64_t* extend_byte_to_single_word(char* op, uint64_t* byte_nid);
uint64_t* extend_byte_to_double_word(char* op, uint64_t* byte_nid);
uint64_t* extend_byte_to_memory_word(uint64_t* byte_nid, uint64_t* memory_nid);

uint64_t* shift_by_alignment_in_bits(uint64_t* vaddr_nid, uint64_t* memory_nid);
uint64_t* shift_from_vaddr(uint64_t* vaddr_nid, uint64_t* value_nid, uint64_t* memory_nid);
uint64_t* shift_to_vaddr(uint64_t* vaddr_nid, uint64_t* value_nid, uint64_t* memory_nid);

uint64_t* slice_byte_from_word(uint64_t* word_nid);

uint64_t* extend_half_word_to_single_word(char* op, uint64_t* word_nid);
uint64_t* extend_half_word_to_double_word(char* op, uint64_t* word_nid);
uint64_t* extend_half_word_to_memory_word(uint64_t* word_nid, uint64_t* memory_nid);
uint64_t* extend_single_word_to_double_word(char* op, uint64_t* word_nid);
uint64_t* extend_single_word_to_memory_word(uint64_t* word_nid, uint64_t* memory_nid);
uint64_t* extend_value_to_memory_word(uint64_t* value_nid, uint64_t* memory_nid);

uint64_t* get_value_mask(uint64_t* value_nid, uint64_t* memory_nid);

uint64_t* insert_value_into_memory_word(uint64_t* vaddr_nid, uint64_t* value_nid, uint64_t* memory_nid);

uint64_t* load_byte_from_memory_word(uint64_t* vaddr_nid, uint64_t* memory_nid);
uint64_t* store_byte_in_memory_word(uint64_t* vaddr_nid, uint64_t* byte_nid, uint64_t* memory_nid);

uint64_t* load_byte_at_virtual_address(uint64_t* vaddr_nid, uint64_t* memory_nid);
uint64_t* store_byte_at_virtual_address(uint64_t* vaddr_nid, uint64_t* byte_nid, uint64_t* memory_nid);

uint64_t* slice_second_byte_from_word(uint64_t* word_nid);

uint64_t* load_half_word_from_bytes(uint64_t* vaddr_nid, uint64_t* memory_nid);
uint64_t* store_half_word_in_bytes(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid);

uint64_t* get_half_word_size_relative_to_memory_word_size(uint64_t* memory_nid);
uint64_t* is_contained_in_memory_word(uint64_t* vaddr_nid, uint64_t* relative_size_nid, uint64_t* memory_nid);
uint64_t* slice_half_word_from_word(uint64_t* word_nid);
uint64_t* slice_half_word_from_memory_word(uint64_t* word_nid, uint64_t* memory_nid);

uint64_t* load_half_word_from_memory_words(uint64_t* vaddr_nid, uint64_t* memory_nid);
uint64_t* store_half_word_in_memory_words(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid);

uint64_t* load_half_word_at_virtual_address(uint64_t* vaddr_nid, uint64_t* memory_nid);
uint64_t* store_half_word_at_virtual_address(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid);

uint64_t* slice_lower_half_word_from_single_word(uint64_t* word_nid);
uint64_t* slice_upper_half_word_from_single_word(uint64_t* word_nid);

uint64_t* load_single_word_from_half_words(uint64_t* vaddr_nid, uint64_t* memory_nid);
uint64_t* store_single_word_in_half_words(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid);

uint64_t* get_single_word_size_relative_to_memory_word_size(uint64_t* memory_nid);
uint64_t* slice_single_word_from_double_word(uint64_t* word_nid);
uint64_t* slice_single_word_from_memory_word(uint64_t* word_nid, uint64_t* memory_nid);

uint64_t* load_single_word_from_memory_words(uint64_t* vaddr_nid, uint64_t* memory_nid);
uint64_t* store_single_word_in_memory_words(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid);

uint64_t* load_single_word_at_virtual_address(uint64_t* vaddr_nid, uint64_t* memory_nid);
uint64_t* store_single_word_at_virtual_address(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid);

uint64_t* slice_lower_single_word_from_double_word(uint64_t* word_nid);
uint64_t* slice_upper_single_word_from_double_word(uint64_t* word_nid);

uint64_t* load_double_word_from_single_words(uint64_t* vaddr_nid, uint64_t* memory_nid);
uint64_t* store_double_word_in_single_words(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid);

uint64_t* load_double_word_from_memory_words(uint64_t* vaddr_nid, uint64_t* memory_nid);
uint64_t* store_double_word_in_memory_words(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid);

uint64_t* load_double_word_at_virtual_address(uint64_t* vaddr_nid, uint64_t* memory_nid);
uint64_t* store_double_word_at_virtual_address(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid);

uint64_t* load_machine_word_at_virtual_address(uint64_t* vaddr_nid, uint64_t* memory_nid);
uint64_t* store_machine_word_at_virtual_address(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid);

uint64_t* cast_virtual_address_to_machine_word(uint64_t* vaddr_nid);
uint64_t* cast_machine_word_to_virtual_address(uint64_t* machine_word_nid);
uint64_t* is_machine_word_virtual_address(uint64_t* machine_word_nid);

uint64_t* load_byte(uint64_t* machine_word_nid, uint64_t* memory_nid);
uint64_t* store_byte(uint64_t* machine_word_nid, uint64_t* byte_nid, uint64_t* memory_nid);

uint64_t* load_half_word(uint64_t* machine_word_nid, uint64_t* memory_nid);
uint64_t* store_half_word(uint64_t* machine_word_nid, uint64_t* word_nid, uint64_t* memory_nid);

uint64_t* load_single_word(uint64_t* machine_word_nid, uint64_t* memory_nid);
uint64_t* store_single_word(uint64_t* machine_word_nid, uint64_t* word_nid, uint64_t* memory_nid);

uint64_t* load_double_word(uint64_t* machine_word_nid, uint64_t* memory_nid);
uint64_t* store_double_word(uint64_t* machine_word_nid, uint64_t* word_nid, uint64_t* memory_nid);

uint64_t* does_machine_word_work_as_virtual_address(uint64_t* machine_word_nid, uint64_t* property_nid);

uint64_t* is_address_in_code_segment(uint64_t* machine_word_nid);
uint64_t* is_address_in_data_segment(uint64_t* machine_word_nid);
uint64_t* is_address_in_heap_segment(uint64_t* machine_word_nid);
uint64_t* is_address_in_stack_segment(uint64_t* machine_word_nid);
uint64_t* is_address_in_main_memory(uint64_t* machine_word_nid);

uint64_t* is_range_in_heap_segment(uint64_t* machine_word_nid, uint64_t* range_nid);

uint64_t* is_sized_block_in_stack_segment(uint64_t* machine_word_nid, uint64_t* size_nid);
uint64_t* is_sized_block_in_main_memory(uint64_t* machine_word_nid, uint64_t* size_nid);

uint64_t* fetch_instruction(uint64_t* pc_nid, uint64_t* code_segment_nid);
uint64_t* fetch_compressed_instruction(uint64_t* pc_nid, uint64_t* code_segment_nid);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t SYNCHRONIZED_MEMORY = 0; // flag for synchronized main memory across cores
uint64_t SHARED_MEMORY = 0;       // flag for shared main memory across cores

uint64_t VIRTUAL_ADDRESS_SPACE = 0; // number of bits in virtual addresses

uint64_t* SID_VIRTUAL_ADDRESS = (uint64_t*) 0;

uint64_t* NID_VIRTUAL_ADDRESS_0 = (uint64_t*) 0;
uint64_t* NID_VIRTUAL_ADDRESS_1 = (uint64_t*) 0;
uint64_t* NID_VIRTUAL_ADDRESS_2 = (uint64_t*) 0;
uint64_t* NID_VIRTUAL_ADDRESS_3 = (uint64_t*) 0;
uint64_t* NID_VIRTUAL_ADDRESS_4 = (uint64_t*) 0;
uint64_t* NID_VIRTUAL_ADDRESS_5 = (uint64_t*) 0;
uint64_t* NID_VIRTUAL_ADDRESS_6 = (uint64_t*) 0;
uint64_t* NID_VIRTUAL_ADDRESS_7 = (uint64_t*) 0;
uint64_t* NID_VIRTUAL_ADDRESS_8 = (uint64_t*) 0;

uint64_t* NID_VIRTUAL_HALF_WORD_SIZE   = (uint64_t*) 0;
uint64_t* NID_VIRTUAL_SINGLE_WORD_SIZE = (uint64_t*) 0;
uint64_t* NID_VIRTUAL_DOUBLE_WORD_SIZE = (uint64_t*) 0;

uint64_t* NID_VIRTUAL_HALF_WORD_SIZE_MINUS_1   = (uint64_t*) 0;
uint64_t* NID_VIRTUAL_SINGLE_WORD_SIZE_MINUS_1 = (uint64_t*) 0;
uint64_t* NID_VIRTUAL_DOUBLE_WORD_SIZE_MINUS_1 = (uint64_t*) 0;

uint64_t* SID_CODE_WORD = (uint64_t*) 0;

uint64_t* NID_CODE_WORD_0 = (uint64_t*) 0;

uint64_t CODE_ADDRESS_SPACE = 0; // number of bits in code segment addresses

uint64_t* SID_CODE_ADDRESS = (uint64_t*) 0;
uint64_t* SID_CODE_STATE   = (uint64_t*) 0;

uint64_t* NID_CODE_START = (uint64_t*) 0;
uint64_t* NID_CODE_END   = (uint64_t*) 0;

uint64_t* SID_MEMORY_WORD = (uint64_t*) 0;

uint64_t* NID_MEMORY_WORD_0 = (uint64_t*) 0;

uint64_t MEMORY_ADDRESS_SPACE = 0; // number of bits in main memory addresses

uint64_t* SID_MEMORY_ADDRESS = (uint64_t*) 0;
uint64_t* SID_MEMORY_STATE   = (uint64_t*) 0;

uint64_t* NID_DATA_START = (uint64_t*) 0;
uint64_t* NID_DATA_END   = (uint64_t*) 0;

uint64_t* NID_HEAP_START = (uint64_t*) 0;
uint64_t* NID_HEAP_END   = (uint64_t*) 0;

uint64_t* NID_STACK_START = (uint64_t*) 0;
uint64_t* NID_STACK_END   = (uint64_t*) 0;

// bit masks and factors

uint64_t* NID_HALF_WORD_SIZE_MASK   = (uint64_t*) 0;
uint64_t* NID_SINGLE_WORD_SIZE_MASK = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_SIZE_MASK = (uint64_t*) 0;

uint64_t* NID_BYTE_MASK        = (uint64_t*) 0;
uint64_t* NID_HALF_WORD_MASK   = (uint64_t*) 0;
uint64_t* NID_SINGLE_WORD_MASK = (uint64_t*) 0;

uint64_t* NID_SINGLE_WORD_SIZE_MINUS_HALF_WORD_SIZE   = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_SIZE_MINUS_HALF_WORD_SIZE   = (uint64_t*) 0;
uint64_t* NID_DOUBLE_WORD_SIZE_MINUS_SINGLE_WORD_SIZE = (uint64_t*) 0;

uint64_t* NID_BYTE_SIZE_IN_BASE_BITS = (uint64_t*) 0;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t heap_start     = 0;
uint64_t heap_size      = 0;
uint64_t heap_allowance = 4096; // must be multiple of WORDSIZE

uint64_t stack_start     = 0;
uint64_t stack_size      = 0;
uint64_t stack_allowance = 4096; // stack allowance must be multiple of WORDSIZE > 0

uint64_t* init_zeroed_code_segment_nid = (uint64_t*) 0;
uint64_t* next_zeroed_code_segment_nid = (uint64_t*) 0;

uint64_t* initial_code_segment_nid  = (uint64_t*) 0;
uint64_t* initial_code_segment_nids = (uint64_t*) 0;

uint64_t* state_code_segment_nid = (uint64_t*) 0;
uint64_t* init_code_segment_nid  = (uint64_t*) 0;
uint64_t* next_code_segment_nid  = (uint64_t*) 0;

uint64_t* init_zeroed_main_memory_nid = (uint64_t*) 0;
uint64_t* next_zeroed_main_memory_nid = (uint64_t*) 0;

uint64_t* initial_main_memory_nid  = (uint64_t*) 0;
uint64_t* initial_data_segment_nid = (uint64_t*) 0;
uint64_t* initial_heap_segment_nid = (uint64_t*) 0;

uint64_t* state_main_memory_nid = (uint64_t*) 0;
uint64_t* init_main_memory_nid  = (uint64_t*) 0;
uint64_t* next_main_memory_nid  = (uint64_t*) 0;

uint64_t* eval_core_0_memory_data_flow_nid  = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_memory_sorts(uint64_t number_of_virtual_address_bits, uint64_t* code_word_sort_nid, uint64_t* memory_word_sort_nid) {
  uint64_t code_size_in_code_words;
  uint64_t saved_reuse_lines;

  // byte-addressed virtual memory

  // assert: number of virtual address bits is a power of 2 >= 8 bits

  VIRTUAL_ADDRESS_SPACE = number_of_virtual_address_bits;

  if (IS64BITSYSTEM * IS64BITTARGET > 0) {
    if (VIRTUAL_ADDRESS_SPACE > DOUBLEWORDSIZEINBITS)
      VIRTUAL_ADDRESS_SPACE = DOUBLEWORDSIZEINBITS;
  } else if (VIRTUAL_ADDRESS_SPACE > SINGLEWORDSIZEINBITS)
      VIRTUAL_ADDRESS_SPACE = SINGLEWORDSIZEINBITS;

  SID_VIRTUAL_ADDRESS = new_bitvec(VIRTUAL_ADDRESS_SPACE,
    format_comment("%lu-bit virtual address", VIRTUAL_ADDRESS_SPACE));

  NID_VIRTUAL_ADDRESS_0 = new_constant(OP_CONSTD, SID_VIRTUAL_ADDRESS, 0, 0, "virtual address 0");
  NID_VIRTUAL_ADDRESS_1 = new_constant(OP_CONSTD, SID_VIRTUAL_ADDRESS, 1, 0, "virtual address 1");
  NID_VIRTUAL_ADDRESS_2 = new_constant(OP_CONSTD, SID_VIRTUAL_ADDRESS, 2, 0, "virtual address 2");
  NID_VIRTUAL_ADDRESS_3 = new_constant(OP_CONSTD, SID_VIRTUAL_ADDRESS, 3, 0, "virtual address 3");
  NID_VIRTUAL_ADDRESS_4 = new_constant(OP_CONSTD, SID_VIRTUAL_ADDRESS, 4, 0, "virtual address 4");
  NID_VIRTUAL_ADDRESS_5 = new_constant(OP_CONSTD, SID_VIRTUAL_ADDRESS, 5, 0, "virtual address 5");
  NID_VIRTUAL_ADDRESS_6 = new_constant(OP_CONSTD, SID_VIRTUAL_ADDRESS, 6, 0, "virtual address 6");
  NID_VIRTUAL_ADDRESS_7 = new_constant(OP_CONSTD, SID_VIRTUAL_ADDRESS, 7, 0, "virtual address 7");
  NID_VIRTUAL_ADDRESS_8 = new_constant(OP_CONSTD, SID_VIRTUAL_ADDRESS, 8, 0, "virtual address 8");

  NID_VIRTUAL_HALF_WORD_SIZE   = NID_VIRTUAL_ADDRESS_2;
  NID_VIRTUAL_SINGLE_WORD_SIZE = NID_VIRTUAL_ADDRESS_4;
  NID_VIRTUAL_DOUBLE_WORD_SIZE = NID_VIRTUAL_ADDRESS_8;

  NID_VIRTUAL_HALF_WORD_SIZE_MINUS_1   = NID_VIRTUAL_ADDRESS_1;
  NID_VIRTUAL_SINGLE_WORD_SIZE_MINUS_1 = NID_VIRTUAL_ADDRESS_3;
  NID_VIRTUAL_DOUBLE_WORD_SIZE_MINUS_1 = NID_VIRTUAL_ADDRESS_7;

  // code segment

  SID_CODE_WORD = code_word_sort_nid;

  NID_CODE_WORD_0 = new_constant(OP_CONSTD, SID_CODE_WORD, 0, 0, "code word 0");

  // assert: code_size > 1 and code word size is a power of 2 >= 8 bits

  code_size_in_code_words = code_size / get_power_of_two_size_in_bytes(eval_bitvec_size(SID_CODE_WORD));

  if (code_size % get_power_of_two_size_in_bytes(eval_bitvec_size(SID_CODE_WORD)) > 0)
    code_size_in_code_words = code_size_in_code_words + 1;

  CODE_ADDRESS_SPACE = log_two(code_size_in_code_words);

  if (code_size_in_code_words > two_to_the_power_of(CODE_ADDRESS_SPACE))
    CODE_ADDRESS_SPACE = CODE_ADDRESS_SPACE + 1;

  SID_CODE_ADDRESS = new_bitvec(CODE_ADDRESS_SPACE,
    format_comment("%lu-bit code segment address", CODE_ADDRESS_SPACE));

  SID_CODE_STATE = new_array(SID_CODE_ADDRESS, SID_CODE_WORD, "code segment state");

  // main memory

  SID_MEMORY_WORD = memory_word_sort_nid;

  NID_MEMORY_WORD_0 = new_constant(OP_CONSTD, SID_MEMORY_WORD, 0, 0, "memory word 0");

  // assert: memory word size is a power of 2 >= 8 bits

  MEMORY_ADDRESS_SPACE =
    VIRTUAL_ADDRESS_SPACE - (get_power_of_two_size_in_bytes(eval_bitvec_size(SID_MEMORY_WORD)) - 1);

  SID_MEMORY_ADDRESS = new_bitvec(MEMORY_ADDRESS_SPACE,
    format_comment("%lu-bit physical memory address", MEMORY_ADDRESS_SPACE));

  saved_reuse_lines = reuse_lines;

  // distinguish from code segment
  reuse_lines = 0;

  SID_MEMORY_STATE = new_array(SID_MEMORY_ADDRESS, SID_MEMORY_WORD, "main memory state");

  reuse_lines = saved_reuse_lines;

  // bit masks and factors

  NID_HALF_WORD_SIZE_MASK   = NID_HALF_WORD_1;
  NID_SINGLE_WORD_SIZE_MASK = NID_SINGLE_WORD_3;
  NID_DOUBLE_WORD_SIZE_MASK = NID_DOUBLE_WORD_7;

  NID_BYTE_MASK        = new_constant(OP_CONSTH, SID_BYTE, 255, 2, "maximum byte value");
  NID_HALF_WORD_MASK   = new_constant(OP_CONSTH, SID_HALF_WORD, 65535, 4, "maximum half-word value");
  NID_SINGLE_WORD_MASK = new_constant(OP_CONSTH, SID_SINGLE_WORD, 4294967295, 8, "maximum single-word value");

  NID_SINGLE_WORD_SIZE_MINUS_HALF_WORD_SIZE   = NID_SINGLE_WORD_2;
  NID_DOUBLE_WORD_SIZE_MINUS_HALF_WORD_SIZE   = NID_DOUBLE_WORD_6;
  NID_DOUBLE_WORD_SIZE_MINUS_SINGLE_WORD_SIZE = NID_DOUBLE_WORD_4;

  NID_BYTE_SIZE_IN_BASE_BITS = NID_BYTE_3;
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

uint64_t* get_instruction_opcode(uint64_t* ir_nid);
uint64_t* get_instruction_funct3(uint64_t* ir_nid);
uint64_t* get_instruction_funct7(uint64_t* ir_nid);
uint64_t* get_instruction_funct6(uint64_t* ir_nid);

uint64_t* get_instruction_rd(uint64_t* ir_nid);
uint64_t* get_instruction_rs1(uint64_t* ir_nid);
uint64_t* get_instruction_rs2(uint64_t* ir_nid);

uint64_t* sign_extend_IS_immediate(uint64_t* imm_nid);
uint64_t* get_instruction_I_immediate(uint64_t* ir_nid);
uint64_t* get_instruction_I_32_bit_immediate(uint64_t* ir_nid);
uint64_t* get_instruction_5_bit_shamt(uint64_t* ir_nid);
uint64_t* get_instruction_shamt(uint64_t* ir_nid);
uint64_t* get_instruction_S_immediate(uint64_t* ir_nid);
uint64_t* sign_extend_SB_immediate(uint64_t* imm_nid);
uint64_t* get_instruction_SB_immediate(uint64_t* ir_nid);
uint64_t* sign_extend_U_immediate(uint64_t* imm_nid);
uint64_t* get_instruction_U_immediate(uint64_t* ir_nid);
uint64_t* sign_extend_UJ_immediate(uint64_t* imm_nid);
uint64_t* get_instruction_UJ_immediate(uint64_t* ir_nid);

uint64_t* decode_opcode(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* opcode_nid, char* opcode_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_opcode_nid);
uint64_t* decode_funct3(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* funct3_nid, char* funct3_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_funct3_nid);
uint64_t* decode_funct3_conditional(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* funct3_nid, char* funct3_comment,
  uint64_t* evaluate_nid, uint64_t* branch_nid, uint64_t* continue_nid, char* branch_comment,
  uint64_t* other_funct3_nid);
uint64_t* decode_funct7(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* funct7_nid, char* funct7_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_funct7_nid);

uint64_t* decode_lui(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* lui_nid, char* comment,
  uint64_t* other_opcode_nid);
uint64_t* decode_auipc(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* auipc_nid, char* comment,
  uint64_t* other_opcode_nid);
uint64_t* decode_funct7_6(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* funct_nid, char* funct_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_funct_nid);
uint64_t* decode_shift_RV64I(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* funct7_sll_srl_nid, uint64_t* slliw_nid, uint64_t* srliw_nid,
  uint64_t* funct7_sra_nid, uint64_t* sraiw_nid, char* comment,
  uint64_t* no_funct_nid);
uint64_t* decode_shift_imm(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* funct_sll_srl_nid, uint64_t* slli_nid, uint64_t* srli_nid,
  uint64_t* funct_sra_nid, uint64_t* srai_nid, char* comment,
  uint64_t* no_funct_nid);
uint64_t* decode_illegal_shamt(uint64_t* ir_nid);
uint64_t* decode_imm_RV64I(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* addiw_nid, uint64_t* slliw_nid, uint64_t* srliw_nid, uint64_t* sraiw_nid, char* comment,
  uint64_t* no_funct_nid, uint64_t* other_opcode_nid);
uint64_t* decode_imm(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* addi_nid, uint64_t* slti_nid, uint64_t* sltiu_nid,
  uint64_t* xori_nid, uint64_t* ori_nid, uint64_t* andi_nid,
  uint64_t* slli_nid, uint64_t* srli_nid, uint64_t* srai_nid,
  uint64_t* addiw_nid, uint64_t* slliw_nid, uint64_t* srliw_nid, uint64_t* sraiw_nid, char* comment,
  uint64_t* no_funct_nid, uint64_t* other_opcode_nid);
uint64_t* decode_op_RV64I(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* addw_nid, uint64_t* subw_nid,
  uint64_t* sllw_nid, uint64_t* srlw_nid, uint64_t* sraw_nid, char* comment,
  uint64_t* no_funct3_nid, uint64_t* RV64M_nid, uint64_t* other_opcode_nid);
uint64_t* decode_op(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* add_nid, uint64_t* sub_nid,
  uint64_t* slt_nid, uint64_t* sltu_nid,
  uint64_t* xor_nid, uint64_t* or_nid, uint64_t* and_nid,
  uint64_t* sll_nid, uint64_t* srl_nid, uint64_t* sra_nid,
  uint64_t* addw_nid, uint64_t* subw_nid,
  uint64_t* sllw_nid, uint64_t* srlw_nid, uint64_t* sraw_nid, char* comment,
  uint64_t* no_funct3_nid, uint64_t* RV32M_nid, uint64_t* RV64M_nid, uint64_t* other_opcode_nid);
uint64_t* decode_RV32M(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* mul_nid, uint64_t* mulh_nid, uint64_t* mulhsu_nid, uint64_t* mulhu_nid,
  uint64_t* div_nid, uint64_t* divu_nid, uint64_t* rem_nid, uint64_t* remu_nid, char* comment,
  uint64_t* no_funct_nid);
uint64_t* decode_RV64M(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* mulw_nid,
  uint64_t* divw_nid, uint64_t* divuw_nid, uint64_t* remw_nid, uint64_t* remuw_nid, char* comment,
  uint64_t* no_funct_nid);
uint64_t* decode_division_remainder_by_zero(uint64_t* ir_nid, uint64_t* register_file_nid);
uint64_t* decode_signed_division_remainder_overflow(uint64_t* ir_nid, uint64_t* register_file_nid);
uint64_t* decode_load_RV64I(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* ld_nid, uint64_t* lwu_nid, char* comment,
  uint64_t* no_funct3_nid);
uint64_t* decode_load(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* ld_nid, uint64_t* lwu_nid,
  uint64_t* lw_nid,
  uint64_t* lh_nid, uint64_t* lhu_nid,
  uint64_t* lb_nid, uint64_t* lbu_nid, char* comment,
  uint64_t* no_funct3_nid, uint64_t* other_opcode_nid);
uint64_t* decode_store_RV64I(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* sd_nid, char* comment,
  uint64_t* no_funct3_nid);
uint64_t* decode_store(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* sd_nid,
  uint64_t* sw_nid, uint64_t* sh_nid, uint64_t* sb_nid, char* comment,
  uint64_t* no_funct3_nid, uint64_t* other_opcode_nid);

uint64_t* decode_branch(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* beq_nid, uint64_t* bne_nid,
  uint64_t* blt_nid, uint64_t* bge_nid,
  uint64_t* bltu_nid, uint64_t* bgeu_nid,
  uint64_t* branch_nid, uint64_t* continue_nid, char* comment,
  uint64_t* no_funct3_nid, uint64_t* other_opcode_nid);

uint64_t* decode_jal(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* jal_nid, char* comment,
  uint64_t* other_opcode_nid);
uint64_t* decode_jalr(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* jalr_nid, char* comment,
  uint64_t* no_funct3_nid, uint64_t* other_opcode_nid);

uint64_t* decode_instruction(uint64_t* ir_nid);

uint64_t* get_rs1_value_plus_I_immediate(uint64_t* ir_nid, uint64_t* register_file_nid);
uint64_t* slice_single_word_from_machine_word(uint64_t* word_nid);
uint64_t* extend_single_word_to_machine_word(char* op, uint64_t* word_nid);

uint64_t* imm_data_flow(uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* other_data_flow_nid);
uint64_t* op_data_flow(uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* other_data_flow_nid);

uint64_t* extend_byte_to_machine_word(char* op, uint64_t* byte_nid);
uint64_t* extend_half_word_to_machine_word(char* op, uint64_t* word_nid);

uint64_t* load_data_flow(uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* memory_nid, uint64_t* other_data_flow_nid);
uint64_t* load_no_seg_faults(uint64_t* ir_nid, uint64_t* register_file_nid);

uint64_t* get_pc_value_plus_4(uint64_t* pc_nid);
uint64_t* jal_data_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* other_data_flow_nid);
uint64_t* jalr_data_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* other_data_flow_nid);

uint64_t* lui_data_flow(uint64_t* ir_nid, uint64_t* other_data_flow_nid);
uint64_t* get_pc_value_plus_U_immediate(uint64_t* pc_nid, uint64_t* ir_nid);
uint64_t* auipc_data_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* other_data_flow_nid);

uint64_t* core_register_data_flow(uint64_t* pc_nid, uint64_t* ir_nid,
  uint64_t* register_file_nid, uint64_t* memory_nid);

uint64_t* get_rs1_value_plus_S_immediate(uint64_t* ir_nid, uint64_t* register_file_nid);
uint64_t* store_data_flow(uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* memory_nid, uint64_t* other_data_flow_nid);
uint64_t* store_no_seg_faults(uint64_t* ir_nid, uint64_t* register_file_nid);

uint64_t* core_memory_data_flow(uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* memory_nid);

uint64_t* get_pc_value_plus_SB_immediate(uint64_t* pc_nid, uint64_t* ir_nid);
uint64_t* branch_control_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* other_control_flow_nid);

uint64_t* get_pc_value_plus_UJ_immediate(uint64_t* pc_nid, uint64_t* ir_nid);
uint64_t* jal_control_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* other_control_flow_nid);

uint64_t* jalr_control_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* other_control_flow_nid);

uint64_t* core_control_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* register_file_nid);

// compressed instructions

uint64_t* get_compressed_instruction_opcode(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_funct3(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_funct2(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_funct4(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_funct6(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_funct(uint64_t* c_ir_nid);

uint64_t* get_compressed_instruction_rd(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_rd_shift(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_rs1(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_rs1_shift(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_rs2(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_rs2_shift(uint64_t* c_ir_nid);

uint64_t* sign_extend_immediate(uint64_t bits, uint64_t* imm_nid);
uint64_t* get_compressed_instruction_shamt_5(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_CI_immediate_shamt(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_CI_immediate(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_CI_32_bit_immediate(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_CUI_immediate(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_CI16SP_immediate(uint64_t* c_ir_nid);
uint64_t* unsigned_extend_immediate_shamt_offset(uint64_t bits, uint64_t* imm_nid);
uint64_t* get_compressed_instruction_CIW_immediate(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_shamt(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_CI32_offset(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_CI64_offset(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_CL32_offset(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_CL64_offset(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_CSS32_offset(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_CSS64_offset(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_CS32_offset(uint64_t* c_ir_nid);
uint64_t* get_compressed_instruction_CS64_offset(uint64_t* c_ir_nid);
uint64_t* sign_extend_CB_offset(uint64_t* offset_nid);
uint64_t* get_compressed_instruction_CB_offset(uint64_t* c_ir_nid);
uint64_t* sign_extend_CJ_offset(uint64_t* offset_nid);
uint64_t* get_compressed_instruction_CJ_offset(uint64_t* c_ir_nid);

uint64_t* decode_compressed_opcode(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_opcode_nid, char* c_opcode_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_c_opcode_nid);
uint64_t* decode_compressed_funct3(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_funct3_nid, char* c_funct3_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_c_funct3_nid);
uint64_t* decode_compressed_funct3_conditional(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_funct3_nid, char* c_funct3_comment,
  uint64_t* evaluate_nid, uint64_t* branch_nid, uint64_t* continue_nid, char* branch_comment,
  uint64_t* other_c_funct3_nid);
uint64_t* decode_compressed_funct2(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_funct2_nid, char* c_funct2_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_c_funct2_nid);
uint64_t* decode_compressed_funct4(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_funct4_nid, char* c_funct4_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_c_funct4_nid);
uint64_t* decode_compressed_funct6(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_funct6_nid, char* c_funct6_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_c_funct6_nid);
uint64_t* decode_compressed_funct(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_funct_nid, char* c_funct_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_c_funct_nid);

uint64_t* decode_compressed_imm(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_li_nid, uint64_t* c_lui_nid,
  uint64_t* c_addi_nid, uint64_t* c_addiw_nid, uint64_t* c_addi16sp_nid,
  uint64_t* c_srli_nid, uint64_t* c_srai_nid, uint64_t* c_andi_nid, char* comment,
  uint64_t* other_c_funct_nid);
uint64_t* decode_compressed_addi4spn(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_addi4spn_nid, char* comment, uint64_t* other_c_funct3_nid);
uint64_t* decode_compressed_slli(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_slli_nid, char* comment, uint64_t* other_c_funct3_nid);
uint64_t* is_illegal_compressed_shift(uint64_t* c_ir_nid, uint64_t* c_shift_nid);
uint64_t* decode_illegal_compressed_instruction_imm_shamt(uint64_t* c_ir_nid);

uint64_t* decode_compressed_mv_add(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_mv_nid, uint64_t* c_add_nid, char* comment,
  uint64_t* other_c_funct4_nid);
uint64_t* decode_compressed_op(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_sub_nid, uint64_t* c_xor_nid, uint64_t* c_or_nid, uint64_t* c_and_nid,
  uint64_t* c_addw_nid, uint64_t* c_subw_nid, char* comment,
  uint64_t* other_c_funct_nid);
uint64_t* decode_compressed_load(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_ld_nid, uint64_t* c_lw_nid, char* comment,
  uint64_t* other_c_funct3_nid);
uint64_t* decode_compressed_store(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_sd_nid, uint64_t* c_sw_nid, char* comment,
  uint64_t* other_c_funct3_nid);
uint64_t* decode_compressed_branch(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_beqz_nid, uint64_t* c_bnez_nid,
  uint64_t* branch_nid, uint64_t* continue_nid, char* comment,
  uint64_t* other_c_funct3_nid);
uint64_t* decode_compressed_j(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_j_nid, char* comment, uint64_t* other_c_funct3_nid);
uint64_t* decode_compressed_jal(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_jal_nid, char* comment, uint64_t* other_c_funct3_nid);
uint64_t* decode_compressed_jr(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_jr_nid, char* comment, uint64_t* other_c_funct4_nid);
uint64_t* decode_compressed_jalr(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_jalr_nid, char* comment, uint64_t* other_c_funct4_nid);
uint64_t* decode_compressed_nonzero_rs1_zero_rs2(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_funct4_nid, uint64_t* other_c_funct4_nid);

uint64_t* is_compressed_instruction(uint64_t* ir_nid);
uint64_t* decode_compressed_instruction(uint64_t* c_ir_nid);

uint64_t* decode_compressed_register_data_flow(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_li_nid, uint64_t* c_lui_nid,
  uint64_t* c_addi_nid, uint64_t* c_addiw_nid,
  uint64_t* c_addi16sp_nid, uint64_t* c_addi4spn_nid,
  uint64_t* c_slli_nid, uint64_t* c_srli_nid, uint64_t* c_srai_nid, uint64_t* c_andi_nid,
  uint64_t* c_mv_nid, uint64_t* c_add_nid,
  uint64_t* c_sub_nid, uint64_t* c_xor_nid, uint64_t* c_or_nid, uint64_t* c_and_nid,
  uint64_t* c_addw_nid, uint64_t* c_subw_nid,
  uint64_t* c_ldsp_nid, uint64_t* c_lwsp_nid,
  uint64_t* c_ld_nid, uint64_t* c_lw_nid,
  uint64_t* c_jal_nid, uint64_t* c_jalr_nid, char* comment,
  uint64_t* other_register_data_flow_nid);

uint64_t* get_sp_value_plus_CI32_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid);
uint64_t* get_sp_value_plus_CI64_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid);
uint64_t* get_rs1_shift_value_plus_CL32_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid);
uint64_t* get_rs1_shift_value_plus_CL64_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid);
uint64_t* decode_compressed_load_with_opcode(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_ldsp_nid, uint64_t* c_lwsp_nid,
  uint64_t* c_ld_nid, uint64_t* c_lw_nid, char* comment,
  uint64_t* no_funct3_nid, uint64_t* no_opcode_nid);
uint64_t* compressed_load_no_seg_faults(uint64_t* c_ir_nid, uint64_t* register_file_nid);
uint64_t* get_pc_value_plus_2(uint64_t* pc_nid);
uint64_t* core_compressed_register_data_flow(uint64_t* pc_nid, uint64_t* c_ir_nid,
  uint64_t* register_file_nid, uint64_t* memory_nid);

uint64_t* decode_compressed_memory_data_flow(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_sdsp_nid, uint64_t* c_swsp_nid,
  uint64_t* c_sd_nid, uint64_t* c_sw_nid, char* comment,
  uint64_t* other_memory_data_flow_nid);

uint64_t* get_sp_value_plus_CSS32_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid);
uint64_t* get_sp_value_plus_CSS64_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid);
uint64_t* get_rs1_shift_value_plus_CS32_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid);
uint64_t* get_rs1_shift_value_plus_CS64_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid);
uint64_t* compressed_store_no_seg_faults(uint64_t* c_ir_nid, uint64_t* register_file_nid);
uint64_t* core_compressed_memory_data_flow(uint64_t* c_ir_nid, uint64_t* register_file_nid, uint64_t* memory_nid);

uint64_t* get_pc_value_plus_CB_offset(uint64_t* pc_nid, uint64_t* c_ir_nid);
uint64_t* compressed_branch_control_flow(uint64_t* pc_nid, uint64_t* c_ir_nid, uint64_t* register_file_nid, uint64_t* other_control_flow_nid);

uint64_t* get_pc_value_plus_CJ_offset(uint64_t* pc_nid, uint64_t* c_ir_nid);
uint64_t* compressed_j_jal_control_flow(uint64_t* pc_nid, uint64_t* c_ir_nid, uint64_t* other_control_flow_nid);

uint64_t* get_rs1_value_CR_format(uint64_t* c_ir_nid, uint64_t* register_file_nid);
uint64_t* compressed_jr_jalr_control_flow(uint64_t* c_ir_nid, uint64_t* register_file_nid, uint64_t* other_control_flow_nid);

uint64_t* core_compressed_control_flow(uint64_t* pc_nid, uint64_t* c_ir_nid, uint64_t* register_file_nid, uint64_t* other_control_flow_nid);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t* SID_INSTRUCTION_WORD = (uint64_t*) 0;

uint64_t* NID_INSTRUCTION_WORD_SIZE_MASK = (uint64_t*) 0;

// RISC-U codes

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

uint64_t* NID_F7_MUL_DIV_REM = (uint64_t*) 0;

uint64_t* SID_FUNCT12 = (uint64_t*) 0;

uint64_t* NID_F12_ECALL = (uint64_t*) 0;

uint64_t* NID_ECALL_I = (uint64_t*) 0;

// immediate sorts

uint64_t* SID_1_BIT_IMM  = (uint64_t*) 0;
uint64_t* SID_4_BIT_IMM  = (uint64_t*) 0;
uint64_t* SID_5_BIT_IMM  = (uint64_t*) 0;
uint64_t* SID_6_BIT_IMM  = (uint64_t*) 0;
uint64_t* SID_8_BIT_IMM  = (uint64_t*) 0;
uint64_t* SID_10_BIT_IMM = (uint64_t*) 0;
uint64_t* SID_11_BIT_IMM = (uint64_t*) 0;
uint64_t* SID_12_BIT_IMM = (uint64_t*) 0;
uint64_t* SID_13_BIT_IMM = (uint64_t*) 0;
uint64_t* SID_20_BIT_IMM = (uint64_t*) 0;
uint64_t* SID_21_BIT_IMM = (uint64_t*) 0;
uint64_t* SID_32_BIT_IMM = (uint64_t*) 0;

uint64_t* NID_1_BIT_IMM_0  = (uint64_t*) 0;
uint64_t* NID_12_BIT_IMM_0 = (uint64_t*) 0;

// RISC-U instruction switches

uint64_t RISCU = 0; // restrict to RISC-U

uint64_t* NID_LUI  = (uint64_t*) 0;
uint64_t* NID_ADDI = (uint64_t*) 0;

uint64_t* NID_ADD  = (uint64_t*) 0;
uint64_t* NID_SUB  = (uint64_t*) 0;
uint64_t* NID_MUL  = (uint64_t*) 0;
uint64_t* NID_DIVU = (uint64_t*) 0;
uint64_t* NID_REMU = (uint64_t*) 0;
uint64_t* NID_SLTU = (uint64_t*) 0;

uint64_t* NID_LD = (uint64_t*) 0;
uint64_t* NID_SD = (uint64_t*) 0;
uint64_t* NID_LW = (uint64_t*) 0;
uint64_t* NID_SW = (uint64_t*) 0;

uint64_t* NID_BEQ = (uint64_t*) 0;

uint64_t* NID_JAL  = (uint64_t*) 0;
uint64_t* NID_JALR = (uint64_t*) 0;

uint64_t* NID_ECALL = (uint64_t*) 0;

// RV32I codes missing in RISC-U

uint64_t OP_AUIPC = 23; // 0010111, U format (AUIPC)

uint64_t F3_BNE  = 1; // 001
uint64_t F3_BLT  = 4; // 100
uint64_t F3_BGE  = 5; // 101
uint64_t F3_BLTU = 6; // 110
uint64_t F3_BGEU = 7; // 111

uint64_t F3_LB  = 0; // 000
uint64_t F3_LH  = 1; // 001
uint64_t F3_LBU = 4; // 100
uint64_t F3_LHU = 5; // 101

uint64_t F3_SB = 0; // 000
uint64_t F3_SH = 1; // 001

uint64_t F3_SLL = 1; // 001
uint64_t F3_SLT = 2; // 010
uint64_t F3_XOR = 4; // 100
uint64_t F3_SRL = 5; // 101
uint64_t F3_SRA = 5; // 101
uint64_t F3_OR  = 6; // 110
uint64_t F3_AND = 7; // 111

uint64_t* NID_OP_AUIPC = (uint64_t*) 0;

uint64_t* NID_F3_BNE  = (uint64_t*) 0;
uint64_t* NID_F3_BLT  = (uint64_t*) 0;
uint64_t* NID_F3_BGE  = (uint64_t*) 0;
uint64_t* NID_F3_BLTU = (uint64_t*) 0;
uint64_t* NID_F3_BGEU = (uint64_t*) 0;

uint64_t* NID_F3_LB  = (uint64_t*) 0;
uint64_t* NID_F3_LH  = (uint64_t*) 0;
uint64_t* NID_F3_LBU = (uint64_t*) 0;
uint64_t* NID_F3_LHU = (uint64_t*) 0;

uint64_t* NID_F3_SB = (uint64_t*) 0;
uint64_t* NID_F3_SH = (uint64_t*) 0;

uint64_t* NID_F3_SLL = (uint64_t*) 0;
uint64_t* NID_F3_SLT = (uint64_t*) 0;
uint64_t* NID_F3_XOR = (uint64_t*) 0;
uint64_t* NID_F3_SRL = (uint64_t*) 0;
uint64_t* NID_F3_SRA = (uint64_t*) 0;
uint64_t* NID_F3_OR  = (uint64_t*) 0;
uint64_t* NID_F3_AND = (uint64_t*) 0;

uint64_t* NID_F7_ADD_SLT_XOR_OR_AND_SLL_SRL = (uint64_t*) 0;
uint64_t* NID_F7_SUB_SRA                    = (uint64_t*) 0;

uint64_t* NID_F7_SLL_SRL_ILLEGAL = (uint64_t*) 0;
uint64_t* NID_F7_SRA_ILLEGAL     = (uint64_t*) 0;

// RV32I instruction switches

uint64_t* NID_AUIPC = (uint64_t*) 0;

uint64_t* NID_BNE  = (uint64_t*) 0;
uint64_t* NID_BLT  = (uint64_t*) 0;
uint64_t* NID_BGE  = (uint64_t*) 0;
uint64_t* NID_BLTU = (uint64_t*) 0;
uint64_t* NID_BGEU = (uint64_t*) 0;

uint64_t* NID_LB  = (uint64_t*) 0;
uint64_t* NID_LH  = (uint64_t*) 0;
uint64_t* NID_LBU = (uint64_t*) 0;
uint64_t* NID_LHU = (uint64_t*) 0;

uint64_t* NID_SB = (uint64_t*) 0;
uint64_t* NID_SH = (uint64_t*) 0;

uint64_t* NID_SLTI  = (uint64_t*) 0;
uint64_t* NID_SLTIU = (uint64_t*) 0;
uint64_t* NID_XORI  = (uint64_t*) 0;
uint64_t* NID_ORI   = (uint64_t*) 0;
uint64_t* NID_ANDI  = (uint64_t*) 0;

uint64_t* NID_SLLI = (uint64_t*) 0;
uint64_t* NID_SRLI = (uint64_t*) 0;
uint64_t* NID_SRAI = (uint64_t*) 0;

uint64_t* NID_SLL = (uint64_t*) 0;
uint64_t* NID_SLT = (uint64_t*) 0;
uint64_t* NID_XOR = (uint64_t*) 0;
uint64_t* NID_SRL = (uint64_t*) 0;
uint64_t* NID_SRA = (uint64_t*) 0;

uint64_t* NID_OR  = (uint64_t*) 0;
uint64_t* NID_AND = (uint64_t*) 0;

// RV64I codes missing in RISC-U

uint64_t* SID_FUNCT6 = (uint64_t*) 0;

uint64_t F6_SLL_SRL = 0;  // 000000
uint64_t F6_SRA     = 16; // 010000

uint64_t* NID_F6_SLL_SRL = (uint64_t*) 0;
uint64_t* NID_F6_SRA     = (uint64_t*) 0;

uint64_t OP_IMM_32 = 27; // 0011011, I format
uint64_t OP_OP_32  = 59; // 0111011, I format

uint64_t F3_LWU = 6; // 110

uint64_t* NID_OP_IMM_32 = (uint64_t*) 0;
uint64_t* NID_OP_OP_32  = (uint64_t*) 0;

uint64_t* NID_F3_LWU = (uint64_t*) 0;

// RV64I instruction switches

uint64_t* NID_LWU = (uint64_t*) 0;

uint64_t* NID_ADDIW = (uint64_t*) 0;
uint64_t* NID_SLLIW = (uint64_t*) 0;
uint64_t* NID_SRLIW = (uint64_t*) 0;
uint64_t* NID_SRAIW = (uint64_t*) 0;

uint64_t* NID_ADDW = (uint64_t*) 0;
uint64_t* NID_SUBW = (uint64_t*) 0;
uint64_t* NID_SLLW = (uint64_t*) 0;
uint64_t* NID_SRLW = (uint64_t*) 0;
uint64_t* NID_SRAW = (uint64_t*) 0;

// RV32M codes missing in RISC-U

uint64_t F3_MULH   = 1; // 001
uint64_t F3_MULHSU = 2; // 010
uint64_t F3_MULHU  = 3; // 011
uint64_t F3_DIV    = 4; // 100
uint64_t F3_REM    = 6; // 110

uint64_t* NID_F3_MULH   = (uint64_t*) 0;
uint64_t* NID_F3_MULHSU = (uint64_t*) 0;
uint64_t* NID_F3_MULHU  = (uint64_t*) 0;
uint64_t* NID_F3_DIV    = (uint64_t*) 0;
uint64_t* NID_F3_REM    = (uint64_t*) 0;

// RV32M instruction switches

uint64_t RV32M = 1; // RV32M support

uint64_t* NID_MULH   = (uint64_t*) 0;
uint64_t* NID_MULHSU = (uint64_t*) 0;
uint64_t* NID_MULHU  = (uint64_t*) 0;
uint64_t* NID_DIV    = (uint64_t*) 0;
uint64_t* NID_REM    = (uint64_t*) 0;

// RV64M instruction switches

uint64_t RV64M = 1; // RV64M support

uint64_t* NID_MULW  = (uint64_t*) 0;
uint64_t* NID_DIVW  = (uint64_t*) 0;
uint64_t* NID_DIVUW = (uint64_t*) 0;
uint64_t* NID_REMW  = (uint64_t*) 0;
uint64_t* NID_REMUW = (uint64_t*) 0;

// RVC codes

uint64_t* SID_OPCODE_C = (uint64_t*) 0;

uint64_t* NID_OP_C0 = (uint64_t*) 0;
uint64_t* NID_OP_C1 = (uint64_t*) 0;
uint64_t* NID_OP_C2 = (uint64_t*) 0;
uint64_t* NID_OP_C3 = (uint64_t*) 0;

uint64_t F3_C_LI           = 2; // 010
uint64_t F3_C_LUI_ADDI16SP = 3; // 011

uint64_t* NID_F3_C_LI           = (uint64_t*) 0;
uint64_t* NID_F3_C_LUI_ADDI16SP = (uint64_t*) 0;

uint64_t F3_C_ADDI      = 0; // 000
uint64_t F3_C_ADDIW_JAL = 1; // 001

uint64_t* NID_F3_C_ADDI      = (uint64_t*) 0;
uint64_t* NID_F3_C_ADDIW_JAL = (uint64_t*) 0;

uint64_t F3_C_ADDI4SPN = 0; // 000

uint64_t* NID_F3_C_ADDI4SPN = (uint64_t*) 0;

uint64_t F3_C_SLLI           = 0; // 000
uint64_t F3_C_SRLI_SRAI_ANDI = 4; // 100

uint64_t* NID_F3_C_SLLI           = (uint64_t*) 0;
uint64_t* NID_F3_C_SRLI_SRAI_ANDI = (uint64_t*) 0;

uint64_t* SID_FUNCT2 = (uint64_t*) 0;

uint64_t F2_C_SRLI = 0; // 00
uint64_t F2_C_SRAI = 1; // 01
uint64_t F2_C_ANDI = 2; // 10

uint64_t* NID_F2_C_SRLI = (uint64_t*) 0;
uint64_t* NID_F2_C_SRAI = (uint64_t*) 0;
uint64_t* NID_F2_C_ANDI = (uint64_t*) 0;

uint64_t F6_C_SUB_XOR_OR_AND = 35; // 100011
uint64_t F6_C_ADDW_SUBW      = 39; // 100111

uint64_t* NID_F6_C_SUB_XOR_OR_AND = (uint64_t*) 0;
uint64_t* NID_F6_C_ADDW_SUBW      = (uint64_t*) 0;

uint64_t F2_C_SUB_SUBW = 0; // 00
uint64_t F2_C_XOR_ADDW = 1; // 01
uint64_t F2_C_OR       = 2; // 10
uint64_t F2_C_AND      = 3; // 11

uint64_t* NID_F2_C_SUB_SUBW = (uint64_t*) 0;
uint64_t* NID_F2_C_XOR_ADDW = (uint64_t*) 0;
uint64_t* NID_F2_C_OR       = (uint64_t*) 0;
uint64_t* NID_F2_C_AND      = (uint64_t*) 0;

uint64_t F3_C_LWSP_LW = 2; // 010
uint64_t F3_C_LDSP_LD = 3; // 011

uint64_t* NID_F3_C_LWSP_LW = (uint64_t*) 0;
uint64_t* NID_F3_C_LDSP_LD = (uint64_t*) 0;

uint64_t F3_C_SWSP_SW = 6; // 110
uint64_t F3_C_SDSP_SD = 7; // 111

uint64_t* NID_F3_C_SWSP_SW = (uint64_t*) 0;
uint64_t* NID_F3_C_SDSP_SD = (uint64_t*) 0;

uint64_t F3_C_BEQZ = 6; // 110
uint64_t F3_C_BNEZ = 7; // 111

uint64_t* NID_F3_C_BEQZ = (uint64_t*) 0;
uint64_t* NID_F3_C_BNEZ = (uint64_t*) 0;

uint64_t F3_C_J = 5; // 101

uint64_t* NID_F3_C_J = (uint64_t*) 0;

uint64_t* SID_FUNCT4 = (uint64_t*) 0;

uint64_t F4_C_MV_JR    = 8; // 1000
uint64_t F4_C_ADD_JALR = 9; // 1001

uint64_t* NID_F4_C_MV_JR    = (uint64_t*) 0;
uint64_t* NID_F4_C_ADD_JALR = (uint64_t*) 0;

// offset sorts

uint64_t* SID_1_BIT_OFFSET  = (uint64_t*) 0;
uint64_t* SID_2_BIT_OFFSET  = (uint64_t*) 0;
uint64_t* SID_3_BIT_OFFSET  = (uint64_t*) 0;
uint64_t* SID_4_BIT_OFFSET  = (uint64_t*) 0;
uint64_t* SID_5_BIT_OFFSET  = (uint64_t*) 0;
uint64_t* SID_6_BIT_OFFSET  = (uint64_t*) 0;
uint64_t* SID_7_BIT_OFFSET  = (uint64_t*) 0;
uint64_t* SID_8_BIT_OFFSET  = (uint64_t*) 0;
uint64_t* SID_9_BIT_OFFSET  = (uint64_t*) 0;
uint64_t* SID_10_BIT_OFFSET = (uint64_t*) 0;
uint64_t* SID_11_BIT_OFFSET = (uint64_t*) 0;
uint64_t* SID_12_BIT_OFFSET = (uint64_t*) 0;
uint64_t* SID_17_BIT_OFFSET = (uint64_t*) 0;
uint64_t* SID_18_BIT_OFFSET = (uint64_t*) 0;

uint64_t* NID_1_BIT_OFFSET_0  = (uint64_t*) 0;
uint64_t* NID_2_BIT_OFFSET_0  = (uint64_t*) 0;
uint64_t* NID_2_BIT_OFFSET_1  = (uint64_t*) 0;
uint64_t* NID_3_BIT_OFFSET_0  = (uint64_t*) 0;
uint64_t* NID_4_BIT_OFFSET_0  = (uint64_t*) 0;
uint64_t* NID_12_BIT_OFFSET_0 = (uint64_t*) 0;

uint64_t* SID_COMPRESSED_REGISTER_ADDRESS = (uint64_t*) 0;

// RVC instruction switches

uint64_t RVC = 1; // RVC support

uint64_t* NID_C_LI  = (uint64_t*) 0;
uint64_t* NID_C_LUI = (uint64_t*) 0;

uint64_t* NID_C_ADDI     = (uint64_t*) 0;
uint64_t* NID_C_ADDIW    = (uint64_t*) 0;
uint64_t* NID_C_ADDI16SP = (uint64_t*) 0;

uint64_t* NID_C_ADDI4SPN = (uint64_t*) 0;

uint64_t* NID_C_ANDI = (uint64_t*) 0;

uint64_t* NID_C_SLLI = (uint64_t*) 0;
uint64_t* NID_C_SRLI = (uint64_t*) 0;
uint64_t* NID_C_SRAI = (uint64_t*) 0;

uint64_t* NID_C_MV   = (uint64_t*) 0;
uint64_t* NID_C_ADD  = (uint64_t*) 0;

uint64_t* NID_C_SUB  = (uint64_t*) 0;
uint64_t* NID_C_XOR  = (uint64_t*) 0;
uint64_t* NID_C_OR   = (uint64_t*) 0;
uint64_t* NID_C_AND  = (uint64_t*) 0;
uint64_t* NID_C_ADDW = (uint64_t*) 0;
uint64_t* NID_C_SUBW = (uint64_t*) 0;

uint64_t* NID_C_LWSP = (uint64_t*) 0;
uint64_t* NID_C_LW   = (uint64_t*) 0;

uint64_t* NID_C_LDSP = (uint64_t*) 0;
uint64_t* NID_C_LD   = (uint64_t*) 0;

uint64_t* NID_C_SWSP = (uint64_t*) 0;
uint64_t* NID_C_SW   = (uint64_t*) 0;

uint64_t* NID_C_SDSP = (uint64_t*) 0;
uint64_t* NID_C_SD   = (uint64_t*) 0;

uint64_t* NID_C_BEQZ = (uint64_t*) 0;
uint64_t* NID_C_BNEZ = (uint64_t*) 0;

uint64_t* NID_C_J   = (uint64_t*) 0;
uint64_t* NID_C_JAL = (uint64_t*) 0;

uint64_t* NID_C_JR   = (uint64_t*) 0;
uint64_t* NID_C_JALR = (uint64_t*) 0;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* eval_known_instructions_nid            = (uint64_t*) 0;
uint64_t* eval_known_compressed_instructions_nid = (uint64_t*) 0;

uint64_t* eval_core_register_data_flow_nid = (uint64_t*) 0;
uint64_t* eval_core_memory_data_flow_nid   = (uint64_t*) 0;

uint64_t* eval_core_instruction_register_data_flow_nid            = (uint64_t*) 0;
uint64_t* eval_core_compressed_instruction_register_data_flow_nid = (uint64_t*) 0;

uint64_t* eval_core_instruction_memory_data_flow_nid            = (uint64_t*) 0;
uint64_t* eval_core_compressed_instruction_memory_data_flow_nid = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_instruction_sorts() {
  SID_INSTRUCTION_WORD = SID_SINGLE_WORD;

  if (RVC)
    NID_INSTRUCTION_WORD_SIZE_MASK = NID_MACHINE_WORD_1;
  else
    NID_INSTRUCTION_WORD_SIZE_MASK = NID_MACHINE_WORD_3;

  SID_OPCODE = new_bitvec(7, "opcode sort");

  NID_OP_LOAD   = new_constant(OP_CONST, SID_OPCODE, OP_LOAD, 7, "OP_LOAD");
  NID_OP_IMM    = new_constant(OP_CONST, SID_OPCODE, OP_IMM, 7, "OP_IMM");
  NID_OP_STORE  = new_constant(OP_CONST, SID_OPCODE, OP_STORE, 7, "OP_STORE");
  NID_OP_OP     = new_constant(OP_CONST, SID_OPCODE, OP_OP, 7, "OP_OP");
  NID_OP_LUI    = new_constant(OP_CONST, SID_OPCODE, OP_LUI, 7, "OP_LUI");
  NID_OP_BRANCH = new_constant(OP_CONST, SID_OPCODE, OP_BRANCH, 7, "OP_BRANCH");
  NID_OP_JALR   = new_constant(OP_CONST, SID_OPCODE, OP_JALR, 7, "OP_JALR");
  NID_OP_JAL    = new_constant(OP_CONST, SID_OPCODE, OP_JAL, 7, "OP_JAL");
  NID_OP_SYSTEM = new_constant(OP_CONST, SID_OPCODE, OP_SYSTEM, 7, "OP_SYSTEM");

  SID_FUNCT3 = new_bitvec(3, "funct3 sort");

  NID_F3_NOP         = new_constant(OP_CONST, SID_FUNCT3, F3_NOP, 3, "F3_NOP");
  NID_F3_ADDI        = new_constant(OP_CONST, SID_FUNCT3, F3_ADDI, 3, "F3_ADDI");
  NID_F3_ADD_SUB_MUL = new_constant(OP_CONST, SID_FUNCT3, F3_ADD, 3, "F3_ADD_SUB_MUL");
  NID_F3_DIVU        = new_constant(OP_CONST, SID_FUNCT3, F3_DIVU, 3, "F3_DIVU");
  NID_F3_REMU        = new_constant(OP_CONST, SID_FUNCT3, F3_REMU, 3, "F3_REMU");
  NID_F3_SLTU        = new_constant(OP_CONST, SID_FUNCT3, F3_SLTU, 3, "F3_SLTU");
  NID_F3_LD          = new_constant(OP_CONST, SID_FUNCT3, F3_LD, 3, "F3_LD");
  NID_F3_SD          = new_constant(OP_CONST, SID_FUNCT3, F3_SD, 3, "F3_SD");
  NID_F3_LW          = new_constant(OP_CONST, SID_FUNCT3, F3_LW, 3, "F3_LW");
  NID_F3_SW          = new_constant(OP_CONST, SID_FUNCT3, F3_SW, 3, "F3_SW");
  NID_F3_BEQ         = new_constant(OP_CONST, SID_FUNCT3, F3_BEQ, 3, "F3_BEQ");
  NID_F3_JALR        = new_constant(OP_CONST, SID_FUNCT3, F3_JALR, 3, "F3_JALR");
  NID_F3_ECALL       = new_constant(OP_CONST, SID_FUNCT3, F3_ECALL, 3, "F3_ECALL");

  SID_FUNCT7 = new_bitvec(7, "funct7 sort");

  NID_F7_ADD  = new_constant(OP_CONST, SID_FUNCT7, F7_ADD, 7, "F7_ADD");
  NID_F7_MUL  = new_constant(OP_CONST, SID_FUNCT7, F7_MUL, 7, "F7_MUL");
  NID_F7_SUB  = new_constant(OP_CONST, SID_FUNCT7, F7_SUB, 7, "F7_SUB");
  NID_F7_DIVU = new_constant(OP_CONST, SID_FUNCT7, F7_DIVU, 7, "F7_DIVU");
  NID_F7_REMU = new_constant(OP_CONST, SID_FUNCT7, F7_REMU, 7, "F7_REMU");
  NID_F7_SLTU = new_constant(OP_CONST, SID_FUNCT7, F7_SLTU, 7, "F7_SLTU");

  NID_F7_MUL_DIV_REM = NID_F7_MUL;

  SID_FUNCT12 = new_bitvec(12, "funct12 sort");

  NID_F12_ECALL = new_constant(OP_CONST, SID_FUNCT12, F12_ECALL, 12, "F12_ECALL");

  NID_ECALL_I = new_constant(OP_CONST, SID_INSTRUCTION_WORD,
    left_shift(left_shift(left_shift(left_shift(F12_ECALL, 5) + REG_ZR, 3)
      + F3_ECALL, 5) + REG_ZR, 7) + OP_SYSTEM,
    32,
    "ECALL instruction");

  // immediate sorts

  SID_1_BIT_IMM  = new_bitvec(1, "1-bit immediate sort");
  SID_4_BIT_IMM  = new_bitvec(4, "4-bit immediate sort");
  SID_5_BIT_IMM  = new_bitvec(5, "5-bit immediate sort");
  SID_6_BIT_IMM  = new_bitvec(6, "6-bit immediate sort");
  SID_8_BIT_IMM  = new_bitvec(8, "8-bit immediate sort");
  SID_10_BIT_IMM = new_bitvec(10, "10-bit immediate sort");
  SID_11_BIT_IMM = new_bitvec(11, "11-bit immediate sort");
  SID_12_BIT_IMM = new_bitvec(12, "12-bit immediate sort");
  SID_13_BIT_IMM = new_bitvec(13, "13-bit immediate sort");
  SID_20_BIT_IMM = new_bitvec(20, "20-bit immediate sort");
  SID_21_BIT_IMM = new_bitvec(21, "21-bit immediate sort");
  SID_32_BIT_IMM = new_bitvec(32, "32-bit immediate sort");

  NID_1_BIT_IMM_0  = NID_FALSE;
  NID_12_BIT_IMM_0 = new_constant(OP_CONST, SID_12_BIT_IMM, 0, 12, "12 LSBs zeroed");

  // RISC-U instructions

  NID_LUI  = NID_TRUE;
  NID_ADDI = NID_TRUE;

  NID_ADD  = NID_TRUE;
  NID_SUB  = NID_TRUE;
  NID_MUL  = NID_TRUE;
  NID_DIVU = NID_TRUE;
  NID_REMU = NID_TRUE;
  NID_SLTU = NID_TRUE;

  NID_LW = NID_TRUE;
  NID_SW = NID_TRUE;

  if (IS64BITTARGET) {
    NID_LD = NID_TRUE;
    NID_SD = NID_TRUE;

    if (RISCU) {
      NID_LW = NID_FALSE;
      NID_SW = NID_FALSE;
    }
  } else {
    NID_LD = NID_FALSE;
    NID_SD = NID_FALSE;
  }

  NID_BEQ = NID_TRUE;

  NID_JAL  = NID_TRUE;
  NID_JALR = NID_TRUE;

  NID_ECALL = NID_TRUE;

  // RV32I codes missing in RISC-U

  NID_OP_AUIPC = new_constant(OP_CONST, SID_OPCODE, OP_AUIPC, 7, "OP_AUIPC");

  NID_F3_BNE  = new_constant(OP_CONST, SID_FUNCT3, F3_BNE, 3, "F3_BNE");
  NID_F3_BLT  = new_constant(OP_CONST, SID_FUNCT3, F3_BLT, 3, "F3_BLT");
  NID_F3_BGE  = new_constant(OP_CONST, SID_FUNCT3, F3_BGE, 3, "F3_BGE");
  NID_F3_BLTU = new_constant(OP_CONST, SID_FUNCT3, F3_BLTU, 3, "F3_BLTU");
  NID_F3_BGEU = new_constant(OP_CONST, SID_FUNCT3, F3_BGEU, 3, "F3_BGEU");

  NID_F3_LB  = new_constant(OP_CONST, SID_FUNCT3, F3_LB, 3, "F3_LB");
  NID_F3_LH  = new_constant(OP_CONST, SID_FUNCT3, F3_LH, 3, "F3_LH");
  NID_F3_LBU = new_constant(OP_CONST, SID_FUNCT3, F3_LBU, 3, "F3_LBU");
  NID_F3_LHU = new_constant(OP_CONST, SID_FUNCT3, F3_LHU, 3, "F3_LHU");

  NID_F3_SB = new_constant(OP_CONST, SID_FUNCT3, F3_SB, 3, "F3_SB");
  NID_F3_SH = new_constant(OP_CONST, SID_FUNCT3, F3_SH, 3, "F3_SH");

  NID_F3_SLL = new_constant(OP_CONST, SID_FUNCT3, F3_SLL, 3, "F3_SLL");
  NID_F3_SLT = new_constant(OP_CONST, SID_FUNCT3, F3_SLT, 3, "F3_SLT");
  NID_F3_XOR = new_constant(OP_CONST, SID_FUNCT3, F3_XOR, 3, "F3_XOR");
  NID_F3_SRL = new_constant(OP_CONST, SID_FUNCT3, F3_SRL, 3, "F3_SRL");
  NID_F3_SRA = new_constant(OP_CONST, SID_FUNCT3, F3_SRA, 3, "F3_SRA");
  NID_F3_OR  = new_constant(OP_CONST, SID_FUNCT3, F3_OR, 3, "F3_OR");
  NID_F3_AND = new_constant(OP_CONST, SID_FUNCT3, F3_AND, 3, "F3_AND");

  NID_F7_ADD_SLT_XOR_OR_AND_SLL_SRL = NID_F7_ADD;
  NID_F7_SUB_SRA                    = NID_F7_SUB;

  NID_F7_SLL_SRL_ILLEGAL = new_constant(OP_CONST, SID_FUNCT7, F7_ADD + 1, 7, "F7_SLL_SRL_ILLEGAL");
  NID_F7_SRA_ILLEGAL     = new_constant(OP_CONST, SID_FUNCT7, F7_SUB + 1, 7, "F7_SRA_ILLEGAL");

  // RV32I instruction switches

  if (RISCU) {
    NID_AUIPC = NID_FALSE;

    NID_BNE  = NID_FALSE;
    NID_BLT  = NID_FALSE;
    NID_BGE  = NID_FALSE;
    NID_BLTU = NID_FALSE;
    NID_BGEU = NID_FALSE;

    NID_LB  = NID_FALSE;
    NID_LH  = NID_FALSE;
    NID_LBU = NID_FALSE;
    NID_LHU = NID_FALSE;

    NID_SB = NID_FALSE;
    NID_SH = NID_FALSE;

    NID_SLTI  = NID_FALSE;
    NID_SLTIU = NID_FALSE;
    NID_XORI  = NID_FALSE;
    NID_ORI   = NID_FALSE;
    NID_ANDI  = NID_FALSE;

    NID_SLLI = NID_FALSE;
    NID_SRLI = NID_FALSE;
    NID_SRAI = NID_FALSE;

    NID_SLL = NID_FALSE;
    NID_SLT = NID_FALSE;
    NID_XOR = NID_FALSE;
    NID_SRL = NID_FALSE;
    NID_SRA = NID_FALSE;

    NID_OR  = NID_FALSE;
    NID_AND = NID_FALSE;
  } else {
    NID_AUIPC = NID_TRUE;

    NID_BNE  = NID_TRUE;
    NID_BLT  = NID_TRUE;
    NID_BGE  = NID_TRUE;
    NID_BLTU = NID_TRUE;
    NID_BGEU = NID_TRUE;

    NID_LB  = NID_TRUE;
    NID_LH  = NID_TRUE;
    NID_LBU = NID_TRUE;
    NID_LHU = NID_TRUE;

    NID_SB = NID_TRUE;
    NID_SH = NID_TRUE;

    NID_SLTI  = NID_TRUE;
    NID_SLTIU = NID_TRUE;
    NID_XORI  = NID_TRUE;
    NID_ORI   = NID_TRUE;
    NID_ANDI  = NID_TRUE;

    NID_SLLI = NID_TRUE;
    NID_SRLI = NID_TRUE;
    NID_SRAI = NID_TRUE;

    NID_SLL = NID_TRUE;
    NID_SLT = NID_TRUE;
    NID_XOR = NID_TRUE;
    NID_SRL = NID_TRUE;
    NID_SRA = NID_TRUE;

    NID_OR  = NID_TRUE;
    NID_AND = NID_TRUE;
  }

  // RV64I codes missing in RISC-U

  SID_FUNCT6 = new_bitvec(6, "funct6 sort");

  NID_F6_SLL_SRL = new_constant(OP_CONST, SID_FUNCT6, F6_SLL_SRL, 6, "F6_SLL_SRL");
  NID_F6_SRA     = new_constant(OP_CONST, SID_FUNCT6, F6_SRA, 6, "F6_SRA");

  NID_OP_IMM_32 = new_constant(OP_CONST, SID_OPCODE, OP_IMM_32, 7, "OP_IMM_32");
  NID_OP_OP_32  = new_constant(OP_CONST, SID_OPCODE, OP_OP_32, 7, "OP_OP_32");

  NID_F3_LWU = new_constant(OP_CONST, SID_FUNCT3, F3_LWU, 3, "F3_LWU");

  // RV64I instruction switches

  NID_LWU = NID_FALSE;

  NID_ADDIW = NID_FALSE;
  NID_SLLIW = NID_FALSE;
  NID_SRLIW = NID_FALSE;
  NID_SRAIW = NID_FALSE;

  NID_ADDW = NID_FALSE;
  NID_SUBW = NID_FALSE;
  NID_SLLW = NID_FALSE;
  NID_SRLW = NID_FALSE;
  NID_SRAW = NID_FALSE;

  if (RISCU == 0)
    if (IS64BITTARGET) {
      NID_LWU = NID_TRUE;

      NID_ADDIW = NID_TRUE;
      NID_SLLIW = NID_TRUE;
      NID_SRLIW = NID_TRUE;
      NID_SRAIW = NID_TRUE;

      NID_ADDW = NID_TRUE;
      NID_SUBW = NID_TRUE;
      NID_SLLW = NID_TRUE;
      NID_SRLW = NID_TRUE;
      NID_SRAW = NID_TRUE;
    }

  // RV32M codes missing in RISC-U

  NID_F3_MULH   = new_constant(OP_CONST, SID_FUNCT3, F3_MULH, 3, "F3_MULH");
  NID_F3_MULHSU = new_constant(OP_CONST, SID_FUNCT3, F3_MULHSU, 3, "F3_MULHSU");
  NID_F3_MULHU  = new_constant(OP_CONST, SID_FUNCT3, F3_MULHU, 3, "F3_MULHU");
  NID_F3_DIV    = new_constant(OP_CONST, SID_FUNCT3, F3_DIV, 3, "F3_DIV");
  NID_F3_REM    = new_constant(OP_CONST, SID_FUNCT3, F3_REM, 3, "F3_REM");

  // RV32M instruction switches

  if (RISCU)
    RV32M = 1;

  NID_MULH   = NID_FALSE;
  NID_MULHSU = NID_FALSE;
  NID_MULHU  = NID_FALSE;
  NID_DIV    = NID_FALSE;
  NID_REM    = NID_FALSE;

  if (RISCU == 0) {
    if (RV32M) {
      NID_MUL    = NID_TRUE;
      NID_MULH   = NID_TRUE;
      NID_MULHSU = NID_TRUE;
      NID_MULHU  = NID_TRUE;
      NID_DIV    = NID_TRUE;
      NID_REM    = NID_TRUE;
    } else
      NID_MUL = NID_FALSE;
  }

  // RV64M instruction switches

  if (RISCU)
    RV64M = 0;

  if (IS64BITTARGET == 0)
    RV64M = 0;

  if (RV64M) {
    NID_MULW  = NID_TRUE;
    NID_DIVW  = NID_TRUE;
    NID_DIVUW = NID_TRUE;
    NID_REMW  = NID_TRUE;
    NID_REMUW = NID_TRUE;
  } else {
    NID_MULW  = NID_FALSE;
    NID_DIVW  = NID_FALSE;
    NID_DIVUW = NID_FALSE;
    NID_REMW  = NID_FALSE;
    NID_REMUW = NID_FALSE;
  }

  // RVC codes

  SID_OPCODE_C = new_bitvec(2, "compressed opcode sort");

  NID_OP_C0 = new_constant(OP_CONST, SID_OPCODE_C, 0, 2, "OP_C0");
  NID_OP_C1 = new_constant(OP_CONST, SID_OPCODE_C, 1, 2, "OP_C1");
  NID_OP_C2 = new_constant(OP_CONST, SID_OPCODE_C, 2, 2, "OP_C2");
  NID_OP_C3 = new_constant(OP_CONST, SID_OPCODE_C, 3, 2, "OP_C3");

  NID_F3_C_LI           = new_constant(OP_CONST, SID_FUNCT3, F3_C_LI, 3, "F3_C_LI");
  NID_F3_C_LUI_ADDI16SP = new_constant(OP_CONST, SID_FUNCT3, F3_C_LUI_ADDI16SP, 3, "F3_C_LUI_ADDI16SP");

  NID_F3_C_ADDI      = new_constant(OP_CONST, SID_FUNCT3, F3_C_ADDI, 3, "F3_C_ADDI");
  NID_F3_C_ADDIW_JAL = new_constant(OP_CONST, SID_FUNCT3, F3_C_ADDIW_JAL, 3, "F3_C_ADDIW_JAL");

  NID_F3_C_ADDI4SPN = new_constant(OP_CONST, SID_FUNCT3, F3_C_ADDI4SPN, 3, "F3_C_ADDI4SPN");

  NID_F3_C_SLLI           = new_constant(OP_CONST, SID_FUNCT3, F3_C_SLLI, 3, "F3_C_SLLI");
  NID_F3_C_SRLI_SRAI_ANDI = new_constant(OP_CONST, SID_FUNCT3, F3_C_SRLI_SRAI_ANDI, 3, "F3_C_SRLI_SRAI_ANDI");

  SID_FUNCT2 = new_bitvec(2, "compressed funct2 sort");

  NID_F2_C_SRLI = new_constant(OP_CONST, SID_FUNCT2, F2_C_SRLI, 2, "F2_C_SRLI");
  NID_F2_C_SRAI = new_constant(OP_CONST, SID_FUNCT2, F2_C_SRAI, 2, "F2_C_SRAI");
  NID_F2_C_ANDI = new_constant(OP_CONST, SID_FUNCT2, F2_C_ANDI, 2, "F2_C_ANDI");

  NID_F6_C_SUB_XOR_OR_AND = new_constant(OP_CONST, SID_FUNCT6, F6_C_SUB_XOR_OR_AND, 6, "F6_C_SUB_XOR_OR_AND");
  NID_F6_C_ADDW_SUBW      = new_constant(OP_CONST, SID_FUNCT6, F6_C_ADDW_SUBW, 6, "F6_C_ADDW_SUBW");

  NID_F2_C_SUB_SUBW = new_constant(OP_CONST, SID_FUNCT2, F2_C_SUB_SUBW, 2, "F2_C_SUB_SUBW");
  NID_F2_C_XOR_ADDW = new_constant(OP_CONST, SID_FUNCT2, F2_C_XOR_ADDW, 2, "F2_C_XOR_ADDW");
  NID_F2_C_OR       = new_constant(OP_CONST, SID_FUNCT2, F2_C_OR, 2, "F2_C_OR");
  NID_F2_C_AND      = new_constant(OP_CONST, SID_FUNCT2, F2_C_AND, 2, "F2_C_AND");

  NID_F3_C_LWSP_LW = new_constant(OP_CONST, SID_FUNCT3, F3_C_LWSP_LW, 3, "F3_C_LWSP_LW");
  NID_F3_C_LDSP_LD = new_constant(OP_CONST, SID_FUNCT3, F3_C_LDSP_LD, 3, "F3_C_LDSP_LD");

  NID_F3_C_SWSP_SW = new_constant(OP_CONST, SID_FUNCT3, F3_C_SWSP_SW, 3, "F3_C_SWSP_SW");
  NID_F3_C_SDSP_SD = new_constant(OP_CONST, SID_FUNCT3, F3_C_SDSP_SD, 3, "F3_C_SDSP_SD");

  NID_F3_C_BEQZ = new_constant(OP_CONST, SID_FUNCT3, F3_C_BEQZ, 3, "F3_C_BEQZ");
  NID_F3_C_BNEZ = new_constant(OP_CONST, SID_FUNCT3, F3_C_BNEZ, 3, "F3_C_BNEZ");

  NID_F3_C_J = new_constant(OP_CONST, SID_FUNCT3, F3_C_J, 3, "F3_C_J");

  SID_FUNCT4 = new_bitvec(4, "compressed funct4 sort");

  NID_F4_C_MV_JR    = new_constant(OP_CONST, SID_FUNCT4, F4_C_MV_JR, 4, "F4_C_MV_JR");
  NID_F4_C_ADD_JALR = new_constant(OP_CONST, SID_FUNCT4, F4_C_ADD_JALR, 4, "F4_C_ADD_JALR");

  // offset sorts

  SID_1_BIT_OFFSET  = new_bitvec(1, "1-bit offset sort");
  SID_2_BIT_OFFSET  = new_bitvec(2, "2-bit offset sort");
  SID_3_BIT_OFFSET  = new_bitvec(3, "3-bit offset sort");
  SID_4_BIT_OFFSET  = new_bitvec(4, "4-bit offset sort");
  SID_5_BIT_OFFSET  = new_bitvec(5, "5-bit offset sort");
  SID_6_BIT_OFFSET  = new_bitvec(6, "6-bit offset sort");
  SID_7_BIT_OFFSET  = new_bitvec(7, "7-bit offset sort");
  SID_8_BIT_OFFSET  = new_bitvec(8, "8-bit offset sort");
  SID_9_BIT_OFFSET  = new_bitvec(9, "9-bit offset sort");
  SID_10_BIT_OFFSET = new_bitvec(10, "10-bit offset sort");
  SID_11_BIT_OFFSET = new_bitvec(11, "11-bit offset sort");
  SID_12_BIT_OFFSET = new_bitvec(12, "12-bit offset sort");
  SID_17_BIT_OFFSET = new_bitvec(17, "17-bit offset sort");
  SID_18_BIT_OFFSET = new_bitvec(18, "18-bit offset sort");

  NID_1_BIT_OFFSET_0  = NID_FALSE;
  NID_2_BIT_OFFSET_0  = new_constant(OP_CONST, SID_2_BIT_OFFSET, 0, 2, "2-bit offset 0");
  NID_2_BIT_OFFSET_1  = new_constant(OP_CONST, SID_2_BIT_OFFSET, 1, 2, "2-bit offset 1, 01000 s0");
  NID_3_BIT_OFFSET_0  = new_constant(OP_CONST, SID_3_BIT_OFFSET, 0, 3, "3-bit offset 0");
  NID_4_BIT_OFFSET_0  = new_constant(OP_CONST, SID_4_BIT_OFFSET, 0, 4, "4-bit offset 0");
  NID_12_BIT_OFFSET_0 = new_constant(OP_CONST, SID_12_BIT_OFFSET, 0, 12, "12-bit offset 0");

  SID_COMPRESSED_REGISTER_ADDRESS = new_bitvec(3, "3-bit compressed register address");

  // RVC instruction switches

  if (RISCU)
    RVC = 0;

  if (RVC) {
    NID_C_LI  = NID_TRUE;
    NID_C_LUI = NID_TRUE;

    NID_C_ADDI = NID_TRUE;
    if (IS64BITTARGET)
      NID_C_ADDIW = NID_TRUE;
    else
      NID_C_ADDIW = NID_FALSE;
    NID_C_ADDI16SP = NID_TRUE;

    NID_C_ADDI4SPN = NID_TRUE;

    NID_C_ANDI = NID_TRUE;

    NID_C_SLLI = NID_TRUE;
    NID_C_SRLI = NID_TRUE;
    NID_C_SRAI = NID_TRUE;

    NID_C_MV   = NID_TRUE;
    NID_C_ADD  = NID_TRUE;

    NID_C_SUB  = NID_TRUE;
    NID_C_XOR  = NID_TRUE;
    NID_C_OR   = NID_TRUE;
    NID_C_AND  = NID_TRUE;

    if (IS64BITTARGET) {
      NID_C_ADDW = NID_TRUE;
      NID_C_SUBW = NID_TRUE;
    } else {
      NID_C_ADDW = NID_FALSE;
      NID_C_SUBW = NID_FALSE;
    }

    NID_C_LWSP = NID_TRUE;
    NID_C_LW   = NID_TRUE;

    NID_C_SWSP = NID_TRUE;
    NID_C_SW   = NID_TRUE;

    if (IS64BITTARGET) {
      NID_C_LDSP = NID_TRUE;
      NID_C_LD   = NID_TRUE;

      NID_C_SDSP = NID_TRUE;
      NID_C_SD   = NID_TRUE;
    } else {
      NID_C_LDSP = NID_FALSE;
      NID_C_LD   = NID_FALSE;

      NID_C_SDSP = NID_FALSE;
      NID_C_SD   = NID_FALSE;
    }

    NID_C_BEQZ = NID_TRUE;
    NID_C_BNEZ = NID_TRUE;

    NID_C_J = NID_TRUE;
    if (IS64BITTARGET)
      NID_C_JAL = NID_FALSE;
    else
      NID_C_JAL = NID_TRUE;

    NID_C_JR   = NID_TRUE;
    NID_C_JALR = NID_TRUE;
  } else {
    NID_C_LI  = NID_FALSE;
    NID_C_LUI = NID_FALSE;

    NID_C_ADDI     = NID_FALSE;
    NID_C_ADDIW    = NID_FALSE;
    NID_C_ADDI16SP = NID_FALSE;

    NID_C_ADDI4SPN = NID_FALSE;

    NID_C_ANDI = NID_FALSE;

    NID_C_SLLI = NID_FALSE;
    NID_C_SRLI = NID_FALSE;
    NID_C_SRAI = NID_FALSE;

    NID_C_MV   = NID_FALSE;
    NID_C_ADD  = NID_FALSE;

    NID_C_SUB  = NID_FALSE;
    NID_C_XOR  = NID_FALSE;
    NID_C_OR   = NID_FALSE;
    NID_C_AND  = NID_FALSE;

    NID_C_ADDW = NID_FALSE;
    NID_C_SUBW = NID_FALSE;

    NID_C_LWSP = NID_FALSE;
    NID_C_LW   = NID_FALSE;

    NID_C_LDSP = NID_FALSE;
    NID_C_LD   = NID_FALSE;

    NID_C_SWSP = NID_FALSE;
    NID_C_SW   = NID_FALSE;

    NID_C_SDSP = NID_FALSE;
    NID_C_SD   = NID_FALSE;

    NID_C_BEQZ = NID_FALSE;
    NID_C_BNEZ = NID_FALSE;

    NID_C_J   = NID_FALSE;
    NID_C_JAL = NID_FALSE;

    NID_C_JR   = NID_FALSE;
    NID_C_JALR = NID_FALSE;
  }
}

// -----------------------------------------------------------------
// ----------------------------- CORE ------------------------------
// -----------------------------------------------------------------

void new_core_state(uint64_t core);
void print_core_state(uint64_t core);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t CORES = 1; // number of cores

uint64_t SYNCHRONIZED_PC = 0; // flag for synchronized program counters across cores

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* eval_core_ir_nid   = (uint64_t*) 0;
uint64_t* eval_core_c_ir_nid = (uint64_t*) 0;

uint64_t* initial_core_pc_nid = (uint64_t*) 0;

uint64_t* state_core_pc_nid = (uint64_t*) 0;
uint64_t* init_core_pc_nid  = (uint64_t*) 0;
uint64_t* next_core_pc_nid  = (uint64_t*) 0;

uint64_t* eval_core_control_flow_nid = (uint64_t*) 0;

uint64_t* eval_core_instruction_control_flow_nid            = (uint64_t*) 0;
uint64_t* eval_core_compressed_instruction_control_flow_nid = (uint64_t*) 0;

uint64_t* eval_core_0_control_flow_nid = (uint64_t*) 0;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------ MODEL GENERATOR ------------------------
// -----------------------------------------------------------------

uint64_t* state_property(uint64_t core, uint64_t* good_nid, uint64_t* bad_nid, char* symbol, char* comment);

void output_model(uint64_t core);

void kernel_combinational(uint64_t* pc_nid, uint64_t* ir_nid,
  uint64_t* control_flow_nid, uint64_t* register_data_flow_nid, uint64_t* memory_data_flow_nid,
  uint64_t* program_break_nid, uint64_t* file_descriptor_nid,
  uint64_t* readable_bytes_nid, uint64_t* read_bytes_nid,
  uint64_t* register_file_nid, uint64_t* memory_nid);
void kernel_sequential(uint64_t core,
  uint64_t* program_break_nid, uint64_t* file_descriptor_nid,
  uint64_t* readable_bytes_nid, uint64_t* read_bytes_nid,
  uint64_t* new_program_break_nid, uint64_t* new_file_descriptor_nid,
  uint64_t* still_reading_active_read_nid, uint64_t* more_than_one_readable_byte_to_read_nid,
  uint64_t* ir_nid, uint64_t* register_file_nid);
void kernel_properties(uint64_t core, uint64_t* ir_nid, uint64_t* read_bytes_nid, uint64_t* register_file_nid);

void rotor_combinational(uint64_t* pc_nid, uint64_t* code_segment_nid, uint64_t* register_file_nid, uint64_t* memory_nid);
void rotor_sequential(uint64_t core, uint64_t* pc_nid, uint64_t* register_file_nid, uint64_t* memory_nid,
  uint64_t* control_flow_nid, uint64_t* register_data_flow_nid, uint64_t* memory_data_flow_nid);
void rotor_properties(uint64_t core, uint64_t* ir_nid, uint64_t* c_ir_nid,
  uint64_t* known_instructions_nid, uint64_t* known_compressed_instructions_nid,
  uint64_t* control_flow_nid, uint64_t* register_file_nid);

void rotor();

uint64_t selfie_model();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t CODE_LOADED = 0; // flag for indicating if code is loaded
uint64_t SYNTHESIZE  = 0; // flag for synthesizing versus analyzing code

char* exit_code_check_option         = (char*) 0;
char* division_by_zero_check_option  = (char*) 0;
char* division_overflow_check_option = (char*) 0;
char* seg_faults_check_option        = (char*) 0;

char* cores_option           = (char*) 0;
char* heap_allowance_option  = (char*) 0;
char* stack_allowance_option = (char*) 0;

uint64_t check_exit_code         = 1;
uint64_t check_division_by_zero  = 1;
uint64_t check_division_overflow = 1;
uint64_t check_seg_faults        = 1;

uint64_t exclude_a0_from_rd = 0;

// ------------------------ GLOBAL VARIABLES -----------------------

char*    model_name = (char*) 0; // name of model file
uint64_t model_fd   = 0;         // file descriptor of open model file

uint64_t w = 0; // number of written characters

uint64_t bad_exit_code = 0; // model for this exit code

uint64_t* prop_is_instruction_known_nid           = (uint64_t*) 0;
uint64_t* prop_illegal_instruction_nid            = (uint64_t*) 0;
uint64_t* prop_illegal_compressed_instruction_nid = (uint64_t*) 0;
uint64_t* prop_next_fetch_unaligned_nid           = (uint64_t*) 0;
uint64_t* prop_next_fetch_seg_faulting_nid        = (uint64_t*) 0;

uint64_t* prop_is_syscall_id_known_nid = (uint64_t*) 0;

uint64_t* prop_bad_exit_code_nid            = (uint64_t*) 0;
uint64_t* prop_exclude_a0_from_rd_nid       = (uint64_t*) 0;
uint64_t* prop_division_by_zero_nid         = (uint64_t*) 0;
uint64_t* prop_signed_division_overflow_nid = (uint64_t*) 0;

uint64_t* prop_load_seg_faulting_nid             = (uint64_t*) 0;
uint64_t* prop_store_seg_faulting_nid            = (uint64_t*) 0;
uint64_t* prop_compressed_load_seg_faulting_nid  = (uint64_t*) 0;
uint64_t* prop_compressed_store_seg_faulting_nid = (uint64_t*) 0;
uint64_t* prop_stack_seg_faulting_nid            = (uint64_t*) 0;

uint64_t* prop_brk_seg_faulting_nid    = (uint64_t*) 0;
uint64_t* prop_openat_seg_faulting_nid = (uint64_t*) 0;
uint64_t* prop_read_seg_faulting_nid   = (uint64_t*) 0;
uint64_t* prop_write_seg_faulting_nid  = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_model_generator() {
  init_model();

  init_interface_sorts();
  init_interface_kernel();

  init_register_file_sorts();

  if (IS64BITTARGET)
    init_memory_sorts(SINGLEWORDSIZEINBITS, SID_SINGLE_WORD, SID_DOUBLE_WORD);
  else
    init_memory_sorts(SINGLEWORDSIZEINBITS, SID_SINGLE_WORD, SID_SINGLE_WORD);

  init_instruction_sorts();
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------------     M O D E L     -----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t are_lines_equal(uint64_t* left_line, uint64_t* right_line) {
  // assert: pointer equivalence iff structural equivalence

  if (get_op(left_line) == get_op(right_line))
    if (get_sid(left_line) == get_sid(right_line))
      if (get_arg1(left_line) == get_arg1(right_line))
        if (get_arg2(left_line) == get_arg2(right_line))
          if (get_arg3(left_line) == get_arg3(right_line))
            return 1;

  return 0;
}

uint64_t* find_equal_line(uint64_t* line) {
  uint64_t* pred_line;

  pred_line = last_line;

  while (pred_line) {
    if (are_lines_equal(pred_line, line))
      return pred_line;

    pred_line = get_pred(pred_line);
  }

  return UNUSED;
}

uint64_t* new_line(char* op, uint64_t* sid, uint64_t* arg1, uint64_t* arg2, uint64_t* arg3, char* comment) {
  uint64_t* new_line;
  uint64_t* old_line;

  // invariant: pointer equivalence iff structural equivalence

  if (unused_line)
    new_line = unused_line;
  else
    new_line = allocate_line();

  set_nid(new_line, 0);
  set_op(new_line, op);
  set_sid(new_line, sid);
  set_arg1(new_line, arg1);
  set_arg2(new_line, arg2);
  set_arg3(new_line, arg3);
  set_comment(new_line, comment);
  set_state(new_line, 0);
  set_step(new_line, -1);
  set_reuse(new_line, 0);

  if (reuse_lines)
    old_line = find_equal_line(new_line);
  else
    old_line = (uint64_t*) 0;

  if (old_line) {
    unused_line = new_line;

    set_reuse(old_line, get_reuse(old_line) + 1);

    // invariant: pointer equivalence iff structural equivalence

    return old_line;
  } else {
    unused_line = UNUSED;

    set_pred(new_line, last_line);

    last_line = new_line;

    number_of_lines = number_of_lines + 1;

    // invariant: pointer equivalence iff structural equivalence

    return new_line;
  }
}

uint64_t* new_bitvec(uint64_t size_in_bits, char* comment) {
  return new_line(OP_SORT, UNUSED, (uint64_t*) BITVEC, (uint64_t*) size_in_bits, UNUSED, comment);
}

uint64_t* new_array(uint64_t* size_sid, uint64_t* element_sid, char* comment) {
  return new_line(OP_SORT, UNUSED, (uint64_t*) ARRAY, size_sid, element_sid, comment);
}

uint64_t* new_constant(char* op, uint64_t* sid, uint64_t constant, uint64_t digits, char* comment) {
  return new_line(op, sid, (uint64_t*) constant, (uint64_t*) digits, UNUSED, comment);
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

uint64_t* new_unary_boolean(char* op, uint64_t* value_nid, char* comment) {
  return new_unary(op, SID_BOOLEAN, value_nid, comment);
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

// -----------------------------------------------------------------
// ---------------------------- SYNTAX -----------------------------
// -----------------------------------------------------------------

void print_nid(uint64_t nid, uint64_t* line) {
  set_nid(line, nid);
  w = w + dprintf(output_fd, "%lu", nid);
}

uint64_t print_sort(uint64_t nid, uint64_t* line) {
  if ((char*) get_arg1(line) == ARRAY) {
    nid = print_referenced_line(nid, get_arg2(line));
    nid = print_referenced_line(nid, get_arg3(line));
  }
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s", OP_SORT);
  if ((char*) get_arg1(line) == BITVEC)
    w = w + dprintf(output_fd, " %s %lu", BITVEC, eval_bitvec_size(line));
  else
    // assert: theory of bitvector arrays
    w = w + dprintf(output_fd, " %s %lu %lu", ARRAY, get_nid(get_arg2(line)), get_nid(get_arg3(line)));
  return nid;
}

uint64_t print_constant(uint64_t nid, uint64_t* line) {
  uint64_t value;
  nid = print_referenced_line(nid, get_sid(line));
  print_nid(nid, line);
  value = eval_constant_value(line);
  if (get_op(line) == OP_CONSTD) {
    if (value == 0)
      w = w + dprintf(output_fd, " zero %lu", get_nid(get_sid(line)));
    else if (value == 1)
      w = w + dprintf(output_fd, " one %lu", get_nid(get_sid(line)));
    else
      w = w + dprintf(output_fd, " %s %lu %ld", get_op(line), get_nid(get_sid(line)), value);
  } else if (get_op(line) == OP_CONST)
    w = w + dprintf(output_fd, " %s %lu %s", get_op(line), get_nid(get_sid(line)),
      itoa(value, string_buffer, 2, 0, eval_constant_digits(line)));
  else
    // assert: get_op(line) == OP_CONSTH
    w = w + dprintf(output_fd, " %s %lu %s", get_op(line), get_nid(get_sid(line)),
      itoa(value, string_buffer, 16, 0, eval_constant_digits(line)));
  return nid;
}

uint64_t print_input(uint64_t nid, uint64_t* line) {
  nid = print_referenced_line(nid, get_sid(line));
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s %lu %s", get_op(line), get_nid(get_sid(line)), (char*) get_arg1(line));
  return nid;
}

uint64_t print_ext(uint64_t nid, uint64_t* line) {
  nid = print_referenced_line(nid, get_sid(line));
  nid = print_referenced_line(nid, get_arg1(line));
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s %lu %lu %lu",
    get_op(line), get_nid(get_sid(line)), get_nid(get_arg1(line)), eval_ext_w(line));
  return nid;
}

uint64_t print_slice(uint64_t nid, uint64_t* line) {
  nid = print_referenced_line(nid, get_sid(line));
  nid = print_referenced_line(nid, get_arg1(line));
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s %lu %lu %lu %lu",
    OP_SLICE, get_nid(get_sid(line)), get_nid(get_arg1(line)), eval_slice_u(line), eval_slice_l(line));
  return nid;
}

uint64_t print_unary_op(uint64_t nid, uint64_t* line) {
  nid = print_referenced_line(nid, get_sid(line));
  nid = print_referenced_line(nid, get_arg1(line));
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s %lu %lu",
    get_op(line), get_nid(get_sid(line)), get_nid(get_arg1(line)));
  return nid;
}

uint64_t print_binary_op(uint64_t nid, uint64_t* line) {
  nid = print_referenced_line(nid, get_sid(line));
  nid = print_referenced_line(nid, get_arg1(line));
  nid = print_referenced_line(nid, get_arg2(line));
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s %lu %lu %lu",
    get_op(line), get_nid(get_sid(line)), get_nid(get_arg1(line)), get_nid(get_arg2(line)));
  return nid;
}

uint64_t print_ternary_op(uint64_t nid, uint64_t* line) {
  nid = print_referenced_line(nid, get_sid(line));
  nid = print_referenced_line(nid, get_arg1(line));
  nid = print_referenced_line(nid, get_arg2(line));
  nid = print_referenced_line(nid, get_arg3(line));
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s %lu %lu %lu %lu",
    get_op(line), get_nid(get_sid(line)), get_nid(get_arg1(line)), get_nid(get_arg2(line)), get_nid(get_arg3(line)));
  return nid;
}

uint64_t print_constraint(uint64_t nid, uint64_t* line) {
  nid = print_referenced_line(nid, get_arg1(line));
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s %lu %s", get_op(line), get_nid(get_arg1(line)), (char*) get_arg2(line));
  return nid;
}

void print_comment(uint64_t* line) {
  if (get_comment(line) != NOCOMMENT) {
    if (get_reuse(line) > 0)
      w = w + dprintf(output_fd, " ; %s [reused %lu time(s)]", get_comment(line), get_reuse(line));
    else
      w = w + dprintf(output_fd, " ; %s", get_comment(line));
  } else if (get_reuse(line) > 0)
    w = w + dprintf(output_fd, " ; [reused %lu time(s)]", get_reuse(line));
  w = w + dprintf(output_fd, "\n");
}

uint64_t is_constant_op(char* op) {
  if (op == OP_CONSTD)
    return 1;
  else if (op == OP_CONST)
    return 1;
  else if (op == OP_CONSTH)
    return 1;
  else
    return 0;
}

uint64_t is_input_op(char* op) {
  if (op == OP_INPUT)
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
  else if (op == OP_NEG)
    return 1;
  else
    return 0;
}

uint64_t print_referenced_line(uint64_t nid, uint64_t* line) {
  char* op;

  op = get_op(line);

  if (get_nid(line) > 0)
    // print lines only once
    return nid;
  else if (op == OP_SORT)
    nid = print_sort(nid, line);
  else if (is_constant_op(op))
    nid = print_constant(nid, line);
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

void print_line(uint64_t* line) {
  if (get_nid(line) > 0)
    // print lines only once but mention reuse at top level
    w = w + dprintf(output_fd, "; skipping line reusing %lu\n", get_nid(line));
  else
    current_nid = print_referenced_line(current_nid, line);
}

void print_break() {
  uint64_t remainder;

  if (current_nid > 10) {
    remainder = current_nid % ten_to_the_power_of(log_ten(current_nid));

    if (remainder > 0) {
      if (remainder > 10)
        current_nid = current_nid -
          remainder % ten_to_the_power_of(log_ten(remainder)) +
          ten_to_the_power_of(log_ten(remainder));
      else
        current_nid = current_nid - remainder + 10;
    }
  } else
    current_nid = 10;

  w = w + dprintf(output_fd, "\n");
}

void print_break_line(uint64_t* line) {
  if (line != UNUSED) {
    print_break();
    print_line(line);
  }
}

void print_break_comment(char* comment) {
  print_break();
  w = w + dprintf(output_fd, "; %s\n\n", comment);
}

void print_break_comment_line(char* comment, uint64_t* line) {
  if (line != UNUSED) {
    print_break_comment(comment);
    print_line(line);
  }
}

void print_aligned_break_comment(char* comment, uint64_t alignment) {
  print_break_comment(comment);

  if (log_ten(current_nid) < alignment)
    current_nid = ten_to_the_power_of(alignment);
}

char* format_comment(char* comment, uint64_t value) {
  sprintf(string_buffer, comment, value);
  return string_copy(string_buffer);
}

char* format_binary(uint64_t value, uint64_t alignment) {
  return string_copy(itoa(value, string_buffer, 2, 0, alignment));
}

char* format_decimal(uint64_t value) {
  return format_comment("%ld", value);
}

char* format_hexadecimal(uint64_t value) {
  return format_comment("%lX", value);
}

char* format_comment_binary(char* comment, uint64_t value) {
  sprintf(string_buffer, "%s %s", comment, format_binary(value, 0));
  return string_copy(string_buffer);
}

// -----------------------------------------------------------------
// -------------------------- SEMANTICS ----------------------------
// -----------------------------------------------------------------

uint64_t eval_bitvec_size(uint64_t* line) {
  uint64_t size;

  if ((char*) get_arg1(line) == BITVEC) {
    size = (uint64_t) get_arg2(line);

    if (size > 0)
      if (size <= SIZEOFUINT64INBITS)
        return size;

    if (size == 2 * WORDSIZEINBITS)
      // TODO: tolerating but not yet supporting double machine word bitvectors
      return size;

    printf("%s: evaluate unsupported %lu-bit bitvector error\n", selfie_name, size);
  } else
    printf("%s: evaluate size of non-bitvector error\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

void fit_bitvec_sort(uint64_t value, uint64_t* sid) {
  uint64_t size;

  size = eval_bitvec_size(sid);

  if (size >= SIZEOFUINT64INBITS)
    // TODO: support of bitvectors larger than machine words
    return;
  else if (value < two_to_the_power_of(size))
    return;

  printf("%s: %lu does not fit %lu-bit bitvector\n", selfie_name, value, size);

  exit(EXITCODE_SYSTEMERROR);
}

void signed_fit_bitvec_sort(uint64_t value, uint64_t* sid) {
  uint64_t size;

  size = eval_bitvec_size(sid);

  if (size >= SIZEOFUINT64INBITS)
    // TODO: support of bitvectors larger than machine words
    return;
  else if (value < two_to_the_power_of(size - 1))
    return;
  else if (value >= -two_to_the_power_of(size - 1))
    return;

  printf("%s: %ld does not fit %lu-bit bitvector\n", selfie_name, value, size);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_array_size(uint64_t* line) {
  if ((char*) get_arg1(line) == ARRAY)
    return eval_bitvec_size(get_arg2(line));

  printf("%s: evaluate size of non-array error\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_array_element_size(uint64_t* line) {
  if ((char*) get_arg1(line) == ARRAY)
    return eval_bitvec_size(get_arg3(line));

  printf("%s: evaluate element size of non-array error\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

void fit_array_sort(uint64_t index, uint64_t value, uint64_t* sid) {
  if ((char*) get_arg1(sid) == ARRAY) {
    fit_bitvec_sort(index, get_arg2(sid));
    fit_bitvec_sort(value, get_arg3(sid));

    return;
  }

  printf("%s: fit %lu @ 0x%lX non-array error\n", selfie_name, value, index);

  exit(EXITCODE_SYSTEMERROR);
}

void match_sorts(uint64_t* sid1, uint64_t* sid2, char* comment) {
  if (sid1 == sid2)
    return;

  printf("%s: %s sort mismatch error\n", selfie_name, comment);

  exit(EXITCODE_SYSTEMERROR);
}

void write_value(uint64_t index, uint64_t value, uint64_t* array_nid) {
  uint64_t* array;

  fit_array_sort(index, value, get_sid(array_nid));

  array = (uint64_t*) get_state(array_nid);

  if (array != (uint64_t*) 0) {
    *(array + index) = value;

    return;
  }

  printf("%s: write uninitialized array error\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_constant_value(uint64_t* line) {
  uint64_t* sid;
  uint64_t value;

  if (get_step(line) == (uint64_t) -1) {
    sid   = get_sid(line);
    value = (uint64_t) get_arg1(line);

    if (get_op(line) == OP_CONSTD) {
      if (value <= 1)
        fit_bitvec_sort(value, sid);
      else {
        signed_fit_bitvec_sort(value, sid);

        value = sign_shrink(value, eval_bitvec_size(sid));
      }
    } else
      fit_bitvec_sort(value, sid);

    set_state(line, value);
  } else
    value = get_state(line);

  set_step(line, current_step);

  return value;
}

uint64_t eval_constant_digits(uint64_t* line) {
  return (uint64_t) get_arg2(line);
}

uint64_t eval_ext_w(uint64_t* line) {
  return (uint64_t) get_arg2(line);
}

uint64_t eval_slice_u(uint64_t* line) {
  return (uint64_t) get_arg2(line);
}

uint64_t eval_slice_l(uint64_t* line) {
  return (uint64_t) get_arg3(line);
}

uint64_t get_cached_state(uint64_t* line) {
  if (get_op(line) == OP_STATE)
    if ((char*) get_arg1(get_sid(line)) == ARRAY)
      return (uint64_t) line;

  return get_state(line);
}

uint64_t eval_input(uint64_t* line) {
  char* op;

  op = get_op(line);

  if (op == OP_STATE)
    return get_cached_state(line);

  printf("%s: unknown line operator %s\n", selfie_name, op);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_ext(uint64_t* line) {
  uint64_t* value_nid;
  uint64_t n;
  uint64_t w;

  value_nid = get_arg1(line);

  n = eval_bitvec_size(get_sid(value_nid));

  w = eval_ext_w(line);

  if (eval_bitvec_size(get_sid(line)) == n + w) {
    if (get_op(line) == OP_SEXT)
      set_state(line, sign_shrink(sign_extend(eval_line(value_nid), n), n + w));
    else
      // assert: unsigned extension
      set_state(line, eval_line(value_nid));

    set_step(line, current_step);

    return get_state(line);
  }

  printf("%s: ext sort error: n==%lu, w==%lu, m==%lu\n", selfie_name,
    n, w, eval_bitvec_size(get_sid(line)));

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_slice(uint64_t* line) {
  uint64_t* value_nid;
  uint64_t n;
  uint64_t u;
  uint64_t l;

  value_nid = get_arg1(line);

  n = eval_bitvec_size(get_sid(value_nid));

  u = eval_slice_u(line);
  l = eval_slice_l(line);

  if (n > u)
    if (u >= l)
      if (eval_bitvec_size(get_sid(line)) == u - l + 1) {
        set_state(line, get_bits(eval_line(value_nid), l, u - l + 1));

        set_step(line, current_step);

        return get_state(line);
      }

  printf("%s: slice sort error: n==%lu, u==%lu, l==%lu, m==%lu\n", selfie_name,
    n, u, l, eval_bitvec_size(get_sid(line)));

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_unary_op(uint64_t* line) {
  char* op;
  uint64_t* value_nid;
  uint64_t size;
  uint64_t value;

  op = get_op(line);

  size = eval_bitvec_size(get_sid(line));

  value_nid = get_arg1(line);

  if (op == OP_DEC) {
    match_sorts(get_sid(line), get_sid(value_nid), "dec operand");

    value = sign_extend(eval_line(value_nid), size);

    set_state(line, sign_shrink(value - 1, size));

    set_step(line, current_step);

    return get_state(line);
  }

  printf("%s: unknown unary operator %s\n", selfie_name, op);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_write(uint64_t* line) {
  uint64_t* array_nid;
  uint64_t index;
  uint64_t value;

  if ((char*) get_arg1(get_sid(line)) == ARRAY) {
    array_nid = get_arg1(line);

    match_sorts(get_sid(line), get_sid(array_nid), "write array");

    array_nid = (uint64_t*) eval_line(array_nid);

    match_sorts(get_sid(get_arg2(line)), get_arg2(get_sid(array_nid)), "write array size");
    match_sorts(get_sid(get_arg3(line)), get_arg3(get_sid(array_nid)), "write array element");

    index = eval_line(get_arg2(line));
    value = eval_line(get_arg3(line));

    write_value(index, value, array_nid);

    set_state(line, (uint64_t) array_nid);

    set_step(line, current_step);

    return get_state(line);
  }

  printf("%s: write non-array error\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_binary_op(uint64_t* line) {
  char* op;
  uint64_t* left_nid;
  uint64_t* right_nid;
  uint64_t size;
  uint64_t left_value;
  uint64_t right_value;
  uint64_t* state_nid;
  uint64_t* value_nid;

  op = get_op(line);

  left_nid  = get_arg1(line);
  right_nid = get_arg2(line);

  if (op == OP_SUB) {
    size = eval_bitvec_size(get_sid(line));

    match_sorts(get_sid(line), get_sid(left_nid), "sub left operand");
    match_sorts(get_sid(line), get_sid(right_nid), "sub right operand");

    left_value  = sign_extend(eval_line(left_nid), size);
    right_value = sign_extend(eval_line(right_nid), size);

    set_state(line, sign_shrink(left_value - right_value, size));

    set_step(line, current_step);

    return get_state(line);
  } else if (op == OP_INIT) {
    state_nid = left_nid;

    if (get_op(state_nid) != OP_STATE) {
      printf("%s: init %s error\n", selfie_name, get_op(state_nid));

      exit(EXITCODE_SYSTEMERROR);
    }

    match_sorts(get_sid(line), get_sid(state_nid), "init state");

    value_nid = right_nid;

    if ((char*) get_arg1(get_sid(state_nid)) == BITVEC) {
      match_sorts(get_sid(state_nid), get_sid(value_nid), "init bitvec");

      set_state(state_nid, eval_line(value_nid));

      set_step(state_nid, current_step);
    } else {
      // assert: sid of state line is ARRAY
      if ((char*) get_arg1(get_sid(value_nid)) == BITVEC) {
        match_sorts(get_arg3(get_sid(state_nid)), get_sid(value_nid), "init array element");

        if (eval_line(value_nid) != 0) {
          printf("%s: init non-zero array element error\n", selfie_name);

          exit(EXITCODE_SYSTEMERROR);
        }

        // assert: element size of state address space <= sizeof(uint64_t)

        set_state(state_nid, (uint64_t) zmalloc(two_to_the_power_of(eval_array_size(get_sid(state_nid))) * sizeof(uint64_t)));

        set_step(state_nid, current_step);
      } else {
        // assert: sid of value line is ARRAY
        match_sorts(get_sid(state_nid), get_sid(value_nid), "init array");

        value_nid = (uint64_t*) eval_line(value_nid);

        if (get_state(state_nid) != get_state(value_nid)) {
          set_state(state_nid, get_state(value_nid));

          set_step(state_nid, current_step);

          // TODO: reinitialize state
          set_state(value_nid, 0);
        }
      }
    }

    set_step(line, current_step);

    // assert: return value is never used
    return (uint64_t) state_nid;
  }

  printf("%s: unknown binary operator %s\n", selfie_name, op);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_line(uint64_t* line) {
  char* op;

  op = get_op(line);

  if (get_step(line) == current_step)
    return get_cached_state(line);
  else if (is_constant_op(op))
    return eval_constant_value(line);
  else if (is_input_op(op))
    return eval_input(line);
  else if (op == OP_SEXT)
    return eval_ext(line);
  else if (op == OP_UEXT)
    return eval_ext(line);
  else if (op == OP_SLICE)
    return eval_slice(line);
  else if (is_unary_op(op))
    return eval_unary_op(line);
  else if (op == OP_WRITE)
    return eval_write(line);
  else
    return eval_binary_op(line);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

void print_interface_sorts() {
  print_line(SID_BOOLEAN);

  print_line(SID_BYTE);
  print_line(SID_HALF_WORD);
  print_line(SID_SINGLE_WORD);
  print_line(SID_DOUBLE_WORD);

  print_break_comment("machine constants");

  print_line(NID_FALSE);
  print_line(NID_TRUE);

  print_break();

  print_line(NID_BYTE_0);
  print_line(NID_BYTE_3);

  print_break();

  print_line(NID_HALF_WORD_0);
  print_line(NID_HALF_WORD_1);

  print_break();

  print_line(NID_SINGLE_WORD_0);
  print_line(NID_SINGLE_WORD_1);
  print_line(NID_SINGLE_WORD_2);
  print_line(NID_SINGLE_WORD_3);
  print_line(NID_SINGLE_WORD_4);
  print_line(NID_SINGLE_WORD_5);
  print_line(NID_SINGLE_WORD_6);
  print_line(NID_SINGLE_WORD_7);
  print_line(NID_SINGLE_WORD_8);

  print_line(NID_SINGLE_WORD_MINUS_1);

  print_break();

  print_line(NID_DOUBLE_WORD_0);
  print_line(NID_DOUBLE_WORD_1);
  print_line(NID_DOUBLE_WORD_2);
  print_line(NID_DOUBLE_WORD_3);
  print_line(NID_DOUBLE_WORD_4);
  print_line(NID_DOUBLE_WORD_5);
  print_line(NID_DOUBLE_WORD_6);
  print_line(NID_DOUBLE_WORD_7);
  print_line(NID_DOUBLE_WORD_8);

  print_line(NID_DOUBLE_WORD_MINUS_1);
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

void print_interface_kernel() {
  print_break_comment("kernel interface");

  print_line(NID_EXIT_SYSCALL_ID);
  print_line(NID_BRK_SYSCALL_ID);
  print_line(NID_OPENAT_SYSCALL_ID);
  print_line(NID_READ_SYSCALL_ID);
  print_line(NID_WRITE_SYSCALL_ID);
}

void new_kernel_state(uint64_t core, uint64_t bytes_to_read) {
  if (core == 0) {
    state_program_break_nid = new_input(OP_STATE, SID_VIRTUAL_ADDRESS, "program-break", "program break");
    init_program_break_nid  = new_binary(OP_INIT, SID_VIRTUAL_ADDRESS, state_program_break_nid,
      NID_HEAP_START, "initial program break is start of heap segment");

    state_file_descriptor_nid = new_input(OP_STATE, SID_MACHINE_WORD, "file-descriptor", "file descriptor");
    init_file_descriptor_nid  = new_binary(OP_INIT, SID_MACHINE_WORD, state_file_descriptor_nid,
      NID_MACHINE_WORD_0, "initial file descriptor is zero");

    next_program_break_nid   = state_program_break_nid;
    next_file_descriptor_nid = state_file_descriptor_nid;
  } else {
    next_program_break_nid   = eval_program_break_nid;
    next_file_descriptor_nid = eval_file_descriptor_nid;
  }

  param_readable_bytes_nid = new_constant(OP_CONSTD, SID_MACHINE_WORD,
    bytes_to_read, 0, "read capacity in bytes");

  state_readable_bytes_nid = new_input(OP_STATE, SID_MACHINE_WORD,
    format_comment("core-%lu-readable-bytes", core), "readable bytes");
  init_readable_bytes_nid  = new_binary(OP_INIT, SID_MACHINE_WORD, state_readable_bytes_nid,
    param_readable_bytes_nid, "number of readable bytes");

  state_read_bytes_nid = new_input(OP_STATE, SID_MACHINE_WORD,
    format_comment("core-%lu-read-bytes", core), "bytes read in active read system call");
  init_read_bytes_nid  = new_binary(OP_INIT, SID_MACHINE_WORD, state_read_bytes_nid,
    NID_MACHINE_WORD_0, "initially zero read bytes");
}

void print_kernel_state(uint64_t core) {
  if (core == 0) {
    print_break_comment_line("system kernel state", init_program_break_nid);

    print_break_line(init_file_descriptor_nid);
  }

  print_break_comment_line(format_comment("core-%lu kernel state", core), init_readable_bytes_nid);

  print_break_line(init_read_bytes_nid);
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
  print_break_comment("register sorts");

  print_line(SID_REGISTER_ADDRESS);
  print_line(SID_REGISTER_STATE);
}

uint64_t* load_register_value(uint64_t* reg_nid, char* comment, uint64_t* register_file_nid) {
  return new_binary(OP_READ, SID_MACHINE_WORD, register_file_nid, reg_nid, comment);
}

uint64_t* store_register_value(uint64_t* reg_nid, uint64_t* value_nid, char* comment, uint64_t* register_file_nid) {
  return new_ternary(OP_WRITE, SID_REGISTER_STATE, register_file_nid, reg_nid, value_nid, comment);
}

uint64_t* get_5_bit_shamt(uint64_t* value_nid) {
  return new_ext(OP_UEXT, SID_SINGLE_WORD,
    new_slice(SID_5_BIT_IMM, value_nid, 4, 0, "get 5-bit shamt"),
    SINGLEWORDSIZEINBITS - 5,
    "unsigned-extend 5-bit shamt");
}

uint64_t* get_shamt(uint64_t* value_nid) {
  if (IS64BITTARGET)
    return new_ext(OP_UEXT, SID_MACHINE_WORD,
      new_slice(SID_6_BIT_IMM, value_nid, 5, 0, "get 6-bit shamt"),
      WORDSIZEINBITS - 6,
      "unsigned-extend 6-bit shamt");
  else
    return get_5_bit_shamt(value_nid);
}

void new_register_file_state(uint64_t core) {
  uint64_t  reg;
  uint64_t* reg_nid;
  uint64_t  value;
  uint64_t* value_nid;

  if (SYNCHRONIZED_REGISTERS) {
    if (core > 0)
      return;
  } else if (SHARED_REGISTERS)
    if (core > 0)
      return;

  state_register_file_nid = new_input(OP_STATE, SID_REGISTER_STATE,
    format_comment("core-%lu-zeroed-register-file", core), "zeroed register file");

  init_zeroed_register_file_nid = new_binary(OP_INIT, SID_REGISTER_STATE,
    state_register_file_nid, NID_MACHINE_WORD_0, "zeroing register file");

  if (CODE_LOADED == 0)
    initial_register_file_nid =
      store_register_value(NID_SP,
        cast_virtual_address_to_machine_word(
          new_unary(OP_DEC, SID_VIRTUAL_ADDRESS, NID_STACK_END, "end of stack segment - 1")),
        "write initial sp value",
        state_register_file_nid);
  else {
    initial_register_file_nid = state_register_file_nid;

    reg = 0;

    while (reg < 32) {
      value = *(get_regs(current_context) + reg);

      if (value != 0) {
        // skipping zero as initial value
        value_nid = new_constant(OP_CONSTH, SID_MACHINE_WORD,
          value,
          0,
          format_comment("initial register value 0x%lX", value));
        // for reuse creating register address exactly as above in register sorts
        reg_nid = new_constant(OP_CONST, SID_REGISTER_ADDRESS,
          reg,
          5,
          format_comment("%s", *(REGISTERS + reg)));
        initial_register_file_nid =
          store_register_value(reg_nid, value_nid,
            "write initial register value", initial_register_file_nid);
      }

      reg = reg + 1;
    }
  }

  if (initial_register_file_nid != state_register_file_nid) {
    eval_line(init_zeroed_register_file_nid);

    next_zeroed_register_file_nid = new_binary(OP_NEXT, SID_REGISTER_STATE,
      state_register_file_nid, state_register_file_nid, "read-only zeroed register file");

    state_register_file_nid = new_input(OP_STATE, SID_REGISTER_STATE,
      format_comment("core-%lu-initialized-register-file", core), "initialized register file");

    init_register_file_nid = new_binary(OP_INIT, SID_REGISTER_STATE,
      state_register_file_nid, initial_register_file_nid, "initializing registers");
  } else
    init_register_file_nid = init_zeroed_register_file_nid;

  eval_line(init_register_file_nid);
}

void print_register_file_state(uint64_t core) {
  if (SYNCHRONIZED_REGISTERS) {
    if (core > 0)
      return;
  } else if (SHARED_REGISTERS)
    if (core > 0)
      return;

  print_break_comment("zeroed register file");

  print_line(init_zeroed_register_file_nid);

  if (init_register_file_nid != init_zeroed_register_file_nid) {
    print_line(next_zeroed_register_file_nid);

    if (CODE_LOADED == 0)
      print_break_comment("initializing sp");
    else
      print_aligned_break_comment("initializing registers", log_ten(32 * 3 + 1) + 1);

    print_line(initial_register_file_nid);

    print_break_comment("initialized register file");

    print_line(init_register_file_nid);
  }
}

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void print_memory_sorts() {
  print_break_comment("memory sorts");

  print_line(SID_VIRTUAL_ADDRESS);

  print_break();

  print_line(SID_CODE_ADDRESS);
  print_line(SID_CODE_STATE);

  print_break();

  print_line(SID_MEMORY_ADDRESS);
  print_line(SID_MEMORY_STATE);
}

void new_segmentation() {
  uint64_t stack_end;
  uint64_t low_stack_address_space;
  uint64_t up_stack_address_space;

  NID_CODE_START = new_constant(OP_CONSTH, SID_VIRTUAL_ADDRESS,
    code_start,
    round_up(VIRTUAL_ADDRESS_SPACE / 4, 4),
    format_comment("start of code segment @ 0x%lX", code_start));

  NID_CODE_END = new_constant(OP_CONSTH, SID_VIRTUAL_ADDRESS,
    code_start + code_size,
    round_up(VIRTUAL_ADDRESS_SPACE / 4, 4),
    format_comment("end of code segment accommodating at least %lu instructions", code_size / INSTRUCTIONSIZE));

  // assert: data_start >= code_start + code_size > 0

  NID_DATA_START = new_constant(OP_CONSTH, SID_VIRTUAL_ADDRESS,
    data_start,
    round_up(VIRTUAL_ADDRESS_SPACE / 4, 4),
    format_comment("start of data segment @ 0x%lX", data_start));

  NID_DATA_END = new_constant(OP_CONSTH, SID_VIRTUAL_ADDRESS,
    data_start + data_size,
    round_up(VIRTUAL_ADDRESS_SPACE / 4, 4),
    format_comment("end of data segment accommodating %lu bytes", data_size));

  // assert: heap_start >= data_start + data_size > 0

  NID_HEAP_START = new_constant(OP_CONSTH, SID_VIRTUAL_ADDRESS,
    heap_start,
    round_up(VIRTUAL_ADDRESS_SPACE / 4, 4),
    format_comment("start of heap segment @ 0x%lX", heap_start));

  NID_HEAP_END = new_constant(OP_CONSTH, SID_VIRTUAL_ADDRESS,
    heap_start + heap_size,
    round_up(VIRTUAL_ADDRESS_SPACE / 4, 4),
    format_comment("static end of heap segment accommodating %lu bytes", heap_size));

  // assert: stack_start >= heap_start + heap_size > 0

  NID_STACK_START = new_constant(OP_CONSTH, SID_VIRTUAL_ADDRESS,
    stack_start,
    round_up(VIRTUAL_ADDRESS_SPACE / 4, 4),
    format_comment("static start of stack segment @ 0x%lX", stack_start));

  stack_end = stack_start + stack_size;

  if (stack_start < stack_end) {
    // no stack end overflow here
    low_stack_address_space = log_two(stack_end);
    up_stack_address_space  = low_stack_address_space;

    if (stack_end > two_to_the_power_of(low_stack_address_space))
      up_stack_address_space = up_stack_address_space + 1;

    if (up_stack_address_space < VIRTUAL_ADDRESS_SPACE)
      // no stack end overflow in btor2
      NID_STACK_END = new_constant(OP_CONSTH, SID_VIRTUAL_ADDRESS,
        stack_end,
        round_up(VIRTUAL_ADDRESS_SPACE / 4, 4),
        format_comment("end of stack segment accommodating %lu bytes", stack_size));
    else if (up_stack_address_space == VIRTUAL_ADDRESS_SPACE) {
      if (low_stack_address_space < up_stack_address_space)
        // still no stack end overflow in btor2
        NID_STACK_END = new_constant(OP_CONSTH, SID_VIRTUAL_ADDRESS,
          stack_end,
          round_up(VIRTUAL_ADDRESS_SPACE / 4, 4),
          format_comment("end of stack segment accommodating %lu bytes", stack_size));
      else
        // stack end overflow in btor2, force wrap-around
        NID_STACK_END = new_constant(OP_CONSTH, SID_VIRTUAL_ADDRESS,
          0,
          round_up(VIRTUAL_ADDRESS_SPACE / 4, 4),
          format_comment("end of stack segment accommodating %lu bytes", stack_size));
    } else {
      printf("%s: end of stack segment at 0x%lX does not fit %lu-bit virtual address space\n", selfie_name,
        stack_end,
        VIRTUAL_ADDRESS_SPACE);

      exit(EXITCODE_SYSTEMERROR);
    }
  } else if (stack_end == 0) {
    // stack end overflow here
    if (VIRTUAL_ADDRESS_SPACE == WORDSIZEINBITS)
      // ok if virtual address space same as address space here, force wrap-around
      NID_STACK_END = new_constant(OP_CONSTH, SID_VIRTUAL_ADDRESS,
        0,
        round_up(VIRTUAL_ADDRESS_SPACE / 4, 4),
        format_comment("end of stack segment accommodating %lu bytes", stack_size));
    else {
      printf("%s: end of stack segment wrapped around to 0x0\n", selfie_name);

      exit(EXITCODE_SYSTEMERROR);
    }
  } else {
    printf("%s: end of stack segment wrapped around to 0x%lX\n", selfie_name, stack_end);

    exit(EXITCODE_SYSTEMERROR);
  }
}

uint64_t* is_block_in_segment(uint64_t* block_start_nid, uint64_t* block_end_nid,
  uint64_t* segment_start_nid, uint64_t* segment_end_nid) {
  // assert: block and segment start <= end
  return new_binary_boolean(OP_AND,
    new_binary_boolean(OP_UGTE,
      block_start_nid,
      segment_start_nid,
      "virtual address of start of block >= start of segment?"),
    new_binary_boolean(OP_ULT,
      block_end_nid,
      segment_end_nid,
      "virtual address of end of block < end of segment?"),
    "block in segment?");
}

uint64_t* is_block_in_code_segment(uint64_t* start_nid, uint64_t* end_nid) {
  // assert: start <= end
  return is_block_in_segment(start_nid, end_nid, NID_CODE_START, NID_CODE_END);
}

uint64_t* is_block_in_data_segment(uint64_t* start_nid, uint64_t* end_nid) {
  // assert: start <= end
  return is_block_in_segment(start_nid, end_nid, NID_DATA_START, NID_DATA_END);
}

uint64_t* is_block_in_heap_segment(uint64_t* start_nid, uint64_t* end_nid) {
  // assert: start <= end
  return is_block_in_segment(start_nid, end_nid, NID_HEAP_START, NID_HEAP_END);
}

uint64_t* is_block_in_stack_segment(uint64_t* start_nid, uint64_t* end_nid) {
  // assert: start <= end
  if ((uint64_t) get_arg1(NID_STACK_END) > 0)
    return is_block_in_segment(start_nid, end_nid, NID_STACK_START, NID_STACK_END);
  else
    // comparing with end of stack segment is unnecessary since end wrapped around to zero
    return new_binary_boolean(OP_UGTE,
      start_nid,
      NID_STACK_START,
      "virtual address of start of block >= start of stack segment?");
}

void print_segmentation() {
  print_break_comment("segmentation");

  print_line(NID_CODE_START);
  print_line(NID_CODE_END);

  print_line(NID_DATA_START);
  print_line(NID_DATA_END);

  print_line(NID_HEAP_START);
  print_line(NID_HEAP_END);

  print_line(NID_STACK_START);
  print_line(NID_STACK_END);
}

void new_code_segment(uint64_t core) {
  uint64_t  number_of_hex_digits;
  uint64_t  code_size_in_instructions;
  uint64_t* vaddr_nid;
  uint64_t* ir_nid;

  if (core > 0) {
    if (SYNTHESIZE)
      state_code_segment_nid = new_input(OP_STATE, SID_CODE_STATE,
        format_comment("core-%lu-code-segment", core), "code segment");

    return;
  }

  if (CODE_LOADED == 0)
    state_code_segment_nid = new_input(OP_STATE, SID_CODE_STATE,
      format_comment("core-%lu-code-segment", core), "code segment");
  else {
    state_code_segment_nid = new_input(OP_STATE, SID_CODE_STATE,
      "code-segment", "code segment");

    init_zeroed_code_segment_nid = new_binary(OP_INIT, SID_CODE_STATE,
      state_code_segment_nid, NID_CODE_WORD_0, "zeroing code segment");

    eval_line(init_zeroed_code_segment_nid);

    number_of_hex_digits = round_up(VIRTUAL_ADDRESS_SPACE, 4) / 4;

    initial_code_segment_nid = state_code_segment_nid;

    code_size_in_instructions = code_size / INSTRUCTIONSIZE;

    if (code_size % INSTRUCTIONSIZE > 0)
      code_size_in_instructions = code_size_in_instructions + 1;

    initial_code_segment_nids = zmalloc(code_size_in_instructions * sizeof(uint64_t*));

    reuse_lines = 0; // TODO: turn on via console argument

    pc = code_start;

    while (pc < code_start + code_size) {
      fetch();

      if (ir != 0) {
        // skipping zero as instruction
        vaddr_nid = new_constant(OP_CONSTH, SID_VIRTUAL_ADDRESS,
          pc,
          number_of_hex_digits,
          format_comment("vaddr 0x%lX", pc));
        ir_nid = new_constant(OP_CONST, SID_INSTRUCTION_WORD,
          ir,
          32,
          format_comment("code 0x%04lX", ir));
        initial_code_segment_nid =
          store_single_word_at_virtual_address(vaddr_nid, ir_nid, initial_code_segment_nid);

        eval_line(initial_code_segment_nid);

        // for printing initial code segment iteratively to avoid stack overflow in recursion
        *(initial_code_segment_nids + (pc - code_start) / INSTRUCTIONSIZE) = (uint64_t) initial_code_segment_nid;
      }

      pc = pc + INSTRUCTIONSIZE;
    }

    reuse_lines = 1;

    if (initial_code_segment_nid != state_code_segment_nid) {
      next_zeroed_code_segment_nid = new_binary(OP_NEXT, SID_CODE_STATE,
        state_code_segment_nid, state_code_segment_nid, "read-only zeroed code segment");

      state_code_segment_nid = new_input(OP_STATE, SID_CODE_STATE,
        "loaded-code-segment", "loaded code segment");

      init_code_segment_nid = new_binary(OP_INIT, SID_CODE_STATE,
        state_code_segment_nid, initial_code_segment_nid, "loaded code");
    } else
      init_code_segment_nid = init_zeroed_code_segment_nid;

    eval_line(init_code_segment_nid);

    next_code_segment_nid = new_binary(OP_NEXT, SID_CODE_STATE,
      state_code_segment_nid, state_code_segment_nid, "read-only code segment");
  }
}

void print_code_segment(uint64_t core) {
  uint64_t code_size_in_instructions;
  uint64_t i;

  if (core > 0) {
    if (SYNTHESIZE) {
      print_break_comment("uninitialized code segment");

      print_line(state_code_segment_nid);
    }

    return;
  }

  if (CODE_LOADED == 0) {
    print_break_comment("uninitialized code segment");

    print_line(state_code_segment_nid);
  } else {
    print_break_comment("zeroed code segment");

    print_line(init_zeroed_code_segment_nid);

    if (initial_code_segment_nid != state_code_segment_nid) {
      print_line(next_zeroed_code_segment_nid);

      code_size_in_instructions = code_size / INSTRUCTIONSIZE;

      if (code_size % INSTRUCTIONSIZE > 0)
        code_size_in_instructions = code_size_in_instructions + 1;

      print_aligned_break_comment("loading code",
        log_ten(code_size_in_instructions * 3 + 1) + 1);

      i = 0;

      while (i < code_size_in_instructions) {
        if (*(initial_code_segment_nids + i) != 0)
          print_line((uint64_t*) *(initial_code_segment_nids + i));

        i = i + 1;
      }

      print_break_comment("loaded code segment");

      print_line(init_code_segment_nid);
    }

    print_line(next_code_segment_nid);
  }
}

void new_memory_state(uint64_t core) {
  uint64_t  number_of_hex_digits;
  uint64_t  vaddr;
  uint64_t  data;
  uint64_t* vaddr_nid;
  uint64_t* data_nid;

  if (SYNCHRONIZED_MEMORY) {
    if (core > 0)
      return;
  } else if (SHARED_MEMORY)
    if (core > 0)
      return;

  state_main_memory_nid = new_input(OP_STATE, SID_MEMORY_STATE,
    format_comment("core-%lu-zeroed-main-memory", core), "zeroed main memory");

  init_zeroed_main_memory_nid = new_binary(OP_INIT, SID_MEMORY_STATE,
    state_main_memory_nid, NID_MEMORY_WORD_0, "zeroing memory");

  if (CODE_LOADED) {
    number_of_hex_digits = round_up(MEMORY_ADDRESS_SPACE, 4) / 4;

    initial_data_segment_nid = state_main_memory_nid;
    initial_heap_segment_nid = state_main_memory_nid;

    initial_main_memory_nid = state_main_memory_nid;

    reuse_lines = 0; // TODO: turn on via console argument

    vaddr = data_start;

    while (vaddr < VIRTUALMEMORYSIZE * GIGABYTE - WORDSIZE) {
      if (vaddr == data_start + data_size) {
        initial_data_segment_nid = initial_main_memory_nid;

        vaddr = heap_start;
      }

      if (vaddr == heap_start + heap_size) {
        initial_heap_segment_nid = initial_data_segment_nid;

        vaddr = stack_start;
      }

      if (is_virtual_address_mapped(get_pt(current_context), vaddr)) {
        // memory allocated but not yet mapped is assumed to be zeroed
        data = load_virtual_memory(get_pt(current_context), vaddr);

        if (data != 0) {
          // skipping zero as initial value
          vaddr_nid = new_constant(OP_CONSTH, SID_VIRTUAL_ADDRESS,
            vaddr,
            number_of_hex_digits,
            format_comment("vaddr 0x%lX", vaddr));
          data_nid = new_constant(OP_CONSTH, SID_MACHINE_WORD,
            data,
            0,
            format_comment("data 0x%lX", data));
          initial_main_memory_nid =
            store_machine_word_at_virtual_address(vaddr_nid, data_nid, initial_main_memory_nid);
        }
      }

      vaddr = vaddr + WORDSIZE;
    }

    reuse_lines = 1;

    if (initial_main_memory_nid != state_main_memory_nid) {
      next_zeroed_main_memory_nid = new_binary(OP_NEXT, SID_MEMORY_STATE,
        state_main_memory_nid, state_main_memory_nid, "read-only zeroed main memory");

      state_main_memory_nid = new_input(OP_STATE, SID_MEMORY_STATE,
        format_comment("core-%lu-loaded-main-memory", core), "loaded main memory");

      init_main_memory_nid = new_binary(OP_INIT, SID_MEMORY_STATE,
        state_main_memory_nid, initial_main_memory_nid, "loaded data");
    } else
      init_main_memory_nid = init_zeroed_main_memory_nid;
  }
}

void print_memory_state(uint64_t core) {
  if (SYNCHRONIZED_MEMORY) {
    if (core > 0)
      return;
  } else if (SHARED_MEMORY)
    if (core > 0)
      return;

  print_break_comment("zeroed main memory");

  print_line(init_zeroed_main_memory_nid);

  if (CODE_LOADED)
    if (initial_main_memory_nid != state_main_memory_nid) {
      print_line(next_zeroed_main_memory_nid);

      // assert: data_size > 0 and non-zero data in data segment

      // conservatively estimating number of lines needed to store one byte
      print_aligned_break_comment("loaded data segment",
        log_ten((data_size + heap_size + stack_size) * 5) + 1);

      print_line(initial_data_segment_nid);

      if (initial_heap_segment_nid != initial_data_segment_nid) {
        print_break_comment("loaded heap segment");

        print_line(initial_heap_segment_nid);
      }

      if (initial_main_memory_nid != initial_heap_segment_nid) {
        print_break_comment("loaded stack segment");

        print_line(initial_main_memory_nid);
      }

      print_break_comment("loaded main memory");

      print_line(init_main_memory_nid);
    }
}

uint64_t get_power_of_two_size_in_bytes(uint64_t size) {
  // constraining: size is a power of 2 >= 8 bits

  if (size % 8 == 0) {
    size = size / 8;

    if (size == two_to_the_power_of(log_two(size)))
      return size;
  }

  printf("%s: power of two size in bytes error\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t* get_memory_address_sort(uint64_t* memory_nid) {
  return get_arg2(get_sid(memory_nid));
}

uint64_t* get_memory_word_sort(uint64_t* memory_nid) {
  return get_arg3(get_sid(memory_nid));
}

uint64_t is_byte_memory(uint64_t* memory_nid) {
  return eval_array_element_size(get_sid(memory_nid)) == 8;
}

uint64_t is_half_word_memory(uint64_t* memory_nid) {
  return eval_array_element_size(get_sid(memory_nid)) == HALFWORDSIZEINBITS;
}

uint64_t is_single_word_memory(uint64_t* memory_nid) {
  return eval_array_element_size(get_sid(memory_nid)) == SINGLEWORDSIZEINBITS;
}

uint64_t is_double_word_memory(uint64_t* memory_nid) {
  return eval_array_element_size(get_sid(memory_nid)) == DOUBLEWORDSIZEINBITS;
}

uint64_t* vaddr_to_paddr(uint64_t* vaddr_nid, uint64_t* memory_nid) {
  uint64_t memory_address_space;
  uint64_t memory_word_size_in_bytes;

  if (get_sid(memory_nid) == SID_CODE_STATE)
    if (code_start > 0)
      vaddr_nid = new_binary(OP_SUB, SID_VIRTUAL_ADDRESS,
        vaddr_nid, NID_CODE_START, "offset non-zero start of code segment");

  memory_address_space = eval_array_size(get_sid(memory_nid));

  if (memory_address_space == VIRTUAL_ADDRESS_SPACE)
    if (is_byte_memory(memory_nid))
      return vaddr_nid;

  memory_word_size_in_bytes =
    get_power_of_two_size_in_bytes(eval_array_element_size(get_sid(memory_nid)));

  return new_slice(get_memory_address_sort(memory_nid), vaddr_nid,
    memory_address_space - 1 + log_two(memory_word_size_in_bytes),
    log_two(memory_word_size_in_bytes),
    format_comment("map virtual address to %lu-bit physical address", memory_address_space));
}

uint64_t* load_aligned_memory_word(uint64_t* vaddr_nid, uint64_t* memory_nid) {
  return new_binary(OP_READ, get_memory_word_sort(memory_nid),
    memory_nid,
    vaddr_to_paddr(vaddr_nid, memory_nid),
    "load aligned word from memory at vaddr");
}

uint64_t* store_aligned_memory_word(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid) {
  return new_ternary(OP_WRITE, get_sid(memory_nid),
    memory_nid,
    vaddr_to_paddr(vaddr_nid, memory_nid),
    word_nid,
    "store aligned word in memory at vaddr");
}

uint64_t* cast_virtual_address_to_word(uint64_t* vaddr_nid, uint64_t* sid_word) {
  if (eval_bitvec_size(sid_word) < VIRTUAL_ADDRESS_SPACE)
    return new_slice(sid_word, vaddr_nid,
      eval_bitvec_size(sid_word) - 1, 0, "slice word from virtual address");
  else if (eval_bitvec_size(sid_word) > VIRTUAL_ADDRESS_SPACE)
    return new_ext(OP_UEXT, sid_word,
      vaddr_nid,
      eval_bitvec_size(sid_word) - VIRTUAL_ADDRESS_SPACE,
      "unsigned extension of virtual address to word");
  else
    return vaddr_nid;
}

uint64_t* cast_virtual_address_to_memory_word(uint64_t* vaddr_nid, uint64_t* memory_nid) {
  return cast_virtual_address_to_word(vaddr_nid, get_memory_word_sort(memory_nid));
}

uint64_t* get_memory_word_size_mask(uint64_t* memory_nid) {
  if (is_half_word_memory(memory_nid))
    return NID_HALF_WORD_SIZE_MASK;
  else if (is_single_word_memory(memory_nid))
    return NID_SINGLE_WORD_SIZE_MASK;
  else if (is_double_word_memory(memory_nid))
    return NID_DOUBLE_WORD_SIZE_MASK;
  else
    // assert: unreachable
    return NID_FALSE;
}

uint64_t* get_vaddr_alignment(uint64_t* vaddr_nid, uint64_t* memory_nid) {
  return new_binary(OP_AND, get_memory_word_sort(memory_nid),
    cast_virtual_address_to_memory_word(vaddr_nid, memory_nid),
    get_memory_word_size_mask(memory_nid),
    "mask alignment bits");
}

uint64_t* extend_byte_to_half_word(char* op, uint64_t* byte_nid) {
  return new_ext(op, SID_HALF_WORD,
    byte_nid,
    HALFWORDSIZEINBITS - 8,
    "extension of byte to half word");
}

uint64_t* extend_byte_to_single_word(char* op, uint64_t* byte_nid) {
  return new_ext(op, SID_SINGLE_WORD,
    byte_nid,
    SINGLEWORDSIZEINBITS - 8,
    "extension of byte to single word");
}

uint64_t* extend_byte_to_double_word(char* op, uint64_t* byte_nid) {
  return new_ext(op, SID_DOUBLE_WORD,
    byte_nid,
    DOUBLEWORDSIZEINBITS - 8,
    "extension of byte to double word");
}

uint64_t* extend_byte_to_memory_word(uint64_t* byte_nid, uint64_t* memory_nid) {
  if (is_half_word_memory(memory_nid))
    return extend_byte_to_half_word(OP_UEXT, byte_nid);
  else if (is_single_word_memory(memory_nid))
    return extend_byte_to_single_word(OP_UEXT, byte_nid);
  else if (is_double_word_memory(memory_nid))
    return extend_byte_to_double_word(OP_UEXT, byte_nid);
  else
    // assert: unreachable
    return byte_nid;
}

uint64_t* shift_by_alignment_in_bits(uint64_t* vaddr_nid, uint64_t* memory_nid) {
  return new_binary(OP_SLL, get_memory_word_sort(memory_nid),
    get_vaddr_alignment(vaddr_nid, memory_nid),
    extend_byte_to_memory_word(NID_BYTE_SIZE_IN_BASE_BITS, memory_nid),
    "multiply by 8 bits");
}

uint64_t* shift_from_vaddr(uint64_t* vaddr_nid, uint64_t* value_nid, uint64_t* memory_nid) {
  return new_binary(OP_SRL, get_memory_word_sort(memory_nid),
    value_nid,
    shift_by_alignment_in_bits(vaddr_nid, memory_nid),
    "shift right from vaddr");
}

uint64_t* shift_to_vaddr(uint64_t* vaddr_nid, uint64_t* value_nid, uint64_t* memory_nid) {
  return new_binary(OP_SLL, get_memory_word_sort(memory_nid),
    value_nid,
    shift_by_alignment_in_bits(vaddr_nid, memory_nid),
    "shift left to vaddr");
}

uint64_t* slice_byte_from_word(uint64_t* word_nid) {
  return new_slice(SID_BYTE, word_nid, 7, 0, "slice least-significant byte");
}

uint64_t* extend_half_word_to_single_word(char* op, uint64_t* word_nid) {
  return new_ext(op, SID_SINGLE_WORD,
    word_nid,
    SINGLEWORDSIZEINBITS - HALFWORDSIZEINBITS,
    "extension of half word to single word");
}

uint64_t* extend_half_word_to_double_word(char* op, uint64_t* word_nid) {
  return new_ext(op, SID_DOUBLE_WORD,
    word_nid,
    DOUBLEWORDSIZEINBITS - HALFWORDSIZEINBITS,
    "extension of half word to double word");
}

uint64_t* extend_half_word_to_memory_word(uint64_t* word_nid, uint64_t* memory_nid) {
  if (is_half_word_memory(memory_nid))
    return word_nid;
  else if (is_single_word_memory(memory_nid))
    return extend_half_word_to_single_word(OP_UEXT, word_nid);
  else if (is_double_word_memory(memory_nid))
    return extend_half_word_to_double_word(OP_UEXT, word_nid);
  else
    // assert: unreachable
    return word_nid;
}

uint64_t* extend_single_word_to_double_word(char* op, uint64_t* word_nid) {
  return new_ext(op, SID_DOUBLE_WORD,
    word_nid,
    DOUBLEWORDSIZEINBITS - SINGLEWORDSIZEINBITS,
    "extension of single word to double word");
}

uint64_t* extend_single_word_to_memory_word(uint64_t* word_nid, uint64_t* memory_nid) {
  if (is_single_word_memory(memory_nid))
    return word_nid;
  else if (is_double_word_memory(memory_nid))
    return extend_single_word_to_double_word(OP_UEXT, word_nid);
  else
    // assert: unreachable
    return word_nid;
}

uint64_t* extend_value_to_memory_word(uint64_t* value_nid, uint64_t* memory_nid) {
  if (get_sid(value_nid) == SID_BYTE)
    return extend_byte_to_memory_word(value_nid, memory_nid);
  else if (get_sid(value_nid) == SID_HALF_WORD)
    return extend_half_word_to_memory_word(value_nid, memory_nid);
  else if (get_sid(value_nid) == SID_SINGLE_WORD)
    return extend_single_word_to_memory_word(value_nid, memory_nid);
  else
    // assert: unreachable
    return value_nid;
}

uint64_t* get_value_mask(uint64_t* value_nid, uint64_t* memory_nid) {
  if (get_sid(value_nid) == SID_BYTE)
    return extend_byte_to_memory_word(NID_BYTE_MASK, memory_nid);
  else if (get_sid(value_nid) == SID_HALF_WORD)
    return extend_half_word_to_memory_word(NID_HALF_WORD_MASK, memory_nid);
  else if (get_sid(value_nid) == SID_SINGLE_WORD)
    return extend_single_word_to_memory_word(NID_SINGLE_WORD_MASK, memory_nid);
  else
    // assert: unreachable
    return value_nid;
}

uint64_t* insert_value_into_memory_word(uint64_t* vaddr_nid, uint64_t* value_nid, uint64_t* memory_nid) {
  if (get_sid(value_nid) == SID_HALF_WORD)
    if (is_half_word_memory(memory_nid))
      return value_nid;

  if (get_sid(value_nid) == SID_SINGLE_WORD)
    if (is_single_word_memory(memory_nid))
      return value_nid;

  return new_binary(OP_OR, get_memory_word_sort(memory_nid),
    new_binary(OP_AND, get_memory_word_sort(memory_nid),
      load_aligned_memory_word(vaddr_nid, memory_nid),
      new_unary(OP_NOT, get_memory_word_sort(memory_nid),
        shift_to_vaddr(vaddr_nid, get_value_mask(value_nid, memory_nid), memory_nid),
        "bitwise-not value mask"),
      "reset bits at value location in aligned memory word"),
    shift_to_vaddr(vaddr_nid, extend_value_to_memory_word(value_nid, memory_nid), memory_nid),
    "insert value at value location in aligned memory word");
}

uint64_t* load_byte_from_memory_word(uint64_t* vaddr_nid, uint64_t* memory_nid) {
  return slice_byte_from_word(shift_from_vaddr(vaddr_nid,
    load_aligned_memory_word(vaddr_nid, memory_nid),
    memory_nid));
}

uint64_t* store_byte_in_memory_word(uint64_t* vaddr_nid, uint64_t* byte_nid, uint64_t* memory_nid) {
  return store_aligned_memory_word(vaddr_nid,
    insert_value_into_memory_word(vaddr_nid, byte_nid, memory_nid),
    memory_nid);
}

uint64_t* load_byte_at_virtual_address(uint64_t* vaddr_nid, uint64_t* memory_nid) {
  if (is_byte_memory(memory_nid))
    return load_aligned_memory_word(vaddr_nid, memory_nid);
  else
    return load_byte_from_memory_word(vaddr_nid, memory_nid);
}

uint64_t* store_byte_at_virtual_address(uint64_t* vaddr_nid, uint64_t* byte_nid, uint64_t* memory_nid) {
  if (is_byte_memory(memory_nid))
    return store_aligned_memory_word(vaddr_nid, byte_nid, memory_nid);
  else
    return store_byte_in_memory_word(vaddr_nid, byte_nid, memory_nid);
}

uint64_t* slice_second_byte_from_word(uint64_t* word_nid) {
  return new_slice(SID_BYTE, word_nid, 15, 8, "slice second least-significant byte from word");
}

uint64_t* load_half_word_from_bytes(uint64_t* vaddr_nid, uint64_t* memory_nid) {
  return new_binary(OP_CONCAT, SID_HALF_WORD,
    load_byte_at_virtual_address(new_unary(OP_INC, SID_VIRTUAL_ADDRESS, vaddr_nid, "vaddr + 1"), memory_nid),
    load_byte_at_virtual_address(vaddr_nid, memory_nid),
    "load half word from bytes");
}

uint64_t* store_half_word_in_bytes(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid) {
  return store_byte_at_virtual_address(vaddr_nid,
    slice_byte_from_word(word_nid),
    store_byte_at_virtual_address(new_unary(OP_INC, SID_VIRTUAL_ADDRESS, vaddr_nid, "vaddr + 1"),
      slice_second_byte_from_word(word_nid),
      memory_nid));
}

uint64_t* get_half_word_size_relative_to_memory_word_size(uint64_t* memory_nid) {
  if (is_half_word_memory(memory_nid))
    return NID_HALF_WORD_0;
  else if (is_single_word_memory(memory_nid))
    return NID_SINGLE_WORD_SIZE_MINUS_HALF_WORD_SIZE;
  else if (is_double_word_memory(memory_nid))
    return NID_DOUBLE_WORD_SIZE_MINUS_HALF_WORD_SIZE;
  else
    // assert: unreachable
    return NID_FALSE;
}

uint64_t* is_contained_in_memory_word(uint64_t* vaddr_nid, uint64_t* relative_size_nid, uint64_t* memory_nid) {
  return new_binary_boolean(OP_ULTE,
    get_vaddr_alignment(vaddr_nid, memory_nid),
    relative_size_nid,
    "is contained in memory word");
}

uint64_t* slice_half_word_from_word(uint64_t* word_nid) {
  return new_slice(SID_HALF_WORD, word_nid, 15, 0, "slice lower half word from word");
}

uint64_t* slice_half_word_from_memory_word(uint64_t* word_nid, uint64_t* memory_nid) {
  if (is_half_word_memory(memory_nid))
    return word_nid;
  else
    // assert: memory words are single or double words
    return slice_half_word_from_word(word_nid);
}

uint64_t* load_half_word_from_memory_words(uint64_t* vaddr_nid, uint64_t* memory_nid) {
  return new_ternary(OP_ITE, SID_HALF_WORD,
    is_contained_in_memory_word(vaddr_nid,
      get_half_word_size_relative_to_memory_word_size(memory_nid),
      memory_nid),
    slice_half_word_from_memory_word(
      shift_from_vaddr(
        vaddr_nid,
        load_aligned_memory_word(vaddr_nid, memory_nid),
        memory_nid),
      memory_nid),
    load_half_word_from_bytes(vaddr_nid, memory_nid),
    "load half word from memory words");
}

uint64_t* store_half_word_in_memory_words(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid) {
  return new_ternary(OP_ITE, get_sid(memory_nid),
    is_contained_in_memory_word(vaddr_nid,
      get_half_word_size_relative_to_memory_word_size(memory_nid),
      memory_nid),
    store_aligned_memory_word(vaddr_nid,
      insert_value_into_memory_word(vaddr_nid, word_nid, memory_nid),
      memory_nid),
    store_half_word_in_bytes(vaddr_nid, word_nid, memory_nid),
    "store half word in memory words");
}

uint64_t* load_half_word_at_virtual_address(uint64_t* vaddr_nid, uint64_t* memory_nid) {
  if (is_byte_memory(memory_nid))
    return load_half_word_from_bytes(vaddr_nid, memory_nid);
  else
    return load_half_word_from_memory_words(vaddr_nid, memory_nid);
}

uint64_t* store_half_word_at_virtual_address(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid) {
  if (is_byte_memory(memory_nid))
    return store_half_word_in_bytes(vaddr_nid, word_nid, memory_nid);
  else
    return store_half_word_in_memory_words(vaddr_nid, word_nid, memory_nid);
}

uint64_t* slice_lower_half_word_from_single_word(uint64_t* word_nid) {
  return new_slice(SID_HALF_WORD, word_nid, 15, 0, "slice lower half word from single word");
}

uint64_t* slice_upper_half_word_from_single_word(uint64_t* word_nid) {
  return new_slice(SID_HALF_WORD, word_nid, 31, 16, "slice upper half word from single word");
}

uint64_t* load_single_word_from_half_words(uint64_t* vaddr_nid, uint64_t* memory_nid) {
  return new_binary(OP_CONCAT, SID_SINGLE_WORD,
    load_half_word_at_virtual_address(new_binary(OP_ADD, SID_VIRTUAL_ADDRESS,
      vaddr_nid,
      NID_VIRTUAL_HALF_WORD_SIZE,
      "vaddr + 2"),
      memory_nid),
    load_half_word_at_virtual_address(vaddr_nid, memory_nid),
    "load single word from half words");
}

uint64_t* store_single_word_in_half_words(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid) {
  return store_half_word_at_virtual_address(vaddr_nid,
    slice_lower_half_word_from_single_word(word_nid),
    store_half_word_at_virtual_address(new_binary(OP_ADD, SID_VIRTUAL_ADDRESS,
      vaddr_nid,
      NID_VIRTUAL_HALF_WORD_SIZE,
      "vaddr + 2"),
      slice_upper_half_word_from_single_word(word_nid),
      memory_nid));
}

uint64_t* get_single_word_size_relative_to_memory_word_size(uint64_t* memory_nid) {
  if (is_single_word_memory(memory_nid))
    return NID_SINGLE_WORD_0;
  else if (is_double_word_memory(memory_nid))
    return NID_DOUBLE_WORD_SIZE_MINUS_SINGLE_WORD_SIZE;
  else
    // assert: unreachable
    return NID_FALSE;
}

uint64_t* slice_single_word_from_double_word(uint64_t* word_nid) {
  return new_slice(SID_SINGLE_WORD, word_nid, 31, 0, "slice lower single word from double word");
}

uint64_t* slice_single_word_from_memory_word(uint64_t* word_nid, uint64_t* memory_nid) {
  if (is_single_word_memory(memory_nid))
    return word_nid;
  else
    // assert: memory words are double words
    return slice_single_word_from_double_word(word_nid);
}

uint64_t* load_single_word_from_memory_words(uint64_t* vaddr_nid, uint64_t* memory_nid) {
  return new_ternary(OP_ITE, SID_SINGLE_WORD,
    is_contained_in_memory_word(vaddr_nid,
      get_single_word_size_relative_to_memory_word_size(memory_nid),
      memory_nid),
    slice_single_word_from_memory_word(
      shift_from_vaddr(
        vaddr_nid,
        load_aligned_memory_word(vaddr_nid, memory_nid),
        memory_nid),
      memory_nid),
    load_single_word_from_half_words(vaddr_nid, memory_nid),
    "load single word from memory words");
}

uint64_t* store_single_word_in_memory_words(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid) {
  if (get_op(vaddr_nid) == OP_CONSTH)
    // optimizes boot loading
    if ((uint64_t) get_arg1(vaddr_nid) % SINGLEWORDSIZE == 0)
      return store_aligned_memory_word(vaddr_nid,
        insert_value_into_memory_word(vaddr_nid, word_nid, memory_nid),
        memory_nid);

  return new_ternary(OP_ITE, get_sid(memory_nid),
    is_contained_in_memory_word(vaddr_nid,
      get_single_word_size_relative_to_memory_word_size(memory_nid),
      memory_nid),
    store_aligned_memory_word(vaddr_nid,
      insert_value_into_memory_word(vaddr_nid, word_nid, memory_nid),
      memory_nid),
    store_single_word_in_half_words(vaddr_nid, word_nid, memory_nid),
    "store single word in memory words");
}

uint64_t* load_single_word_at_virtual_address(uint64_t* vaddr_nid, uint64_t* memory_nid) {
  if (is_byte_memory(memory_nid))
    return load_single_word_from_half_words(vaddr_nid, memory_nid);
  else if (is_half_word_memory(memory_nid))
    return load_single_word_from_half_words(vaddr_nid, memory_nid);
  else
    return load_single_word_from_memory_words(vaddr_nid, memory_nid);
}

uint64_t* store_single_word_at_virtual_address(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid) {
  if (is_byte_memory(memory_nid))
    return store_single_word_in_half_words(vaddr_nid, word_nid, memory_nid);
  else if (is_half_word_memory(memory_nid))
    return store_single_word_in_half_words(vaddr_nid, word_nid, memory_nid);
  else
    return store_single_word_in_memory_words(vaddr_nid, word_nid, memory_nid);
}

uint64_t* slice_lower_single_word_from_double_word(uint64_t* word_nid) {
  return new_slice(SID_SINGLE_WORD, word_nid, 31, 0, "slice lower single word from double word");
}

uint64_t* slice_upper_single_word_from_double_word(uint64_t* word_nid) {
  return new_slice(SID_SINGLE_WORD, word_nid, 63, 32, "slice upper single word from double word");
}

uint64_t* load_double_word_from_single_words(uint64_t* vaddr_nid, uint64_t* memory_nid) {
  return new_binary(OP_CONCAT, SID_DOUBLE_WORD,
    load_single_word_at_virtual_address(new_binary(OP_ADD, SID_VIRTUAL_ADDRESS,
        vaddr_nid,
        NID_VIRTUAL_SINGLE_WORD_SIZE,
        "vaddr + 4"),
      memory_nid),
    load_single_word_at_virtual_address(vaddr_nid, memory_nid),
    "load double word from single words");
}

uint64_t* store_double_word_in_single_words(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid) {
  return store_single_word_at_virtual_address(vaddr_nid,
    slice_lower_single_word_from_double_word(word_nid),
    store_single_word_at_virtual_address(new_binary(OP_ADD, SID_VIRTUAL_ADDRESS,
      vaddr_nid,
      NID_VIRTUAL_SINGLE_WORD_SIZE,
      "vaddr + 4"),
      slice_upper_single_word_from_double_word(word_nid),
      memory_nid));
}

uint64_t* load_double_word_from_memory_words(uint64_t* vaddr_nid, uint64_t* memory_nid) {
  return new_ternary(OP_ITE, SID_DOUBLE_WORD,
    is_contained_in_memory_word(vaddr_nid, NID_DOUBLE_WORD_0, memory_nid),
    load_aligned_memory_word(vaddr_nid, memory_nid),
    load_double_word_from_single_words(vaddr_nid, memory_nid),
    "load double word from memory words");
}

uint64_t* store_double_word_in_memory_words(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid) {
  if (get_op(vaddr_nid) == OP_CONSTH)
    // optimizes boot loading
    if ((uint64_t) get_arg1(vaddr_nid) % DOUBLEWORDSIZE == 0)
      return store_aligned_memory_word(vaddr_nid, word_nid, memory_nid);

  return new_ternary(OP_ITE, get_sid(memory_nid),
    is_contained_in_memory_word(vaddr_nid, NID_DOUBLE_WORD_0, memory_nid),
    store_aligned_memory_word(vaddr_nid, word_nid, memory_nid),
    store_double_word_in_single_words(vaddr_nid, word_nid, memory_nid),
    "store double word in memory words");
}

uint64_t* load_double_word_at_virtual_address(uint64_t* vaddr_nid, uint64_t* memory_nid) {
  if (is_double_word_memory(memory_nid))
    return load_double_word_from_memory_words(vaddr_nid, memory_nid);
  else
    return load_double_word_from_single_words(vaddr_nid, memory_nid);
}

uint64_t* store_double_word_at_virtual_address(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid) {
  if (is_double_word_memory(memory_nid))
    return store_double_word_in_memory_words(vaddr_nid, word_nid, memory_nid);
  else
    return store_double_word_in_single_words(vaddr_nid, word_nid, memory_nid);
}

uint64_t* load_machine_word_at_virtual_address(uint64_t* vaddr_nid, uint64_t* memory_nid) {
  if (IS64BITTARGET)
    return load_double_word_at_virtual_address(vaddr_nid, memory_nid);
  else
    return load_single_word_at_virtual_address(vaddr_nid, memory_nid);
}

uint64_t* store_machine_word_at_virtual_address(uint64_t* vaddr_nid, uint64_t* word_nid, uint64_t* memory_nid) {
  if (IS64BITTARGET)
    return store_double_word_at_virtual_address(vaddr_nid, word_nid, memory_nid);
  else
    return store_single_word_at_virtual_address(vaddr_nid, word_nid, memory_nid);
}

uint64_t* cast_virtual_address_to_machine_word(uint64_t* vaddr_nid) {
  return cast_virtual_address_to_word(vaddr_nid, SID_MACHINE_WORD);
}

uint64_t* cast_machine_word_to_virtual_address(uint64_t* machine_word_nid) {
  if (WORDSIZEINBITS > VIRTUAL_ADDRESS_SPACE)
    return new_slice(SID_VIRTUAL_ADDRESS, machine_word_nid,
      VIRTUAL_ADDRESS_SPACE - 1, 0, "slice virtual address from machine word");
  else if (WORDSIZEINBITS < VIRTUAL_ADDRESS_SPACE)
    return new_ext(OP_UEXT, SID_VIRTUAL_ADDRESS,
      machine_word_nid,
      VIRTUAL_ADDRESS_SPACE - WORDSIZEINBITS,
      "unsigned extension of machine word to virtual address");
  else
    return machine_word_nid;
}

uint64_t* is_machine_word_virtual_address(uint64_t* machine_word_nid) {
  if (WORDSIZEINBITS > VIRTUAL_ADDRESS_SPACE)
    return new_binary_boolean(OP_EQ,
      machine_word_nid,
      cast_virtual_address_to_machine_word(
        cast_machine_word_to_virtual_address(machine_word_nid)),
      "is machine word virtual address?");
  else
    return NID_TRUE;
}

uint64_t* load_byte(uint64_t* machine_word_nid, uint64_t* memory_nid) {
  return load_byte_at_virtual_address(
    cast_machine_word_to_virtual_address(machine_word_nid), memory_nid);
}

uint64_t* store_byte(uint64_t* machine_word_nid, uint64_t* byte_nid, uint64_t* memory_nid) {
  return store_byte_at_virtual_address(
    cast_machine_word_to_virtual_address(machine_word_nid), byte_nid, memory_nid);
}

uint64_t* load_half_word(uint64_t* machine_word_nid, uint64_t* memory_nid) {
  return load_half_word_at_virtual_address(
    cast_machine_word_to_virtual_address(machine_word_nid), memory_nid);
}

uint64_t* store_half_word(uint64_t* machine_word_nid, uint64_t* word_nid, uint64_t* memory_nid) {
  return store_half_word_at_virtual_address(
    cast_machine_word_to_virtual_address(machine_word_nid), word_nid, memory_nid);
}

uint64_t* load_single_word(uint64_t* machine_word_nid, uint64_t* memory_nid) {
  return load_single_word_at_virtual_address(
    cast_machine_word_to_virtual_address(machine_word_nid), memory_nid);
}

uint64_t* store_single_word(uint64_t* machine_word_nid, uint64_t* word_nid, uint64_t* memory_nid) {
  return store_single_word_at_virtual_address(
    cast_machine_word_to_virtual_address(machine_word_nid), word_nid, memory_nid);
}

uint64_t* load_double_word(uint64_t* machine_word_nid, uint64_t* memory_nid) {
  return load_double_word_at_virtual_address(
    cast_machine_word_to_virtual_address(machine_word_nid), memory_nid);
}

uint64_t* store_double_word(uint64_t* machine_word_nid, uint64_t* word_nid, uint64_t* memory_nid) {
  return store_double_word_at_virtual_address(
    cast_machine_word_to_virtual_address(machine_word_nid), word_nid, memory_nid);
}

uint64_t* does_machine_word_work_as_virtual_address(uint64_t* machine_word_nid, uint64_t* property_nid) {
  if (WORDSIZEINBITS > VIRTUAL_ADDRESS_SPACE)
    return new_binary_boolean(OP_AND,
      is_machine_word_virtual_address(machine_word_nid),
      property_nid,
      "does machine word work as virtual address?");
  else
    return property_nid;
}

uint64_t* is_address_in_code_segment(uint64_t* machine_word_nid) {
  uint64_t* vaddr_nid;

  vaddr_nid = cast_machine_word_to_virtual_address(machine_word_nid);

  return does_machine_word_work_as_virtual_address(machine_word_nid,
    is_block_in_code_segment(vaddr_nid, vaddr_nid));
}

uint64_t* is_address_in_data_segment(uint64_t* machine_word_nid) {
  uint64_t* vaddr_nid;

  vaddr_nid = cast_machine_word_to_virtual_address(machine_word_nid);

  return does_machine_word_work_as_virtual_address(machine_word_nid,
    is_block_in_data_segment(vaddr_nid, vaddr_nid));
}

uint64_t* is_address_in_heap_segment(uint64_t* machine_word_nid) {
  uint64_t* vaddr_nid;

  vaddr_nid = cast_machine_word_to_virtual_address(machine_word_nid);

  return does_machine_word_work_as_virtual_address(machine_word_nid,
    is_block_in_heap_segment(vaddr_nid, vaddr_nid));
}

uint64_t* is_address_in_stack_segment(uint64_t* machine_word_nid) {
  uint64_t* vaddr_nid;

  vaddr_nid = cast_machine_word_to_virtual_address(machine_word_nid);

  return does_machine_word_work_as_virtual_address(machine_word_nid,
    is_block_in_stack_segment(vaddr_nid, vaddr_nid));
}

uint64_t* is_address_in_main_memory(uint64_t* machine_word_nid) {
  uint64_t* vaddr_nid;

  vaddr_nid = cast_machine_word_to_virtual_address(machine_word_nid);

  return does_machine_word_work_as_virtual_address(machine_word_nid,
    new_binary_boolean(OP_OR,
      is_block_in_data_segment(vaddr_nid, vaddr_nid),
      new_binary_boolean(OP_OR,
        is_block_in_heap_segment(vaddr_nid, vaddr_nid),
        is_block_in_stack_segment(vaddr_nid, vaddr_nid),
        "virtual address in heap or stack segment?"),
      "virtual address in data, heap, or stack segment?"));
}

uint64_t* is_range_in_heap_segment(uint64_t* machine_word_nid, uint64_t* range_nid) {
  uint64_t* range_end_nid;
  uint64_t* start_nid;
  uint64_t* end_nid;

  // assert: range > 0

  range_end_nid = new_binary(OP_ADD, SID_MACHINE_WORD,
    machine_word_nid,
    new_unary(OP_DEC, SID_MACHINE_WORD, range_nid, "range - 1"),
    "start of block + range - 1");

  start_nid = cast_machine_word_to_virtual_address(machine_word_nid);
  end_nid   = cast_machine_word_to_virtual_address(range_end_nid);

  return does_machine_word_work_as_virtual_address(range_end_nid,
    new_binary_boolean(OP_AND,
      new_binary_boolean(OP_ULTE, start_nid, end_nid, "start of block <= end of block"),
      is_block_in_heap_segment(start_nid, end_nid),
      "all virtual addresses in block in heap segment?"));
}

uint64_t* is_sized_block_in_stack_segment(uint64_t* machine_word_nid, uint64_t* size_nid) {
  uint64_t* start_nid;
  uint64_t* end_nid;

  start_nid = cast_machine_word_to_virtual_address(machine_word_nid);
  end_nid   = new_binary(OP_ADD, SID_VIRTUAL_ADDRESS, start_nid, size_nid, "start of block + size");

  return does_machine_word_work_as_virtual_address(machine_word_nid,
    new_binary_boolean(OP_AND,
      new_binary_boolean(OP_ULTE, start_nid, end_nid, "start of block <= end of block"),
      is_block_in_stack_segment(start_nid, end_nid),
      "all virtual addresses in block in stack segment?"));
}

uint64_t* is_sized_block_in_main_memory(uint64_t* machine_word_nid, uint64_t* size_nid) {
  uint64_t* start_nid;
  uint64_t* end_nid;

  start_nid = cast_machine_word_to_virtual_address(machine_word_nid);
  end_nid   = new_binary(OP_ADD, SID_VIRTUAL_ADDRESS, start_nid, size_nid, "start of block + size");

  return does_machine_word_work_as_virtual_address(machine_word_nid,
    new_binary_boolean(OP_AND,
      new_binary_boolean(OP_ULTE, start_nid, end_nid, "start of block <= end of block"),
      new_binary_boolean(OP_OR,
        is_block_in_data_segment(start_nid, end_nid),
        new_binary_boolean(OP_OR,
          is_block_in_heap_segment(start_nid, end_nid),
          is_block_in_stack_segment(start_nid, end_nid),
          "all virtual addresses in block in heap or stack segment?"),
        "all virtual addresses in block in data, heap, or stack segment?"),
      "all virtual addresses in block in main memory?"));
}

uint64_t* fetch_instruction(uint64_t* pc_nid, uint64_t* code_segment_nid) {
  return load_single_word(pc_nid, code_segment_nid);
}

uint64_t* fetch_compressed_instruction(uint64_t* pc_nid, uint64_t* code_segment_nid) {
  if (RVC)
    return load_half_word(pc_nid, code_segment_nid);
  else
    return UNUSED;
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

uint64_t* get_instruction_opcode(uint64_t* ir_nid) {
  return new_slice(SID_OPCODE, ir_nid, 6, 0, "get opcode");
}

uint64_t* get_instruction_funct3(uint64_t* ir_nid) {
  return new_slice(SID_FUNCT3, ir_nid, 14, 12, "get funct3");
}

uint64_t* get_instruction_funct7(uint64_t* ir_nid) {
  return new_slice(SID_FUNCT7, ir_nid, 31, 25, "get funct7");
}

uint64_t* get_instruction_funct6(uint64_t* ir_nid) {
  return new_slice(SID_FUNCT6, ir_nid, 31, 26, "get funct6");
}

uint64_t* get_instruction_rd(uint64_t* ir_nid) {
  return new_slice(SID_REGISTER_ADDRESS, ir_nid, 11, 7, "get rd");
}

uint64_t* get_instruction_rs1(uint64_t* ir_nid) {
  return new_slice(SID_REGISTER_ADDRESS, ir_nid, 19, 15, "get rs1");
}

uint64_t* get_instruction_rs2(uint64_t* ir_nid) {
  return new_slice(SID_REGISTER_ADDRESS, ir_nid, 24, 20, "get rs2");
}

uint64_t* sign_extend_IS_immediate(uint64_t* imm_nid) {
  return new_ext(OP_SEXT, SID_MACHINE_WORD, imm_nid, WORDSIZEINBITS - 12, "sign-extend IS-immediate");
}

uint64_t* get_instruction_I_immediate(uint64_t* ir_nid) {
  return sign_extend_IS_immediate(
    new_slice(SID_12_BIT_IMM, ir_nid, 31, 20, "get I-immediate"));
}

uint64_t* get_instruction_I_32_bit_immediate(uint64_t* ir_nid) {
  return new_ext(OP_SEXT, SID_SINGLE_WORD,
    new_slice(SID_12_BIT_IMM, ir_nid, 31, 20, "get I-32-bit-immediate"),
    SINGLEWORDSIZEINBITS - 12,
    "sign-extend I-32-bit-immediate");
}

uint64_t* get_instruction_5_bit_shamt(uint64_t* ir_nid) {
  return new_ext(OP_UEXT, SID_SINGLE_WORD,
    new_slice(SID_5_BIT_IMM, ir_nid, 24, 20, "get 5-bit shamt"),
    SINGLEWORDSIZEINBITS - 5,
    "unsigned-extend 5-bit shamt");
}

uint64_t* get_instruction_shamt(uint64_t* ir_nid) {
  if (IS64BITTARGET)
    return new_ext(OP_UEXT, SID_MACHINE_WORD,
      new_slice(SID_6_BIT_IMM, ir_nid, 25, 20, "get 6-bit shamt"),
      WORDSIZEINBITS - 6,
      "unsigned-extend 6-bit shamt");
  else
    return get_instruction_5_bit_shamt(ir_nid);
}

uint64_t* get_instruction_S_immediate(uint64_t* ir_nid) {
  return sign_extend_IS_immediate(
    new_binary(OP_CONCAT, SID_12_BIT_IMM,
      get_instruction_funct7(ir_nid),
      get_instruction_rd(ir_nid),
      "get S-immediate"));
}

uint64_t* sign_extend_SB_immediate(uint64_t* imm_nid) {
  return new_ext(OP_SEXT, SID_MACHINE_WORD, imm_nid, WORDSIZEINBITS - 13, "sign-extend SB-immediate");
}

uint64_t* get_instruction_SB_immediate(uint64_t* ir_nid) {
  return sign_extend_SB_immediate(
    new_binary(OP_CONCAT, SID_13_BIT_IMM,
      new_slice(SID_1_BIT_IMM, ir_nid, 31, 31, "get SB-immediate[12]"),
      new_binary(OP_CONCAT, SID_12_BIT_IMM,
        new_slice(SID_1_BIT_IMM, ir_nid, 7, 7, "get SB-immediate[11]"),
        new_binary(OP_CONCAT, SID_11_BIT_IMM,
          new_slice(SID_6_BIT_IMM, ir_nid, 30, 25, "get SB-immediate[10:5]"),
          new_binary(OP_CONCAT, SID_5_BIT_IMM,
            new_slice(SID_4_BIT_IMM, ir_nid, 11, 8, "get SB-immediate[4:1]"),
            NID_1_BIT_IMM_0,
            "get SB-immediate[4:0]"),
          "get SB-immediate[10:0]"),
        "get SB-immediate[11:0]"),
      "get SB-immediate[12:0]"));
}

uint64_t* sign_extend_U_immediate(uint64_t* imm_nid) {
  // redundant with extend_single_word_to_machine_word
  if (IS64BITTARGET)
    return new_ext(OP_SEXT, SID_MACHINE_WORD, imm_nid, WORDSIZEINBITS - 32, "sign-extend U-immediate");
  else
    return imm_nid;
}

uint64_t* get_instruction_U_immediate(uint64_t* ir_nid) {
  return sign_extend_U_immediate(
    new_binary(OP_CONCAT, SID_32_BIT_IMM,
      new_slice(SID_20_BIT_IMM, ir_nid, 31, 12, "get U-immediate[31:12]"),
      NID_12_BIT_IMM_0,
      "get U-immediate[31:0]"));
}

uint64_t* sign_extend_UJ_immediate(uint64_t* imm_nid) {
  return new_ext(OP_SEXT, SID_MACHINE_WORD, imm_nid, WORDSIZEINBITS - 21, "sign-extend UJ-immediate");
}

uint64_t* get_instruction_UJ_immediate(uint64_t* ir_nid) {
  return sign_extend_UJ_immediate(
    new_binary(OP_CONCAT, SID_21_BIT_IMM,
      new_slice(SID_1_BIT_IMM, ir_nid, 31, 31, "get UJ-immediate[20]"),
      new_binary(OP_CONCAT, SID_20_BIT_IMM,
        new_slice(SID_8_BIT_IMM, ir_nid, 19, 12, "get UJ-immediate[19:12]"),
        new_binary(OP_CONCAT, SID_12_BIT_IMM,
          new_slice(SID_1_BIT_IMM, ir_nid, 20, 20, "get UJ-immediate[11]"),
          new_binary(OP_CONCAT, SID_11_BIT_IMM,
            new_slice(SID_10_BIT_IMM, ir_nid, 30, 21, "get UJ-immediate[10:1]"),
            NID_1_BIT_IMM_0,
            "get UJ-immediate[10:0]"),
          "get UJ-immediate[11:0]"),
        "get UJ-immediate[19:0]"),
      "get UJ-immediate[20:0]"));
}

uint64_t* decode_opcode(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* opcode_nid, char* opcode_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_opcode_nid) {
  return new_ternary(OP_ITE, sid,
    new_binary_boolean(OP_EQ,
      get_instruction_opcode(ir_nid),
      opcode_nid,
      format_comment("opcode == %s", (uint64_t) opcode_comment)),
    execute_nid,
    other_opcode_nid,
    execute_comment);
}

uint64_t* decode_funct3(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* funct3_nid, char* funct3_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_funct3_nid) {
  return new_ternary(OP_ITE, sid,
    new_binary_boolean(OP_EQ,
      get_instruction_funct3(ir_nid),
      funct3_nid,
      format_comment("funct3 == %s", (uint64_t) funct3_comment)),
    execute_nid,
    other_funct3_nid,
    execute_comment);
}

uint64_t* decode_funct3_conditional(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* funct3_nid, char* funct3_comment,
  uint64_t* evaluate_nid, uint64_t* branch_nid, uint64_t* continue_nid, char* branch_comment,
  uint64_t* other_funct3_nid) {
  return decode_funct3(sid, ir_nid,
    funct3_nid, funct3_comment,
    new_ternary(OP_ITE, sid,
      evaluate_nid,
      branch_nid,
      continue_nid,
      branch_comment),
    "evaluate branch condition if funct3 matches",
    other_funct3_nid);
}

uint64_t* decode_funct7(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* funct7_nid, char* funct7_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_funct7_nid) {
  return new_ternary(OP_ITE, sid,
    new_binary_boolean(OP_EQ,
      get_instruction_funct7(ir_nid),
      funct7_nid,
      format_comment("funct7 == %s", (uint64_t) funct7_comment)),
    execute_nid,
    other_funct7_nid,
    execute_comment);
}

uint64_t* decode_lui(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* lui_nid, char* comment,
  uint64_t* other_opcode_nid) {
  return decode_opcode(sid, ir_nid,
    NID_OP_LUI, "LUI?",
    lui_nid, format_comment("lui %s", (uint64_t) comment),
    other_opcode_nid);
}

uint64_t* decode_auipc(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* auipc_nid, char* comment,
  uint64_t* other_opcode_nid) {
  if (RISCU)
    return other_opcode_nid;

  return decode_opcode(sid, ir_nid,
    NID_OP_AUIPC, "AUIPC?",
    auipc_nid, format_comment("auipc %s", (uint64_t) comment),
    other_opcode_nid);
}

uint64_t* decode_funct7_6(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* funct_nid, char* funct_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_funct_nid) {
  if (IS64BITTARGET)
    return new_ternary(OP_ITE, sid,
      new_binary_boolean(OP_EQ,
        get_instruction_funct6(ir_nid),
        funct_nid,
        format_comment("funct6 == %s", (uint64_t) funct_comment)),
      execute_nid,
      other_funct_nid,
      execute_comment);
  else
    return new_ternary(OP_ITE, sid,
      new_binary_boolean(OP_EQ,
        get_instruction_funct7(ir_nid),
        funct_nid,
        format_comment("funct7 == %s", (uint64_t) funct_comment)),
      execute_nid,
      other_funct_nid,
      execute_comment);
}

uint64_t* decode_shift_RV64I(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* funct7_sll_srl_nid, uint64_t* slliw_nid, uint64_t* srliw_nid,
  uint64_t* funct7_sra_nid, uint64_t* sraiw_nid, char* comment,
  uint64_t* no_funct_nid) {
  return decode_funct7(sid, ir_nid,
    funct7_sll_srl_nid, "SLLIW or SRLIW?",
    decode_funct3(sid, ir_nid,
      NID_F3_SLL, "SLLIW?",
      slliw_nid, format_comment("slliw %s", (uint64_t) comment),
      decode_funct3(sid, ir_nid,
        NID_F3_SRL, "SRLIW?",
        srliw_nid, format_comment("srliw %s", (uint64_t) comment),
        no_funct_nid)),
    format_comment("slliw or srliw %s", (uint64_t) comment),
    decode_funct7(sid, ir_nid,
      funct7_sra_nid, "SRAIW?",
      decode_funct3(sid, ir_nid,
        NID_F3_SRA, "SRAIW?",
        sraiw_nid, format_comment("sraiw %s", (uint64_t) comment),
        no_funct_nid),
      format_comment("sraiw %s", (uint64_t) comment),
      no_funct_nid));
}

uint64_t* decode_shift_imm(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* funct_sll_srl_nid, uint64_t* slli_nid, uint64_t* srli_nid,
  uint64_t* funct_sra_nid, uint64_t* srai_nid, char* comment,
  uint64_t* no_funct_nid) {
  return decode_funct7_6(sid, ir_nid,
    funct_sll_srl_nid, "SLLI or SRLI?",
    decode_funct3(sid, ir_nid,
      NID_F3_SLL, "SLLI?",
      slli_nid, format_comment("slli %s", (uint64_t) comment),
      decode_funct3(sid, ir_nid,
        NID_F3_SRL, "SRLI?",
        srli_nid, format_comment("srli %s", (uint64_t) comment),
        no_funct_nid)),
    format_comment("slli or srli %s", (uint64_t) comment),
    decode_funct7_6(sid, ir_nid,
      funct_sra_nid, "SRAI?",
      decode_funct3(sid, ir_nid,
        NID_F3_SRA, "SRAI?",
        srai_nid, format_comment("srai %s", (uint64_t) comment),
        no_funct_nid),
      format_comment("srai %s", (uint64_t) comment),
      no_funct_nid));
}

uint64_t* decode_illegal_shamt(uint64_t* ir_nid) {
  if (IS64BITTARGET)
    return decode_opcode(SID_BOOLEAN, ir_nid,
      NID_OP_IMM_32, "IMM-32?",
      decode_shift_RV64I(SID_BOOLEAN, ir_nid,
        NID_F7_SLL_SRL_ILLEGAL, NID_SLLIW, NID_SRLIW,
        NID_F7_SRA_ILLEGAL, NID_SRAIW, "there?",
        NID_FALSE),
      "illegal shamt there?",
      NID_FALSE);
  else
    return decode_opcode(SID_BOOLEAN, ir_nid,
      NID_OP_IMM, "IMM?",
      decode_shift_imm(SID_BOOLEAN, ir_nid,
        NID_F7_SLL_SRL_ILLEGAL, NID_C_SLLI, NID_SRLI,
        NID_F7_SRA_ILLEGAL, NID_SRAI, "there?",
        NID_FALSE),
      "illegal shamt there?",
      NID_FALSE);
}

uint64_t* decode_imm_RV64I(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* addiw_nid, uint64_t* slliw_nid, uint64_t* srliw_nid, uint64_t* sraiw_nid, char* comment,
  uint64_t* no_funct_nid, uint64_t* other_opcode_nid) {
  if (IS64BITTARGET)
    return decode_opcode(sid, ir_nid,
      NID_OP_IMM_32, "IMM-32?",
      decode_funct3(sid, ir_nid,
        NID_F3_ADDI, "ADDIW?",
        addiw_nid, format_comment("addiw %s", (uint64_t) comment),
        decode_shift_RV64I(sid, ir_nid,
          NID_F7_ADD_SLT_XOR_OR_AND_SLL_SRL, slliw_nid, srliw_nid,
          NID_F7_SUB_SRA, sraiw_nid, comment,
          no_funct_nid)),
      format_comment("imm-32 %s", (uint64_t) comment),
      other_opcode_nid);
  else
    return other_opcode_nid;
}

uint64_t* decode_imm(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* addi_nid, uint64_t* slti_nid, uint64_t* sltiu_nid,
  uint64_t* xori_nid, uint64_t* ori_nid, uint64_t* andi_nid,
  uint64_t* slli_nid, uint64_t* srli_nid, uint64_t* srai_nid,
  uint64_t* addiw_nid, uint64_t* slliw_nid, uint64_t* srliw_nid, uint64_t* sraiw_nid, char* comment,
  uint64_t* no_funct_nid, uint64_t* other_opcode_nid) {
  uint64_t* funct_sll_srl_nid;
  uint64_t* funct_sra_nid;

  if (IS64BITTARGET) {
    funct_sll_srl_nid = NID_F6_SLL_SRL;
    funct_sra_nid     = NID_F6_SRA;
  } else {
    funct_sll_srl_nid = NID_F7_ADD_SLT_XOR_OR_AND_SLL_SRL;
    funct_sra_nid     = NID_F7_SUB_SRA;
  }

  if (RISCU)
    return decode_opcode(sid, ir_nid,
      NID_OP_IMM, "IMM?",
      decode_funct3(sid, ir_nid,
        NID_F3_ADDI, "ADDI?",
        addi_nid, format_comment("addi %s", (uint64_t) comment),
        no_funct_nid),
      format_comment("imm %s", (uint64_t) comment),
      other_opcode_nid);

  return decode_opcode(sid, ir_nid,
    NID_OP_IMM, "IMM?",
    decode_funct3(sid, ir_nid,
      NID_F3_ADDI, "ADDI?",
      addi_nid, format_comment("addi %s", (uint64_t) comment),
      decode_funct3(sid, ir_nid,
        NID_F3_SLT, "SLTI?",
        slti_nid, format_comment("slti %s", (uint64_t) comment),
        decode_funct3(sid, ir_nid,
          NID_F3_SLTU, "SLTIU?",
          sltiu_nid, format_comment("sltiu %s", (uint64_t) comment),
          decode_funct3(sid, ir_nid,
            NID_F3_XOR, "XORI?",
            xori_nid, format_comment("xori %s", (uint64_t) comment),
            decode_funct3(sid, ir_nid,
              NID_F3_OR, "ORI?",
              ori_nid, format_comment("ori %s", (uint64_t) comment),
              decode_funct3(sid, ir_nid,
                NID_F3_AND, "ANDI?",
                andi_nid, format_comment("andi %s", (uint64_t) comment),
                decode_shift_imm(sid, ir_nid,
                  funct_sll_srl_nid, slli_nid, srli_nid,
                  funct_sra_nid, srai_nid, comment,
                  no_funct_nid))))))),
    format_comment("imm %s", (uint64_t) comment),
    decode_imm_RV64I(sid, ir_nid,
      addiw_nid, slliw_nid, srliw_nid, sraiw_nid, comment,
      no_funct_nid, other_opcode_nid));
}

uint64_t* decode_op_RV64I(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* addw_nid, uint64_t* subw_nid,
  uint64_t* sllw_nid, uint64_t* srlw_nid, uint64_t* sraw_nid, char* comment,
  uint64_t* no_funct3_nid, uint64_t* RV64M_nid, uint64_t* other_opcode_nid) {
  if (IS64BITTARGET)
    return decode_opcode(sid, ir_nid,
      NID_OP_OP_32, "OP-32?",
      decode_funct7(sid, ir_nid,
        NID_F7_ADD_SLT_XOR_OR_AND_SLL_SRL, "ADDW or SLLW or SRLW?",
        decode_funct3(sid, ir_nid,
          NID_F3_ADD_SUB_MUL, "ADDW?",
          addw_nid, format_comment("addw %s", (uint64_t) comment),
          decode_funct3(sid, ir_nid,
            NID_F3_SLL, "SLLW?",
            sllw_nid, format_comment("sllw %s", (uint64_t) comment),
            decode_funct3(sid, ir_nid,
              NID_F3_SRL, "SRLW?",
              srlw_nid, format_comment("srlw %s", (uint64_t) comment),
              no_funct3_nid))),
        format_comment("addw or sllw or srlw %s", (uint64_t) comment),
        decode_funct7(sid, ir_nid,
          NID_F7_SUB_SRA, "SUBW or SRAW?",
          decode_funct3(sid, ir_nid,
            NID_F3_ADD_SUB_MUL, "SUBW?",
            subw_nid, format_comment("subw %s", (uint64_t) comment),
            decode_funct3(sid, ir_nid,
              NID_F3_SRA, "SRAW?",
              sraw_nid, format_comment("sraw %s", (uint64_t) comment),
              no_funct3_nid)),
          format_comment("subw or sraw %s", (uint64_t) comment),
          RV64M_nid)),
      format_comment("op-32 %s", (uint64_t) comment),
      other_opcode_nid);
  else
    return other_opcode_nid;
}

uint64_t* decode_op(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* add_nid, uint64_t* sub_nid,
  uint64_t* slt_nid, uint64_t* sltu_nid,
  uint64_t* xor_nid, uint64_t* or_nid, uint64_t* and_nid,
  uint64_t* sll_nid, uint64_t* srl_nid, uint64_t* sra_nid,
  uint64_t* addw_nid, uint64_t* subw_nid,
  uint64_t* sllw_nid, uint64_t* srlw_nid, uint64_t* sraw_nid, char* comment,
  uint64_t* no_funct3_nid, uint64_t* RV32M_nid, uint64_t* RV64M_nid, uint64_t* other_opcode_nid) {
  if (RISCU)
    return decode_opcode(sid, ir_nid,
      NID_OP_OP, "OP?",
      decode_funct7(sid, ir_nid,
        NID_F7_ADD_SLT_XOR_OR_AND_SLL_SRL, "ADD or SLTU?",
        decode_funct3(sid, ir_nid,
          NID_F3_ADD_SUB_MUL, "ADD?",
          add_nid, format_comment("add %s", (uint64_t) comment),
          decode_funct3(sid, ir_nid,
            NID_F3_SLTU, "SLTU?",
            sltu_nid, format_comment("sltu %s", (uint64_t) comment),
            no_funct3_nid)),
        format_comment("add or sltu %s", (uint64_t) comment),
        decode_funct7(sid, ir_nid,
          NID_F7_SUB_SRA, "SUB?",
          decode_funct3(sid, ir_nid,
            NID_F3_ADD_SUB_MUL, "SUB?",
            sub_nid, format_comment("sub %s", (uint64_t) comment),
            no_funct3_nid),
          format_comment("sub %s", (uint64_t) comment),
          RV32M_nid)),
      format_comment("op %s", (uint64_t) comment),
      other_opcode_nid);

  return decode_opcode(sid, ir_nid,
    NID_OP_OP, "OP?",
    decode_funct7(sid, ir_nid,
      NID_F7_ADD_SLT_XOR_OR_AND_SLL_SRL, "ADD or SLT or SLTU or XOR or OR or AND or SLL or SRL?",
      decode_funct3(sid, ir_nid,
        NID_F3_ADD_SUB_MUL, "ADD?",
        add_nid, format_comment("add %s", (uint64_t) comment),
        decode_funct3(sid, ir_nid,
          NID_F3_SLT, "SLT?",
          slt_nid, format_comment("slt %s", (uint64_t) comment),
          decode_funct3(sid, ir_nid,
            NID_F3_SLTU, "SLTU?",
            sltu_nid, format_comment("sltu %s", (uint64_t) comment),
            decode_funct3(sid, ir_nid,
              NID_F3_XOR, "XOR?",
              xor_nid, format_comment("xor %s", (uint64_t) comment),
              decode_funct3(sid, ir_nid,
                NID_F3_OR, "OR?",
                or_nid, format_comment("or %s", (uint64_t) comment),
                decode_funct3(sid, ir_nid,
                  NID_F3_AND, "AND?",
                  and_nid, format_comment("and %s", (uint64_t) comment),
                  decode_funct3(sid, ir_nid,
                    NID_F3_SLL, "SLL?",
                    sll_nid, format_comment("sll %s", (uint64_t) comment),
                    decode_funct3(sid, ir_nid,
                      NID_F3_SRL, "SRL?",
                      srl_nid, format_comment("srl %s", (uint64_t) comment),
                      no_funct3_nid)))))))),
      format_comment("add or slt or sltu or xor or or or and or sll or srl %s", (uint64_t) comment),
      decode_funct7(sid, ir_nid,
        NID_F7_SUB_SRA, "SUB or SRA?",
        decode_funct3(sid, ir_nid,
          NID_F3_ADD_SUB_MUL, "SUB?",
          sub_nid, format_comment("sub %s", (uint64_t) comment),
          decode_funct3(sid, ir_nid,
            NID_F3_SRA, "SRA?",
            sra_nid, format_comment("sra %s", (uint64_t) comment),
            no_funct3_nid)),
        format_comment("sub or sra %s", (uint64_t) comment),
        RV32M_nid)),
    format_comment("op %s", (uint64_t) comment),
    decode_op_RV64I(sid, ir_nid,
      addw_nid, subw_nid, sllw_nid, srlw_nid, sraw_nid, comment,
      no_funct3_nid, RV64M_nid, other_opcode_nid));
}

uint64_t* decode_RV32M(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* mul_nid, uint64_t* mulh_nid, uint64_t* mulhsu_nid, uint64_t* mulhu_nid,
  uint64_t* div_nid, uint64_t* divu_nid, uint64_t* rem_nid, uint64_t* remu_nid, char* comment,
  uint64_t* no_funct_nid) {
  if (RISCU)
    return decode_funct7(sid, ir_nid,
      NID_F7_MUL_DIV_REM, "MUL or DIVU or REMU?",
      decode_funct3(sid, ir_nid,
        NID_F3_ADD_SUB_MUL, "MUL?",
        mul_nid, format_comment("mul %s", (uint64_t) comment),
        decode_funct3(sid, ir_nid,
          NID_F3_DIVU, "DIVU?",
          divu_nid, format_comment("divu %s", (uint64_t) comment),
          decode_funct3(sid, ir_nid,
            NID_F3_REMU, "REMU?",
            remu_nid, format_comment("remu %s", (uint64_t) comment),
            no_funct_nid))),
      format_comment("mul or divu or remu %s", (uint64_t) comment),
      no_funct_nid);

  if (RV32M)
    return decode_funct7(sid, ir_nid,
      NID_F7_MUL_DIV_REM, "MUL or MULH or MULHSU or MULHU or DIV or DIVU or REM or REMU?",
      decode_funct3(sid, ir_nid,
        NID_F3_ADD_SUB_MUL, "MUL?",
        mul_nid, format_comment("mul %s", (uint64_t) comment),
        decode_funct3(sid, ir_nid,
          NID_F3_MULH, "MULH?",
          mulh_nid, format_comment("mulh %s", (uint64_t) comment),
          decode_funct3(sid, ir_nid,
            NID_F3_MULHSU, "MULHSU?",
            mulhsu_nid, format_comment("mulhsu %s", (uint64_t) comment),
            decode_funct3(sid, ir_nid,
              NID_F3_MULHU, "MULHU?",
              mulhu_nid, format_comment("mulhu %s", (uint64_t) comment),
              decode_funct3(sid, ir_nid,
                NID_F3_DIV, "DIV?",
                div_nid, format_comment("div %s", (uint64_t) comment),
                decode_funct3(sid, ir_nid,
                  NID_F3_DIVU, "DIVU?",
                  divu_nid, format_comment("divu %s", (uint64_t) comment),
                  decode_funct3(sid, ir_nid,
                    NID_F3_REM, "REM?",
                    rem_nid, format_comment("rem %s", (uint64_t) comment),
                    decode_funct3(sid, ir_nid,
                      NID_F3_REMU, "REMU?",
                      remu_nid, format_comment("remu %s", (uint64_t) comment),
                      no_funct_nid)))))))),
      format_comment("mul or mulh or mulhsu or mulhu or div or divu or rem or remu %s", (uint64_t) comment),
      no_funct_nid);
  else
    return no_funct_nid;
}

uint64_t* decode_RV64M(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* mulw_nid,
  uint64_t* divw_nid, uint64_t* divuw_nid, uint64_t* remw_nid, uint64_t* remuw_nid, char* comment,
  uint64_t* no_funct_nid) {
  if (RISCU)
    return no_funct_nid;

  if (RV64M)
    return decode_funct7(sid, ir_nid,
      NID_F7_MUL_DIV_REM, "MULW or DIVW or DIVUW or REMW or REMUW?",
      decode_funct3(sid, ir_nid,
        NID_F3_ADD_SUB_MUL, "MULW?",
        mulw_nid, format_comment("mulw %s", (uint64_t) comment),
        decode_funct3(sid, ir_nid,
          NID_F3_DIV, "DIVW?",
          divw_nid, format_comment("divw %s", (uint64_t) comment),
          decode_funct3(sid, ir_nid,
            NID_F3_DIVU, "DIVUW?",
            divuw_nid, format_comment("divuw %s", (uint64_t) comment),
            decode_funct3(sid, ir_nid,
              NID_F3_REM, "REMW?",
              remw_nid, format_comment("remw %s", (uint64_t) comment),
              decode_funct3(sid, ir_nid,
                NID_F3_REMU, "REMUW?",
                remuw_nid, format_comment("remuw %s", (uint64_t) comment),
                no_funct_nid))))),
      format_comment("mulw or divw or divuw or remw or remuw %s", (uint64_t) comment),
      no_funct_nid);
  else
    return no_funct_nid;
}

uint64_t* decode_division_remainder_by_zero(uint64_t* ir_nid, uint64_t* register_file_nid) {
  uint64_t* RV64M_nid;
  uint64_t* RV32M_nid;

  if (RISCU + RV32M + RV64M) {
    if (RISCU)
      RV32M_nid = decode_opcode(SID_BOOLEAN, ir_nid,
        NID_OP_OP, "OP?",
        decode_RV32M(SID_BOOLEAN, ir_nid,
          NID_FALSE, NID_FALSE, NID_FALSE, NID_FALSE,
          NID_FALSE, NID_DIVU, NID_FALSE, NID_REMU, "active?",
          NID_FALSE),
        "divu or remu active?",
        NID_FALSE);
    else {
      if (RV64M)
        RV64M_nid = decode_opcode(SID_BOOLEAN, ir_nid,
          NID_OP_OP_32, "OP-32?",
          decode_RV64M(SID_BOOLEAN, ir_nid,
            NID_FALSE,
            NID_DIVW, NID_DIVUW, NID_REMW, NID_REMUW, "active?",
            NID_FALSE),
          "divw or divuw or remw or remuw active?",
          NID_FALSE);
      else
        RV64M_nid = NID_FALSE;

      if (RV32M)
        RV32M_nid = decode_opcode(SID_BOOLEAN, ir_nid,
          NID_OP_OP, "OP?",
          decode_RV32M(SID_BOOLEAN, ir_nid,
            NID_FALSE, NID_FALSE, NID_FALSE, NID_FALSE,
            NID_DIV, NID_DIVU, NID_REM, NID_REMU, "active?",
            NID_FALSE),
          "div or divu or rem or remu active?",
          RV64M_nid);
      else
        RV32M_nid = RV64M_nid;
    }

    return new_binary_boolean(OP_AND,
      RV32M_nid,
      new_binary_boolean(OP_EQ,
        load_register_value(get_instruction_rs2(ir_nid), "rs2 value", register_file_nid),
        NID_MACHINE_WORD_0,
        "rs2 value == zero?"),
      "division or remainder by zero?");
  } else
    return UNUSED;
}

uint64_t* decode_signed_division_remainder_overflow(uint64_t* ir_nid, uint64_t* register_file_nid) {
  uint64_t* rs1_value_nid;
  uint64_t* rs2_value_nid;

  uint64_t* rs1_value_single_word_nid;
  uint64_t* rs2_value_single_word_nid;

  uint64_t* RV64M_nid;
  uint64_t* RV32M_nid;

  if (RISCU == 0)
    if (RV32M + RV64M) {
      rs1_value_nid = load_register_value(get_instruction_rs1(ir_nid), "rs1 value", register_file_nid);
      rs2_value_nid = load_register_value(get_instruction_rs2(ir_nid), "rs2 value", register_file_nid);

      rs1_value_single_word_nid = slice_single_word_from_machine_word(rs1_value_nid);
      rs2_value_single_word_nid = slice_single_word_from_machine_word(rs2_value_nid);

      if (RV64M)
        RV64M_nid = decode_opcode(SID_BOOLEAN, ir_nid,
          NID_OP_OP_32, "OP-32?",
          new_binary_boolean(OP_AND,
            decode_RV64M(SID_BOOLEAN, ir_nid,
              NID_FALSE,
              NID_DIVW, NID_FALSE, NID_REMW, NID_FALSE, "active?",
              NID_FALSE),
            new_binary_boolean(OP_AND,
              new_binary_boolean(OP_EQ,
                rs1_value_single_word_nid,
                NID_SINGLE_WORD_INT_MIN,
                "rs1 value == INT_MIN?"),
              new_binary_boolean(OP_EQ,
                rs2_value_single_word_nid,
                NID_SINGLE_WORD_MINUS_1,
                "rs2 value == -1?"),
              "rs1 value == INT_MIN and rs2 value == -1?"),
            "divw or remw overflow?"),
          "active divw or remw overflow?",
          NID_FALSE);
      else
        RV64M_nid = NID_FALSE;

      if (RV32M)
        RV32M_nid = decode_opcode(SID_BOOLEAN, ir_nid,
          NID_OP_OP, "OP?",
          new_binary_boolean(OP_AND,
            decode_RV32M(SID_BOOLEAN, ir_nid,
              NID_FALSE, NID_FALSE, NID_FALSE, NID_FALSE,
              NID_DIV, NID_FALSE, NID_REM, NID_FALSE, "active?",
              NID_FALSE),
            new_binary_boolean(OP_AND,
              new_binary_boolean(OP_EQ,
                rs1_value_nid,
                NID_MACHINE_WORD_INT_MIN,
                "rs1 value == INT_MIN?"),
              new_binary_boolean(OP_EQ,
                rs2_value_nid,
                NID_MACHINE_WORD_MINUS_1,
                "rs2 value == -1?"),
              "rs1 value == INT_MIN and rs2 value == -1?"),
            "div or rem overflow?"),
          "active div or rem overflow?",
          RV64M_nid);
      else
        RV32M_nid = RV64M_nid;

      return RV32M_nid;
    }

  return UNUSED;
}

uint64_t* decode_load_RV64I(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* ld_nid, uint64_t* lwu_nid, char* comment,
  uint64_t* no_funct3_nid) {
  if (IS64BITTARGET)
    if (RISCU)
      return decode_funct3(sid, ir_nid,
        NID_F3_LD, "LD?",
        ld_nid, format_comment("ld %s", (uint64_t) comment),
        no_funct3_nid);
    else
      return decode_funct3(sid, ir_nid,
        NID_F3_LD, "LD?",
        ld_nid, format_comment("ld %s", (uint64_t) comment),
        decode_funct3(sid, ir_nid,
          NID_F3_LWU, "LWU?",
          lwu_nid, format_comment("lwu %s", (uint64_t) comment),
          no_funct3_nid));
  else
    return no_funct3_nid;
}

uint64_t* decode_load(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* ld_nid, uint64_t* lwu_nid,
  uint64_t* lw_nid,
  uint64_t* lh_nid, uint64_t* lhu_nid,
  uint64_t* lb_nid, uint64_t* lbu_nid, char* comment,
  uint64_t* no_funct3_nid, uint64_t* other_opcode_nid) {
  if (RISCU) {
    if (IS64BITTARGET)
      return decode_opcode(sid, ir_nid,
        NID_OP_LOAD, "LOAD?",
        decode_load_RV64I(sid, ir_nid,
          ld_nid, lwu_nid, comment,
          no_funct3_nid),
        format_comment("load %s", (uint64_t) comment),
        other_opcode_nid);
    else
      return decode_opcode(sid, ir_nid,
        NID_OP_LOAD, "LOAD?",
        decode_funct3(sid, ir_nid,
          NID_F3_LW, "LW?",
          lw_nid, format_comment("lw %s", (uint64_t) comment),
          no_funct3_nid),
        format_comment("load %s", (uint64_t) comment),
        other_opcode_nid);
  }

  return decode_opcode(sid, ir_nid,
    NID_OP_LOAD, "LOAD?",
    decode_load_RV64I(sid, ir_nid,
      ld_nid, lwu_nid, comment,
      decode_funct3(sid, ir_nid,
        NID_F3_LW, "LW?",
        lw_nid, format_comment("lw %s", (uint64_t) comment),
        decode_funct3(sid, ir_nid,
          NID_F3_LH, "LH?",
          lh_nid, format_comment("lh %s", (uint64_t) comment),
          decode_funct3(sid, ir_nid,
            NID_F3_LHU, "LHU?",
            lhu_nid, format_comment("lhu %s", (uint64_t) comment),
            decode_funct3(sid, ir_nid,
              NID_F3_LB, "LB?",
              lb_nid, format_comment("lb %s", (uint64_t) comment),
              decode_funct3(sid, ir_nid,
                NID_F3_LBU, "LBU?",
                lbu_nid, format_comment("lbu %s", (uint64_t) comment),
                no_funct3_nid)))))),
    format_comment("load %s", (uint64_t) comment),
    other_opcode_nid);
}

uint64_t* decode_store_RV64I(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* sd_nid, char* comment,
  uint64_t* no_funct3_nid) {
  if (IS64BITTARGET)
    return decode_funct3(sid, ir_nid,
      NID_F3_SD, "SD?",
      sd_nid, format_comment("sd %s", (uint64_t) comment),
      no_funct3_nid);
  else
    return no_funct3_nid;
}

uint64_t* decode_store(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* sd_nid,
  uint64_t* sw_nid, uint64_t* sh_nid, uint64_t* sb_nid, char* comment,
  uint64_t* no_funct3_nid, uint64_t* other_opcode_nid) {
  if (RISCU) {
    if (IS64BITTARGET)
      return decode_opcode(sid, ir_nid,
        NID_OP_STORE, "STORE?",
        decode_store_RV64I(sid, ir_nid,
          sd_nid, comment,
          no_funct3_nid),
        format_comment("store %s", (uint64_t) comment),
        other_opcode_nid);
    else
      return decode_opcode(sid, ir_nid,
        NID_OP_STORE, "STORE?",
        decode_funct3(sid, ir_nid,
          NID_F3_SW, "SW?",
          sw_nid, format_comment("sw %s", (uint64_t) comment),
          no_funct3_nid),
        format_comment("store %s", (uint64_t) comment),
        other_opcode_nid);
  }

  return decode_opcode(sid, ir_nid,
    NID_OP_STORE, "STORE?",
    decode_store_RV64I(sid, ir_nid,
      sd_nid, comment,
      decode_funct3(sid, ir_nid,
        NID_F3_SW, "SW?",
        sw_nid, format_comment("sw %s", (uint64_t) comment),
        decode_funct3(sid, ir_nid,
          NID_F3_SH, "SH?",
          sh_nid, format_comment("sh %s", (uint64_t) comment),
          decode_funct3(sid, ir_nid,
            NID_F3_SB, "SB?",
            sb_nid, format_comment("sb %s", (uint64_t) comment),
            no_funct3_nid)))),
    format_comment("store %s", (uint64_t) comment),
    other_opcode_nid);
}

uint64_t* decode_branch(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* beq_nid, uint64_t* bne_nid,
  uint64_t* blt_nid, uint64_t* bge_nid,
  uint64_t* bltu_nid, uint64_t* bgeu_nid,
  uint64_t* branch_nid, uint64_t* continue_nid, char* comment,
  uint64_t* no_funct3_nid, uint64_t* other_opcode_nid) {
  if (RISCU)
    return decode_opcode(sid, ir_nid,
      NID_OP_BRANCH, "BRANCH?",
      decode_funct3_conditional(sid, ir_nid,
        NID_F3_BEQ, "BEQ?",
        beq_nid, branch_nid, continue_nid, format_comment("beq %s", (uint64_t) comment),
        no_funct3_nid),
      format_comment("branch %s", (uint64_t) comment),
      other_opcode_nid);

  return decode_opcode(sid, ir_nid,
    NID_OP_BRANCH, "BRANCH?",
    decode_funct3_conditional(sid, ir_nid,
      NID_F3_BEQ, "BEQ?",
      beq_nid, branch_nid, continue_nid, format_comment("beq %s", (uint64_t) comment),
      decode_funct3_conditional(sid, ir_nid,
        NID_F3_BNE, "BNE?",
        bne_nid, branch_nid, continue_nid, format_comment("bne %s", (uint64_t) comment),
        decode_funct3_conditional(sid, ir_nid,
          NID_F3_BLT, "BLT?",
          blt_nid, branch_nid, continue_nid, format_comment("blt %s", (uint64_t) comment),
          decode_funct3_conditional(sid, ir_nid,
            NID_F3_BGE, "BGE?",
            bge_nid, branch_nid, continue_nid, format_comment("bge %s", (uint64_t) comment),
            decode_funct3_conditional(sid, ir_nid,
              NID_F3_BLTU, "BLTU?",
              bltu_nid, branch_nid, continue_nid, format_comment("bltu %s", (uint64_t) comment),
              decode_funct3_conditional(sid, ir_nid,
                NID_F3_BGEU, "BGEU?",
                bgeu_nid, branch_nid, continue_nid, format_comment("bgeu %s", (uint64_t) comment),
                no_funct3_nid)))))),
    format_comment("branch %s", (uint64_t) comment),
    other_opcode_nid);
}

uint64_t* decode_jal(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* jal_nid, char* comment,
  uint64_t* other_opcode_nid) {
  return decode_opcode(sid, ir_nid,
    NID_OP_JAL, "JAL?",
    jal_nid, format_comment("jal %s", (uint64_t) comment),
    other_opcode_nid);
}

uint64_t* decode_jalr(uint64_t* sid, uint64_t* ir_nid,
  uint64_t* jalr_nid, char* comment,
  uint64_t* no_funct3_nid, uint64_t* other_opcode_nid) {
  return decode_opcode(sid, ir_nid,
    NID_OP_JALR, "JALR?",
    decode_funct3(sid, ir_nid,
      NID_F3_JALR, "JALR?",
      jalr_nid, format_comment("jalr %s", (uint64_t) comment),
      no_funct3_nid),
    format_comment("jalr %s", (uint64_t) comment),
    other_opcode_nid);
}

uint64_t* decode_instruction(uint64_t* ir_nid) {
  return new_ternary(OP_ITE, SID_BOOLEAN,
    new_binary_boolean(OP_EQ, ir_nid, NID_ECALL_I, "ir == ECALL?"),
    NID_ECALL,
    decode_imm(SID_BOOLEAN, ir_nid,
      NID_ADDI,
      NID_SLTI,
      NID_SLTIU,
      NID_XORI,
      NID_ORI,
      NID_ANDI,
      NID_SLLI,
      NID_SRLI,
      NID_SRAI,
      NID_ADDIW,
      NID_SLLIW,
      NID_SRLIW,
      NID_SRAIW,
      "known?", NID_FALSE,
      decode_op(SID_BOOLEAN, ir_nid,
        NID_ADD,
        NID_SUB,
        NID_SLT,
        NID_SLTU,
        NID_XOR,
        NID_OR,
        NID_AND,
        NID_SLL,
        NID_SRL,
        NID_SRA,
        NID_ADDW,
        NID_SUBW,
        NID_SLLW,
        NID_SRLW,
        NID_SRAW,
        "known?", NID_FALSE,
        decode_RV32M(SID_BOOLEAN, ir_nid,
          NID_MUL,
          NID_MULH,
          NID_MULHSU,
          NID_MULHU,
          NID_DIV,
          NID_DIVU,
          NID_REM,
          NID_REMU,
          "known?", NID_FALSE),
        decode_RV64M(SID_BOOLEAN, ir_nid,
          NID_MULW,
          NID_DIVW,
          NID_DIVUW,
          NID_REMW,
          NID_REMUW,
          "known?", NID_FALSE),
        decode_load(SID_BOOLEAN, ir_nid,
          NID_LD, NID_LWU,
          NID_LW,
          NID_LH, NID_LHU,
          NID_LB, NID_LBU,
          "known?", NID_FALSE,
          decode_store(SID_BOOLEAN, ir_nid,
            NID_SD,
            NID_SW, NID_SH, NID_SB, "known?", NID_FALSE,
            decode_branch(SID_BOOLEAN, ir_nid,
              NID_BEQ, NID_BNE,
              NID_BLT, NID_BGE,
              NID_BLTU, NID_BGEU,
              NID_TRUE, NID_FALSE, "known?", NID_FALSE,
              decode_jal(SID_BOOLEAN, ir_nid,
                NID_JAL, "known?",
                decode_jalr(SID_BOOLEAN, ir_nid,
                  NID_JALR, "known?", NID_FALSE,
                  decode_lui(SID_BOOLEAN, ir_nid,
                    NID_LUI, "known?",
                    decode_auipc(SID_BOOLEAN, ir_nid,
                      NID_AUIPC, "known?",
                      NID_FALSE))))))))),
    "ecall known?");
}

uint64_t* get_rs1_value_plus_I_immediate(uint64_t* ir_nid, uint64_t* register_file_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    load_register_value(get_instruction_rs1(ir_nid), "rs1 value", register_file_nid),
    get_instruction_I_immediate(ir_nid),
    "rs1 value + I-immediate");
}

uint64_t* slice_single_word_from_machine_word(uint64_t* word_nid) {
  if (IS64BITTARGET)
    return slice_single_word_from_double_word(word_nid);
  else
    return word_nid;
}

uint64_t* extend_single_word_to_machine_word(char* op, uint64_t* word_nid) {
  if (IS64BITTARGET)
    return extend_single_word_to_double_word(op, word_nid);
  else
    return word_nid;
}

uint64_t* imm_data_flow(uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* other_data_flow_nid) {
  uint64_t* rs1_value_nid;
  uint64_t* rs1_value_single_word_nid;

  rs1_value_nid             = load_register_value(get_instruction_rs1(ir_nid), "rs1 value", register_file_nid);
  rs1_value_single_word_nid = slice_single_word_from_machine_word(rs1_value_nid);

  return decode_imm(SID_MACHINE_WORD, ir_nid,
    get_rs1_value_plus_I_immediate(ir_nid, register_file_nid),
    new_ext(OP_UEXT, SID_MACHINE_WORD,
      new_binary_boolean(OP_SLT,
        rs1_value_nid,
        get_instruction_I_immediate(ir_nid),
        "rs1 value < I-immediate?"),
      WORDSIZEINBITS - 1,
      "unsigned-extend Boolean to machine word"),
    new_ext(OP_UEXT, SID_MACHINE_WORD,
      new_binary_boolean(OP_ULT,
        rs1_value_nid,
        get_instruction_I_immediate(ir_nid),
        "rs1 value < I-immediate (unsigned)?"),
      WORDSIZEINBITS - 1,
      "unsigned-extend Boolean to machine word"),
    new_binary(OP_XOR, SID_MACHINE_WORD,
      rs1_value_nid,
      get_instruction_I_immediate(ir_nid),
      "rs1 value ^ I-immediate"),
    new_binary(OP_OR, SID_MACHINE_WORD,
      rs1_value_nid,
      get_instruction_I_immediate(ir_nid),
      "rs1 value | I-immediate"),
    new_binary(OP_AND, SID_MACHINE_WORD,
      rs1_value_nid,
      get_instruction_I_immediate(ir_nid),
      "rs1 value & I-immediate"),
    new_binary(OP_SLL, SID_MACHINE_WORD,
      rs1_value_nid,
      get_instruction_shamt(ir_nid),
      "rs1 value << shamt"),
    new_binary(OP_SRL, SID_MACHINE_WORD,
      rs1_value_nid,
      get_instruction_shamt(ir_nid),
      "rs1 value >> shamt"),
    new_binary(OP_SRA, SID_MACHINE_WORD,
      rs1_value_nid,
      get_instruction_shamt(ir_nid),
      "signed rs1 value >> shamt"),
    extend_single_word_to_machine_word(OP_SEXT,
      new_binary(OP_ADD, SID_SINGLE_WORD,
        rs1_value_single_word_nid,
        get_instruction_I_32_bit_immediate(ir_nid),
        "lower 32 bits of rs1 value + I-32-bit-immediate")),
    extend_single_word_to_machine_word(OP_SEXT,
      new_binary(OP_SLL, SID_SINGLE_WORD,
        rs1_value_single_word_nid,
        get_instruction_5_bit_shamt(ir_nid),
        "lower 32 bits of rs1 value << 5-bit shamt")),
    extend_single_word_to_machine_word(OP_SEXT,
      new_binary(OP_SRL, SID_SINGLE_WORD,
        rs1_value_single_word_nid,
        get_instruction_5_bit_shamt(ir_nid),
        "lower 32 bits of rs1 value >> 5-bit shamt")),
    extend_single_word_to_machine_word(OP_SEXT,
      new_binary(OP_SRA, SID_SINGLE_WORD,
        rs1_value_single_word_nid,
        get_instruction_5_bit_shamt(ir_nid),
        "signed lower 32 bits of rs1 value >> 5-bit shamt")),
    "imm register data flow",
    load_register_value(get_instruction_rd(ir_nid), "current unmodified rd value", register_file_nid),
    other_data_flow_nid);
}

uint64_t* op_data_flow(uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* other_data_flow_nid) {
  uint64_t* rd_value_nid;

  uint64_t* rs1_value_nid;
  uint64_t* rs2_value_nid;

  uint64_t* rs1_value_single_word_nid;
  uint64_t* rs2_value_single_word_nid;

  rd_value_nid = load_register_value(get_instruction_rd(ir_nid), "current unmodified rd value", register_file_nid);

  rs1_value_nid = load_register_value(get_instruction_rs1(ir_nid), "rs1 value", register_file_nid);
  rs2_value_nid = load_register_value(get_instruction_rs2(ir_nid), "rs2 value", register_file_nid);

  rs1_value_single_word_nid = slice_single_word_from_machine_word(rs1_value_nid);
  rs2_value_single_word_nid = slice_single_word_from_machine_word(rs2_value_nid);

  return decode_op(SID_MACHINE_WORD, ir_nid,
    new_binary(OP_ADD, SID_MACHINE_WORD,
      rs1_value_nid,
      rs2_value_nid,
      "rs1 value + rs2 value"),
    new_binary(OP_SUB, SID_MACHINE_WORD,
      rs1_value_nid,
      rs2_value_nid,
      "rs1 value - rs2 value"),
    new_ext(OP_UEXT, SID_MACHINE_WORD,
      new_binary_boolean(OP_SLT,
        rs1_value_nid,
        rs2_value_nid,
        "rs1 value < rs2 value?"),
      WORDSIZEINBITS - 1,
      "unsigned-extend Boolean to machine word"),
    new_ext(OP_UEXT, SID_MACHINE_WORD,
      new_binary_boolean(OP_ULT,
        rs1_value_nid,
        rs2_value_nid,
        "rs1 value < rs2 value (unsigned)?"),
      WORDSIZEINBITS - 1,
      "unsigned-extend Boolean to machine word"),
    new_binary(OP_XOR, SID_MACHINE_WORD,
      rs1_value_nid,
      rs2_value_nid,
      "rs1 value ^ rs2 value"),
    new_binary(OP_OR, SID_MACHINE_WORD,
      rs1_value_nid,
      rs2_value_nid,
      "rs1 value | rs2 value"),
    new_binary(OP_AND, SID_MACHINE_WORD,
      rs1_value_nid,
      rs2_value_nid,
      "rs1 value & rs2 value"),
    new_binary(OP_SLL, SID_MACHINE_WORD,
      rs1_value_nid,
      get_shamt(rs2_value_nid),
      "rs1 value << rs2 shamt value"),
    new_binary(OP_SRL, SID_MACHINE_WORD,
      rs1_value_nid,
      get_shamt(rs2_value_nid),
      "rs1 value >> rs2 shamt value"),
    new_binary(OP_SRA, SID_MACHINE_WORD,
      rs1_value_nid,
      get_shamt(rs2_value_nid),
      "signed rs1 value >> rs2 shamt value"),
    extend_single_word_to_machine_word(OP_SEXT,
      new_binary(OP_ADD, SID_SINGLE_WORD,
        rs1_value_single_word_nid,
        rs2_value_single_word_nid,
        "lower 32 bits of rs1 value + lower 32 bits of rs2 value")),
    extend_single_word_to_machine_word(OP_SEXT,
      new_binary(OP_SUB, SID_SINGLE_WORD,
        rs1_value_single_word_nid,
        rs2_value_single_word_nid,
        "lower 32 bits of rs1 value - lower 32 bits of rs2 value")),
    extend_single_word_to_machine_word(OP_SEXT,
      new_binary(OP_SLL, SID_SINGLE_WORD,
        rs1_value_single_word_nid,
        get_5_bit_shamt(rs2_value_nid),
        "lower 32 bits of rs1 value << rs2 5-bit shamt value")),
    extend_single_word_to_machine_word(OP_SEXT,
      new_binary(OP_SRL, SID_SINGLE_WORD,
        rs1_value_single_word_nid,
        get_5_bit_shamt(rs2_value_nid),
        "lower 32 bits of rs1 value >> rs2 5-bit shamt value")),
    extend_single_word_to_machine_word(OP_SEXT,
      new_binary(OP_SRA, SID_SINGLE_WORD,
        rs1_value_single_word_nid,
        get_5_bit_shamt(rs2_value_nid),
        "signed lower 32 bits of rs1 value >> rs2 5-bit shamt value")),
    "op register data flow",
    rd_value_nid,
    decode_RV32M(SID_MACHINE_WORD, ir_nid,
      new_binary(OP_MUL, SID_MACHINE_WORD,
        rs1_value_nid,
        rs2_value_nid,
        "rs1 value * rs2 value"),
      new_slice(SID_MACHINE_WORD,
        new_binary(OP_MUL, SID_DOUBLE_MACHINE_WORD,
          new_ext(OP_SEXT, SID_DOUBLE_MACHINE_WORD,
            rs1_value_nid, WORDSIZEINBITS, "sign-extend rs1 value to double machine word"),
          new_ext(OP_SEXT, SID_DOUBLE_MACHINE_WORD,
            rs2_value_nid, WORDSIZEINBITS, "sign-extend rs2 value to double machine word"),
          "double precision rs1 value * rs2 value"),
        2 * WORDSIZEINBITS - 1,
        WORDSIZEINBITS,
        "upper machine word"),
      new_slice(SID_MACHINE_WORD,
        new_binary(OP_MUL, SID_DOUBLE_MACHINE_WORD,
          new_ext(OP_SEXT, SID_DOUBLE_MACHINE_WORD,
            rs1_value_nid, WORDSIZEINBITS, "sign-extend rs1 value to double machine word"),
          new_ext(OP_UEXT, SID_DOUBLE_MACHINE_WORD,
            rs2_value_nid, WORDSIZEINBITS, "unsigned-extend rs2 value to double machine word"),
          "double precision rs1 value * rs2 value"),
        2 * WORDSIZEINBITS - 1,
        WORDSIZEINBITS,
        "upper machine word"),
      new_slice(SID_MACHINE_WORD,
        new_binary(OP_MUL, SID_DOUBLE_MACHINE_WORD,
          new_ext(OP_UEXT, SID_DOUBLE_MACHINE_WORD,
            rs1_value_nid, WORDSIZEINBITS, "unsigned-extend rs1 value to double machine word"),
          new_ext(OP_UEXT, SID_DOUBLE_MACHINE_WORD,
            rs2_value_nid, WORDSIZEINBITS, "unsigned-extend rs2 value to double machine word"),
          "double precision rs1 value * rs2 value"),
        2 * WORDSIZEINBITS - 1,
        WORDSIZEINBITS,
        "upper machine word"),
      new_binary(OP_SDIV, SID_MACHINE_WORD,
        rs1_value_nid,
        rs2_value_nid,
        "rs1 value / rs2 value"),
      new_binary(OP_UDIV, SID_MACHINE_WORD,
        rs1_value_nid,
        rs2_value_nid,
        "rs1 value / rs2 value (unsigned)"),
      new_binary(OP_SREM, SID_MACHINE_WORD,
        rs1_value_nid,
        rs2_value_nid,
        "rs1 value % rs2 value"),
      new_binary(OP_UREM, SID_MACHINE_WORD,
        rs1_value_nid,
        rs2_value_nid,
        "rs1 value % rs2 value (unsigned)"),
      "RV32M register data flow",
      rd_value_nid),
    decode_RV64M(SID_MACHINE_WORD, ir_nid,
      extend_single_word_to_machine_word(OP_SEXT,
        new_binary(OP_MUL, SID_SINGLE_WORD,
          rs1_value_single_word_nid,
          rs2_value_single_word_nid,
          "lower 32 bits of rs1 value * lower 32 bits of rs2 value")),
      extend_single_word_to_machine_word(OP_SEXT,
        new_binary(OP_SDIV, SID_SINGLE_WORD,
          rs1_value_single_word_nid,
          rs2_value_single_word_nid,
          "lower 32 bits of rs1 value / lower 32 bits of rs2 value")),
      extend_single_word_to_machine_word(OP_SEXT,
        new_binary(OP_UDIV, SID_SINGLE_WORD,
          rs1_value_single_word_nid,
          rs2_value_single_word_nid,
          "lower 32 bits of rs1 value / lower 32 bits of rs2 value (unsigned)")),
      extend_single_word_to_machine_word(OP_SEXT,
        new_binary(OP_SREM, SID_SINGLE_WORD,
          rs1_value_single_word_nid,
          rs2_value_single_word_nid,
          "lower 32 bits of rs1 value % lower 32 bits of rs2 value")),
      extend_single_word_to_machine_word(OP_SEXT,
        new_binary(OP_UREM, SID_SINGLE_WORD,
          rs1_value_single_word_nid,
          rs2_value_single_word_nid,
          "lower 32 bits of rs1 value % lower 32 bits of rs2 value (unsigned)")),
      "RV64M register data flow",
      rd_value_nid),
    other_data_flow_nid);
}

uint64_t* extend_byte_to_machine_word(char* op, uint64_t* byte_nid) {
  if (IS64BITTARGET)
    return extend_byte_to_double_word(op, byte_nid);
  else
    return extend_byte_to_single_word(op, byte_nid);
}

uint64_t* extend_half_word_to_machine_word(char* op, uint64_t* word_nid) {
  if (IS64BITTARGET)
    return extend_half_word_to_double_word(op, word_nid);
  else
    return extend_half_word_to_single_word(op, word_nid);
}

uint64_t* load_data_flow(uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* memory_nid, uint64_t* other_data_flow_nid) {
  return decode_load(SID_MACHINE_WORD, ir_nid,
    load_double_word(get_rs1_value_plus_I_immediate(ir_nid, register_file_nid), memory_nid),
    extend_single_word_to_machine_word(OP_UEXT,
      load_single_word(get_rs1_value_plus_I_immediate(ir_nid, register_file_nid), memory_nid)),
    extend_single_word_to_machine_word(OP_SEXT,
      load_single_word(get_rs1_value_plus_I_immediate(ir_nid, register_file_nid), memory_nid)),
    extend_half_word_to_machine_word(OP_SEXT,
      load_half_word(get_rs1_value_plus_I_immediate(ir_nid, register_file_nid), memory_nid)),
    extend_half_word_to_machine_word(OP_UEXT,
      load_half_word(get_rs1_value_plus_I_immediate(ir_nid, register_file_nid), memory_nid)),
    extend_byte_to_machine_word(OP_SEXT,
      load_byte(get_rs1_value_plus_I_immediate(ir_nid, register_file_nid), memory_nid)),
    extend_byte_to_machine_word(OP_UEXT,
      load_byte(get_rs1_value_plus_I_immediate(ir_nid, register_file_nid), memory_nid)),
    "register data flow",
    load_register_value(get_instruction_rd(ir_nid), "current unmodified rd value", register_file_nid),
    other_data_flow_nid);
}

uint64_t* load_no_seg_faults(uint64_t* ir_nid, uint64_t* register_file_nid) {
  return decode_load(SID_BOOLEAN, ir_nid,
    is_sized_block_in_main_memory(get_rs1_value_plus_I_immediate(ir_nid, register_file_nid), NID_VIRTUAL_DOUBLE_WORD_SIZE_MINUS_1),
    is_sized_block_in_main_memory(get_rs1_value_plus_I_immediate(ir_nid, register_file_nid), NID_VIRTUAL_SINGLE_WORD_SIZE_MINUS_1),
    is_sized_block_in_main_memory(get_rs1_value_plus_I_immediate(ir_nid, register_file_nid), NID_VIRTUAL_SINGLE_WORD_SIZE_MINUS_1),
    is_sized_block_in_main_memory(get_rs1_value_plus_I_immediate(ir_nid, register_file_nid), NID_VIRTUAL_HALF_WORD_SIZE_MINUS_1),
    is_sized_block_in_main_memory(get_rs1_value_plus_I_immediate(ir_nid, register_file_nid), NID_VIRTUAL_HALF_WORD_SIZE_MINUS_1),
    is_address_in_main_memory(get_rs1_value_plus_I_immediate(ir_nid, register_file_nid)),
    is_address_in_main_memory(get_rs1_value_plus_I_immediate(ir_nid, register_file_nid)),
    "no-seg-faults",
    NID_TRUE,
    NID_TRUE);
}

uint64_t* get_pc_value_plus_4(uint64_t* pc_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    pc_nid,
    NID_MACHINE_WORD_4,
    "pc value + 4");
}

uint64_t* jal_data_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* other_data_flow_nid) {
  return decode_jal(SID_MACHINE_WORD, ir_nid,
    get_pc_value_plus_4(pc_nid),
    "register data flow",
    other_data_flow_nid);
}

uint64_t* jalr_data_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* other_data_flow_nid) {
  return decode_jalr(SID_MACHINE_WORD, ir_nid,
    get_pc_value_plus_4(pc_nid),
    "register data flow",
    load_register_value(get_instruction_rd(ir_nid), "current unmodified rd value", register_file_nid),
    other_data_flow_nid);
}

uint64_t* lui_data_flow(uint64_t* ir_nid, uint64_t* other_data_flow_nid) {
  return decode_lui(SID_MACHINE_WORD, ir_nid,
    get_instruction_U_immediate(ir_nid),
    "register data flow",
    other_data_flow_nid);
}

uint64_t* get_pc_value_plus_U_immediate(uint64_t* pc_nid, uint64_t* ir_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    pc_nid,
    get_instruction_U_immediate(ir_nid),
    "pc value + U-immediate");
}

uint64_t* auipc_data_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* other_data_flow_nid) {
  return decode_auipc(SID_MACHINE_WORD, ir_nid,
    get_pc_value_plus_U_immediate(pc_nid, ir_nid),
    "register data flow",
    other_data_flow_nid);
}

uint64_t* core_register_data_flow(uint64_t* pc_nid, uint64_t* ir_nid,
  uint64_t* register_file_nid, uint64_t* memory_nid) {
  uint64_t* opcode_nid;

  uint64_t* rd_nid;
  uint64_t* rd_value_nid;

  uint64_t* no_register_data_flow_nid;

  opcode_nid = get_instruction_opcode(ir_nid);

  rd_nid       = get_instruction_rd(ir_nid);
  rd_value_nid = load_register_value(rd_nid, "current rd value", register_file_nid);

  no_register_data_flow_nid = new_binary_boolean(OP_OR,
    new_binary_boolean(OP_EQ, rd_nid, NID_ZR, "rd == register zero?"),
    new_binary_boolean(OP_OR,
      new_binary_boolean(OP_EQ, opcode_nid, NID_OP_STORE, "opcode == STORE?"),
      new_binary_boolean(OP_EQ, opcode_nid, NID_OP_BRANCH, "opcode == BRANCH?"),
      "STORE or BRANCH?"), // redundant
    "rd == zero register or STORE or BRANCH?");

  rd_value_nid =
    imm_data_flow(ir_nid, register_file_nid,
      op_data_flow(ir_nid, register_file_nid,
        load_data_flow(ir_nid, register_file_nid, memory_nid,
          jal_data_flow(pc_nid, ir_nid,
            jalr_data_flow(pc_nid, ir_nid, register_file_nid,
              lui_data_flow(ir_nid,
                auipc_data_flow(pc_nid, ir_nid, rd_value_nid)))))));

  return new_ternary(OP_ITE, SID_REGISTER_STATE,
    no_register_data_flow_nid,
    register_file_nid,
    store_register_value(rd_nid, rd_value_nid, "rd update", register_file_nid),
    "update non-zero register");
}

uint64_t* get_rs1_value_plus_S_immediate(uint64_t* ir_nid, uint64_t* register_file_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    load_register_value(get_instruction_rs1(ir_nid), "rs1 value", register_file_nid),
    get_instruction_S_immediate(ir_nid),
    "rs1 value + S-immediate");
}

uint64_t* store_data_flow(uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* memory_nid, uint64_t* other_data_flow_nid) {
  uint64_t* rs2_value_nid;

  rs2_value_nid = load_register_value(get_instruction_rs2(ir_nid), "rs2 value", register_file_nid);

  return decode_store(SID_MEMORY_STATE, ir_nid,
    store_double_word(get_rs1_value_plus_S_immediate(ir_nid, register_file_nid),
      rs2_value_nid,
      memory_nid),
    store_single_word(get_rs1_value_plus_S_immediate(ir_nid, register_file_nid),
      slice_single_word_from_machine_word(rs2_value_nid),
      memory_nid),
    store_half_word(get_rs1_value_plus_S_immediate(ir_nid, register_file_nid),
      slice_half_word_from_word(rs2_value_nid),
      memory_nid),
    store_byte(get_rs1_value_plus_S_immediate(ir_nid, register_file_nid),
      slice_byte_from_word(rs2_value_nid),
      memory_nid),
    "memory data flow",
    memory_nid,
    other_data_flow_nid);
}

uint64_t* store_no_seg_faults(uint64_t* ir_nid, uint64_t* register_file_nid) {
  return decode_store(SID_BOOLEAN, ir_nid,
    is_sized_block_in_main_memory(get_rs1_value_plus_S_immediate(ir_nid, register_file_nid), NID_VIRTUAL_DOUBLE_WORD_SIZE_MINUS_1),
    is_sized_block_in_main_memory(get_rs1_value_plus_S_immediate(ir_nid, register_file_nid), NID_VIRTUAL_SINGLE_WORD_SIZE_MINUS_1),
    is_sized_block_in_main_memory(get_rs1_value_plus_S_immediate(ir_nid, register_file_nid), NID_VIRTUAL_HALF_WORD_SIZE_MINUS_1),
    is_address_in_main_memory(get_rs1_value_plus_S_immediate(ir_nid, register_file_nid)),
    "no-seg-faults",
    NID_TRUE,
    NID_TRUE);
}

uint64_t* core_memory_data_flow(uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* memory_nid) {
  return store_data_flow(ir_nid, register_file_nid, memory_nid, memory_nid);
}

uint64_t* get_pc_value_plus_SB_immediate(uint64_t* pc_nid, uint64_t* ir_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    pc_nid,
    get_instruction_SB_immediate(ir_nid),
    "pc value + SB-immediate");
}

uint64_t* branch_control_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* other_control_flow_nid) {
  uint64_t* rs1_value_nid;
  uint64_t* rs2_value_nid;

  rs1_value_nid = load_register_value(get_instruction_rs1(ir_nid), "rs1 value", register_file_nid);
  rs2_value_nid = load_register_value(get_instruction_rs2(ir_nid), "rs2 value", register_file_nid);

  return decode_branch(SID_MACHINE_WORD, ir_nid,
    new_binary_boolean(OP_EQ, rs1_value_nid, rs2_value_nid, "rs1 value == rs2 value?"),
    new_binary_boolean(OP_NEQ, rs1_value_nid, rs2_value_nid, "rs1 value != rs2 value?"),
    new_binary_boolean(OP_SLT, rs1_value_nid, rs2_value_nid, "rs1 value < rs2 value?"),
    new_binary_boolean(OP_SGTE, rs1_value_nid, rs2_value_nid, "rs1 value >= rs2 value?"),
    new_binary_boolean(OP_ULT, rs1_value_nid, rs2_value_nid, "rs1 value < rs2 value (unsigned)?"),
    new_binary_boolean(OP_UGTE, rs1_value_nid, rs2_value_nid, "rs1 value >= rs2 value (unsigned)?"),
    get_pc_value_plus_SB_immediate(pc_nid, ir_nid),
    get_pc_value_plus_4(pc_nid),
    "pc-relative control flow",
    pc_nid,
    other_control_flow_nid);
}

uint64_t* get_pc_value_plus_UJ_immediate(uint64_t* pc_nid, uint64_t* ir_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    pc_nid,
    get_instruction_UJ_immediate(ir_nid),
    "pc value + UJ-immediate");
}

uint64_t* jal_control_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* other_control_flow_nid) {
  return decode_jal(SID_MACHINE_WORD, ir_nid,
    get_pc_value_plus_UJ_immediate(pc_nid, ir_nid),
    "pc-relative control flow",
    other_control_flow_nid);
}

uint64_t* jalr_control_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* other_control_flow_nid) {
  return decode_jalr(SID_MACHINE_WORD, ir_nid,
    new_binary(OP_AND, SID_MACHINE_WORD,
      get_rs1_value_plus_I_immediate(ir_nid, register_file_nid),
      NID_LSB_MASK,
      "reset LSB"),
    "register-relative control flow",
    get_pc_value_plus_4(pc_nid),
    other_control_flow_nid);
}

uint64_t* core_control_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* register_file_nid) {
  return
    branch_control_flow(pc_nid, ir_nid, register_file_nid,
      jal_control_flow(pc_nid, ir_nid,
        jalr_control_flow(pc_nid, ir_nid, register_file_nid,
          get_pc_value_plus_4(pc_nid))));
}

// compressed instructions

uint64_t* get_compressed_instruction_opcode(uint64_t* c_ir_nid) {
  return new_slice(SID_OPCODE_C, c_ir_nid, 1, 0, "get compressed opcode");
}

uint64_t* get_compressed_instruction_funct3(uint64_t* c_ir_nid) {
  return new_slice(SID_FUNCT3, c_ir_nid, 15, 13, "get compressed funct3");
}

uint64_t* get_compressed_instruction_funct2(uint64_t* c_ir_nid) {
  return new_slice(SID_FUNCT2, c_ir_nid, 11, 10, "get compressed funct2");
}

uint64_t* get_compressed_instruction_funct4(uint64_t* c_ir_nid) {
  return new_slice(SID_FUNCT4, c_ir_nid, 15, 12, "get compressed funct4");
}

uint64_t* get_compressed_instruction_funct6(uint64_t* c_ir_nid) {
  return new_slice(SID_FUNCT6, c_ir_nid, 15, 10, "get compressed funct6");
}

uint64_t* get_compressed_instruction_funct(uint64_t* c_ir_nid) {
  return new_slice(SID_FUNCT2, c_ir_nid, 6, 5, "get compressed funct");
}

uint64_t* get_compressed_instruction_rd(uint64_t* c_ir_nid) {
  return get_instruction_rd(c_ir_nid);
}

uint64_t* get_compressed_instruction_rd_shift(uint64_t* c_ir_nid) {
  return new_binary(OP_CONCAT, SID_REGISTER_ADDRESS,
    NID_2_BIT_OFFSET_1,
    new_slice(SID_COMPRESSED_REGISTER_ADDRESS, c_ir_nid,
      4, 2, "get compressed rd' in CL or CIW format (or rs2' in CS format)"),
    "01000 s0 offset + 3-bit compressed register address");
}

uint64_t* get_compressed_instruction_rs1(uint64_t* c_ir_nid) {
  return get_instruction_rd(c_ir_nid);
}

uint64_t* get_compressed_instruction_rs1_shift(uint64_t* c_ir_nid) {
  return new_binary(OP_CONCAT, SID_REGISTER_ADDRESS,
    NID_2_BIT_OFFSET_1,
    new_slice(SID_COMPRESSED_REGISTER_ADDRESS, c_ir_nid,
      9, 7, "get compressed rs1' in CL, CS, or CB format (or rd' in CS or CB format)"),
    "01000 s0 offset + 3-bit compressed register address");
}

uint64_t* get_compressed_instruction_rs2(uint64_t* c_ir_nid) {
  return new_slice(SID_REGISTER_ADDRESS, c_ir_nid, 6, 2, "get compressed rs2");
}

uint64_t* get_compressed_instruction_rs2_shift(uint64_t* c_ir_nid) {
  return get_compressed_instruction_rd_shift(c_ir_nid);
}

uint64_t* sign_extend_immediate(uint64_t bits, uint64_t* imm_nid) {
  return new_ext(OP_SEXT, SID_MACHINE_WORD,
    imm_nid,
    WORDSIZEINBITS - bits,
    format_comment("sign-extend %lu-bit immediate", bits));
}

uint64_t* get_compressed_instruction_shamt_5(uint64_t* c_ir_nid) {
  return new_slice(SID_1_BIT_OFFSET, c_ir_nid, 12, 12, "get compressed shamt[5]");
}

uint64_t* get_compressed_instruction_CI_immediate_shamt(uint64_t* c_ir_nid) {
  return new_binary(OP_CONCAT, SID_6_BIT_OFFSET,
    get_compressed_instruction_shamt_5(c_ir_nid),
    new_slice(SID_5_BIT_OFFSET, c_ir_nid, 6, 2, "get CI-immediate[4:0] or shamt[4:0]"),
    "get CI-immediate[5:0] or shamt[5:0]");
}

uint64_t* get_compressed_instruction_CI_immediate(uint64_t* c_ir_nid) {
  return sign_extend_immediate(6, get_compressed_instruction_CI_immediate_shamt(c_ir_nid));
}

uint64_t* get_compressed_instruction_CI_32_bit_immediate(uint64_t* c_ir_nid) {
  return new_ext(OP_SEXT, SID_SINGLE_WORD,
    get_compressed_instruction_CI_immediate_shamt(c_ir_nid),
    SINGLEWORDSIZEINBITS - 6,
    "sign-extend CI-32-bit-immediate");
}

uint64_t* get_compressed_instruction_CUI_immediate(uint64_t* c_ir_nid) {
  return sign_extend_immediate(18,
    new_binary(OP_CONCAT, SID_18_BIT_OFFSET,
      get_compressed_instruction_CI_immediate_shamt(c_ir_nid),
      NID_12_BIT_OFFSET_0,
      "get CUI-immediate[17:0]"));
}

uint64_t* get_compressed_instruction_CI16SP_immediate(uint64_t* c_ir_nid) {
  return sign_extend_immediate(10,
    new_binary(OP_CONCAT, SID_10_BIT_OFFSET,
      new_slice(SID_1_BIT_OFFSET, c_ir_nid, 12, 12, "get CI16SP-immediate[9]"),
      new_binary(OP_CONCAT, SID_9_BIT_OFFSET,
        new_slice(SID_2_BIT_OFFSET, c_ir_nid, 4, 3, "get CI16SP-immediate[8:7]"),
        new_binary(OP_CONCAT, SID_7_BIT_OFFSET,
          new_slice(SID_1_BIT_OFFSET, c_ir_nid, 5, 5, "get CI16SP-immediate[6]"),
          new_binary(OP_CONCAT, SID_6_BIT_OFFSET,
            new_slice(SID_1_BIT_OFFSET, c_ir_nid, 2, 2, "get CI16SP-immediate[5]"),
            new_binary(OP_CONCAT, SID_5_BIT_OFFSET,
              new_slice(SID_1_BIT_OFFSET, c_ir_nid, 6, 6, "get CI16SP-immediate[4]"),
              NID_4_BIT_OFFSET_0,
              "get CI16SP-immediate[4:0]"),
            "get CI16SP-immediate[5:0]"),
          "get CI16SP-immediate[6:0]"),
        "get CI16SP-immediate[8:0]"),
      "get CI16SP-immediate[9:0]"));
}

uint64_t* unsigned_extend_immediate_shamt_offset(uint64_t bits, uint64_t* imm_nid) {
  return new_ext(OP_UEXT, SID_MACHINE_WORD,
    imm_nid,
    WORDSIZEINBITS - bits,
    format_comment("unsigned-extend %lu-bit immediate or shamt or offset", bits));
}

uint64_t* get_compressed_instruction_CIW_immediate(uint64_t* c_ir_nid) {
  return unsigned_extend_immediate_shamt_offset(10,
    new_binary(OP_CONCAT, SID_10_BIT_OFFSET,
      new_slice(SID_4_BIT_OFFSET, c_ir_nid, 10, 7, "get CIW-immediate[9:6]"),
      new_binary(OP_CONCAT, SID_6_BIT_OFFSET,
        new_slice(SID_2_BIT_OFFSET, c_ir_nid, 12, 11, "get CIW-immediate[5:4]"),
        new_binary(OP_CONCAT, SID_4_BIT_OFFSET,
          new_slice(SID_1_BIT_OFFSET, c_ir_nid, 5, 5, "get CIW-immediate[3]"),
          new_binary(OP_CONCAT, SID_3_BIT_OFFSET,
            new_slice(SID_1_BIT_OFFSET, c_ir_nid, 6, 6, "get CIW-immediate[2]"),
            NID_2_BIT_OFFSET_0,
            "get CIW-immediate[2:0]"),
          "get CIW-immediate[3:0]"),
        "get CIW-immediate[5:0]"),
      "get CIW-immediate[9:0]"));
}

uint64_t* get_compressed_instruction_shamt(uint64_t* c_ir_nid) {
  return unsigned_extend_immediate_shamt_offset(6, get_compressed_instruction_CI_immediate_shamt(c_ir_nid));
}

uint64_t* get_compressed_instruction_CI32_offset(uint64_t* c_ir_nid) {
  return unsigned_extend_immediate_shamt_offset(8,
    new_binary(OP_CONCAT, SID_8_BIT_OFFSET,
      new_slice(SID_2_BIT_OFFSET, c_ir_nid, 3, 2, "get CI32-offset[7:6]"),
      new_binary(OP_CONCAT, SID_6_BIT_OFFSET,
        new_slice(SID_1_BIT_OFFSET, c_ir_nid, 12, 12, "get CI32-offset[5]"),
        new_binary(OP_CONCAT, SID_5_BIT_OFFSET,
          new_slice(SID_3_BIT_OFFSET, c_ir_nid, 6, 4, "get CI32-offset[4:2]"),
          NID_2_BIT_OFFSET_0,
          "get CI32-offset[4:0]"),
        "get CI32-offset[5:0]"),
      "get CI32-offset[7:0]"));
}

uint64_t* get_compressed_instruction_CI64_offset(uint64_t* c_ir_nid) {
  return unsigned_extend_immediate_shamt_offset(9,
    new_binary(OP_CONCAT, SID_9_BIT_OFFSET,
      new_slice(SID_3_BIT_OFFSET, c_ir_nid, 4, 2, "get CI64-offset[8:6]"),
      new_binary(OP_CONCAT, SID_6_BIT_OFFSET,
        new_slice(SID_1_BIT_OFFSET, c_ir_nid, 12, 12, "get CI64-offset[5]"),
        new_binary(OP_CONCAT, SID_5_BIT_OFFSET,
          new_slice(SID_2_BIT_OFFSET, c_ir_nid, 6, 5, "get CI64-offset[4:3]"),
          NID_3_BIT_OFFSET_0,
          "get CI64-offset[4:0]"),
        "get CI64-offset[5:0]"),
      "get CI64-offset[7:0]"));
}

uint64_t* get_compressed_instruction_CL32_offset(uint64_t* c_ir_nid) {
  return unsigned_extend_immediate_shamt_offset(7,
    new_binary(OP_CONCAT, SID_7_BIT_OFFSET,
      new_slice(SID_1_BIT_OFFSET, c_ir_nid, 5, 5, "get CL32-or-CS32-offset[6]"),
      new_binary(OP_CONCAT, SID_6_BIT_OFFSET,
        new_slice(SID_3_BIT_OFFSET, c_ir_nid, 12, 10, "get CL32-or-CS32-offset[5:3]"),
        new_binary(OP_CONCAT, SID_3_BIT_OFFSET,
          new_slice(SID_1_BIT_OFFSET, c_ir_nid, 6, 6, "get CL32-or-CS32-offset[2]"),
          NID_2_BIT_OFFSET_0,
          "get CL32-or-CS32-offset[2:0]"),
        "get CL32-or-CS32-offset[5:0]"),
      "get CL32-or-CS32-offset[6:0]"));
}

uint64_t* get_compressed_instruction_CL64_offset(uint64_t* c_ir_nid) {
  return unsigned_extend_immediate_shamt_offset(8,
    new_binary(OP_CONCAT, SID_8_BIT_OFFSET,
      new_slice(SID_2_BIT_OFFSET, c_ir_nid, 6, 5, "get CL64-or-CS64-offset[7:6]"),
      new_binary(OP_CONCAT, SID_6_BIT_OFFSET,
        new_slice(SID_3_BIT_OFFSET, c_ir_nid, 12, 10, "get CL64-or-CS64-offset[5:3]"),
        NID_3_BIT_OFFSET_0,
        "get CL64-or-CS64-offset[5:0]"),
      "get CL64-or-CS64-offset[7:0]"));
}

uint64_t* get_compressed_instruction_CSS32_offset(uint64_t* c_ir_nid) {
  return unsigned_extend_immediate_shamt_offset(8,
    new_binary(OP_CONCAT, SID_8_BIT_OFFSET,
      new_slice(SID_2_BIT_OFFSET, c_ir_nid, 8, 7, "get CSS32-offset[7:6]"),
      new_binary(OP_CONCAT, SID_6_BIT_OFFSET,
        new_slice(SID_4_BIT_OFFSET, c_ir_nid, 12, 9, "get CSS32-offset[5:2]"),
        NID_2_BIT_OFFSET_0,
        "get CSS32-offset[5:0]"),
      "get CSS32-offset[7:0]"));
}

uint64_t* get_compressed_instruction_CSS64_offset(uint64_t* c_ir_nid) {
  return unsigned_extend_immediate_shamt_offset(9,
    new_binary(OP_CONCAT, SID_9_BIT_OFFSET,
      new_slice(SID_3_BIT_OFFSET, c_ir_nid, 9, 7, "get CSS64-offset[8:6]"),
      new_binary(OP_CONCAT, SID_6_BIT_OFFSET,
        new_slice(SID_3_BIT_OFFSET, c_ir_nid, 12, 10, "get CSS64-offset[5:3]"),
        NID_3_BIT_OFFSET_0,
        "get CSS64-offset[5:0]"),
      "get CSS64-offset[8:0]"));
}

uint64_t* get_compressed_instruction_CS32_offset(uint64_t* c_ir_nid) {
  return get_compressed_instruction_CL32_offset(c_ir_nid);
}

uint64_t* get_compressed_instruction_CS64_offset(uint64_t* c_ir_nid) {
  return get_compressed_instruction_CL64_offset(c_ir_nid);
}

uint64_t* sign_extend_CB_offset(uint64_t* offset_nid) {
  return new_ext(OP_SEXT, SID_MACHINE_WORD, offset_nid, WORDSIZEINBITS - 9, "sign-extend");
}

uint64_t* get_compressed_instruction_CB_offset(uint64_t* c_ir_nid) {
  return sign_extend_CB_offset(
    new_binary(OP_CONCAT, SID_9_BIT_OFFSET,
      new_slice(SID_1_BIT_OFFSET, c_ir_nid, 12, 12, "get CB-offset[8]"),
      new_binary(OP_CONCAT, SID_8_BIT_OFFSET,
        new_slice(SID_2_BIT_OFFSET, c_ir_nid, 6, 5, "get CB-offset[7:6]"),
        new_binary(OP_CONCAT, SID_6_BIT_OFFSET,
          new_slice(SID_1_BIT_OFFSET, c_ir_nid, 2, 2, "get CB-offset[5]"),
          new_binary(OP_CONCAT, SID_5_BIT_OFFSET,
            new_slice(SID_2_BIT_OFFSET, c_ir_nid, 11, 10, "get CB-offset[4:3]"),
            new_binary(OP_CONCAT, SID_3_BIT_OFFSET,
              new_slice(SID_2_BIT_OFFSET, c_ir_nid, 4, 3, "get CB-offset[2:1]"),
              NID_1_BIT_OFFSET_0,
              "get CB-offset[2:0]"),
            "get CB-offset[4:0]"),
          "get CB-offset[5:0]"),
        "get CB-offset[7:0]"),
      "get CB-offset[8:0]"));
}

uint64_t* sign_extend_CJ_offset(uint64_t* offset_nid) {
  return new_ext(OP_SEXT, SID_MACHINE_WORD, offset_nid, WORDSIZEINBITS - 12, "sign-extend");
}

uint64_t* get_compressed_instruction_CJ_offset(uint64_t* c_ir_nid) {
  return sign_extend_CJ_offset(
    new_binary(OP_CONCAT, SID_12_BIT_OFFSET,
      new_slice(SID_1_BIT_OFFSET, c_ir_nid, 12, 12, "get CJ-offset[11]"),
      new_binary(OP_CONCAT, SID_11_BIT_OFFSET,
        new_slice(SID_1_BIT_OFFSET, c_ir_nid, 8, 8, "get CJ-offset[10]"),
        new_binary(OP_CONCAT, SID_10_BIT_OFFSET,
          new_slice(SID_2_BIT_OFFSET, c_ir_nid, 10, 9, "get CJ-offset[9:8]"),
          new_binary(OP_CONCAT, SID_8_BIT_OFFSET,
            new_slice(SID_1_BIT_OFFSET, c_ir_nid, 6, 6, "get CJ-offset[7]"),
            new_binary(OP_CONCAT, SID_7_BIT_OFFSET,
              new_slice(SID_1_BIT_OFFSET, c_ir_nid, 7, 7, "get CJ-offset[6]"),
              new_binary(OP_CONCAT, SID_6_BIT_OFFSET,
                new_slice(SID_1_BIT_OFFSET, c_ir_nid, 2, 2, "get CJ-offset[5]"),
                new_binary(OP_CONCAT, SID_5_BIT_OFFSET,
                  new_slice(SID_1_BIT_OFFSET, c_ir_nid, 11, 11, "get CJ-offset[4]"),
                  new_binary(OP_CONCAT, SID_4_BIT_OFFSET,
                    new_slice(SID_3_BIT_OFFSET, c_ir_nid, 5, 3, "get CJ-offset[3:1]"),
                    NID_1_BIT_OFFSET_0,
                    "get CJ-offset[3:0]"),
                  "get CJ-offset[4:0]"),
                "get CJ-offset[5:0]"),
              "get CJ-offset[6:0]"),
            "get CJ-offset[7:0]"),
          "get CJ-offset[9:0]"),
        "get CJ-offset[10:0]"),
      "get CJ-offset[11:0]"));
}

uint64_t* decode_compressed_opcode(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_opcode_nid, char* c_opcode_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_c_opcode_nid) {
  return new_ternary(OP_ITE, sid,
    new_binary_boolean(OP_EQ,
      get_compressed_instruction_opcode(c_ir_nid),
      c_opcode_nid,
      format_comment("compressed opcode == %s", (uint64_t) c_opcode_comment)),
    execute_nid,
    other_c_opcode_nid,
    execute_comment);
}

uint64_t* decode_compressed_funct3(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_funct3_nid, char* c_funct3_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_c_funct3_nid) {
  return new_ternary(OP_ITE, sid,
    new_binary_boolean(OP_EQ,
      get_compressed_instruction_funct3(c_ir_nid),
      c_funct3_nid,
      format_comment("compressed funct3 == %s", (uint64_t) c_funct3_comment)),
    execute_nid,
    other_c_funct3_nid,
    execute_comment);
}

uint64_t* decode_compressed_funct3_conditional(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_funct3_nid, char* c_funct3_comment,
  uint64_t* evaluate_nid, uint64_t* branch_nid, uint64_t* continue_nid, char* branch_comment,
  uint64_t* other_c_funct3_nid) {
  return decode_compressed_funct3(sid, c_ir_nid,
    c_funct3_nid, c_funct3_comment,
    new_ternary(OP_ITE, sid,
      evaluate_nid,
      branch_nid,
      continue_nid,
      branch_comment),
    "evaluate branch condition if compressed funct3 matches",
    other_c_funct3_nid);
}

uint64_t* decode_compressed_funct2(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_funct2_nid, char* c_funct2_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_c_funct2_nid) {
  return new_ternary(OP_ITE, sid,
    new_binary_boolean(OP_EQ,
      get_compressed_instruction_funct2(c_ir_nid),
      c_funct2_nid,
      format_comment("compressed funct2 == %s", (uint64_t) c_funct2_comment)),
    execute_nid,
    other_c_funct2_nid,
    execute_comment);
}

uint64_t* decode_compressed_funct4(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_funct4_nid, char* c_funct4_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_c_funct4_nid) {
  return new_ternary(OP_ITE, sid,
    new_binary_boolean(OP_EQ,
      get_compressed_instruction_funct4(c_ir_nid),
      c_funct4_nid,
      format_comment("compressed funct4 == %s", (uint64_t) c_funct4_comment)),
    execute_nid,
    other_c_funct4_nid,
    execute_comment);
}

uint64_t* decode_compressed_funct6(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_funct6_nid, char* c_funct6_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_c_funct6_nid) {
  return new_ternary(OP_ITE, sid,
    new_binary_boolean(OP_EQ,
      get_compressed_instruction_funct6(c_ir_nid),
      c_funct6_nid,
      format_comment("compressed funct6 == %s", (uint64_t) c_funct6_comment)),
    execute_nid,
    other_c_funct6_nid,
    execute_comment);
}

uint64_t* decode_compressed_funct(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_funct_nid, char* c_funct_comment,
  uint64_t* execute_nid, char* execute_comment,
  uint64_t* other_c_funct_nid) {
  return new_ternary(OP_ITE, sid,
    new_binary_boolean(OP_EQ,
      get_compressed_instruction_funct(c_ir_nid),
      c_funct_nid,
      format_comment("compressed funct == %s", (uint64_t) c_funct_comment)),
    execute_nid,
    other_c_funct_nid,
    execute_comment);
}

uint64_t* decode_compressed_imm(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_li_nid, uint64_t* c_lui_nid,
  uint64_t* c_addi_nid, uint64_t* c_addiw_nid, uint64_t* c_addi16sp_nid,
  uint64_t* c_srli_nid, uint64_t* c_srai_nid, uint64_t* c_andi_nid, char* comment,
  uint64_t* other_c_funct_nid) {
  other_c_funct_nid = decode_compressed_funct3(sid, c_ir_nid,
    NID_F3_C_ADDI, "C.ADDI?",
    c_addi_nid, format_comment("c.addi %s", (uint64_t) comment),
    decode_compressed_funct3(sid, c_ir_nid,
      NID_F3_C_LI, "C.LI?",
      c_li_nid, format_comment("c.li %s", (uint64_t) comment),
      decode_compressed_funct3(sid, c_ir_nid,
        NID_F3_C_LUI_ADDI16SP, "C.LUI or C.ADDI16SP?",
        new_ternary(OP_ITE, sid,
          new_binary_boolean(OP_NEQ,
            get_compressed_instruction_rd(c_ir_nid), NID_SP, "compressed rd != sp?"),
          c_lui_nid,
          c_addi16sp_nid,
          "c.lui (rd != sp) or c.addi16sp (rd == sp)?"),
        format_comment("c.lui or c.addi16sp %s", (uint64_t) comment),
        decode_compressed_funct3(sid, c_ir_nid,
          NID_F3_C_SRLI_SRAI_ANDI, "C.SRLI or C.SRAI or C.ANDI?",
          decode_compressed_funct2(sid, c_ir_nid,
            NID_F2_C_SRLI, "C.SRLI?",
            c_srli_nid, format_comment("c.srli %s", (uint64_t) comment),
            decode_compressed_funct2(sid, c_ir_nid,
              NID_F2_C_SRAI, "C.SRAI?",
              c_srai_nid, format_comment("c.srai %s", (uint64_t) comment),
              decode_compressed_funct2(sid, c_ir_nid,
                NID_F2_C_ANDI, "C.ANDI?",
                c_andi_nid, format_comment("c.andi %s", (uint64_t) comment),
                other_c_funct_nid))),
          format_comment("c.srli or c.srai or c.andi %s", (uint64_t) comment),
          other_c_funct_nid))));

  if (IS64BITTARGET)
    return decode_compressed_funct3(sid, c_ir_nid,
      NID_F3_C_ADDIW_JAL, "C.ADDIW?",
      c_addiw_nid, format_comment("c.addiw %s", (uint64_t) comment),
      other_c_funct_nid);
  else
    return other_c_funct_nid;
}

uint64_t* decode_compressed_addi4spn(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_addi4spn_nid, char* comment, uint64_t* other_c_funct3_nid) {
  return decode_compressed_funct3(sid, c_ir_nid,
    NID_F3_C_ADDI4SPN, "C.ADDI4SPN?",
    c_addi4spn_nid, format_comment("c.addi4spn %s", (uint64_t) comment),
    other_c_funct3_nid);
}

uint64_t* decode_compressed_slli(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_slli_nid, char* comment, uint64_t* other_c_funct3_nid) {
  return decode_compressed_funct3(sid, c_ir_nid,
    NID_F3_C_SLLI, "C.SLLI?",
    c_slli_nid, format_comment("c.slli %s", (uint64_t) comment),
    other_c_funct3_nid);
}

uint64_t* is_illegal_compressed_shift(uint64_t* c_ir_nid, uint64_t* c_shift_nid) {
  uint64_t* illegal_shamt_nid;

  illegal_shamt_nid = new_binary_boolean(OP_EQ,
    get_compressed_instruction_shamt(c_ir_nid),
    NID_MACHINE_WORD_0,
    "CI-shamt == 0?");

  if (IS64BITTARGET == 0)
    illegal_shamt_nid = new_binary_boolean(OP_OR,
      get_compressed_instruction_shamt_5(c_ir_nid),
      illegal_shamt_nid,
      "CI-shamt[5] == 1 or CI-shamt == 0?");

  return new_binary_boolean(OP_AND,
    illegal_shamt_nid,
    c_shift_nid,
    "compressed shift with illegal shamt?");
}

uint64_t* decode_illegal_compressed_instruction_imm_shamt(uint64_t* c_ir_nid) {
  uint64_t* c_lui_nid;
  uint64_t* c_addi_nid;
  uint64_t* c_addi16sp_nid;
  uint64_t* c_addi4spn_nid;

  if (RVC) {
    c_lui_nid = new_binary_boolean(OP_AND,
      NID_C_LUI,
      new_binary_boolean(OP_EQ,
        get_compressed_instruction_CUI_immediate(c_ir_nid),
        NID_MACHINE_WORD_0,
        "CUI-immediate == 0?"),
      "c.lui with CUI-immediate == 0?");

    c_addi_nid = new_binary_boolean(OP_AND,
      NID_C_ADDI,
      new_binary_boolean(OP_AND,
        new_binary_boolean(OP_NEQ,
          get_compressed_instruction_rd(c_ir_nid),
          NID_ZR,
          "compressed rd != zero?"),
        new_binary_boolean(OP_EQ,
          get_compressed_instruction_CI_immediate(c_ir_nid),
          NID_MACHINE_WORD_0,
          "CI-immediate == 0?"),
        "compressed rd != zero and CI-immediate == 0?"),
      "c.addi with compressed rd != zero and CI-immediate == 0?");

    c_addi16sp_nid = new_binary_boolean(OP_AND,
      NID_C_ADDI16SP,
      new_binary_boolean(OP_EQ,
        get_compressed_instruction_CI16SP_immediate(c_ir_nid),
        NID_MACHINE_WORD_0,
        "CI16SP-immediate == 0?"),
      "c.addi16sp with CI16SP-immediate == 0?");

    c_addi4spn_nid = new_binary_boolean(OP_AND,
      NID_C_ADDI4SPN,
      new_binary_boolean(OP_EQ,
        get_compressed_instruction_CIW_immediate(c_ir_nid),
        NID_MACHINE_WORD_0,
        "CIW-immediate == 0?"),
      "c.addi4spn with CIW-immediate == 0?");

    return new_ternary(OP_ITE, SID_BOOLEAN,
      is_compressed_instruction(c_ir_nid),
      new_ternary(OP_ITE, SID_BOOLEAN,
        new_binary_boolean(OP_NEQ,
          c_ir_nid,
          NID_HALF_WORD_0,
          "is not defined illegal compressed instruction?"),
        decode_compressed_opcode(SID_BOOLEAN, c_ir_nid,
          NID_OP_C2, "C2?",
          decode_compressed_slli(SID_BOOLEAN, c_ir_nid,
            is_illegal_compressed_shift(c_ir_nid, NID_C_SLLI), "with illegal shamt?",
            NID_FALSE),
          "C2 compressed instruction with illegal shamt?",
          decode_compressed_opcode(SID_BOOLEAN, c_ir_nid,
            NID_OP_C0, "C0?",
            decode_compressed_addi4spn(SID_BOOLEAN, c_ir_nid,
              c_addi4spn_nid, "with illegal immediate?",
              NID_FALSE),
            "C0 compressed instruction with illegal immediate?",
            decode_compressed_opcode(SID_BOOLEAN, c_ir_nid,
              NID_OP_C1, "C1?",
              decode_compressed_imm(SID_BOOLEAN, c_ir_nid,
                NID_FALSE, c_lui_nid,
                c_addi_nid, NID_FALSE, c_addi16sp_nid,
                is_illegal_compressed_shift(c_ir_nid, NID_C_SRLI),
                is_illegal_compressed_shift(c_ir_nid, NID_C_SRAI),
                NID_FALSE, "with illegal immediate or shamt?",
                NID_FALSE),
              "C1 compressed instruction with illegal immediate or shamt?",
              NID_FALSE))),
        NID_TRUE,
        "is defined illegal compressed instruction or has illegal immediate or shamt?"),
      NID_FALSE,
      "compressed instruction with illegal immediate or shamt?");
  } else
    return UNUSED;
}

uint64_t* decode_compressed_mv_add(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_mv_nid, uint64_t* c_add_nid, char* comment,
  uint64_t* other_c_funct4_nid) {
  return new_ternary(OP_ITE, sid,
    new_binary_boolean(OP_AND,
      new_binary_boolean(OP_NEQ,
        get_compressed_instruction_rd(c_ir_nid),
        NID_ZR,
        "compressed rd != zero?"),
      new_binary_boolean(OP_NEQ,
        get_compressed_instruction_rs2(c_ir_nid),
        NID_ZR,
        "compressed rs2 != zero?"),
      "compressed rd != zero and compressed rs2 != zero?"),
    decode_compressed_funct4(sid, c_ir_nid,
      NID_F4_C_MV_JR, "C.MV?",
      c_mv_nid, format_comment("c.mv %s", (uint64_t) comment),
      decode_compressed_funct4(sid, c_ir_nid,
        NID_F4_C_ADD_JALR, "C.ADD?",
        c_add_nid, format_comment("c.add %s", (uint64_t) comment),
        other_c_funct4_nid)),
    other_c_funct4_nid,
    format_comment("c.mv or c.add %s", (uint64_t) comment));
}

uint64_t* decode_compressed_op(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_sub_nid, uint64_t* c_xor_nid, uint64_t* c_or_nid, uint64_t* c_and_nid,
  uint64_t* c_addw_nid, uint64_t* c_subw_nid, char* comment,
  uint64_t* other_c_funct_nid) {
  uint64_t* c_funct_nid;

  c_funct_nid = decode_compressed_funct6(sid, c_ir_nid,
    NID_F6_C_SUB_XOR_OR_AND, "C.SUB or C.XOR or C.OR or C.AND?",
    decode_compressed_funct(sid, c_ir_nid,
      NID_F2_C_SUB_SUBW, "C.SUB?",
      c_sub_nid, format_comment("c.sub %s", (uint64_t) comment),
      decode_compressed_funct(sid, c_ir_nid,
        NID_F2_C_XOR_ADDW, "C.XOR?",
        c_xor_nid, format_comment("c.xor %s", (uint64_t) comment),
        decode_compressed_funct(sid, c_ir_nid,
          NID_F2_C_OR, "C.OR?",
          c_or_nid, format_comment("c.or %s", (uint64_t) comment),
          decode_compressed_funct(sid, c_ir_nid,
            NID_F2_C_AND, "C.AND?",
            c_and_nid, format_comment("c.and %s", (uint64_t) comment),
            other_c_funct_nid)))),
    format_comment("c.sub or c.xor or c.or or c.and %s", (uint64_t) comment),
    other_c_funct_nid);

  if (IS64BITTARGET)
    return decode_compressed_funct6(sid, c_ir_nid,
      NID_F6_C_ADDW_SUBW, "C.ADDW or C.SUBW?",
      decode_compressed_funct(sid, c_ir_nid,
        NID_F2_C_XOR_ADDW, "C.ADDW?",
        c_addw_nid, format_comment("c.addw %s", (uint64_t) comment),
        decode_compressed_funct(sid, c_ir_nid,
          NID_F2_C_SUB_SUBW, "C.SUBW?",
          c_subw_nid, format_comment("c.subw %s", (uint64_t) comment),
          other_c_funct_nid)),
      format_comment("c.addw or c.subw %s", (uint64_t) comment),
      c_funct_nid);
  else
    return c_funct_nid;
}

uint64_t* decode_compressed_load(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_ld_nid, uint64_t* c_lw_nid, char* comment,
  uint64_t* other_c_funct3_nid) {
  other_c_funct3_nid = decode_compressed_funct3(sid, c_ir_nid,
    NID_F3_C_LWSP_LW, "C.LWSP or C.LW?",
    c_lw_nid, format_comment("c.lwsp or c.lw %s", (uint64_t) comment),
    other_c_funct3_nid);

  if (IS64BITTARGET)
    return decode_compressed_funct3(sid, c_ir_nid,
      NID_F3_C_LDSP_LD, "C.LDSP or C.LD?",
      c_ld_nid, format_comment("c.ldsp or c.ld %s", (uint64_t) comment),
      other_c_funct3_nid);
  else
    return other_c_funct3_nid;
}

uint64_t* decode_compressed_store(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_sd_nid, uint64_t* c_sw_nid, char* comment,
  uint64_t* other_c_funct3_nid) {
  other_c_funct3_nid = decode_compressed_funct3(sid, c_ir_nid,
    NID_F3_C_SWSP_SW, "C.SWSP or C.SW?",
    c_sw_nid, format_comment("c.swsp or c.sw %s", (uint64_t) comment),
    other_c_funct3_nid);

  if (IS64BITTARGET)
    return decode_compressed_funct3(sid, c_ir_nid,
      NID_F3_C_SDSP_SD, "C.SDSP or C.SD?",
      c_sd_nid, format_comment("c.sdsp or c.sd %s", (uint64_t) comment),
      other_c_funct3_nid);
  else
    return other_c_funct3_nid;
}

uint64_t* decode_compressed_branch(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_beqz_nid, uint64_t* c_bnez_nid,
  uint64_t* branch_nid, uint64_t* continue_nid, char* comment,
  uint64_t* other_c_funct3_nid) {
  return decode_compressed_funct3_conditional(sid, c_ir_nid,
    NID_F3_C_BEQZ, "C.BEQZ?",
    c_beqz_nid, branch_nid, continue_nid, format_comment("c.beqz %s", (uint64_t) comment),
    decode_compressed_funct3_conditional(sid, c_ir_nid,
      NID_F3_C_BNEZ, "C.BNEZ?",
      c_bnez_nid, branch_nid, continue_nid, format_comment("c.bnez %s", (uint64_t) comment),
      other_c_funct3_nid));
}

uint64_t* decode_compressed_j(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_j_nid, char* comment, uint64_t* other_c_funct3_nid) {
  return decode_compressed_funct3(sid, c_ir_nid,
    NID_F3_C_J, "C.J?",
    c_j_nid, format_comment("c.j %s", (uint64_t) comment),
    other_c_funct3_nid);
}

uint64_t* decode_compressed_jal(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_jal_nid, char* comment, uint64_t* other_c_funct3_nid) {
  if (IS64BITTARGET)
    return other_c_funct3_nid;
  else
    return decode_compressed_funct3(sid, c_ir_nid,
      NID_F3_C_ADDIW_JAL, "C.JAL?",
      c_jal_nid, format_comment("c.jal %s", (uint64_t) comment),
      other_c_funct3_nid);
}

uint64_t* decode_compressed_jr(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_jr_nid, char* comment, uint64_t* other_c_funct4_nid) {
  return decode_compressed_funct4(sid, c_ir_nid,
    NID_F4_C_MV_JR, "C.JR?",
    c_jr_nid, format_comment("c.jr %s", (uint64_t) comment),
    other_c_funct4_nid);
}

uint64_t* decode_compressed_jalr(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_jalr_nid, char* comment, uint64_t* other_c_funct4_nid) {
  return decode_compressed_funct4(sid, c_ir_nid,
    NID_F4_C_ADD_JALR, "C.JALR?",
    c_jalr_nid, format_comment("c.jalr %s", (uint64_t) comment),
    other_c_funct4_nid);
}

uint64_t* decode_compressed_nonzero_rs1_zero_rs2(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_funct4_nid, uint64_t* other_c_funct4_nid) {
  return new_ternary(OP_ITE, sid,
    new_binary_boolean(OP_AND,
      new_binary_boolean(OP_NEQ,
        get_compressed_instruction_rs1(c_ir_nid),
        NID_ZR,
        "compressed rs1 != zero?"),
      new_binary_boolean(OP_EQ,
        get_compressed_instruction_rs2(c_ir_nid),
        NID_ZR,
        "compressed rs2 == zero?"),
      "compressed rs1 != zero and compressed rs2 == zero?"),
    c_funct4_nid,
    other_c_funct4_nid,
    "compressed rs1 != zero and compressed rs2 == zero!");
}

uint64_t* is_compressed_instruction(uint64_t* ir_nid) {
  return new_binary_boolean(OP_NEQ,
    get_compressed_instruction_opcode(ir_nid),
    NID_OP_C3,
    "is compressed instruction?");
}

uint64_t* decode_compressed_instruction(uint64_t* c_ir_nid) {
  if (RVC)
    return
      decode_compressed_opcode(SID_BOOLEAN, c_ir_nid,
        NID_OP_C2, "C2?",
        decode_compressed_mv_add(SID_BOOLEAN, c_ir_nid,
          NID_C_MV, NID_C_ADD, "known?",
          decode_compressed_slli(SID_BOOLEAN, c_ir_nid,
            NID_C_SLLI, "known?",
            decode_compressed_load(SID_BOOLEAN, c_ir_nid,
              NID_C_LDSP, NID_C_LWSP, "known?",
              decode_compressed_store(SID_BOOLEAN, c_ir_nid,
                NID_C_SDSP, NID_C_SWSP, "known?",
                decode_compressed_nonzero_rs1_zero_rs2(SID_BOOLEAN, c_ir_nid,
                  decode_compressed_jr(SID_BOOLEAN, c_ir_nid,
                    NID_C_JR, "known?",
                    decode_compressed_jalr(SID_BOOLEAN, c_ir_nid,
                      NID_C_JALR, "known?",
                      NID_FALSE)),
                  NID_FALSE))))),
        "C2 compressed instruction known?",
        decode_compressed_opcode(SID_BOOLEAN, c_ir_nid,
          NID_OP_C0, "C0?",
          decode_compressed_addi4spn(SID_BOOLEAN, c_ir_nid,
            NID_C_ADDI4SPN, "known?",
          decode_compressed_load(SID_BOOLEAN, c_ir_nid,
            NID_C_LD, NID_C_LW, "known?",
            decode_compressed_store(SID_BOOLEAN, c_ir_nid,
              NID_C_SD, NID_C_SW, "known?",
              NID_FALSE))),
          "C0 compressed instruction known?",
          decode_compressed_opcode(SID_BOOLEAN, c_ir_nid,
            NID_OP_C1, "C1?",
            decode_compressed_imm(SID_BOOLEAN, c_ir_nid,
              NID_C_LI, NID_C_LUI,
              NID_C_ADDI, NID_C_ADDIW, NID_C_ADDI16SP,
              NID_C_SRLI, NID_C_SRAI, NID_C_ANDI, "known?",
              decode_compressed_op(SID_BOOLEAN, c_ir_nid,
                NID_C_SUB, NID_C_XOR, NID_C_OR, NID_C_AND,
                NID_C_ADDW, NID_C_SUBW, "known?",
                decode_compressed_branch(SID_BOOLEAN, c_ir_nid,
                  NID_C_BEQZ, NID_C_BNEZ,
                  NID_TRUE, NID_FALSE, "known?",
                  decode_compressed_j(SID_BOOLEAN, c_ir_nid,
                    NID_C_J, "known?",
                    decode_compressed_jal(SID_BOOLEAN, c_ir_nid,
                      NID_C_JAL, "known?",
                      NID_FALSE))))),
            "C1 compressed instruction known?",
            NID_FALSE)));
  else
    return UNUSED;
}

uint64_t* decode_compressed_register_data_flow(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_li_nid, uint64_t* c_lui_nid,
  uint64_t* c_addi_nid, uint64_t* c_addiw_nid,
  uint64_t* c_addi16sp_nid, uint64_t* c_addi4spn_nid,
  uint64_t* c_slli_nid, uint64_t* c_srli_nid, uint64_t* c_srai_nid, uint64_t* c_andi_nid,
  uint64_t* c_mv_nid, uint64_t* c_add_nid,
  uint64_t* c_sub_nid, uint64_t* c_xor_nid, uint64_t* c_or_nid, uint64_t* c_and_nid,
  uint64_t* c_addw_nid, uint64_t* c_subw_nid,
  uint64_t* c_ldsp_nid, uint64_t* c_lwsp_nid,
  uint64_t* c_ld_nid, uint64_t* c_lw_nid,
  uint64_t* c_jal_nid, uint64_t* c_jalr_nid, char* comment,
  uint64_t* other_register_data_flow_nid) {
  return decode_compressed_opcode(sid, c_ir_nid,
    NID_OP_C2, "C2?",
    decode_compressed_mv_add(sid, c_ir_nid,
      c_mv_nid, c_add_nid, comment,
      decode_compressed_slli(sid, c_ir_nid,
        c_slli_nid, comment,
        decode_compressed_load(sid, c_ir_nid,
          c_ldsp_nid, c_lwsp_nid, comment,
          decode_compressed_nonzero_rs1_zero_rs2(sid, c_ir_nid,
            decode_compressed_jalr(sid, c_ir_nid,
              c_jalr_nid, comment,
              other_register_data_flow_nid),
            other_register_data_flow_nid)))),
    "C2 compressed instruction register data flow",
    decode_compressed_opcode(sid, c_ir_nid,
      NID_OP_C0, "C0?",
      decode_compressed_addi4spn(sid, c_ir_nid,
        c_addi4spn_nid, comment,
        decode_compressed_load(sid, c_ir_nid,
          c_ld_nid, c_lw_nid, comment,
          other_register_data_flow_nid)),
      "C0 compressed instruction register data flow",
      decode_compressed_opcode(sid, c_ir_nid,
        NID_OP_C1, "C1?",
        decode_compressed_imm(sid, c_ir_nid,
          c_li_nid, c_lui_nid,
          c_addi_nid, c_addiw_nid, c_addi16sp_nid,
          c_srli_nid, c_srai_nid, c_andi_nid, comment,
          decode_compressed_op(sid, c_ir_nid,
            c_sub_nid, c_xor_nid, c_or_nid, c_and_nid,
            c_addw_nid, c_subw_nid, comment,
            decode_compressed_jal(sid, c_ir_nid,
              c_jal_nid, comment,
              other_register_data_flow_nid))),
        "C1 compressed instruction register data flow",
        other_register_data_flow_nid)));
}

uint64_t* get_sp_value_plus_CI32_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    load_register_value(NID_SP, "sp value", register_file_nid),
    get_compressed_instruction_CI32_offset(c_ir_nid),
    "sp value plus CI32-offset");
}

uint64_t* get_sp_value_plus_CI64_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    load_register_value(NID_SP, "sp value", register_file_nid),
    get_compressed_instruction_CI64_offset(c_ir_nid),
    "sp value plus CI64-offset");
}

uint64_t* get_rs1_shift_value_plus_CL32_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    load_register_value(get_compressed_instruction_rs1_shift(c_ir_nid), "rs1' value", register_file_nid),
    get_compressed_instruction_CL32_offset(c_ir_nid),
    "rs1' value plus CL32-offset");
}

uint64_t* get_rs1_shift_value_plus_CL64_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    load_register_value(get_compressed_instruction_rs1_shift(c_ir_nid), "rs1' value", register_file_nid),
    get_compressed_instruction_CL64_offset(c_ir_nid),
    "rs1' value plus CL64-offset");
}

uint64_t* decode_compressed_load_with_opcode(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_ldsp_nid, uint64_t* c_lwsp_nid,
  uint64_t* c_ld_nid, uint64_t* c_lw_nid, char* comment,
  uint64_t* no_funct3_nid, uint64_t* no_opcode_nid) {
  return decode_compressed_opcode(sid, c_ir_nid,
    NID_OP_C2, "C2?",
    decode_compressed_load(sid, c_ir_nid,
      c_ldsp_nid, c_lwsp_nid, comment,
      no_funct3_nid),
    "C2 compressed load instruction",
    decode_compressed_opcode(sid, c_ir_nid,
      NID_OP_C0, "C0?",
      decode_compressed_load(sid, c_ir_nid,
        c_ld_nid, c_lw_nid, comment,
        no_funct3_nid),
      "C0 compressed load instruction",
      no_opcode_nid));
}

uint64_t* compressed_load_no_seg_faults(uint64_t* c_ir_nid, uint64_t* register_file_nid) {
  if (RVC)
    return new_ternary(OP_ITE, SID_BOOLEAN,
      is_compressed_instruction(c_ir_nid),
      decode_compressed_load_with_opcode(SID_BOOLEAN, c_ir_nid,
        is_sized_block_in_stack_segment(get_sp_value_plus_CI64_offset(c_ir_nid, register_file_nid), NID_VIRTUAL_DOUBLE_WORD_SIZE_MINUS_1),
        is_sized_block_in_stack_segment(get_sp_value_plus_CI32_offset(c_ir_nid, register_file_nid), NID_VIRTUAL_SINGLE_WORD_SIZE_MINUS_1),
        is_sized_block_in_main_memory(get_rs1_shift_value_plus_CL64_offset(c_ir_nid, register_file_nid), NID_VIRTUAL_DOUBLE_WORD_SIZE_MINUS_1),
        is_sized_block_in_main_memory(get_rs1_shift_value_plus_CL32_offset(c_ir_nid, register_file_nid), NID_VIRTUAL_SINGLE_WORD_SIZE_MINUS_1),
        "no-seg-faults",
        NID_TRUE,
        NID_TRUE),
      NID_TRUE,
      "no compressed load segmentation faults");
  else
    return UNUSED;
}

uint64_t* get_pc_value_plus_2(uint64_t* pc_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    pc_nid,
    NID_MACHINE_WORD_2,
    "pc value + 2");
}

uint64_t* core_compressed_register_data_flow(uint64_t* pc_nid, uint64_t* c_ir_nid,
  uint64_t* register_file_nid, uint64_t* memory_nid) {
  uint64_t* rd_nid;
  uint64_t* rd_value_nid;
  uint64_t* rd_shift_nid;
  uint64_t* rs1_shift_nid;
  uint64_t* rs1_shift_value_nid;
  uint64_t* rs2_value_nid;
  uint64_t* rs2_shift_value_nid;

  if (RVC) {
    rd_nid       = get_compressed_instruction_rd(c_ir_nid);
    rd_value_nid = load_register_value(rd_nid, "compressed rd value", register_file_nid);

    rd_shift_nid = get_compressed_instruction_rd_shift(c_ir_nid);

    rs1_shift_nid       = get_compressed_instruction_rs1_shift(c_ir_nid);
    rs1_shift_value_nid = load_register_value(rs1_shift_nid, "compressed rs1' or rd' value", register_file_nid);

    rs2_value_nid = load_register_value(get_compressed_instruction_rs2(c_ir_nid), "compressed rs2 value", register_file_nid);

    rs2_shift_value_nid = load_register_value(get_compressed_instruction_rs2_shift(c_ir_nid), "compressed rs2' value", register_file_nid);

    rd_nid = decode_compressed_register_data_flow(SID_REGISTER_ADDRESS, c_ir_nid,
      rd_nid, // c.li
      rd_nid, // c.lui
      rd_nid, // c.addi
      rd_nid, // c.addiw
      NID_SP, // c.addi16sp
      rd_shift_nid, // c.addi4spn
      rd_nid, // c.slli
      rs1_shift_nid, // c.srli
      rs1_shift_nid, // c.srai
      rs1_shift_nid, // c.andi
      rd_nid, // c.mv
      rd_nid, // c.add
      rs1_shift_nid, // c.sub
      rs1_shift_nid, // c.xor
      rs1_shift_nid, // c.or
      rs1_shift_nid, // c.and
      rs1_shift_nid, // c.addw
      rs1_shift_nid, // c.subw
      rd_nid, // c.ldsp
      rd_nid, // c.lwsp
      rd_shift_nid, // c.ld
      rd_shift_nid, // c.lw
      NID_RA, // c.jal
      NID_RA, // c.jalr
      "register destination",
      NID_ZR);

    rd_value_nid = decode_compressed_register_data_flow(SID_MACHINE_WORD, c_ir_nid,
      get_compressed_instruction_CI_immediate(c_ir_nid), // c.li
      get_compressed_instruction_CUI_immediate(c_ir_nid), // c.lui
      new_binary(OP_ADD, SID_MACHINE_WORD, // c.addi
        rd_value_nid,
        get_compressed_instruction_CI_immediate(c_ir_nid),
        "compressed rd value + CI-immediate"),
      extend_single_word_to_machine_word(OP_SEXT, // c.addiw
        new_binary(OP_ADD, SID_SINGLE_WORD,
          slice_single_word_from_machine_word(rd_value_nid),
          get_compressed_instruction_CI_32_bit_immediate(c_ir_nid),
          "lower 32 bits of compressed rd value + CI-32-bit-immediate")),
      new_binary(OP_ADD, SID_MACHINE_WORD, // c.addi16sp
        load_register_value(NID_SP, "sp value", register_file_nid),
        get_compressed_instruction_CI16SP_immediate(c_ir_nid),
        "sp value + CI16SP-immediate"),
      new_binary(OP_ADD, SID_MACHINE_WORD, // c.addi4spn
        load_register_value(NID_SP, "sp value", register_file_nid),
        get_compressed_instruction_CIW_immediate(c_ir_nid),
        "sp value + CIW-immediate"),
      new_binary(OP_SLL, SID_MACHINE_WORD, // c.slli
        rd_value_nid,
        get_compressed_instruction_shamt(c_ir_nid),
        "compressed rd value << CI-shamt"),
      new_binary(OP_SRL, SID_MACHINE_WORD, // c.srli
        rs1_shift_value_nid,
        get_compressed_instruction_shamt(c_ir_nid),
        "compressed rd' value >> CB-shamt"),
      new_binary(OP_SRA, SID_MACHINE_WORD, // c.srai
        rs1_shift_value_nid,
        get_compressed_instruction_shamt(c_ir_nid),
        "compressed signed rd' value >> CB-shamt"),
      new_binary(OP_AND, SID_MACHINE_WORD, // c.andi
        rs1_shift_value_nid,
        get_compressed_instruction_CI_immediate(c_ir_nid),
        "compressed rd' value & CI-immediate"),
      rs2_value_nid, // c.mv
      new_binary(OP_ADD, SID_MACHINE_WORD, // c.add
        rd_value_nid,
        rs2_value_nid,
        "compressed rd value + compressed rs2 value"),
      new_binary(OP_SUB, SID_MACHINE_WORD, // c.sub
        rs1_shift_value_nid,
        rs2_shift_value_nid,
        "compressed rd' value - compressed rs2' value"),
      new_binary(OP_XOR, SID_MACHINE_WORD, // c.xor
        rs1_shift_value_nid,
        rs2_shift_value_nid,
        "compressed rd' value ^ compressed rs2' value"),
      new_binary(OP_OR, SID_MACHINE_WORD, // c.or
        rs1_shift_value_nid,
        rs2_shift_value_nid,
        "compressed rd' value | compressed rs2' value"),
      new_binary(OP_AND, SID_MACHINE_WORD, // c.and
        rs1_shift_value_nid,
        rs2_shift_value_nid,
        "compressed rd' value & compressed rs2' value"),
      extend_single_word_to_machine_word(OP_SEXT, // c.addw
        new_binary(OP_ADD, SID_SINGLE_WORD,
          slice_single_word_from_machine_word(rs1_shift_value_nid),
          slice_single_word_from_machine_word(rs2_shift_value_nid),
          "lower 32 bits of compressed rd' value + lower 32 bits of compressed rs2' value")),
      extend_single_word_to_machine_word(OP_SEXT, // c.subw
        new_binary(OP_SUB, SID_SINGLE_WORD,
          slice_single_word_from_machine_word(rs1_shift_value_nid),
          slice_single_word_from_machine_word(rs2_shift_value_nid),
          "lower 32 bits of compressed rd' value - lower 32 bits of compressed rs2' value")),
      load_double_word(get_sp_value_plus_CI64_offset(c_ir_nid, register_file_nid), memory_nid),
      extend_single_word_to_machine_word(OP_SEXT,
        load_single_word(get_sp_value_plus_CI32_offset(c_ir_nid, register_file_nid), memory_nid)),
      load_double_word(get_rs1_shift_value_plus_CL64_offset(c_ir_nid, register_file_nid), memory_nid),
      extend_single_word_to_machine_word(OP_SEXT,
        load_single_word(get_rs1_shift_value_plus_CL32_offset(c_ir_nid, register_file_nid), memory_nid)),
      get_pc_value_plus_2(pc_nid),
      get_pc_value_plus_2(pc_nid),
      "register data flow",
      load_register_value(rd_nid, "current compressed rd value", register_file_nid));

    return new_ternary(OP_ITE, SID_REGISTER_STATE,
      new_binary_boolean(OP_AND,
        is_compressed_instruction(c_ir_nid),
        new_binary_boolean(OP_NEQ, rd_nid, NID_ZR, "rd != register zero?"),
        "is compressed instruction and rd != register zero?"),
      store_register_value(rd_nid, rd_value_nid,
        "compressed instruction rd update", register_file_nid),
      register_file_nid,
      "compressed instruction and other register data flow");
  } else
    return register_file_nid;
}

uint64_t* decode_compressed_memory_data_flow(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_sdsp_nid, uint64_t* c_swsp_nid,
  uint64_t* c_sd_nid, uint64_t* c_sw_nid, char* comment,
  uint64_t* other_memory_data_flow_nid) {
  return decode_compressed_opcode(sid, c_ir_nid,
    NID_OP_C2, "C2?",
    decode_compressed_store(sid, c_ir_nid, c_sdsp_nid, c_swsp_nid, comment, other_memory_data_flow_nid),
    "C2 compressed instruction memory data flow",
    decode_compressed_opcode(sid, c_ir_nid,
      NID_OP_C0, "C0?",
      decode_compressed_store(sid, c_ir_nid, c_sd_nid, c_sw_nid, comment, other_memory_data_flow_nid),
      "C0 compressed instruction memory data flow",
    other_memory_data_flow_nid));
}

uint64_t* get_sp_value_plus_CSS32_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    load_register_value(NID_SP, "sp value", register_file_nid),
    get_compressed_instruction_CSS32_offset(c_ir_nid),
    "sp value plus CSS32-offset");
}

uint64_t* get_sp_value_plus_CSS64_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    load_register_value(NID_SP, "sp value", register_file_nid),
    get_compressed_instruction_CSS64_offset(c_ir_nid),
    "sp value plus CSS64-offset");
}

uint64_t* get_rs1_shift_value_plus_CS32_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    load_register_value(get_compressed_instruction_rs1_shift(c_ir_nid), "rs1' value", register_file_nid),
    get_compressed_instruction_CS32_offset(c_ir_nid),
    "rs1' value plus CS32-offset");
}

uint64_t* get_rs1_shift_value_plus_CS64_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    load_register_value(get_compressed_instruction_rs1_shift(c_ir_nid), "rs1' value", register_file_nid),
    get_compressed_instruction_CS64_offset(c_ir_nid),
    "rs1' value plus CS64-offset");
}

uint64_t* compressed_store_no_seg_faults(uint64_t* c_ir_nid, uint64_t* register_file_nid) {
  if (RVC)
    return new_ternary(OP_ITE, SID_BOOLEAN,
      is_compressed_instruction(c_ir_nid),
      decode_compressed_memory_data_flow(SID_BOOLEAN, c_ir_nid,
        is_sized_block_in_stack_segment(get_sp_value_plus_CSS64_offset(c_ir_nid, register_file_nid), NID_VIRTUAL_DOUBLE_WORD_SIZE_MINUS_1),
        is_sized_block_in_stack_segment(get_sp_value_plus_CSS32_offset(c_ir_nid, register_file_nid), NID_VIRTUAL_SINGLE_WORD_SIZE_MINUS_1),
        is_sized_block_in_main_memory(get_rs1_shift_value_plus_CS64_offset(c_ir_nid, register_file_nid), NID_VIRTUAL_DOUBLE_WORD_SIZE_MINUS_1),
        is_sized_block_in_main_memory(get_rs1_shift_value_plus_CS32_offset(c_ir_nid, register_file_nid), NID_VIRTUAL_SINGLE_WORD_SIZE_MINUS_1),
        "no-seg-faults",
        NID_TRUE),
      NID_TRUE,
      "no compressed store and other store segmentation faults");
  else
    return UNUSED;
}

uint64_t* core_compressed_memory_data_flow(uint64_t* c_ir_nid, uint64_t* register_file_nid, uint64_t* memory_nid) {
  uint64_t* rs2_value_nid;
  uint64_t* rs2_shift_value_nid;

  if (RVC) {
    rs2_value_nid       = load_register_value(get_compressed_instruction_rs2(c_ir_nid), "compressed rs2 value", register_file_nid);
    rs2_shift_value_nid = load_register_value(get_compressed_instruction_rs2_shift(c_ir_nid), "compressed rs2' value", register_file_nid);

    return new_ternary(OP_ITE, SID_MEMORY_STATE,
      is_compressed_instruction(c_ir_nid),
      decode_compressed_memory_data_flow(SID_MEMORY_STATE, c_ir_nid,
        store_double_word(get_sp_value_plus_CSS64_offset(c_ir_nid, register_file_nid),
          rs2_value_nid,
          memory_nid),
        store_single_word(get_sp_value_plus_CSS32_offset(c_ir_nid, register_file_nid),
          slice_single_word_from_machine_word(rs2_value_nid),
          memory_nid),
        store_double_word(get_rs1_shift_value_plus_CS64_offset(c_ir_nid, register_file_nid),
          rs2_shift_value_nid,
          memory_nid),
        store_single_word(get_rs1_shift_value_plus_CS32_offset(c_ir_nid, register_file_nid),
          slice_single_word_from_machine_word(rs2_shift_value_nid),
          memory_nid),
        "compressed instruction memory data flow",
        memory_nid),
      memory_nid,
      "compressed instruction and other memory data flow");
  } else
    return memory_nid;
}

uint64_t* get_pc_value_plus_CB_offset(uint64_t* pc_nid, uint64_t* c_ir_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    pc_nid,
    get_compressed_instruction_CB_offset(c_ir_nid),
    "pc value + CB-offset");
}

uint64_t* compressed_branch_control_flow(uint64_t* pc_nid, uint64_t* c_ir_nid, uint64_t* register_file_nid, uint64_t* other_control_flow_nid) {
  uint64_t* rs1_value_nid;

  rs1_value_nid = load_register_value(get_compressed_instruction_rs1_shift(c_ir_nid), "rs1' value", register_file_nid);

  return decode_compressed_branch(SID_MACHINE_WORD, c_ir_nid,
    new_binary_boolean(OP_EQ, rs1_value_nid, NID_MACHINE_WORD_0, "rs1' value == 0?"),
    new_binary_boolean(OP_NEQ, rs1_value_nid, NID_MACHINE_WORD_0, "rs1' value != 0?"),
    get_pc_value_plus_CB_offset(pc_nid, c_ir_nid),
    get_pc_value_plus_2(pc_nid),
    "pc-relative compressed branch control flow",
    other_control_flow_nid);
}

uint64_t* get_pc_value_plus_CJ_offset(uint64_t* pc_nid, uint64_t* c_ir_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    pc_nid,
    get_compressed_instruction_CJ_offset(c_ir_nid),
    "pc value + CJ-offset");
}

uint64_t* compressed_j_jal_control_flow(uint64_t* pc_nid, uint64_t* c_ir_nid, uint64_t* other_control_flow_nid) {
  return decode_compressed_j(SID_MACHINE_WORD, c_ir_nid,
    get_pc_value_plus_CJ_offset(pc_nid, c_ir_nid),
    "pc-relative compressed jump control flow",
    decode_compressed_jal(SID_MACHINE_WORD, c_ir_nid,
      get_pc_value_plus_CJ_offset(pc_nid, c_ir_nid),
      "pc-relative compressed jump control flow",
      other_control_flow_nid));
}

uint64_t* get_rs1_value_CR_format(uint64_t* c_ir_nid, uint64_t* register_file_nid) {
  return load_register_value(get_compressed_instruction_rs1(c_ir_nid), "compressed rs1 value", register_file_nid);
}

uint64_t* compressed_jr_jalr_control_flow(uint64_t* c_ir_nid, uint64_t* register_file_nid, uint64_t* other_control_flow_nid) {
  return decode_compressed_nonzero_rs1_zero_rs2(SID_MACHINE_WORD, c_ir_nid,
    decode_compressed_jr(SID_MACHINE_WORD, c_ir_nid,
      get_rs1_value_CR_format(c_ir_nid, register_file_nid), "register-relative c.jr control flow",
      decode_compressed_jalr(SID_MACHINE_WORD, c_ir_nid,
        get_rs1_value_CR_format(c_ir_nid, register_file_nid), "register-relative c.jalr control flow",
        other_control_flow_nid)),
    other_control_flow_nid);
}

uint64_t* core_compressed_control_flow(uint64_t* pc_nid, uint64_t* c_ir_nid, uint64_t* register_file_nid, uint64_t* other_control_flow_nid) {
  if (RVC)
    return new_ternary(OP_ITE, SID_MACHINE_WORD,
      is_compressed_instruction(c_ir_nid),
      decode_compressed_opcode(SID_MACHINE_WORD, c_ir_nid,
        NID_OP_C2, "C2?",
        compressed_jr_jalr_control_flow(c_ir_nid, register_file_nid,
          get_pc_value_plus_2(pc_nid)),
        "C2 compressed instruction control flow",
        decode_compressed_opcode(SID_MACHINE_WORD, c_ir_nid,
          NID_OP_C0, "C0?",
          get_pc_value_plus_2(pc_nid),
          "C0 compressed instruction control flow",
          decode_compressed_opcode(SID_MACHINE_WORD, c_ir_nid,
            NID_OP_C1, "C1?",
            compressed_branch_control_flow(pc_nid, c_ir_nid, register_file_nid,
              compressed_j_jal_control_flow(pc_nid, c_ir_nid,
                get_pc_value_plus_2(pc_nid))),
            "C1 compressed instruction control flow",
            get_pc_value_plus_2(pc_nid)))),
      other_control_flow_nid,
      "compressed instruction and other control flow");
  else
    return other_control_flow_nid;
}

// -----------------------------------------------------------------
// ----------------------------- CORE ------------------------------
// -----------------------------------------------------------------

void new_core_state(uint64_t core) {
  if (SYNCHRONIZED_PC)
    if (core > 0)
      return;

  if (CODE_LOADED)
    initial_core_pc_nid = new_constant(OP_CONSTH, SID_MACHINE_WORD, get_pc(current_context), 8, "entry pc value");
  else
    initial_core_pc_nid = new_constant(OP_CONSTH, SID_MACHINE_WORD, code_start, 8, "initial pc value");

  state_core_pc_nid = new_input(OP_STATE, SID_MACHINE_WORD, format_comment("core-%lu-pc", core), "program counter");
  init_core_pc_nid  = new_binary(OP_INIT, SID_MACHINE_WORD, state_core_pc_nid, initial_core_pc_nid, "initial value of pc");
}

void print_core_state(uint64_t core) {
  if (SYNCHRONIZED_PC)
    if (core > 0)
      return;

  print_break_comment(format_comment("core-%lu program counter", core));

  print_line(initial_core_pc_nid);
  print_line(init_core_pc_nid);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------ MODEL GENERATOR ------------------------
// -----------------------------------------------------------------

uint64_t* state_property(uint64_t core, uint64_t* good_nid, uint64_t* bad_nid, char* symbol, char* comment) {
  if (good_nid == UNUSED)
    if (bad_nid == UNUSED)
      return UNUSED;

  if (((CODE_LOADED == 0) + (SYNTHESIZE * (core > 0))) > 0) {
    if (good_nid == UNUSED)
      good_nid = new_unary_boolean(OP_NOT, bad_nid, "asserting");

    return new_property(OP_CONSTRAINT, good_nid, symbol, comment);
  } else {
    if (bad_nid == UNUSED)
      bad_nid = new_unary_boolean(OP_NOT, good_nid, "targeting");

    return new_property(OP_BAD, bad_nid, symbol, comment);
  }
}

void output_model(uint64_t core) {
  print_kernel_state(core);

  print_core_state(core);

  print_register_file_state(core);

  print_code_segment(core);

  print_memory_state(core);

  print_break_comment_line("fetch instruction", eval_core_ir_nid);

  print_break_comment_line("fetch compressed instruction", eval_core_c_ir_nid);

  print_break_comment_line("decode instruction", eval_known_instructions_nid);

  print_break_comment_line("decode compressed instruction",
    eval_known_compressed_instructions_nid);

  print_break_comment_line("instruction control flow", eval_core_instruction_control_flow_nid);

  print_break_comment_line("compressed instruction control flow",
    eval_core_compressed_instruction_control_flow_nid);

  print_break_comment_line("update kernel state", next_program_break_nid);

  print_break_line(next_file_descriptor_nid);

  print_break_line(next_readable_bytes_nid);

  print_break_line(next_read_bytes_nid);

  print_break_comment_line("kernel and instruction control flow", eval_core_control_flow_nid);

  print_break_comment_line("update program counter", next_core_pc_nid);

  print_break_comment_line("instruction register data flow",
    eval_core_instruction_register_data_flow_nid);

  print_break_comment_line("compressed instruction register data flow",
    eval_core_compressed_instruction_register_data_flow_nid);

  print_break_comment_line("kernel and instruction register data flow",
    eval_core_register_data_flow_nid);

  print_break_comment_line("update register data flow", next_register_file_nid);

  print_break_comment_line("instruction memory data flow",
    eval_core_instruction_memory_data_flow_nid);

  print_break_comment_line("compressed instruction memory data flow",
    eval_core_compressed_instruction_memory_data_flow_nid);

  print_break_comment_line("kernel and instruction memory data flow",
    eval_core_memory_data_flow_nid);

  print_break_comment_line("update memory data flow", next_main_memory_nid);

  print_break_comment("state properties");

  print_line(prop_illegal_instruction_nid);

  print_break_line(prop_illegal_compressed_instruction_nid);

  print_break_line(prop_is_instruction_known_nid);

  print_break_line(prop_next_fetch_unaligned_nid);

  print_break_line(prop_next_fetch_seg_faulting_nid);

  print_break_line(prop_is_syscall_id_known_nid);

  // optional state properties

  if (core == CORES - 1)
    print_break_line(prop_bad_exit_code_nid);

  print_break_line(prop_exclude_a0_from_rd_nid);

  print_break_line(prop_division_by_zero_nid);

  print_break_line(prop_signed_division_overflow_nid);

  // segmentation faults in main memory

  print_break_line(prop_load_seg_faulting_nid);

  print_break_line(prop_store_seg_faulting_nid);

  print_break_line(prop_compressed_load_seg_faulting_nid);

  print_break_line(prop_compressed_store_seg_faulting_nid);

  print_break_line(prop_stack_seg_faulting_nid);

  print_break_line(prop_brk_seg_faulting_nid);

  print_break_line(prop_openat_seg_faulting_nid);

  print_break_line(prop_read_seg_faulting_nid);

  print_break_line(prop_write_seg_faulting_nid);
}

void kernel_combinational(uint64_t* pc_nid, uint64_t* ir_nid,
  uint64_t* control_flow_nid, uint64_t* register_data_flow_nid, uint64_t* memory_data_flow_nid,
  uint64_t* program_break_nid, uint64_t* file_descriptor_nid,
  uint64_t* readable_bytes_nid, uint64_t* read_bytes_nid,
  uint64_t* register_file_nid, uint64_t* memory_nid) {
  uint64_t* active_ecall_nid;

  uint64_t* a7_value_nid;

  uint64_t* exit_syscall_nid;
  uint64_t* brk_syscall_nid;
  uint64_t* openat_syscall_nid;

  uint64_t* read_syscall_nid;
  uint64_t* active_read_nid;

  uint64_t* write_syscall_nid;

  uint64_t* a0_value_nid;
  uint64_t* a2_value_nid;

  uint64_t* more_readable_bytes_nid;

  uint64_t* incremented_read_bytes_nid;
  uint64_t* more_than_one_byte_to_read_nid;
  uint64_t* more_than_one_readable_byte_nid;

  uint64_t* read_return_value_nid;

  uint64_t* a1_value_nid;

  // system call ABI control flow

  active_ecall_nid = new_binary_boolean(OP_EQ, ir_nid, NID_ECALL_I, "ir == ECALL?");

  a7_value_nid = load_register_value(NID_A7, "a7 value", register_file_nid);

  exit_syscall_nid   = new_binary_boolean(OP_EQ, a7_value_nid, NID_EXIT_SYSCALL_ID, "a7 == exit syscall ID?");
  brk_syscall_nid    = new_binary_boolean(OP_EQ, a7_value_nid, NID_BRK_SYSCALL_ID, "a7 == brk syscall ID?");
  openat_syscall_nid = new_binary_boolean(OP_EQ, a7_value_nid, NID_OPENAT_SYSCALL_ID, "a7 == openat syscall ID?");

  read_syscall_nid = new_binary_boolean(OP_EQ, a7_value_nid, NID_READ_SYSCALL_ID, "a7 == read syscall ID?");
  active_read_nid  = new_binary_boolean(OP_AND, active_ecall_nid, read_syscall_nid, "active read system call");

  write_syscall_nid = new_binary_boolean(OP_EQ, a7_value_nid, NID_WRITE_SYSCALL_ID, "a7 == write syscall ID?");

  // system call ABI data flow

  a0_value_nid = load_register_value(NID_A0, "a0 value", register_file_nid);

  // new brk kernel state

  eval_program_break_nid =
    new_ternary(OP_ITE, SID_VIRTUAL_ADDRESS,
      new_binary_boolean(OP_AND,
        new_binary_boolean(OP_UGTE,
          cast_machine_word_to_virtual_address(a0_value_nid),
          program_break_nid,
          "new program break >= current program break?"),
        new_binary_boolean(OP_ULTE,
          cast_machine_word_to_virtual_address(a0_value_nid),
          NID_HEAP_END,
          "new program break <= end of heap segment?"),
        "is new program break in heap segment?"),
      cast_machine_word_to_virtual_address(a0_value_nid),
      program_break_nid,
      "update a0 if new program break is in heap segment");

  // new openat kernel state

  eval_file_descriptor_nid = new_unary(OP_INC, SID_MACHINE_WORD,
    file_descriptor_nid,
    "increment file descriptor");

  // system call ABI data flow

  a2_value_nid = load_register_value(NID_A2, "a2 value", register_file_nid);

  // new read kernel state

  more_readable_bytes_nid =
    new_binary_boolean(OP_UGT,
      readable_bytes_nid,
      NID_MACHINE_WORD_0,
      "more readable bytes");

  eval_still_reading_active_read_nid =
    new_binary_boolean(OP_AND,
      active_read_nid,
      new_binary_boolean(OP_AND,
        new_binary_boolean(OP_ULT,
          read_bytes_nid,
          a2_value_nid,
          "more bytes to read as requested in a2"),
        more_readable_bytes_nid,
        "can and still would like to read more bytes"),
      "still reading active read system call");

  incremented_read_bytes_nid =
    new_unary(OP_INC,
      SID_MACHINE_WORD,
      read_bytes_nid,
      "increment bytes already read by read system call");

  more_than_one_byte_to_read_nid =
    new_binary_boolean(OP_ULT,
      incremented_read_bytes_nid,
      a2_value_nid,
      "more than one byte to read as requested in a2");

  more_than_one_readable_byte_nid =
    new_binary_boolean(OP_UGT,
      readable_bytes_nid,
      NID_MACHINE_WORD_1,
      "more than one readable byte");

  eval_more_than_one_readable_byte_to_read_nid =
    new_binary_boolean(OP_AND,
      more_than_one_byte_to_read_nid,
      more_than_one_readable_byte_nid,
      "can and still would like to read more than one byte");

  // kernel and instruction control flow

  eval_core_control_flow_nid = new_ternary(OP_ITE, SID_MACHINE_WORD,
    new_binary_boolean(OP_AND,
      active_ecall_nid,
      new_binary_boolean(OP_OR,
        exit_syscall_nid,
        new_binary_boolean(OP_AND,
          read_syscall_nid,
          eval_more_than_one_readable_byte_to_read_nid,
          "ongoing read system call"),
        "ongoing exit or read system call"),
      "active system call"),
    pc_nid,
    control_flow_nid,
    "update program counter unless in kernel mode");

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

  // kernel and instruction register data flow

  eval_core_register_data_flow_nid = new_ternary(OP_ITE, SID_REGISTER_STATE,
    active_ecall_nid,
    new_ternary(OP_ITE, SID_REGISTER_STATE,
      brk_syscall_nid,
      store_register_value(
        NID_A0,
        cast_virtual_address_to_machine_word(eval_program_break_nid),
        "store new program break in a0",
        register_file_nid),
      new_ternary(OP_ITE, SID_REGISTER_STATE,
        openat_syscall_nid,
        store_register_value(
          NID_A0,
          eval_file_descriptor_nid,
          "store new file descriptor in a0",
          register_file_nid),
        new_ternary(OP_ITE, SID_REGISTER_STATE,
          new_binary_boolean(OP_AND,
            read_syscall_nid,
            new_unary_boolean(OP_NOT,
              eval_more_than_one_readable_byte_to_read_nid,
              "read system call returns if there is at most one more byte to read"),
            "update a0 when read system call returns"),
          store_register_value(
            NID_A0,
            read_return_value_nid,
            "store read return value in a0",
            register_file_nid),
          new_ternary(OP_ITE, SID_REGISTER_STATE,
            write_syscall_nid,
            store_register_value(
              NID_A0,
              a2_value_nid,
              "store write return value in a0",
              register_file_nid),
            register_file_nid,
            "write system call register data flow"),
          "read system call register data flow"),
        "openat system call register data flow"),
      "brk system call register data flow"),
    register_data_flow_nid,
    "register data flow");

  // system call ABI data flow

  a1_value_nid = load_register_value(NID_A1, "a1 value", register_file_nid);

  // kernel and instruction memory data flow

  eval_core_memory_data_flow_nid = new_ternary(OP_ITE, SID_MEMORY_STATE,
    eval_still_reading_active_read_nid,
    store_byte(new_binary(OP_ADD, SID_MACHINE_WORD,
      a1_value_nid,
      read_bytes_nid,
      "a1 + number of already read_bytes"),
      new_input(OP_INPUT, SID_BYTE, "read-input-byte", "input byte by read system call"),
      memory_nid),
    memory_data_flow_nid,
    "main memory data flow");
}

void kernel_sequential(uint64_t core,
  uint64_t* program_break_nid, uint64_t* file_descriptor_nid,
  uint64_t* readable_bytes_nid, uint64_t* read_bytes_nid,
  uint64_t* new_program_break_nid, uint64_t* new_file_descriptor_nid,
  uint64_t* still_reading_active_read_nid, uint64_t* more_than_one_readable_byte_to_read_nid,
  uint64_t* ir_nid, uint64_t* register_file_nid) {
  uint64_t* active_ecall_nid;

  uint64_t* a7_value_nid;

  uint64_t* brk_syscall_nid;
  uint64_t* active_brk_nid;

  uint64_t* openat_syscall_nid;
  uint64_t* active_openat_nid;

  uint64_t* read_syscall_nid;
  uint64_t* active_read_nid;

  // system call ABI control flow

  active_ecall_nid = new_binary_boolean(OP_EQ, ir_nid, NID_ECALL_I, "ir == ECALL?");

  a7_value_nid = load_register_value(NID_A7, "a7 value", register_file_nid);

  brk_syscall_nid = new_binary_boolean(OP_EQ, a7_value_nid, NID_BRK_SYSCALL_ID, "a7 == brk syscall ID?");
  active_brk_nid  = new_binary_boolean(OP_AND, active_ecall_nid, brk_syscall_nid, "active brk system call");

  openat_syscall_nid = new_binary_boolean(OP_EQ, a7_value_nid, NID_OPENAT_SYSCALL_ID, "a7 == openat syscall ID?");
  active_openat_nid  = new_binary_boolean(OP_AND, active_ecall_nid, openat_syscall_nid, "active openat system call");

  read_syscall_nid = new_binary_boolean(OP_EQ, a7_value_nid, NID_READ_SYSCALL_ID, "a7 == read syscall ID?");
  active_read_nid  = new_binary_boolean(OP_AND, active_ecall_nid, read_syscall_nid, "active read system call");

  // update brk kernel state

  next_program_break_nid =
    new_ternary(OP_ITE, SID_VIRTUAL_ADDRESS,
      active_brk_nid,
      new_program_break_nid,
      program_break_nid,
      "new program break");

  if (core == CORES - 1)
    next_program_break_nid =
      new_binary(OP_NEXT, SID_VIRTUAL_ADDRESS,
        program_break_nid,
        next_program_break_nid,
        "new program break");

  // update openat kernel state

  next_file_descriptor_nid =
    new_ternary(OP_ITE, SID_MACHINE_WORD,
      active_openat_nid,
      new_file_descriptor_nid,
      file_descriptor_nid,
      "new file descriptor");

  if (core == CORES - 1)
    next_file_descriptor_nid =
      new_binary(OP_NEXT, SID_MACHINE_WORD,
        file_descriptor_nid,
        next_file_descriptor_nid,
        "new file descriptor");

  // update read kernel state

  next_readable_bytes_nid =
    new_binary(OP_NEXT, SID_MACHINE_WORD,
      readable_bytes_nid,
      new_ternary(OP_ITE, SID_MACHINE_WORD,
        still_reading_active_read_nid,
        new_unary(OP_DEC, SID_MACHINE_WORD,
          readable_bytes_nid,
          "decrement readable bytes"),
        readable_bytes_nid,
        "decrement readable bytes if system call is still reading"),
      "readable bytes");

  next_read_bytes_nid =
    new_binary(OP_NEXT, SID_MACHINE_WORD,
      read_bytes_nid,
      new_ternary(OP_ITE, SID_MACHINE_WORD,
        new_binary_boolean(OP_AND,
          active_read_nid,
          more_than_one_readable_byte_to_read_nid,
          "more than one byte to read by active read system call"),
        new_unary(OP_INC,
          SID_MACHINE_WORD,
          read_bytes_nid,
          "increment bytes already read by read system call"),
        NID_MACHINE_WORD_0,
        "increment bytes already read if read system call is active"),
      "bytes already read in active read system call");
}

void kernel_properties(uint64_t core, uint64_t* ir_nid, uint64_t* read_bytes_nid, uint64_t* register_file_nid) {
  uint64_t* active_ecall_nid;

  uint64_t* a7_value_nid;

  uint64_t* exit_syscall_nid;
  uint64_t* active_exit_nid;

  uint64_t* brk_syscall_nid;
  uint64_t* active_brk_nid;

  uint64_t* openat_syscall_nid;
  uint64_t* active_openat_nid;

  uint64_t* read_syscall_nid;
  uint64_t* active_read_nid;

  uint64_t* write_syscall_nid;
  uint64_t* active_write_nid;

  uint64_t* a0_value_nid;
  uint64_t* a1_value_nid;
  uint64_t* a2_value_nid;

  uint64_t* bad_exit_code_nid;

  // system call ABI control flow

  active_ecall_nid = new_binary_boolean(OP_EQ, ir_nid, NID_ECALL_I, "ir == ECALL?");

  a7_value_nid = load_register_value(NID_A7, "a7 value", register_file_nid);

  exit_syscall_nid = new_binary_boolean(OP_EQ, a7_value_nid, NID_EXIT_SYSCALL_ID, "a7 == exit syscall ID?");
  active_exit_nid  = new_binary_boolean(OP_AND, active_ecall_nid, exit_syscall_nid, "active exit system call");

  brk_syscall_nid = new_binary_boolean(OP_EQ, a7_value_nid, NID_BRK_SYSCALL_ID, "a7 == brk syscall ID?");
  active_brk_nid  = new_binary_boolean(OP_AND, active_ecall_nid, brk_syscall_nid, "active brk system call");

  openat_syscall_nid = new_binary_boolean(OP_EQ, a7_value_nid, NID_OPENAT_SYSCALL_ID, "a7 == openat syscall ID?");
  active_openat_nid  = new_binary_boolean(OP_AND, active_ecall_nid, openat_syscall_nid, "active openat system call");

  read_syscall_nid = new_binary_boolean(OP_EQ, a7_value_nid, NID_READ_SYSCALL_ID, "a7 == read syscall ID?");
  active_read_nid  = new_binary_boolean(OP_AND, active_ecall_nid, read_syscall_nid, "active read system call");

  write_syscall_nid = new_binary_boolean(OP_EQ, a7_value_nid, NID_WRITE_SYSCALL_ID, "a7 == write syscall ID?");
  active_write_nid  = new_binary_boolean(OP_AND, active_ecall_nid, write_syscall_nid, "active write system call");

  // system call ABI data flow

  a0_value_nid = load_register_value(NID_A0, "a0 value", register_file_nid);
  a1_value_nid = load_register_value(NID_A1, "a1 value", register_file_nid);
  a2_value_nid = load_register_value(NID_A2, "a2 value", register_file_nid);

  // kernel properties

  prop_is_syscall_id_known_nid = state_property(core,
    UNUSED,
    new_binary_boolean(OP_AND,
      active_ecall_nid,
      new_binary_boolean(OP_AND,
        new_binary_boolean(OP_NEQ, a7_value_nid, NID_EXIT_SYSCALL_ID, "a7 != exit syscall ID?"),
        new_binary_boolean(OP_AND,
          new_binary_boolean(OP_NEQ, a7_value_nid, NID_BRK_SYSCALL_ID, "a7 != brk syscall ID?"),
          new_binary_boolean(OP_AND,
            new_binary_boolean(OP_NEQ, a7_value_nid, NID_OPENAT_SYSCALL_ID, "a7 != openat syscall ID?"),
            new_binary_boolean(OP_AND,
              new_binary_boolean(OP_NEQ, a7_value_nid, NID_READ_SYSCALL_ID, "a7 != read syscall ID?"),
              new_binary_boolean(OP_NEQ, a7_value_nid, NID_WRITE_SYSCALL_ID, "a7 != write syscall ID?"),
              "a7 != read or write syscall ID"),
            "a7 != openat or read or write syscall ID"),
          "a7 != brk or openat or read or write syscall ID"),
        "a7 != exit or brk or openat or read or write syscall ID"),
      "active ecall and a7 != known syscall ID"),
    format_comment("core-%lu-unknown-syscall-ID", core),
    format_comment("core-%lu unknown syscall ID", core));

  if (check_seg_faults)
    prop_brk_seg_faulting_nid = state_property(core,
      UNUSED,
      new_binary_boolean(OP_AND,
        active_brk_nid,
        new_unary_boolean(OP_NOT,
          does_machine_word_work_as_virtual_address(a0_value_nid,
            new_binary_boolean(OP_ULTE,
              cast_machine_word_to_virtual_address(a0_value_nid),
              NID_HEAP_END,
              "new program break cast to virtual address <= end of heap segment?")),
          "is new program break invalid?"),
        "invalid new program break with active brk system call"),
      format_comment("core-%lu-brk-seg-fault", core),
      format_comment("core-%lu possible brk segmentation fault", core));

  // TODO: validate openat arguments other than filename

  if (check_seg_faults)
    prop_openat_seg_faulting_nid = state_property(core,
      UNUSED,
      new_binary_boolean(OP_AND,
        active_openat_nid,
        new_unary_boolean(OP_NOT,
          is_range_in_heap_segment(a1_value_nid, NID_MAX_STRING_LENGTH),
          "is filename access not in heap segment?"),
        "openat system call filename access may cause segmentation fault"),
      format_comment("core-%lu-openat-seg-fault", core),
      format_comment("core-%lu possible openat segmentation fault", core));

  // TODO: further validate read arguments

  if (check_seg_faults)
    prop_read_seg_faulting_nid = state_property(core,
      UNUSED,
      new_binary_boolean(OP_AND,
        new_binary_boolean(OP_AND,
          active_read_nid,
          new_binary_boolean(OP_EQ,
            read_bytes_nid,
            NID_MACHINE_WORD_0,
            "have bytes been read yet?"),
          "no bytes read yet by active read system call"),
        new_binary_boolean(OP_AND,
          new_binary_boolean(OP_UGT, a2_value_nid, NID_MACHINE_WORD_0, "bytes to be read > 0?"),
          new_unary_boolean(OP_NOT,
            is_range_in_heap_segment(a1_value_nid, a2_value_nid),
            "is read system call access not in heap segment?"),
          "may bytes to be read not be stored in heap segment?"),
        "storing bytes to be read may cause segmentation fault"),
      format_comment("core-%lu-read-seg-fault", core),
      format_comment("core-%lu possible read segmentation fault", core));

  // TODO: further validate write arguments

  if (check_seg_faults)
    prop_write_seg_faulting_nid = state_property(core,
      UNUSED,
      new_binary_boolean(OP_AND,
        active_write_nid,
          new_binary_boolean(OP_AND,
            new_binary_boolean(OP_UGT, a2_value_nid, NID_MACHINE_WORD_0, "bytes to be written > 0?"),
            new_unary_boolean(OP_NOT,
              is_range_in_heap_segment(a1_value_nid, a2_value_nid),
              "is write system call access not in heap segment?"),
          "may bytes to be written not be loaded from heap segment?"),
        "loading bytes to be written may cause segmentation fault"),
      format_comment("core-%lu-write-seg-fault", core),
      format_comment("core-%lu possible write segmentation fault", core));

  if (check_exit_code) {
    bad_exit_code_nid = new_binary_boolean(OP_AND,
      active_exit_nid,
      new_binary_boolean(OP_EQ,
        a0_value_nid,
        new_constant(OP_CONSTD, SID_MACHINE_WORD,
          bad_exit_code, 0, format_comment("bad exit code %ld", bad_exit_code)),
        "actual exit code == bad exit code?"),
      format_comment("core-%lu active exit system call with bad exit code", core));

    if (core == 0)
      prop_bad_exit_code_nid = bad_exit_code_nid;
    else
      prop_bad_exit_code_nid = new_binary_boolean(OP_AND,
        prop_bad_exit_code_nid,
        bad_exit_code_nid,
        "and next bad exit");

    if (core == CORES - 1)
      prop_bad_exit_code_nid = new_property(OP_BAD,
        prop_bad_exit_code_nid,
        "bad-exit-code",
        format_comment("exit(%ld)", bad_exit_code));
  }
}

void rotor_combinational(uint64_t* pc_nid, uint64_t* code_segment_nid, uint64_t* register_file_nid, uint64_t* memory_nid) {
  // fetch instruction

  eval_core_ir_nid = fetch_instruction(pc_nid, code_segment_nid);

  // fetch compressed instruction

  eval_core_c_ir_nid = fetch_compressed_instruction(pc_nid, code_segment_nid);

  // decode instruction

  eval_known_instructions_nid = decode_instruction(eval_core_ir_nid);

  // decode compressed instruction

  eval_known_compressed_instructions_nid = decode_compressed_instruction(eval_core_c_ir_nid);

  // instruction control flow

  eval_core_instruction_control_flow_nid =
    core_control_flow(pc_nid, eval_core_ir_nid, register_file_nid);

  // compressed instruction control flow

  eval_core_compressed_instruction_control_flow_nid =
    core_compressed_control_flow(pc_nid, eval_core_c_ir_nid, register_file_nid,
      eval_core_instruction_control_flow_nid);

  // instruction register data flow

  eval_core_instruction_register_data_flow_nid =
    core_register_data_flow(pc_nid, eval_core_ir_nid, register_file_nid, memory_nid);

  // compressed instruction register data flow

  eval_core_compressed_instruction_register_data_flow_nid =
    core_compressed_register_data_flow(pc_nid, eval_core_c_ir_nid,
      eval_core_instruction_register_data_flow_nid, memory_nid);

  // instruction memory data flow

  eval_core_instruction_memory_data_flow_nid =
    core_memory_data_flow(eval_core_ir_nid, register_file_nid, memory_nid);

  // compressed instruction memory data flow

  eval_core_compressed_instruction_memory_data_flow_nid =
    core_compressed_memory_data_flow(eval_core_c_ir_nid, register_file_nid,
      eval_core_instruction_memory_data_flow_nid);
}

void rotor_sequential(uint64_t core, uint64_t* pc_nid, uint64_t* register_file_nid, uint64_t* memory_nid,
  uint64_t* control_flow_nid, uint64_t* register_data_flow_nid, uint64_t* memory_data_flow_nid) {
  // update control flow

  if (SYNCHRONIZED_PC)
    if (core == 0) {
      next_core_pc_nid = new_binary(OP_NEXT, SID_MACHINE_WORD,
        pc_nid, control_flow_nid, "program counter");

      eval_core_0_control_flow_nid = control_flow_nid;
    } else
      next_core_pc_nid = new_property(OP_CONSTRAINT,
        new_binary_boolean(OP_EQ,
          control_flow_nid,
          eval_core_0_control_flow_nid,
          "new pc value == new core-0 pc value?"),
        format_comment("new-core-%lu-pc-value", core),
        "asserting new pc value == new core-0 pc value");
  else
    next_core_pc_nid = new_binary(OP_NEXT, SID_MACHINE_WORD,
      pc_nid, control_flow_nid, "program counter");

  // update register data flow

  if (SYNCHRONIZED_REGISTERS)
    if (core == 0) {
      next_register_file_nid = new_binary(OP_NEXT, SID_REGISTER_STATE,
        register_file_nid, register_data_flow_nid, "register file");

      eval_core_0_register_data_flow_nid = register_data_flow_nid;
    } else
      next_register_file_nid = new_property(OP_CONSTRAINT,
        new_binary_boolean(OP_EQ,
          register_data_flow_nid,
          eval_core_0_register_data_flow_nid,
          "new register data flow == new core-0 register data flow?"),
        format_comment("new-core-%lu-register-data-flow", core),
        "asserting new register data flow == new core-0 register data flow");
  else if (SHARED_REGISTERS) {
    if (core < CORES - 1)
      state_register_file_nid = register_data_flow_nid;
    else
      next_register_file_nid = new_binary(OP_NEXT, SID_REGISTER_STATE,
        register_file_nid, register_data_flow_nid, "register file");
  } else
    next_register_file_nid = new_binary(OP_NEXT, SID_REGISTER_STATE,
      register_file_nid, register_data_flow_nid, "register file");

  // update memory data flow

  if (SYNCHRONIZED_MEMORY)
    if (core == 0) {
      next_main_memory_nid = new_binary(OP_NEXT, SID_MEMORY_STATE,
        memory_nid, memory_data_flow_nid, "main memory");

      eval_core_0_memory_data_flow_nid = memory_data_flow_nid;
    } else
      next_main_memory_nid = new_property(OP_CONSTRAINT,
        new_binary_boolean(OP_EQ,
          memory_data_flow_nid,
          eval_core_0_memory_data_flow_nid,
          "new memory data flow == new core-0 memory data flow?"),
        format_comment("new-core-%lu-memory-data-flow", core),
        "asserting new memory data flow == new core-0 memory data flow");
  else if (SHARED_MEMORY) {
    if (core < CORES - 1)
      state_main_memory_nid = memory_data_flow_nid;
    else
      next_main_memory_nid = new_binary(OP_NEXT, SID_MEMORY_STATE,
        memory_nid, memory_data_flow_nid, "main memory");
  } else
    next_main_memory_nid = new_binary(OP_NEXT, SID_MEMORY_STATE,
      memory_nid, memory_data_flow_nid, "main memory");
}

void rotor_properties(uint64_t core, uint64_t* ir_nid, uint64_t* c_ir_nid,
  uint64_t* known_instructions_nid, uint64_t* known_compressed_instructions_nid,
  uint64_t* control_flow_nid, uint64_t* register_file_nid) {

  // mandatory state properties

  prop_illegal_instruction_nid = state_property(core,
    UNUSED,
    decode_illegal_shamt(ir_nid),
    format_comment("core-%lu-illegal-instruction", core),
    format_comment("core-%lu illegal instruction", core));

  prop_illegal_compressed_instruction_nid = state_property(core,
    UNUSED,
    decode_illegal_compressed_instruction_imm_shamt(c_ir_nid),
    format_comment("core-%lu-illegal-compressed-instruction", core),
    format_comment("core-%lu illegal compressed instruction", core));

  if (known_compressed_instructions_nid != UNUSED)
    known_instructions_nid = new_ternary(OP_ITE, SID_BOOLEAN,
      is_compressed_instruction(ir_nid),
      known_compressed_instructions_nid,
      known_instructions_nid,
      "is known uncompressed or compressed instruction?");

  prop_is_instruction_known_nid = state_property(core,
    known_instructions_nid,
    UNUSED,
    format_comment("core-%lu-known-instructions", core),
    format_comment("core-%lu known instructions", core));

  prop_next_fetch_unaligned_nid = state_property(core,
    new_binary_boolean(OP_EQ,
      new_binary(OP_AND, SID_MACHINE_WORD,
        control_flow_nid,
        NID_INSTRUCTION_WORD_SIZE_MASK,
        "next pc alignment"),
      NID_MACHINE_WORD_0,
      "next pc unaligned"),
    UNUSED,
    format_comment("core-%lu-fetch-unaligned", core),
    format_comment("core-%lu imminent unaligned fetch", core));

  prop_next_fetch_seg_faulting_nid = state_property(core,
    is_address_in_code_segment(control_flow_nid),
    UNUSED,
    format_comment("core-%lu-fetch-seg-fault", core),
    format_comment("core-%lu imminent fetch segmentation fault", core));

  // optional state properties

  if (exclude_a0_from_rd)
    prop_exclude_a0_from_rd_nid = state_property(core,
      new_binary_boolean(OP_NEQ,
        get_instruction_rd(ir_nid),
        NID_A0,
        "rd != a0"),
      UNUSED,
      format_comment("core-%lu-exclude-a0-from-rd", core),
      format_comment("core-%lu only brk and read system call may update a0", core));

  if (check_division_by_zero)
    prop_division_by_zero_nid = state_property(core,
      UNUSED,
      decode_division_remainder_by_zero(ir_nid, register_file_nid),
      format_comment("core-%lu-division-by-zero", core),
      format_comment("core-%lu division by zero", core));

  if (check_division_overflow)
    prop_signed_division_overflow_nid = state_property(core,
      UNUSED,
      decode_signed_division_remainder_overflow(ir_nid, register_file_nid),
      format_comment("core-%lu-signed-division-overflow", core),
      format_comment("core-%lu signed division overflow", core));

  // segmentation faults in main memory

  if (check_seg_faults) {
    prop_load_seg_faulting_nid = state_property(core,
      load_no_seg_faults(ir_nid, register_file_nid),
      UNUSED,
      format_comment("core-%lu-load-seg-fault", core),
      format_comment("core-%lu load segmentation fault", core));

    prop_store_seg_faulting_nid = state_property(core,
      store_no_seg_faults(ir_nid, register_file_nid),
      UNUSED,
      format_comment("core-%lu-store-seg-fault", core),
      format_comment("core-%lu store segmentation fault", core));

    prop_compressed_load_seg_faulting_nid = state_property(core,
      compressed_load_no_seg_faults(c_ir_nid, register_file_nid),
      UNUSED,
      format_comment("core-%lu-compressed-load-seg-fault", core),
      format_comment("core-%lu compressed load segmentation fault", core));

    prop_compressed_store_seg_faulting_nid = state_property(core,
      compressed_store_no_seg_faults(c_ir_nid, register_file_nid),
      UNUSED,
      format_comment("core-%lu-compressed-store-seg-fault", core),
      format_comment("core-%lu compressed store segmentation fault", core));

    // TODO: check stack pointer segfault earlier upon sp update

    prop_stack_seg_faulting_nid = state_property(core,
      is_address_in_stack_segment(load_register_value(NID_SP, "sp value", register_file_nid)),
      UNUSED,
      format_comment("core-%lu-stack-seg-fault", core),
      format_comment("core-%lu stack segmentation fault", core));
  }
}

void rotor() {
  uint64_t i;
  uint64_t core;

  w = w
    + dprintf(output_fd, "; %s\n\n", SELFIE_URL)
    + dprintf(output_fd, "; BTOR2 file %s generated by %s\n\n", model_name, selfie_name);
  if (check_exit_code == 0)
    w = w + dprintf(output_fd, "; with %s\n", exit_code_check_option);
  if (check_division_by_zero == 0)
    w = w + dprintf(output_fd, "; with %s\n", division_by_zero_check_option);
  if (check_division_overflow == 0)
    w = w + dprintf(output_fd, "; with %s\n", division_overflow_check_option);
  if (check_seg_faults == 0)
    w = w + dprintf(output_fd, "; with %s\n", seg_faults_check_option);
  w = w + dprintf(output_fd, "; with %s %lu\n", cores_option, CORES);
  w = w + dprintf(output_fd, "; with %s %lu\n", heap_allowance_option, heap_allowance);
  w = w + dprintf(output_fd, "; with %s %lu\n\n", stack_allowance_option, stack_allowance);
  if (binary_name) {
    w = w + dprintf(output_fd, "; RISC-V code obtained from %s and invoked as:", binary_name);
    i = 0;
    while (i < number_of_remaining_arguments()) {
      w = w + dprintf(output_fd, " %s", (char*) *(remaining_arguments() + i));
      i = i + 1;
    }
    w = w + dprintf(output_fd, "\n\n");
  }

  init_model_generator();

  print_interface_sorts();
  print_interface_kernel();

  print_register_sorts();
  print_memory_sorts();

  new_segmentation();

  print_segmentation();

  core = 0;

  while (core < CORES) {
    new_kernel_state(core, 1);

    new_core_state(core);

    new_register_file_state(core);

    new_code_segment(core);

    new_memory_state(core);

    rotor_combinational(state_core_pc_nid, state_code_segment_nid,
      state_register_file_nid, state_main_memory_nid);
    kernel_combinational(state_core_pc_nid, eval_core_ir_nid,
      eval_core_compressed_instruction_control_flow_nid,
      eval_core_compressed_instruction_register_data_flow_nid,
      eval_core_compressed_instruction_memory_data_flow_nid,
      next_program_break_nid, next_file_descriptor_nid,
      state_readable_bytes_nid, state_read_bytes_nid,
      state_register_file_nid, state_main_memory_nid);

    rotor_sequential(core, state_core_pc_nid,
      state_register_file_nid, state_main_memory_nid,
      eval_core_control_flow_nid,
      eval_core_register_data_flow_nid,
      eval_core_memory_data_flow_nid);
    kernel_sequential(core,
      state_program_break_nid, state_file_descriptor_nid,
      state_readable_bytes_nid, state_read_bytes_nid,
      eval_program_break_nid, eval_file_descriptor_nid,
      eval_still_reading_active_read_nid, eval_more_than_one_readable_byte_to_read_nid,
      eval_core_ir_nid, state_register_file_nid);

    rotor_properties(core,
      eval_core_ir_nid, eval_core_c_ir_nid,
      eval_known_instructions_nid, eval_known_compressed_instructions_nid,
      eval_core_control_flow_nid, state_register_file_nid);
    kernel_properties(core,
      eval_core_ir_nid,
      state_read_bytes_nid,
      state_register_file_nid);

    output_model(core);

    core = core + 1;
  }
}

uint64_t selfie_model() {
  uint64_t model_arguments;

  if (string_compare(argument, "-")) {
    if (number_of_remaining_arguments() > 0) {
      bad_exit_code = atoi(peek_argument(0));

      exit_code_check_option         = "-Pnoexitcode";
      division_by_zero_check_option  = "-Pnodivbyzero";
      division_overflow_check_option = "-Pnodivoverflow";
      seg_faults_check_option        = "-Pnosegfaults";
      cores_option                   = "-cores";
      heap_allowance_option          = "-heap";
      stack_allowance_option         = "-stack";

      model_arguments = 0;

      while (model_arguments == 0) {
        if (number_of_remaining_arguments() > 1) {
          if (string_compare(peek_argument(1), exit_code_check_option)) {
            check_exit_code = 0;

            get_argument();
          } else if (string_compare(peek_argument(1), division_by_zero_check_option)) {
            check_division_by_zero = 0;

            get_argument();
          } else if (string_compare(peek_argument(1), division_overflow_check_option)) {
            check_division_overflow = 0;

            get_argument();
          } else if (string_compare(peek_argument(1), seg_faults_check_option)) {
            check_seg_faults = 0;

            get_argument();
          } else if (string_compare(peek_argument(1), cores_option)) {
            get_argument();

            if (number_of_remaining_arguments() > 1) {
              CORES = atoi(peek_argument(1));

              get_argument();
            } else
              return EXITCODE_BADARGUMENTS;
          } else if (string_compare(peek_argument(1), heap_allowance_option)) {
            get_argument();

            if (number_of_remaining_arguments() > 1) {
              heap_allowance = round_up(atoi(peek_argument(1)), WORDSIZE);

              get_argument();
            } else
              return EXITCODE_BADARGUMENTS;
          } else if (string_compare(peek_argument(1), stack_allowance_option)) {
            get_argument();

            if (number_of_remaining_arguments() > 1) {
              stack_allowance = round_up(atoi(peek_argument(1)), WORDSIZE);

              get_argument();
            } else
              return EXITCODE_BADARGUMENTS;
          } else if (string_compare(peek_argument(1), "-")) {
            get_argument();

            model_arguments = 1;
          } else
            return EXITCODE_BADARGUMENTS;
        } else
          model_arguments = 1;
      }

      if (code_size > 0) {
        reset_interpreter();
        reset_profiler();
        reset_microkernel();

        init_memory(1);

        current_context = create_context(MY_CONTEXT, 0);

        // assert: number_of_remaining_arguments() > 0

        boot_loader(current_context);

        restore_context(current_context);

        do_switch(current_context, TIMEROFF);

        // assert: allowances are multiples of word size

        if (get_program_break(current_context) - get_heap_seg_start(current_context) > heap_allowance)
          heap_allowance = round_up(get_program_break(current_context) - get_heap_seg_start(current_context), PAGESIZE);

        heap_start = get_heap_seg_start(current_context);
        heap_size  = heap_allowance;

        if (VIRTUALMEMORYSIZE * GIGABYTE - *(get_regs(current_context) + REG_SP) > stack_allowance)
          stack_allowance = round_up(VIRTUALMEMORYSIZE * GIGABYTE - *(get_regs(current_context) + REG_SP), PAGESIZE);

        stack_start = VIRTUALMEMORYSIZE * GIGABYTE - stack_allowance;
        stack_size  = stack_allowance;

        // assert: stack_start >= heap_start + heap_size > 0

        CODE_LOADED = 1;

        if (CORES > 1) {
          SYNTHESIZE = 1;

          SYNCHRONIZED_PC = 0;

          SYNCHRONIZED_REGISTERS = 1;
          SHARED_REGISTERS       = 0;

          SYNCHRONIZED_MEMORY = 1;
          SHARED_MEMORY       = 0;
        }

        model_name = replace_extension(binary_name, "-rotorized", "btor2");
      } else {
        code_start = 4096;
        code_size  = 7 * 4;

        data_start = 8192;
        data_size  = 0;

        heap_start = 12288;
        heap_size  = heap_allowance;

        stack_start = VIRTUALMEMORYSIZE * GIGABYTE - stack_allowance;
        stack_size  = stack_allowance;

        // assert: stack_start >= heap_start + heap_size > 0

        CODE_LOADED = 0;

        SYNTHESIZE = 1;

        SYNCHRONIZED_PC = 0;

        SYNCHRONIZED_REGISTERS = 0;
        SHARED_REGISTERS       = 0;

        SYNCHRONIZED_MEMORY = 0;
        SHARED_MEMORY       = 0;

        if (IS64BITTARGET)
          model_name = "64-bit-riscv-machine.btor2";
        else
          model_name = "32-bit-riscv-machine.btor2";
      }

      // assert: model_name is mapped and not longer than MAX_FILENAME_LENGTH

      model_fd = open_write_only(model_name, S_IRUSR_IWUSR_IRGRP_IROTH);

      if (signed_less_than(model_fd, 0)) {
        printf("%s: could not create model file %s\n", selfie_name, model_name);

        exit(EXITCODE_IOERROR);
      }

      reset_library();

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