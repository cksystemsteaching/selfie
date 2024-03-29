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
  return smalloc(6 * sizeof(uint64_t*) + 2 * sizeof(char*) + 4 * sizeof(uint64_t));
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
uint64_t* get_succ(uint64_t* line)    { return (uint64_t*) *(line + 11); }

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
void set_succ(uint64_t* line, uint64_t* succ)   { *(line + 11) = (uint64_t) succ; }

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

uint64_t* new_init(uint64_t* sid, uint64_t* state_nid, uint64_t* value_nid, char* comment);
uint64_t* new_next(uint64_t* sid, uint64_t* state_nid, uint64_t* value_nid, char* comment);

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

char* OP_IMPLIES = (char*) 0;
char* OP_EQ      = (char*) 0;
char* OP_NEQ     = (char*) 0;
char* OP_SGT     = (char*) 0;
char* OP_UGT     = (char*) 0;
char* OP_SGTE    = (char*) 0;
char* OP_UGTE    = (char*) 0;
char* OP_SLT     = (char*) 0;
char* OP_ULT     = (char*) 0;
char* OP_SLTE    = (char*) 0;
char* OP_ULTE    = (char*) 0;

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

  OP_IMPLIES = "implies";
  OP_EQ      = "eq";
  OP_NEQ     = "neq";
  OP_SGT     = "sgt";
  OP_UGT     = "ugt";
  OP_SGTE    = "sgte";
  OP_UGTE    = "ugte";
  OP_SLT     = "slt";
  OP_ULT     = "ult";
  OP_SLTE    = "slte";
  OP_ULTE    = "ulte";

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

uint64_t is_bitvector(uint64_t* line);
uint64_t is_array(uint64_t* line);

uint64_t is_constant_op(char* op);
uint64_t is_input_op(char* op);
uint64_t is_unary_op(char* op);

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

uint64_t print_referenced_line(uint64_t nid, uint64_t* line);

void print_line(uint64_t* line);
void print_line_for(uint64_t core, uint64_t* lines);

void print_break();
void print_break_line(uint64_t* line);
void print_break_line_for(uint64_t core, uint64_t* lines);
void print_break_comment(char* comment);
void print_break_comment_for(uint64_t core, char* comment);
void print_break_comment_line(char* comment, uint64_t* line);
void print_break_comment_line_for(uint64_t core, char* comment, uint64_t* line);

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

void fit_bitvec_sort(uint64_t* sid, uint64_t value);
void signed_fit_bitvec_sort(uint64_t* sid, uint64_t value);

uint64_t eval_array_size(uint64_t* line);
uint64_t eval_element_size(uint64_t* line);

void fit_array_sorts(uint64_t* array_sid, uint64_t index, uint64_t value);

void match_sorts(uint64_t* sid1, uint64_t* sid2, char* comment);
void match_array_sorts(uint64_t* array_sid, uint64_t* index_sid, uint64_t* value_sid);

uint64_t calculate_address_space(uint64_t number_of_bytes, uint64_t word_size);

uint64_t* allocate_array(uint64_t* sid);

uint64_t* get_data_array(uint64_t* arrays)  { return (uint64_t*) *(arrays + 0); }
uint64_t* get_heap_array(uint64_t* arrays)  { return (uint64_t*) *(arrays + 1); }
uint64_t* get_stack_array(uint64_t* arrays) { return (uint64_t*) *(arrays + 2); }

void set_data_array(uint64_t* arrays, uint64_t* array)  { *(arrays + 0) = (uint64_t) array; }
void set_heap_array(uint64_t* arrays, uint64_t* array)  { *(arrays + 1) = (uint64_t) array; }
void set_stack_array(uint64_t* arrays, uint64_t* array) { *(arrays + 2) = (uint64_t) array; }

uint64_t is_virtual_address_in_segment(uint64_t vaddr, uint64_t start, uint64_t end);
uint64_t is_virtual_address_in_data_segment(uint64_t vaddr);
uint64_t is_virtual_address_in_heap_segment(uint64_t vaddr);
uint64_t is_virtual_address_in_stack_segment(uint64_t vaddr);

uint64_t vaddr_to_index(uint64_t vaddr);
uint64_t index_to_vaddr(uint64_t index);

uint64_t read_or_write(uint64_t* state_nid, uint64_t index, uint64_t value, uint64_t read);

uint64_t is_comparison_operator(char* op);
uint64_t is_bitwise_operator(char* op);
uint64_t is_arithmetic_operator(char* op);
uint64_t is_binary_operator(char* op);

uint64_t bitwise(uint64_t a, uint64_t b, uint64_t and_xor, uint64_t or_xor);
uint64_t bitwise_and(uint64_t a, uint64_t b);
uint64_t bitwise_or(uint64_t a, uint64_t b);
uint64_t bitwise_xor(uint64_t a, uint64_t b);

uint64_t arithmetic_right_shift(uint64_t n, uint64_t b, uint64_t size);
uint64_t signed_less_than_or_equal_to(uint64_t a, uint64_t b);

uint64_t get_cached_state(uint64_t* line);

uint64_t eval_constant_value(uint64_t* line);
uint64_t eval_constant_digits(uint64_t* line);

uint64_t eval_ext_w(uint64_t* line);

uint64_t eval_slice_u(uint64_t* line);
uint64_t eval_slice_l(uint64_t* line);

uint64_t eval_input(uint64_t* line);
uint64_t eval_ext(uint64_t* line);
uint64_t eval_slice(uint64_t* line);
uint64_t eval_concat(uint64_t* line);
uint64_t eval_ite(uint64_t* line);
uint64_t eval_read(uint64_t* line);
uint64_t eval_write(uint64_t* line);
uint64_t eval_unary_op(uint64_t* line);
uint64_t eval_binary_op(uint64_t* line);

uint64_t eval_line(uint64_t* line);
uint64_t eval_line_for(uint64_t core, uint64_t* lines);

uint64_t eval_property(uint64_t core, uint64_t* line);
uint64_t eval_property_for(uint64_t core, uint64_t* lines);

uint64_t eval_init(uint64_t* line);

uint64_t eval_next(uint64_t* line);
uint64_t eval_next_for(uint64_t core, uint64_t* lines);
void apply_next(uint64_t* line);
void apply_next_for(uint64_t core, uint64_t* lines);

uint64_t* memcopy(uint64_t* destination, uint64_t* source, uint64_t bytes);

void save_state(uint64_t* line);
void save_state_for(uint64_t core, uint64_t* lines);
void restore_state(uint64_t* line);
void restore_state_for(uint64_t core, uint64_t* lines);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t UNINITIALIZED = -1; // uninitialized state
uint64_t INITIALIZED   = 0;  // initialized state

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t current_step = 0; // first step in evaluation is 0
uint64_t next_step    = 0; // initial next step in evaluation is 0

uint64_t current_offset = 0; // keeps track of absolute current step

uint64_t input_steps = 0; // number of steps until most recent input has been consumed

uint64_t current_input = 0; // current input byte value

uint64_t first_input = 0; // indicates if input has been consumed for the first time

uint64_t any_input = 0; // indicates if any input has been consumed

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
uint64_t* next_readable_bytes_nids = (uint64_t*) 0;

uint64_t* eval_still_reading_active_read_nid = (uint64_t*) 0;

uint64_t* state_read_bytes_nid = (uint64_t*) 0;
uint64_t* init_read_bytes_nid  = (uint64_t*) 0;
uint64_t* next_read_bytes_nids = (uint64_t*) 0;

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

void init_kernels(uint64_t number_of_cores) {
  next_readable_bytes_nids = zmalloc(number_of_cores * sizeof(uint64_t*));
  next_read_bytes_nids     = zmalloc(number_of_cores * sizeof(uint64_t*));
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

uint64_t* state_register_file_nids = (uint64_t*) 0;
uint64_t* next_register_file_nids  = (uint64_t*) 0;
uint64_t* sync_register_file_nids  = (uint64_t*) 0;

uint64_t* eval_core_0_register_data_flow_nid = (uint64_t*) 0;

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

void init_register_files(uint64_t number_of_cores) {
  state_register_file_nids = zmalloc(number_of_cores * sizeof(uint64_t*));
  next_register_file_nids  = zmalloc(number_of_cores * sizeof(uint64_t*));
  sync_register_file_nids  = zmalloc(number_of_cores * sizeof(uint64_t*));
}

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void print_memory_sorts();

void new_segmentation(uint64_t core);
void print_segmentation(uint64_t core);

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

uint64_t* is_address_in_machine_word_in_code_segment(uint64_t* machine_word_nid);
uint64_t* is_address_in_machine_word_in_data_segment(uint64_t* machine_word_nid);
uint64_t* is_address_in_machine_word_in_heap_segment(uint64_t* machine_word_nid);
uint64_t* is_address_in_machine_word_in_stack_segment(uint64_t* machine_word_nid);
uint64_t* is_address_in_machine_word_in_main_memory(uint64_t* machine_word_nid);

uint64_t* is_range_in_machine_word_in_heap_segment(uint64_t* machine_word_nid, uint64_t* range_nid);

uint64_t* is_sized_block_in_stack_segment(uint64_t* machine_word_nid, uint64_t* size_nid);
uint64_t* is_sized_block_in_main_memory(uint64_t* machine_word_nid, uint64_t* size_nid);

uint64_t* fetch_instruction(uint64_t* pc_nid, uint64_t* code_segment_nid);
uint64_t* fetch_compressed_instruction(uint64_t* pc_nid, uint64_t* code_segment_nid);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t SYNCHRONIZED_MEMORY = 0; // flag for synchronized main memory across cores
uint64_t SHARED_MEMORY       = 0; // flag for shared main memory across cores

uint64_t VIRTUAL_ADDRESS_SPACE = 32; // number of bits in virtual addresses

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

uint64_t CODEWORDSIZEINBITS = 32;

uint64_t* SID_CODE_WORD = (uint64_t*) 0;

uint64_t* NID_CODE_WORD_0 = (uint64_t*) 0;

uint64_t CODE_ADDRESS_SPACE = 0; // number of bits in code segment addresses

uint64_t* SID_CODE_ADDRESS = (uint64_t*) 0;
uint64_t* SID_CODE_STATE   = (uint64_t*) 0;

uint64_t* NID_CODE_START = (uint64_t*) 0;
uint64_t* NID_CODE_END   = (uint64_t*) 0;

uint64_t MEMORYWORDSIZEINBITS = 64;

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

uint64_t heap_initial_size = 0;
uint64_t heap_allowance    = 4096; // must be multiple of WORDSIZE

uint64_t heap_start = 0;
uint64_t heap_size  = 0;

uint64_t stack_initial_size = 0;
uint64_t stack_allowance    = 4096; // must be multiple of WORDSIZE > 0

uint64_t stack_start = 0;
uint64_t stack_size  = 0;

uint64_t* state_zeroed_code_segment_nid = (uint64_t*) 0;
uint64_t* init_zeroed_code_segment_nid  = (uint64_t*) 0;
uint64_t* next_zeroed_code_segment_nid  = (uint64_t*) 0;

uint64_t* initial_code_nid = (uint64_t*) 0;

uint64_t* initial_code_segment_nid = (uint64_t*) 0;

uint64_t* state_code_segment_nid = (uint64_t*) 0;
uint64_t* init_code_segment_nid  = (uint64_t*) 0;
uint64_t* next_code_segment_nid  = (uint64_t*) 0;

uint64_t* state_code_segment_nids = (uint64_t*) 0;
uint64_t* next_code_segment_nids  = (uint64_t*) 0;

uint64_t* init_zeroed_main_memory_nid = (uint64_t*) 0;
uint64_t* next_zeroed_main_memory_nid = (uint64_t*) 0;

uint64_t* initial_data_nid  = (uint64_t*) 0;
uint64_t* initial_heap_nid  = (uint64_t*) 0;
uint64_t* initial_stack_nid = (uint64_t*) 0;

uint64_t* initial_main_memory_nid = (uint64_t*) 0;

uint64_t* state_main_memory_nid = (uint64_t*) 0;
uint64_t* init_main_memory_nid  = (uint64_t*) 0;
uint64_t* next_main_memory_nid  = (uint64_t*) 0;

uint64_t* state_main_memory_nids = (uint64_t*) 0;
uint64_t* next_main_memory_nids  = (uint64_t*) 0;
uint64_t* sync_main_memory_nids  = (uint64_t*) 0;

uint64_t* eval_core_0_memory_data_flow_nid = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_memory_sorts(uint64_t max_code_size) {
  uint64_t saved_reuse_lines;

  if (VIRTUAL_ADDRESS_SPACE > WORDSIZEINBITS)
    VIRTUAL_ADDRESS_SPACE = WORDSIZEINBITS;

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

  if (CODEWORDSIZEINBITS > WORDSIZEINBITS)
    CODEWORDSIZEINBITS = WORDSIZEINBITS;

  SID_CODE_WORD = new_bitvec(CODEWORDSIZEINBITS,
    format_comment("%lu-bit code word", CODEWORDSIZEINBITS));

  NID_CODE_WORD_0 = new_constant(OP_CONSTD, SID_CODE_WORD, 0, 0, "code word 0");

  CODE_ADDRESS_SPACE = calculate_address_space(max_code_size, eval_bitvec_size(SID_CODE_WORD));

  SID_CODE_ADDRESS = new_bitvec(CODE_ADDRESS_SPACE,
    format_comment("%lu-bit code segment address", CODE_ADDRESS_SPACE));

  SID_CODE_STATE = new_array(SID_CODE_ADDRESS, SID_CODE_WORD, "code segment state");

  // main memory

  if (MEMORYWORDSIZEINBITS > WORDSIZEINBITS)
    MEMORYWORDSIZEINBITS = WORDSIZEINBITS;

  SID_MEMORY_WORD = new_bitvec(MEMORYWORDSIZEINBITS,
    format_comment("%lu-bit memory word", MEMORYWORDSIZEINBITS));

  NID_MEMORY_WORD_0 = new_constant(OP_CONSTD, SID_MEMORY_WORD, 0, 0, "memory word 0");

  // assert: memory word size is a power of 2 >= 8 bits

  MEMORY_ADDRESS_SPACE =
    VIRTUAL_ADDRESS_SPACE -
      log_two(get_power_of_two_size_in_bytes(eval_bitvec_size(SID_MEMORY_WORD)));

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

void init_memories(uint64_t number_of_cores) {
  state_code_segment_nids = zmalloc(number_of_cores * sizeof(uint64_t*));
  next_code_segment_nids  = zmalloc(number_of_cores * sizeof(uint64_t*));

  state_main_memory_nids = zmalloc(number_of_cores * sizeof(uint64_t*));
  next_main_memory_nids  = zmalloc(number_of_cores * sizeof(uint64_t*));
  sync_main_memory_nids  = zmalloc(number_of_cores * sizeof(uint64_t*));
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

char* get_instruction_mnemonic(uint64_t instruction_ID);

uint64_t is_R_type(uint64_t instruction_ID);
uint64_t is_I_type(uint64_t instruction_ID);
uint64_t is_register_relative_I_type(uint64_t instruction_ID);
uint64_t is_shift_I_type(uint64_t instruction_ID);
uint64_t is_32_bit_shift_I_type(uint64_t instruction_ID);
uint64_t is_S_type(uint64_t instruction_ID);
uint64_t is_SB_type(uint64_t instruction_ID);
uint64_t is_U_type(uint64_t instruction_ID);

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

uint64_t* is_enabled(uint64_t* instruction_nid);
uint64_t* is_illegal_shamt(uint64_t* ir_nid);

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

uint64_t* is_division_remainder_by_zero(uint64_t* ir_nid, uint64_t* register_file_nid);
uint64_t* is_signed_division_remainder_overflow(uint64_t* ir_nid, uint64_t* register_file_nid);

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
  uint64_t* bltu_nid, uint64_t* bgeu_nid, char* comment,
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
uint64_t* execute_branch(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* condition_nid);
uint64_t* branch_control_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* other_control_flow_nid);

uint64_t* get_pc_value_plus_UJ_immediate(uint64_t* pc_nid, uint64_t* ir_nid);
uint64_t* jal_control_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* other_control_flow_nid);

uint64_t* jalr_control_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* other_control_flow_nid);

uint64_t* core_control_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* register_file_nid);

// compressed instructions

uint64_t is_compressed_instruction_ID(uint64_t instruction_ID);
uint64_t is_CR_type(uint64_t instruction_ID);
uint64_t is_jump_CR_type(uint64_t instruction_ID);
uint64_t is_CI_type(uint64_t instruction_ID);
uint64_t is_CL_type(uint64_t instruction_ID);
uint64_t is_CS_type(uint64_t instruction_ID);
uint64_t is_register_CS_type(uint64_t instruction_ID);
uint64_t is_CB_type(uint64_t instruction_ID);
uint64_t is_CJ_type(uint64_t instruction_ID);

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
uint64_t* is_illegal_compressed_instruction_imm_shamt(uint64_t* c_ir_nid);

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
  uint64_t* c_beqz_nid, uint64_t* c_bnez_nid, char* comment,
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
  uint64_t* register_file_nid, uint64_t* memory_nid, uint64_t* other_register_data_flow_nid);

uint64_t* decode_compressed_memory_data_flow(uint64_t* sid, uint64_t* c_ir_nid,
  uint64_t* c_sdsp_nid, uint64_t* c_swsp_nid,
  uint64_t* c_sd_nid, uint64_t* c_sw_nid, char* comment,
  uint64_t* other_memory_data_flow_nid);

uint64_t* get_sp_value_plus_CSS32_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid);
uint64_t* get_sp_value_plus_CSS64_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid);
uint64_t* get_rs1_shift_value_plus_CS32_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid);
uint64_t* get_rs1_shift_value_plus_CS64_offset(uint64_t* c_ir_nid, uint64_t* register_file_nid);
uint64_t* compressed_store_no_seg_faults(uint64_t* c_ir_nid, uint64_t* register_file_nid);
uint64_t* core_compressed_memory_data_flow(uint64_t* c_ir_nid,
  uint64_t* register_file_nid, uint64_t* memory_nid, uint64_t* other_memory_data_flow_nid);

uint64_t* get_pc_value_plus_CB_offset(uint64_t* pc_nid, uint64_t* c_ir_nid);
uint64_t* execute_compressed_branch(uint64_t* pc_nid, uint64_t* c_ir_nid, uint64_t* condition_nid);
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

uint64_t* SID_INSTRUCTION_ID = (uint64_t*) 0;

uint64_t* NID_DISABLED = (uint64_t*) 0;

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

uint64_t* NID_BEQ  = (uint64_t*) 0;
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

// instruction IDs

uint64_t ID_UNKOWN = 0;

uint64_t ID_ECALL = 1;

// R-type

uint64_t ID_ADD  = 2;
uint64_t ID_SUB  = 3;
uint64_t ID_SLL  = 4;
uint64_t ID_SLT  = 5;
uint64_t ID_SLTU = 6;
uint64_t ID_XOR  = 7;
uint64_t ID_SRL  = 8;
uint64_t ID_SRA  = 9;
uint64_t ID_OR   = 10;
uint64_t ID_AND  = 11;

uint64_t ID_ADDW = 12;
uint64_t ID_SUBW = 13;
uint64_t ID_SLLW = 14;
uint64_t ID_SRLW = 15;
uint64_t ID_SRAW = 16;

uint64_t ID_MUL    = 17;
uint64_t ID_MULH   = 18;
uint64_t ID_MULHSU = 19;
uint64_t ID_MULHU  = 20;
uint64_t ID_DIV    = 21;
uint64_t ID_DIVU   = 22;
uint64_t ID_REM    = 23;
uint64_t ID_REMU   = 24;

uint64_t ID_MULW  = 25;
uint64_t ID_DIVW  = 26;
uint64_t ID_DIVUW = 27;
uint64_t ID_REMW  = 28;
uint64_t ID_REMUW = 29;

// I-type

uint64_t ID_JALR = 30;

uint64_t ID_LB  = 31;
uint64_t ID_LH  = 32;
uint64_t ID_LW  = 33;
uint64_t ID_LBU = 34;
uint64_t ID_LHU = 35;
uint64_t ID_LWU = 36;
uint64_t ID_LD  = 37;

uint64_t ID_ADDI  = 38;
uint64_t ID_SLTI  = 39;
uint64_t ID_SLTIU = 40;
uint64_t ID_XORI  = 41;
uint64_t ID_ORI   = 42;
uint64_t ID_ANDI  = 43;

uint64_t ID_ADDIW = 44;

uint64_t ID_SLLI = 45;
uint64_t ID_SRLI = 46;
uint64_t ID_SRAI = 47;

uint64_t ID_SLLIW = 48;
uint64_t ID_SRLIW = 49;
uint64_t ID_SRAIW = 50;

// S-type

uint64_t ID_SB = 51;
uint64_t ID_SH = 52;
uint64_t ID_SW = 53;
uint64_t ID_SD = 54;

// SB-type

uint64_t ID_BEQ  = 55;
uint64_t ID_BNE  = 56;
uint64_t ID_BLT  = 57;
uint64_t ID_BGE  = 58;
uint64_t ID_BLTU = 59;
uint64_t ID_BGEU = 60;

// U-type

uint64_t ID_LUI   = 61;
uint64_t ID_AUIPC = 62;

// UJ-type

uint64_t ID_JAL = 63;

// compressed instruction IDs

// CR-type

uint64_t ID_C_MV  = 64; // "c.mv";
uint64_t ID_C_ADD = 65; // "c.add";

uint64_t ID_C_JR   = 66; // "c.jr";
uint64_t ID_C_JALR = 67; // "c.jalr";

// CI-type

uint64_t ID_C_LI  = 68; // "c.li";
uint64_t ID_C_LUI = 69; // "c.lui";

uint64_t ID_C_ADDI     = 70; // "c.addi";
uint64_t ID_C_ADDIW    = 71; // "c.addiw";
uint64_t ID_C_ADDI16SP = 72; // "c.addi16sp";

// CIW-type

uint64_t ID_C_ADDI4SPN = 73; // "c.addi4spn";

// CI-type

uint64_t ID_C_SLLI = 74; // "c.slli";

uint64_t ID_C_LWSP = 75; // "c.lwsp";
uint64_t ID_C_LDSP = 76; // "c.ldsp";

// CL-type

uint64_t ID_C_LW = 77; // "c.lw";
uint64_t ID_C_LD = 78; // "c.ld";

// CS-type

uint64_t ID_C_SW = 79; // "c.sw";
uint64_t ID_C_SD = 80; // "c.sd";

uint64_t ID_C_SUB = 81; // "c.sub";
uint64_t ID_C_XOR = 82; // "c.xor";
uint64_t ID_C_OR  = 83; // "c.or";
uint64_t ID_C_AND = 84; // "c.and";

uint64_t ID_C_ADDW = 85; // "c.addw";
uint64_t ID_C_SUBW = 86; // "c.subw";

// CSS-type

uint64_t ID_C_SWSP = 87; // "c.swsp";
uint64_t ID_C_SDSP = 88; // "c.sdsp";

// CB-type

uint64_t ID_C_BEQZ = 89; // "c.beqz";
uint64_t ID_C_BNEZ = 90; // "c.bnez";

uint64_t ID_C_ANDI = 91; // "c.andi";

uint64_t ID_C_SRLI = 92; // "c.srli";
uint64_t ID_C_SRAI = 93; // "c.srai";

// CJ-type

uint64_t ID_C_J   = 94; // "c.j";
uint64_t ID_C_JAL = 95; // "c.jal";

uint64_t* RISC_V_MNEMONICS = (uint64_t*) 0;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* eval_instruction_ID_nid            = (uint64_t*) 0;
uint64_t* eval_compressed_instruction_ID_nid = (uint64_t*) 0;

uint64_t* eval_instruction_ID_nids = (uint64_t*) 0;

uint64_t* eval_register_data_flow_nid = (uint64_t*) 0;
uint64_t* eval_memory_data_flow_nid   = (uint64_t*) 0;

uint64_t* eval_instruction_register_data_flow_nid            = (uint64_t*) 0;
uint64_t* eval_compressed_instruction_register_data_flow_nid = (uint64_t*) 0;

uint64_t* eval_instruction_memory_data_flow_nid            = (uint64_t*) 0;
uint64_t* eval_compressed_instruction_memory_data_flow_nid = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_instruction_mnemonics() {
  RISC_V_MNEMONICS = smalloc((ID_C_JAL + 1) * sizeof(char*));

  *(RISC_V_MNEMONICS + ID_UNKOWN) = (uint64_t) "unkown";

  *(RISC_V_MNEMONICS + ID_ECALL) = (uint64_t) "ecall";

  // R-type

  *(RISC_V_MNEMONICS + ID_ADD)  = (uint64_t) "add";
  *(RISC_V_MNEMONICS + ID_SUB)  = (uint64_t) "sub";
  *(RISC_V_MNEMONICS + ID_SLL)  = (uint64_t) "sll";
  *(RISC_V_MNEMONICS + ID_SLT)  = (uint64_t) "slt";
  *(RISC_V_MNEMONICS + ID_SLTU) = (uint64_t) "sltu";
  *(RISC_V_MNEMONICS + ID_XOR)  = (uint64_t) "xor";
  *(RISC_V_MNEMONICS + ID_SRL)  = (uint64_t) "srl";
  *(RISC_V_MNEMONICS + ID_SRA)  = (uint64_t) "sra";
  *(RISC_V_MNEMONICS + ID_OR)   = (uint64_t) "or";
  *(RISC_V_MNEMONICS + ID_AND)  = (uint64_t) "and";

  *(RISC_V_MNEMONICS + ID_ADDW) = (uint64_t) "addw";
  *(RISC_V_MNEMONICS + ID_SUBW) = (uint64_t) "subw";
  *(RISC_V_MNEMONICS + ID_SLLW) = (uint64_t) "sllw";
  *(RISC_V_MNEMONICS + ID_SRLW) = (uint64_t) "srlw";
  *(RISC_V_MNEMONICS + ID_SRAW) = (uint64_t) "sraw";

  *(RISC_V_MNEMONICS + ID_MUL)    = (uint64_t) "mul";
  *(RISC_V_MNEMONICS + ID_MULH)   = (uint64_t) "mulh";
  *(RISC_V_MNEMONICS + ID_MULHSU) = (uint64_t) "mulhsu";
  *(RISC_V_MNEMONICS + ID_MULHU)  = (uint64_t) "mulhu";
  *(RISC_V_MNEMONICS + ID_DIV)    = (uint64_t) "div";
  *(RISC_V_MNEMONICS + ID_DIVU)   = (uint64_t) "divu";
  *(RISC_V_MNEMONICS + ID_REM)    = (uint64_t) "rem";
  *(RISC_V_MNEMONICS + ID_REMU)   = (uint64_t) "remu";

  *(RISC_V_MNEMONICS + ID_MULW)  = (uint64_t) "mulw";
  *(RISC_V_MNEMONICS + ID_DIVW)  = (uint64_t) "divw";
  *(RISC_V_MNEMONICS + ID_DIVUW) = (uint64_t) "divuw";
  *(RISC_V_MNEMONICS + ID_REMW)  = (uint64_t) "remw";
  *(RISC_V_MNEMONICS + ID_REMUW) = (uint64_t) "remuw";

  // I-type

  *(RISC_V_MNEMONICS + ID_JALR) = (uint64_t) "jalr";

  *(RISC_V_MNEMONICS + ID_LB)  = (uint64_t) "lb";
  *(RISC_V_MNEMONICS + ID_LH)  = (uint64_t) "lh";
  *(RISC_V_MNEMONICS + ID_LW)  = (uint64_t) "lw";
  *(RISC_V_MNEMONICS + ID_LBU) = (uint64_t) "lbu";
  *(RISC_V_MNEMONICS + ID_LHU) = (uint64_t) "lhu";
  *(RISC_V_MNEMONICS + ID_LWU) = (uint64_t) "lwu";
  *(RISC_V_MNEMONICS + ID_LD)  = (uint64_t) "ld";

  *(RISC_V_MNEMONICS + ID_ADDI)  = (uint64_t) "addi";
  *(RISC_V_MNEMONICS + ID_SLTI)  = (uint64_t) "slti";
  *(RISC_V_MNEMONICS + ID_SLTIU) = (uint64_t) "sltiu";
  *(RISC_V_MNEMONICS + ID_XORI)  = (uint64_t) "xori";
  *(RISC_V_MNEMONICS + ID_ORI)   = (uint64_t) "ori";
  *(RISC_V_MNEMONICS + ID_ANDI)  = (uint64_t) "andi";

  *(RISC_V_MNEMONICS + ID_ADDIW) = (uint64_t) "addiw";

  *(RISC_V_MNEMONICS + ID_SLLI) = (uint64_t) "slli";
  *(RISC_V_MNEMONICS + ID_SRLI) = (uint64_t) "srli";
  *(RISC_V_MNEMONICS + ID_SRAI) = (uint64_t) "srai";

  *(RISC_V_MNEMONICS + ID_SLLIW) = (uint64_t) "slliw";
  *(RISC_V_MNEMONICS + ID_SRLIW) = (uint64_t) "srliw";
  *(RISC_V_MNEMONICS + ID_SRAIW) = (uint64_t) "sraiw";

  // S-type

  *(RISC_V_MNEMONICS + ID_SB) = (uint64_t) "sb";
  *(RISC_V_MNEMONICS + ID_SH) = (uint64_t) "sh";
  *(RISC_V_MNEMONICS + ID_SW) = (uint64_t) "sw";
  *(RISC_V_MNEMONICS + ID_SD) = (uint64_t) "sd";

  // SB-type

  *(RISC_V_MNEMONICS + ID_BEQ)  = (uint64_t) "beq";
  *(RISC_V_MNEMONICS + ID_BNE)  = (uint64_t) "bne";
  *(RISC_V_MNEMONICS + ID_BLT)  = (uint64_t) "blt";
  *(RISC_V_MNEMONICS + ID_BGE)  = (uint64_t) "bge";
  *(RISC_V_MNEMONICS + ID_BLTU) = (uint64_t) "bltu";
  *(RISC_V_MNEMONICS + ID_BGEU) = (uint64_t) "bgeu";

  // U-type

  *(RISC_V_MNEMONICS + ID_LUI)   = (uint64_t) "lui";
  *(RISC_V_MNEMONICS + ID_AUIPC) = (uint64_t) "auipc";

  // UJ-type

  *(RISC_V_MNEMONICS + ID_JAL) = (uint64_t) "jal";

  // compressed instruction IDs

  // CR-type

  *(RISC_V_MNEMONICS + ID_C_MV)  = (uint64_t) "c.mv";
  *(RISC_V_MNEMONICS + ID_C_ADD) = (uint64_t) "c.add";

  *(RISC_V_MNEMONICS + ID_C_JR)   = (uint64_t) "c.jr";
  *(RISC_V_MNEMONICS + ID_C_JALR) = (uint64_t) "c.jalr";

  // CI-type

  *(RISC_V_MNEMONICS + ID_C_LI)  = (uint64_t) "c.li";
  *(RISC_V_MNEMONICS + ID_C_LUI) = (uint64_t) "c.lui";

  *(RISC_V_MNEMONICS + ID_C_ADDI)     = (uint64_t) "c.addi";
  *(RISC_V_MNEMONICS + ID_C_ADDIW)    = (uint64_t) "c.addiw";
  *(RISC_V_MNEMONICS + ID_C_ADDI16SP) = (uint64_t) "c.addi16sp";

  // CIW-type

  *(RISC_V_MNEMONICS + ID_C_ADDI4SPN) = (uint64_t) "c.addi4spn";

  // CI-type

  *(RISC_V_MNEMONICS + ID_C_SLLI) = (uint64_t) "c.slli";

  *(RISC_V_MNEMONICS + ID_C_LWSP) = (uint64_t) "c.lwsp";
  *(RISC_V_MNEMONICS + ID_C_LDSP) = (uint64_t) "c.ldsp";

  // CL-type

  *(RISC_V_MNEMONICS + ID_C_LW) = (uint64_t) "c.lw";
  *(RISC_V_MNEMONICS + ID_C_LD) = (uint64_t) "c.ld";

  // CS-type

  *(RISC_V_MNEMONICS + ID_C_SW) = (uint64_t) "c.sw";
  *(RISC_V_MNEMONICS + ID_C_SD) = (uint64_t) "c.sd";

  *(RISC_V_MNEMONICS + ID_C_SUB) = (uint64_t) "c.sub";
  *(RISC_V_MNEMONICS + ID_C_XOR) = (uint64_t) "c.xor";
  *(RISC_V_MNEMONICS + ID_C_OR)  = (uint64_t) "c.or";
  *(RISC_V_MNEMONICS + ID_C_AND) = (uint64_t) "c.and";

  *(RISC_V_MNEMONICS + ID_C_ADDW) = (uint64_t) "c.addw";
  *(RISC_V_MNEMONICS + ID_C_SUBW) = (uint64_t) "c.subw";

  // CSS-type

  *(RISC_V_MNEMONICS + ID_C_SWSP) = (uint64_t) "c.swsp";
  *(RISC_V_MNEMONICS + ID_C_SDSP) = (uint64_t) "c.sdsp";

  // CB-type

  *(RISC_V_MNEMONICS + ID_C_BEQZ) = (uint64_t) "c.beqz";
  *(RISC_V_MNEMONICS + ID_C_BNEZ) = (uint64_t) "c.bnez";

  *(RISC_V_MNEMONICS + ID_C_ANDI) = (uint64_t) "c.andi";

  *(RISC_V_MNEMONICS + ID_C_SRLI) = (uint64_t) "c.srli";
  *(RISC_V_MNEMONICS + ID_C_SRAI) = (uint64_t) "c.srai";

  // CJ-type

  *(RISC_V_MNEMONICS + ID_C_J)   = (uint64_t) "c.j";
  *(RISC_V_MNEMONICS + ID_C_JAL) = (uint64_t) "c.jal";
}

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

  SID_INSTRUCTION_ID = new_bitvec(7, "7-bit instruction ID");

  NID_DISABLED = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_UNKOWN, 0, get_instruction_mnemonic(ID_UNKOWN));

  NID_LUI  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_LUI, 0, get_instruction_mnemonic(ID_LUI));
  NID_ADDI = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_ADDI, 0, get_instruction_mnemonic(ID_ADDI));

  NID_ADD  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_ADD, 0, get_instruction_mnemonic(ID_ADD));
  NID_SUB  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SUB, 0, get_instruction_mnemonic(ID_SUB));
  NID_MUL  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_MUL, 0, get_instruction_mnemonic(ID_MUL));
  NID_DIVU = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_DIVU, 0, get_instruction_mnemonic(ID_DIVU));
  NID_REMU = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_REMU, 0, get_instruction_mnemonic(ID_REMU));
  NID_SLTU = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SLTU, 0, get_instruction_mnemonic(ID_SLTU));

  NID_LW = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_LW, 0, get_instruction_mnemonic(ID_LW));
  NID_SW = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SW, 0, get_instruction_mnemonic(ID_SW));

  NID_LD = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_LD, 0, get_instruction_mnemonic(ID_LD));
  NID_SD = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SD, 0, get_instruction_mnemonic(ID_SD));

  NID_BEQ  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_BEQ, 0, get_instruction_mnemonic(ID_BEQ));
  NID_JAL  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_JAL, 0, get_instruction_mnemonic(ID_JAL));
  NID_JALR = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_JALR, 0, get_instruction_mnemonic(ID_JALR));

  NID_ECALL = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_ECALL, 0, get_instruction_mnemonic(ID_ECALL));

  if (IS64BITTARGET) {
    if (RISCU) {
      NID_LW = NID_DISABLED;
      NID_SW = NID_DISABLED;
    }
  } else {
    NID_LD = NID_DISABLED;
    NID_SD = NID_DISABLED;
  }

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
    NID_AUIPC = NID_DISABLED;

    NID_BNE  = NID_DISABLED;
    NID_BLT  = NID_DISABLED;
    NID_BGE  = NID_DISABLED;
    NID_BLTU = NID_DISABLED;
    NID_BGEU = NID_DISABLED;

    NID_LB  = NID_DISABLED;
    NID_LH  = NID_DISABLED;
    NID_LBU = NID_DISABLED;
    NID_LHU = NID_DISABLED;

    NID_SB = NID_DISABLED;
    NID_SH = NID_DISABLED;

    NID_SLTI  = NID_DISABLED;
    NID_SLTIU = NID_DISABLED;
    NID_XORI  = NID_DISABLED;
    NID_ORI   = NID_DISABLED;
    NID_ANDI  = NID_DISABLED;

    NID_SLLI = NID_DISABLED;
    NID_SRLI = NID_DISABLED;
    NID_SRAI = NID_DISABLED;

    NID_SLL = NID_DISABLED;
    NID_SLT = NID_DISABLED;
    NID_XOR = NID_DISABLED;
    NID_SRL = NID_DISABLED;
    NID_SRA = NID_DISABLED;

    NID_OR  = NID_DISABLED;
    NID_AND = NID_DISABLED;
  } else {
    NID_AUIPC = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_AUIPC, 0, get_instruction_mnemonic(ID_AUIPC));

    NID_BNE  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_BNE, 0, get_instruction_mnemonic(ID_BNE));
    NID_BLT  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_BLT, 0, get_instruction_mnemonic(ID_BLT));
    NID_BGE  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_BGE, 0, get_instruction_mnemonic(ID_BGE));
    NID_BLTU = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_BLTU, 0, get_instruction_mnemonic(ID_BLTU));
    NID_BGEU = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_BGEU, 0, get_instruction_mnemonic(ID_BGEU));

    NID_LB  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_LB, 0, get_instruction_mnemonic(ID_LB));
    NID_LH  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_LH, 0, get_instruction_mnemonic(ID_LH));
    NID_LBU = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_LBU, 0, get_instruction_mnemonic(ID_LBU));
    NID_LHU = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_LHU, 0, get_instruction_mnemonic(ID_LHU));

    NID_SB = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SB, 0, get_instruction_mnemonic(ID_SB));
    NID_SH = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SH, 0, get_instruction_mnemonic(ID_SH));

    NID_SLTI  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SLTI, 0, get_instruction_mnemonic(ID_SLTI));
    NID_SLTIU = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SLTIU, 0, get_instruction_mnemonic(ID_SLTIU));
    NID_XORI  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_XORI, 0, get_instruction_mnemonic(ID_XORI));
    NID_ORI   = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_ORI, 0, get_instruction_mnemonic(ID_ORI));
    NID_ANDI  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_ANDI, 0, get_instruction_mnemonic(ID_ANDI));

    NID_SLLI = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SLLI, 0, get_instruction_mnemonic(ID_SLLI));
    NID_SRLI = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SRLI, 0, get_instruction_mnemonic(ID_SRLI));
    NID_SRAI = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SRAI, 0, get_instruction_mnemonic(ID_SRAI));

    NID_SLL = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SLL, 0, get_instruction_mnemonic(ID_SLL));
    NID_SLT = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SLT, 0, get_instruction_mnemonic(ID_SLT));
    NID_XOR = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_XOR, 0, get_instruction_mnemonic(ID_XOR));
    NID_SRL = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SRL, 0, get_instruction_mnemonic(ID_SRL));
    NID_SRA = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SRA, 0, get_instruction_mnemonic(ID_SRA));

    NID_OR  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_OR, 0, get_instruction_mnemonic(ID_OR));
    NID_AND = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_AND, 0, get_instruction_mnemonic(ID_AND));
  }

  // RV64I codes missing in RISC-U

  SID_FUNCT6 = new_bitvec(6, "funct6 sort");

  NID_F6_SLL_SRL = new_constant(OP_CONST, SID_FUNCT6, F6_SLL_SRL, 6, "F6_SLL_SRL");
  NID_F6_SRA     = new_constant(OP_CONST, SID_FUNCT6, F6_SRA, 6, "F6_SRA");

  NID_OP_IMM_32 = new_constant(OP_CONST, SID_OPCODE, OP_IMM_32, 7, "OP_IMM_32");
  NID_OP_OP_32  = new_constant(OP_CONST, SID_OPCODE, OP_OP_32, 7, "OP_OP_32");

  NID_F3_LWU = new_constant(OP_CONST, SID_FUNCT3, F3_LWU, 3, "F3_LWU");

  // RV64I instruction switches

  NID_LWU = NID_DISABLED;

  NID_ADDIW = NID_DISABLED;
  NID_SLLIW = NID_DISABLED;
  NID_SRLIW = NID_DISABLED;
  NID_SRAIW = NID_DISABLED;

  NID_ADDW = NID_DISABLED;
  NID_SUBW = NID_DISABLED;
  NID_SLLW = NID_DISABLED;
  NID_SRLW = NID_DISABLED;
  NID_SRAW = NID_DISABLED;

  if (RISCU == 0)
    if (IS64BITTARGET) {
      NID_LWU = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_LWU, 0, get_instruction_mnemonic(ID_LWU));

      NID_ADDIW = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_ADDIW, 0, get_instruction_mnemonic(ID_ADDIW));
      NID_SLLIW = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SLLIW, 0, get_instruction_mnemonic(ID_SLLIW));
      NID_SRLIW = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SRLIW, 0, get_instruction_mnemonic(ID_SRLIW));
      NID_SRAIW = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SRAIW, 0, get_instruction_mnemonic(ID_SRAIW));

      NID_ADDW = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_ADDW, 0, get_instruction_mnemonic(ID_ADDW));
      NID_SUBW = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SUBW, 0, get_instruction_mnemonic(ID_SUBW));
      NID_SLLW = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SLLW, 0, get_instruction_mnemonic(ID_SLLW));
      NID_SRLW = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SRLW, 0, get_instruction_mnemonic(ID_SRLW));
      NID_SRAW = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_SRAW, 0, get_instruction_mnemonic(ID_SRAW));
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

  NID_MULH   = NID_DISABLED;
  NID_MULHSU = NID_DISABLED;
  NID_MULHU  = NID_DISABLED;
  NID_DIV    = NID_DISABLED;
  NID_REM    = NID_DISABLED;

  if (RISCU == 0) {
    if (RV32M) {
      // MUL, DIVU, REMU already defined
      NID_MULH   = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_MULH, 0, get_instruction_mnemonic(ID_MULH));
      NID_MULHSU = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_MULHSU, 0, get_instruction_mnemonic(ID_MULHSU));
      NID_MULHU  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_MULHU, 0, get_instruction_mnemonic(ID_MULHU));
      NID_DIV    = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_DIV, 0, get_instruction_mnemonic(ID_DIV));
      NID_REM    = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_REM, 0, get_instruction_mnemonic(ID_REM));
    } else {
      NID_MUL  = NID_DISABLED;
      NID_DIVU = NID_DISABLED;
      NID_REMU = NID_DISABLED;
    }
  }

  // RV64M instruction switches

  if (RISCU)
    RV64M = 0;

  if (IS64BITTARGET == 0)
    RV64M = 0;

  if (RV64M) {
    NID_MULW  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_MULW, 0, get_instruction_mnemonic(ID_MULW));
    NID_DIVW  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_DIVW, 0, get_instruction_mnemonic(ID_DIVW));
    NID_DIVUW = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_DIVUW, 0, get_instruction_mnemonic(ID_DIVUW));
    NID_REMW  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_REMW, 0, get_instruction_mnemonic(ID_REMW));
    NID_REMUW = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_REMUW, 0, get_instruction_mnemonic(ID_REMUW));
  } else {
    NID_MULW  = NID_DISABLED;
    NID_DIVW  = NID_DISABLED;
    NID_DIVUW = NID_DISABLED;
    NID_REMW  = NID_DISABLED;
    NID_REMUW = NID_DISABLED;
  }
}

void init_compressed_instruction_sorts() {
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

  NID_C_LI  = NID_DISABLED;
  NID_C_LUI = NID_DISABLED;

  NID_C_ADDI     = NID_DISABLED;
  NID_C_ADDIW    = NID_DISABLED;
  NID_C_ADDI16SP = NID_DISABLED;

  NID_C_ADDI4SPN = NID_DISABLED;

  NID_C_ANDI = NID_DISABLED;

  NID_C_SLLI = NID_DISABLED;
  NID_C_SRLI = NID_DISABLED;
  NID_C_SRAI = NID_DISABLED;

  NID_C_MV  = NID_DISABLED;
  NID_C_ADD = NID_DISABLED;

  NID_C_SUB = NID_DISABLED;
  NID_C_XOR = NID_DISABLED;
  NID_C_OR  = NID_DISABLED;
  NID_C_AND = NID_DISABLED;

  NID_C_ADDW = NID_DISABLED;
  NID_C_SUBW = NID_DISABLED;

  NID_C_LWSP = NID_DISABLED;
  NID_C_LW   = NID_DISABLED;

  NID_C_LDSP = NID_DISABLED;
  NID_C_LD   = NID_DISABLED;

  NID_C_SWSP = NID_DISABLED;
  NID_C_SW   = NID_DISABLED;

  NID_C_SDSP = NID_DISABLED;
  NID_C_SD   = NID_DISABLED;

  NID_C_BEQZ = NID_DISABLED;
  NID_C_BNEZ = NID_DISABLED;

  NID_C_J   = NID_DISABLED;
  NID_C_JAL = NID_DISABLED;

  NID_C_JR   = NID_DISABLED;
  NID_C_JALR = NID_DISABLED;

  if (RVC == 0)
    // avoiding oversized then case
    return;

  NID_C_LI  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_LI, 0, get_instruction_mnemonic(ID_C_LI));
  NID_C_LUI = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_LUI, 0, get_instruction_mnemonic(ID_C_LUI));

  NID_C_ADDI = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_ADDI, 0, get_instruction_mnemonic(ID_C_ADDI));
  if (IS64BITTARGET)
    NID_C_ADDIW = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_ADDIW, 0, get_instruction_mnemonic(ID_C_ADDIW));
  else
    NID_C_ADDIW = NID_DISABLED;
  NID_C_ADDI16SP = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_ADDI16SP, 0, get_instruction_mnemonic(ID_C_ADDI16SP));

  NID_C_ADDI4SPN = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_ADDI4SPN, 0, get_instruction_mnemonic(ID_C_ADDI4SPN));

  NID_C_ANDI = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_ANDI, 0, get_instruction_mnemonic(ID_C_ANDI));

  NID_C_SLLI = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_SLLI, 0, get_instruction_mnemonic(ID_C_SLLI));
  NID_C_SRLI = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_SRLI, 0, get_instruction_mnemonic(ID_C_SRLI));
  NID_C_SRAI = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_SRAI, 0, get_instruction_mnemonic(ID_C_SRAI));

  NID_C_MV  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_MV, 0, get_instruction_mnemonic(ID_C_MV));
  NID_C_ADD = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_ADD, 0, get_instruction_mnemonic(ID_C_ADD));

  NID_C_SUB = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_SUB, 0, get_instruction_mnemonic(ID_C_SUB));
  NID_C_XOR = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_XOR, 0, get_instruction_mnemonic(ID_C_XOR));
  NID_C_OR  = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_OR, 0, get_instruction_mnemonic(ID_C_OR));
  NID_C_AND = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_AND, 0, get_instruction_mnemonic(ID_C_AND));

  if (IS64BITTARGET) {
    NID_C_ADDW = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_ADDW, 0, get_instruction_mnemonic(ID_C_ADDW));
    NID_C_SUBW = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_SUBW, 0, get_instruction_mnemonic(ID_C_SUBW));
  } else {
    NID_C_ADDW = NID_DISABLED;
    NID_C_SUBW = NID_DISABLED;
  }

  NID_C_LWSP = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_LWSP, 0, get_instruction_mnemonic(ID_C_LWSP));
  NID_C_LW   = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_LW, 0, get_instruction_mnemonic(ID_C_LW));

  NID_C_SWSP = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_SWSP, 0, get_instruction_mnemonic(ID_C_SWSP));
  NID_C_SW   = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_SW, 0, get_instruction_mnemonic(ID_C_SW));

  if (IS64BITTARGET) {
    NID_C_LDSP = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_LDSP, 0, get_instruction_mnemonic(ID_C_LDSP));
    NID_C_LD   = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_LD, 0, get_instruction_mnemonic(ID_C_LD));

    NID_C_SDSP = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_SDSP, 0, get_instruction_mnemonic(ID_C_SDSP));
    NID_C_SD   = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_SD, 0, get_instruction_mnemonic(ID_C_SD));
  } else {
    NID_C_LDSP = NID_DISABLED;
    NID_C_LD   = NID_DISABLED;

    NID_C_SDSP = NID_DISABLED;
    NID_C_SD   = NID_DISABLED;
  }

  NID_C_BEQZ = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_BEQZ, 0, get_instruction_mnemonic(ID_C_BEQZ));
  NID_C_BNEZ = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_BNEZ, 0, get_instruction_mnemonic(ID_C_BNEZ));

  NID_C_J = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_J, 0, get_instruction_mnemonic(ID_C_J));
  if (IS64BITTARGET)
    NID_C_JAL = NID_DISABLED;
  else
    NID_C_JAL = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_JAL, 0, get_instruction_mnemonic(ID_C_JAL));

  NID_C_JR   = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_JR, 0, get_instruction_mnemonic(ID_C_JR));
  NID_C_JALR = new_constant(OP_CONSTD, SID_INSTRUCTION_ID, ID_C_JALR, 0, get_instruction_mnemonic(ID_C_JALR));
}

void init_decoders(uint64_t number_of_cores) {
  eval_instruction_ID_nids = zmalloc(number_of_cores * sizeof(uint64_t*));
}

// -----------------------------------------------------------------
// ----------------------------- CORE ------------------------------
// -----------------------------------------------------------------

uint64_t* get_for(uint64_t core, uint64_t* lines)            { return (uint64_t*) *(lines + core); }
void set_for(uint64_t core, uint64_t* lines, uint64_t* line) { *(lines + core) = (uint64_t) line; }

void new_core_state(uint64_t core);
void print_core_state(uint64_t core);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t number_of_cores = 1; // number of cores

uint64_t SYNCHRONIZED_PC = 0; // flag for synchronized program counters across cores

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* eval_ir_nid   = (uint64_t*) 0;
uint64_t* eval_c_ir_nid = (uint64_t*) 0;

uint64_t* eval_ir_nids   = (uint64_t*) 0;
uint64_t* eval_c_ir_nids = (uint64_t*) 0;

uint64_t* initial_pc_nid = (uint64_t*) 0;

uint64_t* state_pc_nid = (uint64_t*) 0;
uint64_t* init_pc_nid  = (uint64_t*) 0;
uint64_t* next_pc_nid  = (uint64_t*) 0;

uint64_t* state_pc_nids = (uint64_t*) 0;
uint64_t* next_pc_nids  = (uint64_t*) 0;
uint64_t* sync_pc_nids  = (uint64_t*) 0;

uint64_t* eval_control_flow_nid = (uint64_t*) 0;

uint64_t* eval_instruction_control_flow_nid            = (uint64_t*) 0;
uint64_t* eval_compressed_instruction_control_flow_nid = (uint64_t*) 0;

uint64_t* eval_core_0_control_flow_nid = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_cores(uint64_t number_of_cores) {
  eval_ir_nids   = zmalloc(number_of_cores * sizeof(uint64_t*));
  eval_c_ir_nids = zmalloc(number_of_cores * sizeof(uint64_t*));

  state_pc_nids = zmalloc(number_of_cores * sizeof(uint64_t*));
  next_pc_nids  = zmalloc(number_of_cores * sizeof(uint64_t*));
  sync_pc_nids  = zmalloc(number_of_cores * sizeof(uint64_t*));
}

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

void rotor_combinational(uint64_t core, uint64_t* pc_nid, uint64_t* code_segment_nid, uint64_t* register_file_nid, uint64_t* memory_nid);
void rotor_sequential(uint64_t core, uint64_t* pc_nid, uint64_t* register_file_nid, uint64_t* memory_nid,
  uint64_t* control_flow_nid, uint64_t* register_data_flow_nid, uint64_t* memory_data_flow_nid);
void rotor_properties(uint64_t core, uint64_t* ir_nid, uint64_t* c_ir_nid,
  uint64_t* instruction_ID_nids, uint64_t* control_flow_nid, uint64_t* register_file_nid);

void load_binary(uint64_t binary);

void model_rotor();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t number_of_binaries = 0; // number of loaded binaries

char* bad_exit_code_check_option = (char*) 0;
char* exit_codes_check_option    = (char*) 0;

char* division_by_zero_check_option  = (char*) 0;
char* division_overflow_check_option = (char*) 0;

char* seg_faults_check_option = (char*) 0;

char* cores_option                 = (char*) 0;
char* virtual_address_space_option = (char*) 0;
char* code_word_size_option        = (char*) 0;
char* memory_word_size_option      = (char*) 0;
char* heap_allowance_option        = (char*) 0;
char* stack_allowance_option       = (char*) 0;

uint64_t evaluate_model    = 1;
uint64_t output_assembly   = 0;
uint64_t disassemble_model = 0;

uint64_t check_bad_exit_code = 1;
uint64_t check_exit_codes    = 1;

uint64_t check_division_by_zero  = 1;
uint64_t check_division_overflow = 1;

uint64_t check_seg_faults = 1;

// ------------------------ GLOBAL VARIABLES -----------------------

char*    model_name = (char*) 0; // name of model file
uint64_t model_fd   = 0;         // file descriptor of open model file

uint64_t w = 0; // number of written characters

uint64_t bad_exit_code = 0; // model for this exit code

uint64_t* prop_is_instruction_known_nids           = (uint64_t*) 0;
uint64_t* prop_illegal_instruction_nids            = (uint64_t*) 0;
uint64_t* prop_illegal_compressed_instruction_nids = (uint64_t*) 0;
uint64_t* prop_next_fetch_unaligned_nids           = (uint64_t*) 0;
uint64_t* prop_next_fetch_seg_faulting_nids        = (uint64_t*) 0;

uint64_t* prop_is_syscall_id_known_nids = (uint64_t*) 0;

uint64_t* prop_bad_exit_code_nid  = (uint64_t*) 0;
uint64_t* prop_bad_exit_code_nids = (uint64_t*) 0;

uint64_t* prop_active_exits_nid           = (uint64_t*) 0;
uint64_t* prop_previous_core_a0_value_nid = (uint64_t*) 0;

uint64_t* prop_exit_codes_nid       = (uint64_t*) 0;
uint64_t* prop_all_cores_exited_nid = (uint64_t*) 0;

uint64_t are_exit_codes_different = 0;

uint64_t* prop_division_by_zero_nids         = (uint64_t*) 0;
uint64_t* prop_signed_division_overflow_nids = (uint64_t*) 0;

uint64_t* prop_load_seg_faulting_nids             = (uint64_t*) 0;
uint64_t* prop_store_seg_faulting_nids            = (uint64_t*) 0;
uint64_t* prop_compressed_load_seg_faulting_nids  = (uint64_t*) 0;
uint64_t* prop_compressed_store_seg_faulting_nids = (uint64_t*) 0;
uint64_t* prop_stack_seg_faulting_nids            = (uint64_t*) 0;

uint64_t* prop_brk_seg_faulting_nids    = (uint64_t*) 0;
uint64_t* prop_openat_seg_faulting_nids = (uint64_t*) 0;
uint64_t* prop_read_seg_faulting_nids   = (uint64_t*) 0;
uint64_t* prop_write_seg_faulting_nids  = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_properties(uint64_t number_of_cores) {
  prop_is_instruction_known_nids           = zmalloc(number_of_cores * sizeof(uint64_t*));
  prop_illegal_instruction_nids            = zmalloc(number_of_cores * sizeof(uint64_t*));
  prop_illegal_compressed_instruction_nids = zmalloc(number_of_cores * sizeof(uint64_t*));
  prop_next_fetch_unaligned_nids           = zmalloc(number_of_cores * sizeof(uint64_t*));
  prop_next_fetch_seg_faulting_nids        = zmalloc(number_of_cores * sizeof(uint64_t*));

  prop_is_syscall_id_known_nids = zmalloc(number_of_cores * sizeof(uint64_t*));

  prop_bad_exit_code_nids = zmalloc(number_of_cores * sizeof(uint64_t*));

  prop_division_by_zero_nids         = zmalloc(number_of_cores * sizeof(uint64_t*));
  prop_signed_division_overflow_nids = zmalloc(number_of_cores * sizeof(uint64_t*));

  prop_load_seg_faulting_nids             = zmalloc(number_of_cores * sizeof(uint64_t*));
  prop_store_seg_faulting_nids            = zmalloc(number_of_cores * sizeof(uint64_t*));
  prop_compressed_load_seg_faulting_nids  = zmalloc(number_of_cores * sizeof(uint64_t*));
  prop_compressed_store_seg_faulting_nids = zmalloc(number_of_cores * sizeof(uint64_t*));
  prop_stack_seg_faulting_nids            = zmalloc(number_of_cores * sizeof(uint64_t*));

  prop_brk_seg_faulting_nids    = zmalloc(number_of_cores * sizeof(uint64_t*));
  prop_openat_seg_faulting_nids = zmalloc(number_of_cores * sizeof(uint64_t*));
  prop_read_seg_faulting_nids   = zmalloc(number_of_cores * sizeof(uint64_t*));
  prop_write_seg_faulting_nids  = zmalloc(number_of_cores * sizeof(uint64_t*));
}

// -----------------------------------------------------------------
// ---------------------------- EMULATOR ---------------------------
// -----------------------------------------------------------------

void save_binary(uint64_t binary);
void restore_binary(uint64_t binary);

void print_assembly(uint64_t core);
void print_multicore_assembly();

uint64_t eval_properties(uint64_t core);
uint64_t eval_multicore_properties();

uint64_t eval_sequential(uint64_t core);
uint64_t eval_multicore_sequential();

void apply_sequential(uint64_t core);
void apply_multicore_sequential();

void save_states(uint64_t core);
void save_multicore_states();

void restore_states(uint64_t core);
void restore_multicore_states();

void eval_multicore_states();

void eval_rotor();

void disassemble_rotor(uint64_t core);

uint64_t rotor_arguments();

uint64_t selfie_model();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t MAX_BINARIES = 3;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* binary_names = (uint64_t*) 0;

uint64_t* e_entries = (uint64_t*) 0;

uint64_t* code_binaries = (uint64_t*) 0;
uint64_t* data_binaries = (uint64_t*) 0;

uint64_t* code_starts = (uint64_t*) 0;
uint64_t* code_sizes  = (uint64_t*) 0;
uint64_t* data_starts = (uint64_t*) 0;
uint64_t* data_sizes  = (uint64_t*) 0;

uint64_t max_code_size = 0;

uint64_t min_steps = -1;
uint64_t max_steps = 0;

uint64_t min_input = 0;
uint64_t max_input = 0;

// ------------------------- INITIALIZATION ------------------------

void init_binaries() {
  binary_names = smalloc(MAX_BINARIES * sizeof(char*));

  e_entries = smalloc(MAX_BINARIES * sizeof(uint64_t*));

  code_binaries = smalloc(MAX_BINARIES * sizeof(uint64_t*));
  data_binaries = smalloc(MAX_BINARIES * sizeof(uint64_t*));

  code_starts = smalloc(MAX_BINARIES * sizeof(uint64_t*));
  code_sizes  = smalloc(MAX_BINARIES * sizeof(uint64_t*));
  data_starts = smalloc(MAX_BINARIES * sizeof(uint64_t*));
  data_sizes  = smalloc(MAX_BINARIES * sizeof(uint64_t*));
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
  set_step(new_line, UNINITIALIZED);
  set_reuse(new_line, 0);
  set_pred(new_line, UNUSED);
  set_succ(new_line, UNUSED);

  if (reuse_lines)
    old_line = find_equal_line(new_line);
  else
    old_line = UNUSED;

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

uint64_t* new_init(uint64_t* sid, uint64_t* state_nid, uint64_t* value_nid, char* comment) {
  return new_binary(OP_INIT, sid, state_nid, value_nid, comment);
}

uint64_t* new_next(uint64_t* sid, uint64_t* state_nid, uint64_t* value_nid, char* comment) {
  return new_binary(OP_NEXT, sid, state_nid, value_nid, comment);
}

uint64_t* new_property(char* op, uint64_t* condition_nid, char* symbol, char* comment) {
  return new_line(op, UNUSED, condition_nid, (uint64_t*) symbol, UNUSED, comment);
}

// -----------------------------------------------------------------
// ---------------------------- SYNTAX -----------------------------
// -----------------------------------------------------------------

uint64_t is_bitvector(uint64_t* line) {
  return (char*) get_arg1(line) == BITVEC;
}

uint64_t is_array(uint64_t* line) {
  return (char*) get_arg1(line) == ARRAY;
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

void print_nid(uint64_t nid, uint64_t* line) {
  set_nid(line, nid);
  w = w + dprintf(output_fd, "%lu", nid);
}

uint64_t print_sort(uint64_t nid, uint64_t* line) {
  if (is_array(line)) {
    nid = print_referenced_line(nid, get_arg2(line));
    nid = print_referenced_line(nid, get_arg3(line));
  }
  print_nid(nid, line);
  w = w + dprintf(output_fd, " %s", OP_SORT);
  if (is_bitvector(line))
    w = w + dprintf(output_fd, " %s %lu", BITVEC, eval_bitvec_size(line));
  else
    // assert: array
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

void print_line_for(uint64_t core, uint64_t* lines) {
  print_line(get_for(core, lines));
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

void print_break_line_for(uint64_t core, uint64_t* lines) {
  print_break_line(get_for(core, lines));
}

void print_break_comment(char* comment) {
  print_break();
  w = w + dprintf(output_fd, "; %s\n\n", comment);
}

void print_break_comment_for(uint64_t core, char* comment) {
  print_break();
  w = w + dprintf(output_fd, "; core-%lu %s\n\n", core, comment);
}

void print_break_comment_line(char* comment, uint64_t* line) {
  if (line != UNUSED) {
    print_break_comment(comment);
    print_line(line);
  }
}

void print_break_comment_line_for(uint64_t core, char* comment, uint64_t* line) {
  if (line != UNUSED) {
    print_break_comment_for(core, comment);
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

  if (is_bitvector(line)) {
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

void fit_bitvec_sort(uint64_t* sid, uint64_t value) {
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

void signed_fit_bitvec_sort(uint64_t* sid, uint64_t value) {
  uint64_t size;

  size = eval_bitvec_size(sid);

  if (size >= SIZEOFUINT64INBITS)
    // TODO: support of bitvectors larger than machine words
    return;
  else if (is_signed_integer(value, size))
    return;

  fit_bitvec_sort(sid, value);
}

uint64_t eval_array_size(uint64_t* line) {
  uint64_t size;

  if (is_array(line)) {
    size = eval_bitvec_size(get_arg2(line));

    if (size <= VIRTUAL_ADDRESS_SPACE)
      return size;

    printf("%s: unsupported %lu-bit array size error\n", selfie_name, size);
  } else
    printf("%s: evaluate array size of non-array error\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_element_size(uint64_t* line) {
  uint64_t size;

  if (is_array(line)) {
    size = eval_bitvec_size(get_arg3(line));

    if (size <= SIZEOFUINT64INBITS)
      return size;

    printf("%s: unsupported %lu-bit array element size error\n", selfie_name, size);
  } else
    printf("%s: evaluate element size of non-array error\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

void fit_array_sorts(uint64_t* array_sid, uint64_t index, uint64_t value) {
  if (is_array(array_sid)) {
    fit_bitvec_sort(get_arg2(array_sid), index);
    fit_bitvec_sort(get_arg3(array_sid), value);

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

void match_array_sorts(uint64_t* array_sid, uint64_t* index_sid, uint64_t* value_sid) {
  match_sorts(get_arg2(array_sid), index_sid, "array size");
  match_sorts(get_arg3(array_sid), value_sid, "array element");
}

uint64_t calculate_address_space(uint64_t number_of_bytes, uint64_t word_size) {
  uint64_t size_in_words;
  uint64_t address_space;

  // assert: word size is a power of 2 >= 8 bits

  size_in_words = number_of_bytes / get_power_of_two_size_in_bytes(word_size);

  if (number_of_bytes % get_power_of_two_size_in_bytes(word_size) > 0)
    size_in_words = size_in_words + 1;

  address_space = log_two(size_in_words);

  if (size_in_words > two_to_the_power_of(address_space))
    address_space = address_space + 1;

  return address_space;
}

uint64_t* allocate_array(uint64_t* sid) {
  uint64_t array_size;
  uint64_t element_size;
  uint64_t* arrays;

  array_size   = eval_array_size(sid);
  element_size = eval_element_size(sid);

  // assert: element size of array <= sizeof(uint64_t)

  if (sid != SID_MEMORY_STATE)
    // assert: register files and code segments
    return zmalloc(two_to_the_power_of(array_size) * sizeof(uint64_t));
  else {
    arrays = smalloc(3 * sizeof(uint64_t*));

    set_data_array(arrays,
      zmalloc(two_to_the_power_of(calculate_address_space(data_size, element_size)) * sizeof(uint64_t)));
    set_heap_array(arrays,
      zmalloc(two_to_the_power_of(calculate_address_space(heap_size, element_size)) * sizeof(uint64_t)));
    set_stack_array(arrays,
      zmalloc(two_to_the_power_of(calculate_address_space(stack_size, element_size)) * sizeof(uint64_t)));

    return arrays;
  }
}

uint64_t is_virtual_address_in_segment(uint64_t vaddr, uint64_t start, uint64_t end) {
  if (vaddr >= start)
    if (vaddr < end)
      return 1;

  return 0;
}

uint64_t is_virtual_address_in_data_segment(uint64_t vaddr) {
  return is_virtual_address_in_segment(vaddr, data_start, data_start + data_size);
}

uint64_t is_virtual_address_in_heap_segment(uint64_t vaddr) {
  return is_virtual_address_in_segment(vaddr, heap_start, heap_start + heap_size);
}

uint64_t is_virtual_address_in_stack_segment(uint64_t vaddr) {
  if (stack_start < stack_start + stack_size)
    return is_virtual_address_in_segment(vaddr, stack_start, stack_start + stack_size);
  else if (vaddr >= stack_start)
    // assert: stack_start + stack_size == 0
    return 1;

  return 0;
}

uint64_t vaddr_to_index(uint64_t vaddr) {
  return right_shift(vaddr,
    log_two(get_power_of_two_size_in_bytes(eval_element_size(SID_MEMORY_STATE))));
}

uint64_t index_to_vaddr(uint64_t index) {
  return left_shift(index,
    log_two(get_power_of_two_size_in_bytes(eval_element_size(SID_MEMORY_STATE))));
}

uint64_t read_or_write(uint64_t* state_nid, uint64_t index, uint64_t value, uint64_t read) {
  uint64_t* array;
  uint64_t vaddr;

  fit_array_sorts(get_sid(state_nid), index, value);

  array = (uint64_t*) get_state(state_nid);

  if (array != (uint64_t*) 0) {
    if (get_sid(state_nid) == SID_MEMORY_STATE) {
      vaddr = index_to_vaddr(index);

      if (is_virtual_address_in_data_segment(vaddr)) {
        index = vaddr_to_index(vaddr - data_start);
        array = get_data_array(array);
      } else if (is_virtual_address_in_heap_segment(vaddr)) {
        index = vaddr_to_index(vaddr - heap_start);
        array = get_heap_array(array);
      } else if (is_virtual_address_in_stack_segment(vaddr)) {
        index = vaddr_to_index(vaddr - stack_start);
        array = get_stack_array(array);
      } else {
        printf("%s: segmentation fault with index %lu @ 0x%lX\n", selfie_name, index, vaddr);

        exit(EXITCODE_SYSTEMERROR);
      }
    }

    if (read)
      value = *(array + index);
    else
      // TODO: log writes and only apply with init and next
      *(array + index) = value;

    return value;
  }

  printf("%s: uninitialized state access error\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t is_comparison_operator(char* op) {
  if (op == OP_EQ)
    return 1;
  else if (op == OP_NEQ)
    return 1;
  else if (op == OP_SGT)
    return 1;
  else if (op == OP_UGT)
    return 1;
  else if (op == OP_SGTE)
    return 1;
  else if (op == OP_UGTE)
    return 1;
  else if (op == OP_SLT)
    return 1;
  else if (op == OP_ULT)
    return 1;
  else if (op == OP_SLTE)
    return 1;
  else if (op == OP_ULTE)
    return 1;
  else
    return 0;
}

uint64_t is_bitwise_operator(char* op) {
  if (op == OP_AND)
    return 1;
  else if (op == OP_OR)
    return 1;
  else if (op == OP_XOR)
    return 1;
  else if (op == OP_SLL)
    return 1;
  else if (op == OP_SRL)
    return 1;
  else if (op == OP_SRA)
    return 1;
  else
    return 0;
}

uint64_t is_arithmetic_operator(char* op) {
  if (op == OP_ADD)
    return 1;
  else if (op == OP_SUB)
    return 1;
  else if (op == OP_MUL)
    return 1;
  else if (op == OP_SDIV)
    return 1;
  else if (op == OP_UDIV)
    return 1;
  else if (op == OP_SREM)
    return 1;
  else if (op == OP_UREM)
    return 1;
  else
    return 0;
}

uint64_t is_binary_operator(char* op) {
  if (op == OP_IMPLIES)
    return 1;
  else if (is_comparison_operator(op))
    return 1;
  else if (is_bitwise_operator(op))
    return 1;
  else if (is_arithmetic_operator(op))
    return 1;
  else
    return 0;
}

uint64_t bitwise(uint64_t a, uint64_t b, uint64_t and_xor, uint64_t or_xor) {
  uint64_t r;
  uint64_t i;

  if (a == b)
    return a;
  else if (a < b)
    r = b;
  else {
    r = a;

    a = b;
    b = r;
  }

  // assert: a < b and r == b

  i = 0;

  while (i < SIZEOFUINT64INBITS) {
    if (a == 0) {
      if (or_xor)
        return r;
      else
        return r % two_to_the_power_of(i);
    }

    if (a % 2 == or_xor) {
      if (b % 2)
        r = r - and_xor * two_to_the_power_of(i);
      else
        r = r + or_xor * two_to_the_power_of(i);
    }

    a = a / 2;
    b = b / 2;

    i = i + 1;
  }

  return r;
}

uint64_t bitwise_and(uint64_t a, uint64_t b) {
  return bitwise(a, b, 1, 0);
}

uint64_t bitwise_or(uint64_t a, uint64_t b) {
  return bitwise(a, b, 0, 1);
}

uint64_t bitwise_xor(uint64_t a, uint64_t b) {
  return bitwise(a, b, 1, 1);
}

uint64_t arithmetic_right_shift(uint64_t n, uint64_t b, uint64_t size) {
  if (b < size)
    return sign_shrink(sign_extend(right_shift(n, b), size - b), size);
  else if (signed_less_than(sign_extend(n, size), 0))
    return sign_shrink(-1, size);
  else
    return 0;
}

uint64_t signed_less_than_or_equal_to(uint64_t a, uint64_t b) {
  if (a == b)
    return 1;
  else
    return signed_less_than(a, b);
}

uint64_t get_cached_state(uint64_t* line) {
  if (get_step(line) != UNINITIALIZED) {
    if (get_op(line) == OP_STATE) {
      if (get_step(line) >= current_step) {
        if (is_bitvector(get_sid(line))) {
          if (get_step(line) == current_step)
            return get_state(line);
        } else {
          // assert: array
          if (get_step(line) <= next_step)
            // TODO: log writes and only apply with init and next
            return (uint64_t) line;
        }
      }

      printf("%s: non-current state access\n", selfie_name);
    } else if (get_step(line) == next_step)
      return get_state(line);
    else
      printf("%s: cache miss\n", selfie_name);
  } else
    printf("%s: uninitialized state or cache access\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_constant_value(uint64_t* line) {
  uint64_t* sid;
  uint64_t value;

  if (get_step(line) == UNINITIALIZED) {
    sid   = get_sid(line);
    value = (uint64_t) get_arg1(line);

    if (get_op(line) == OP_CONSTD) {
      signed_fit_bitvec_sort(sid, value);

      value = sign_shrink(value, eval_bitvec_size(sid));
    } else
      fit_bitvec_sort(sid, value);

    set_state(line, value);
  } else
    value = get_state(line);

  set_step(line, next_step);

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

uint64_t eval_input(uint64_t* line) {
  char* op;

  op = get_op(line);

  if (op == OP_STATE)
    return get_cached_state(line);
  else if (op == OP_INPUT) {
    if (input_steps == 0)
      // TODO: input is consumed more than once
      input_steps = current_step;

    set_state(line, current_input);

    set_step(line, next_step);

    if (any_input == 0)
      first_input = 1;

    any_input = 1;

    return get_state(line);
  }

  printf("%s: unknown operator %s\n", selfie_name, op);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_ext(uint64_t* line) {
  uint64_t* value_nid;
  uint64_t n;
  uint64_t w;

  value_nid = get_arg1(line);

  n = eval_bitvec_size(get_sid(value_nid));

  w = eval_ext_w(line);

  if (n + w <= WORDSIZEINBITS)
    // TODO: support of double machine words
    if (eval_bitvec_size(get_sid(line)) == n + w) {
      if (get_op(line) == OP_SEXT)
        set_state(line, sign_shrink(sign_extend(eval_line(value_nid), n), n + w));
      else
        // assert: unsigned extension
        set_state(line, eval_line(value_nid));

      set_step(line, next_step);

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

        set_step(line, next_step);

        return get_state(line);
      }

  printf("%s: slice sort error: n==%lu, u==%lu, l==%lu, m==%lu\n", selfie_name,
    n, u, l, eval_bitvec_size(get_sid(line)));

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_concat(uint64_t* line) {
  uint64_t size;
  uint64_t* left_nid;
  uint64_t* right_nid;
  uint64_t left_size;
  uint64_t right_size;
  uint64_t left_value;
  uint64_t right_value;

  size = eval_bitvec_size(get_sid(line));

  left_nid  = get_arg1(line);
  right_nid = get_arg2(line);

  left_size  = eval_bitvec_size(get_sid(left_nid));
  right_size = eval_bitvec_size(get_sid(right_nid));

  if (size == left_size + right_size) {
    left_value  = eval_line(left_nid);
    right_value = eval_line(right_nid);

    set_state(line, left_shift(left_value, right_size) + right_value);

    set_step(line, next_step);

    return get_state(line);
  }

  printf("%s: concat %lu-bit and %lu-bit bitvectors to missorted %lu-bit bitvector\n", selfie_name,
    left_size, right_size, size);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_ite(uint64_t* line) {
  uint64_t* if_nid;
  uint64_t* then_nid;
  uint64_t* else_nid;

  if_nid   = get_arg1(line);
  then_nid = get_arg2(line);
  else_nid = get_arg3(line);

  match_sorts(get_sid(if_nid), SID_BOOLEAN, "ite if");

  match_sorts(get_sid(line), get_sid(then_nid), "ite then");
  match_sorts(get_sid(line), get_sid(else_nid), "ite else");

  if (eval_line(if_nid))
    set_state(line, eval_line(then_nid));
  else
    set_state(line, eval_line(else_nid));

  set_step(line, next_step);

  return get_state(line);
}

uint64_t eval_read(uint64_t* line) {
  uint64_t* read_nid;
  uint64_t* index_nid;
  uint64_t* state_nid;
  uint64_t index;

  read_nid = get_arg1(line);

  if (is_array(get_sid(read_nid))) {
    index_nid = get_arg2(line);

    match_array_sorts(get_sid(read_nid), get_sid(index_nid), get_sid(line));

    state_nid = (uint64_t*) eval_line(read_nid);

    if (get_op(state_nid) == OP_STATE) {
      // TODO: if current_step == next_step (during init) read after write is not detected
      if (get_step(state_nid) == current_step) {
        index = eval_line(index_nid);

        set_state(line, read_or_write(state_nid, index, 0, 1));

        set_step(line, next_step);

        return get_state(line);
      } else
        printf("%s: read non-current state error\n", selfie_name);
    } else
      printf("%s: read non-state error\n", selfie_name);
  } else
    printf("%s: read non-array error\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_write(uint64_t* line) {
  uint64_t* write_nid;
  uint64_t* index_nid;
  uint64_t* value_nid;
  uint64_t* state_nid;
  uint64_t index;
  uint64_t value;

  if (is_array(get_sid(line))) {
    write_nid = get_arg1(line);
    index_nid = get_arg2(line);
    value_nid = get_arg3(line);

    match_sorts(get_sid(line), get_sid(write_nid), "write");
    match_array_sorts(get_sid(write_nid), get_sid(index_nid), get_sid(value_nid));

    state_nid = (uint64_t*) eval_line(write_nid);

    if (get_op(state_nid) == OP_STATE) {
      if (get_step(state_nid) != UNINITIALIZED) {
        if (get_step(state_nid) >= current_step) {
          index = eval_line(index_nid);
          value = eval_line(value_nid);

          read_or_write(state_nid, index, value, 0);

          // TODO: log writes and only apply with init and next
          set_step(state_nid, next_step);

          set_state(line, (uint64_t) state_nid);

          set_step(line, next_step);

          return get_state(line);
        } else
          printf("%s: write non-current state error\n", selfie_name);
      } else
        printf("%s: write uninitialized state error\n", selfie_name);
    } else
      printf("%s: write non-state error\n", selfie_name);
  } else
    printf("%s: write non-array error\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_unary_op(uint64_t* line) {
  char* op;
  uint64_t* value_nid;
  uint64_t value;
  uint64_t size;

  op = get_op(line);

  if (is_unary_op(op)) {
    value_nid = get_arg1(line);

    match_sorts(get_sid(line), get_sid(value_nid), "unary operand");

    value = eval_line(value_nid);

    size = eval_bitvec_size(get_sid(value_nid));

    if (op == OP_NOT)
      set_state(line, sign_shrink(-value - 1, size));
    else if (op == OP_INC)
      set_state(line, sign_shrink(value + 1, size));
    else if (op == OP_DEC)
      set_state(line, sign_shrink(value - 1, size));
    else if (op == OP_NEG)
      set_state(line, sign_shrink(-value, size));

    set_step(line, next_step);

    return get_state(line);
  }

  printf("%s: unknown unary operator %s\n", selfie_name, op);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_binary_op(uint64_t* line) {
  char* op;
  uint64_t* left_nid;
  uint64_t* right_nid;
  uint64_t left_value;
  uint64_t right_value;
  uint64_t size;

  op = get_op(line);

  if (is_binary_operator(op)) {
    left_nid  = get_arg1(line);
    right_nid = get_arg2(line);

    match_sorts(get_sid(left_nid), get_sid(right_nid), "left and right operand");

    if (op == OP_IMPLIES) {
      match_sorts(get_sid(left_nid), SID_BOOLEAN, "implication operator");
      match_sorts(get_sid(line), SID_BOOLEAN, "implication operator");

      left_value = eval_line(left_nid);

      if (left_value == 0)
        set_state(line, left_value == 0);
      else {
        // lazy evaluation of right operand
        right_value = eval_line(right_nid);

        set_state(line, right_value != 0);
      }
    } else {
      left_value  = eval_line(left_nid);
      right_value = eval_line(right_nid);

      size = eval_bitvec_size(get_sid(left_nid));

      if (is_bitwise_operator(op)) {
        match_sorts(get_sid(line), get_sid(left_nid), "bitwise operator");

        if (op == OP_AND)
          set_state(line, bitwise_and(left_value, right_value));
        else if (op == OP_OR)
          set_state(line, bitwise_or(left_value, right_value));
        else if (op == OP_XOR)
          set_state(line, bitwise_xor(left_value, right_value));
        else if (op == OP_SLL)
          set_state(line, sign_shrink(left_shift(left_value, right_value), size));
        else if (op == OP_SRL)
          set_state(line, right_shift(left_value, right_value));
        else if (op == OP_SRA)
          set_state(line, arithmetic_right_shift(left_value, right_value, size));
      } else if (is_arithmetic_operator(op)) {
        match_sorts(get_sid(line), get_sid(left_nid), "arithmetic operator");

        if (op == OP_ADD)
          set_state(line, left_value + right_value);
        else if (op == OP_SUB)
          set_state(line, left_value - right_value);
        else if (op == OP_MUL)
          set_state(line, left_value * right_value);
        else if (op == OP_UDIV)
          set_state(line, left_value / right_value);
        else if (op == OP_UREM)
          set_state(line, left_value % right_value);
        else {
          left_value  = sign_extend(left_value, size);
          right_value = sign_extend(right_value, size);

          if (op == OP_SDIV)
            set_state(line, sign_shrink(signed_division(left_value, right_value), size));
          else if (op == OP_SREM)
            set_state(line,
              sign_shrink(left_value - signed_division(left_value, right_value) * right_value, size));
        }
      } else if (is_comparison_operator(op)) {
        match_sorts(get_sid(line), SID_BOOLEAN, "comparison operator");

        if (op == OP_EQ)
          set_state(line, left_value == right_value);
        else if (op == OP_NEQ)
          set_state(line, left_value != right_value);
        else if (op == OP_UGT)
          set_state(line, left_value > right_value);
        else if (op == OP_UGTE)
          set_state(line, left_value >= right_value);
        else if (op == OP_ULT)
          set_state(line, left_value < right_value);
        else if (op == OP_ULTE)
          set_state(line, left_value <= right_value);
        else {
          left_value  = sign_extend(left_value, size);
          right_value = sign_extend(right_value, size);

          if (op == OP_SGT)
            set_state(line, signed_less_than(right_value, left_value));
          else if (op == OP_SGTE)
            set_state(line, signed_less_than_or_equal_to(right_value, left_value));
          else if (op == OP_SLT)
            set_state(line, signed_less_than(left_value, right_value));
          else if (op == OP_SLTE)
            set_state(line, signed_less_than_or_equal_to(left_value, right_value));
        }
      }
    }

    set_step(line, next_step);

    return get_state(line);
  }

  printf("%s: unknown binary operator %s\n", selfie_name, op);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_line(uint64_t* line) {
  char* op;

  op = get_op(line);

  if (get_step(line) == next_step)
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
  else if (op == OP_CONCAT)
    return eval_concat(line);
  else if (op == OP_ITE)
    return eval_ite(line);
  else if (op == OP_READ)
    return eval_read(line);
  else if (op == OP_WRITE)
    return eval_write(line);
  else if (is_unary_op(op))
    return eval_unary_op(line);
  else
    return eval_binary_op(line);
}

uint64_t eval_line_for(uint64_t core, uint64_t* lines) {
  return eval_line(get_for(core, lines));
}

uint64_t eval_property(uint64_t core, uint64_t* line) {
  char* op;
  uint64_t* condition_nid;
  char* symbol;
  uint64_t condition;

  if (line == UNUSED)
    // no property to evaluate: do not halt
    return 0;

  op = get_op(line);

  condition_nid = get_arg1(line);
  symbol        = (char*) get_arg2(line);

  condition = eval_line(condition_nid);

  if (op == OP_BAD) {
    if (condition != 0) {
      printf("%s: bad %s satisfied on core-%lu @ 0x%lX after %lu steps", selfie_name,
        symbol, core, eval_line_for(core, state_pc_nids), next_step - current_offset);
      if (any_input) printf(" with input %lu\n", current_input); else printf("\n");
    }

    set_state(line, condition != 0);
    set_step(line, next_step);

    return condition != 0;
  } else if (op == OP_CONSTRAINT) {
    if (condition == 0) {
      printf("%s: constraint %s violated on core-%lu @ 0x%lX after %lu steps\n", selfie_name,
        symbol, core, eval_line_for(core, state_pc_nids), next_step - current_offset);
      if (any_input) printf(" with input %lu\n", current_input); else printf("\n");
    }

    set_state(line, condition == 0);
    set_step(line, next_step);

    return condition == 0;
  }

  printf("%s: unknown property operator %s\n", selfie_name, op);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_property_for(uint64_t core, uint64_t* lines) {
  return eval_property(core, get_for(core, lines));
}

uint64_t eval_init(uint64_t* line) {
  uint64_t* state_nid;
  uint64_t* value_nid;

  if (get_op(line) == OP_INIT)
    if (current_step == INITIALIZED)
      if (current_step == next_step) {
        if (get_step(line) == UNINITIALIZED) {
          state_nid = get_arg1(line);

          if (get_op(state_nid) == OP_STATE) {
            if (get_step(state_nid) == UNINITIALIZED) {
              match_sorts(get_sid(line), get_sid(state_nid), "init state");

              value_nid = get_arg2(line);

              if (is_bitvector(get_sid(state_nid))) {
                match_sorts(get_sid(state_nid), get_sid(value_nid), "init bitvector");

                set_state(state_nid, eval_line(value_nid));

                set_step(state_nid, INITIALIZED);
              } else {
                // assert: sid of state line is ARRAY
                if (is_bitvector(get_sid(value_nid))) {
                  match_sorts(get_arg3(get_sid(state_nid)), get_sid(value_nid), "init array element");

                  if (eval_line(value_nid) != 0) {
                    printf("%s: init non-zero array element error\n", selfie_name);

                    exit(EXITCODE_SYSTEMERROR);
                  }

                  set_state(state_nid, (uint64_t) allocate_array(get_sid(state_nid)));

                  set_step(state_nid, INITIALIZED);
                } else {
                  // assert: sid of value line is ARRAY
                  match_sorts(get_sid(state_nid), get_sid(value_nid), "init array");

                  value_nid = (uint64_t*) eval_line(value_nid);

                  if (get_state(state_nid) != get_state(value_nid)) {
                    set_state(state_nid, get_state(value_nid));

                    set_step(state_nid, INITIALIZED);

                    // TODO: reinitialize value state
                    set_state(value_nid, 0);
                    set_step(value_nid, UNINITIALIZED);
                  } else {
                    printf("%s: init reinitializing array error\n", selfie_name);

                    exit(EXITCODE_SYSTEMERROR);
                  }
                }
              }

              set_step(line, INITIALIZED);

              // assert: return value is never used
              return (uint64_t) state_nid;
            } else
              printf("%s: init reinitializing state error\n", selfie_name);
          } else
            printf("%s: init %s error\n", selfie_name, get_op(state_nid));
        } else
          printf("%s: init reinitializing init error\n", selfie_name);

        exit(EXITCODE_SYSTEMERROR);
      }

  printf("%s: init error\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_next(uint64_t* line) {
  uint64_t current_next;
  uint64_t* state_nid;
  uint64_t* value_nid;
  uint64_t value;
  uint64_t no_update;

  if (get_op(line) == OP_NEXT)
    if (current_step < next_step)
      if (current_step + 1 == next_step) {
        current_next = current_step;

        if (current_next == 0)
          current_next = UNINITIALIZED;

        if (get_step(line) == current_next) {
          state_nid = get_arg1(line);

          if (get_op(state_nid) == OP_STATE) {
            if (get_step(state_nid) >= current_step) {
              match_sorts(get_sid(line), get_sid(state_nid), "next state");

              value_nid = get_arg2(line);

              match_sorts(get_sid(state_nid), get_sid(value_nid), "next state and value");

              if (is_bitvector(get_sid(state_nid))) {
                if (get_step(state_nid) == current_step) {
                  value = eval_line(value_nid);

                  no_update = get_state(state_nid) == value;
                } else {
                  printf("%s: next reupdating bitvector state error\n", selfie_name);

                  exit(EXITCODE_SYSTEMERROR);
                }
              } else {
                // assert: sid of state line is ARRAY
                if (get_step(state_nid) <= next_step) {
                  value_nid = (uint64_t*) eval_line(value_nid);

                  if (get_state(state_nid) == get_state(value_nid))
                    no_update = state_nid == value_nid;
                  else {
                    printf("%s: next reupdating state array error\n", selfie_name);

                    exit(EXITCODE_SYSTEMERROR);
                  }
                } else {
                  printf("%s: next reupdating array state error\n", selfie_name);

                  exit(EXITCODE_SYSTEMERROR);
                }
              }

              set_step(line, next_step);

              return no_update;
            } else
              printf("%s: next non-current state error\n", selfie_name);
          } else
            printf("%s: next %s error\n", selfie_name, get_op(state_nid));

          exit(EXITCODE_SYSTEMERROR);
        }
      }

  printf("%s: next error\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_next_for(uint64_t core, uint64_t* lines) {
  if (get_for(core, lines) == UNUSED)
    // no impact on state: do not halt
    return 1;
  else
    return eval_next(get_for(core, lines));
}

void apply_next(uint64_t* line) {
  uint64_t* state_nid;
  uint64_t* value_nid;

  if (get_step(line) == next_step) {
    state_nid = get_arg1(line);

    if (is_bitvector(get_sid(state_nid))) {
      value_nid = get_arg2(line);

      set_state(state_nid, get_state(value_nid));
    } // TODO: log writes and only apply with init and next

    set_step(state_nid, next_step);

    return;
  }

  printf("%s: apply error\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

void apply_next_for(uint64_t core, uint64_t* lines) {
  if (get_for(core, lines) == UNUSED)
    return;
  else
    apply_next(get_for(core, lines));
}

uint64_t* memcopy(uint64_t* destination, uint64_t* source, uint64_t bytes) {
  uint64_t i;

  // assert: bytes is multiple of sizeof(uint64_t)

  bytes = bytes / sizeof(uint64_t);

  i = 0;

  while (i < bytes) {
    *(destination + i) = *(source + i);

    i = i + 1;
  }

  return destination;
}

void save_state(uint64_t* line) {
  uint64_t* state_nid;
  uint64_t* sid;
  uint64_t array_size;
  uint64_t element_size;
  uint64_t* source;
  uint64_t* destination;

  state_nid = get_arg1(line);

  sid = get_sid(state_nid);

  if (is_bitvector(sid))
    set_state(line, get_state(state_nid));
  else if (sid != SID_CODE_STATE) {
    // assert: array
    array_size   = eval_array_size(sid);
    element_size = eval_element_size(sid);

    source      = (uint64_t*) get_state(state_nid);
    destination = (uint64_t*) get_state(line);

    if (destination == (uint64_t*) 0) {
      destination = allocate_array(get_sid(state_nid));

      set_state(line, (uint64_t) destination);
    }

    if (sid != SID_MEMORY_STATE)
      // assert: register files
      memcopy(destination, source, two_to_the_power_of(array_size) * sizeof(uint64_t));
    else {
      memcopy(get_data_array(destination),
        get_data_array(source),
        two_to_the_power_of(calculate_address_space(data_size, element_size)) * sizeof(uint64_t));
      memcopy(get_heap_array(destination),
        get_heap_array(source),
        two_to_the_power_of(calculate_address_space(heap_size, element_size)) * sizeof(uint64_t));
      memcopy(get_stack_array(destination),
        get_stack_array(source),
        two_to_the_power_of(calculate_address_space(stack_size, element_size)) * sizeof(uint64_t));
    }
  }
}

void save_state_for(uint64_t core, uint64_t* lines) {
  if (get_for(core, lines) == UNUSED)
    return;
  else
    save_state(get_for(core, lines));
}

void restore_state(uint64_t* line) {
  uint64_t* state_nid;
  uint64_t current_state;

  state_nid = get_arg1(line);

  if (get_sid(state_nid) != SID_CODE_STATE) {
    current_state = get_state(state_nid);

    set_state(state_nid, get_state(line));

    // keep current state to avoid reallocating arrays
    set_state(line, current_state);
  }

  set_step(state_nid, next_step);

  set_step(line, next_step);
}

void restore_state_for(uint64_t core, uint64_t* lines) {
  if (get_for(core, lines) == UNUSED)
    return;
  else
    restore_state(get_for(core, lines));
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
    init_program_break_nid  = new_init(SID_VIRTUAL_ADDRESS, state_program_break_nid,
      NID_HEAP_START, "initial program break is start of heap segment");

    eval_init(init_program_break_nid);

    state_file_descriptor_nid = new_input(OP_STATE, SID_MACHINE_WORD, "file-descriptor", "file descriptor");
    init_file_descriptor_nid  = new_init(SID_MACHINE_WORD, state_file_descriptor_nid,
      NID_MACHINE_WORD_0, "initial file descriptor is zero");

    eval_init(init_file_descriptor_nid);

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
  init_readable_bytes_nid  = new_init(SID_MACHINE_WORD, state_readable_bytes_nid,
    param_readable_bytes_nid, "number of readable bytes");

  eval_init(init_readable_bytes_nid);

  state_read_bytes_nid = new_input(OP_STATE, SID_MACHINE_WORD,
    format_comment("core-%lu-read-bytes", core), "bytes read in active read system call");
  init_read_bytes_nid  = new_init(SID_MACHINE_WORD, state_read_bytes_nid,
    NID_MACHINE_WORD_0, "initially zero read bytes");

  eval_init(init_read_bytes_nid);
}

void print_kernel_state(uint64_t core) {
  if (core == 0) {
    print_break_comment_line("system kernel state", init_program_break_nid);

    print_break_line(init_file_descriptor_nid);
  }

  print_break_comment_line_for(core, "kernel state", init_readable_bytes_nid);

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

  set_for(core, state_register_file_nids, state_register_file_nid);

  if (SYNCHRONIZED_REGISTERS) {
    if (core > 0)
      return;
  } else if (SHARED_REGISTERS)
    if (core > 0)
      return;

  state_register_file_nid = new_input(OP_STATE, SID_REGISTER_STATE,
    format_comment("core-%lu-zeroed-register-file", core), "zeroed register file");

  set_for(core, state_register_file_nids, state_register_file_nid);

  init_zeroed_register_file_nid = new_init(SID_REGISTER_STATE,
    state_register_file_nid, NID_MACHINE_WORD_0, "zeroing register file");

  eval_init(init_zeroed_register_file_nid);

  if (number_of_binaries == 0) {
    value_nid = cast_virtual_address_to_machine_word(
      new_unary(OP_DEC, SID_VIRTUAL_ADDRESS, NID_STACK_END, "end of stack segment - 1"));
    initial_register_file_nid =
      store_register_value(NID_SP, value_nid, "write initial sp value", state_register_file_nid);

    if (eval_line(load_register_value(NID_SP, "read initial sp value", initial_register_file_nid)) != eval_line(value_nid)) {
      printf("%s: initial register file value mismatch @ %s\n", selfie_name, get_register_name(REG_SP));

      exit(EXITCODE_SYSTEMERROR);
    }
  } else {
    initial_register_file_nid = state_register_file_nid;

    reg = 0;

    while (reg < NUMBEROFREGISTERS) {
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

        if (eval_line(load_register_value(reg_nid, "read initial register value", initial_register_file_nid)) != value) {
          printf("%s: initial register file value mismatch @ %s\n", selfie_name, get_register_name(reg));

          exit(EXITCODE_SYSTEMERROR);
        }
      }

      reg = reg + 1;
    }
  }

  if (initial_register_file_nid != state_register_file_nid) {
    next_zeroed_register_file_nid = new_next(SID_REGISTER_STATE,
      state_register_file_nid, state_register_file_nid, "read-only zeroed register file");

    state_register_file_nid = new_input(OP_STATE, SID_REGISTER_STATE,
      format_comment("core-%lu-initialized-register-file", core), "initialized register file");

    set_for(core, state_register_file_nids, state_register_file_nid);

    init_register_file_nid = new_init(SID_REGISTER_STATE,
      state_register_file_nid, initial_register_file_nid, "initializing registers");
  } else
    init_register_file_nid = init_zeroed_register_file_nid;

  eval_init(init_register_file_nid);
}

void print_register_file_state(uint64_t core) {
  if (SYNCHRONIZED_REGISTERS) {
    if (core > 0)
      return;
  } else if (SHARED_REGISTERS)
    if (core > 0)
      return;

  print_break_comment_for(core, "zeroed register file");

  print_line(init_zeroed_register_file_nid);

  if (init_register_file_nid != init_zeroed_register_file_nid) {
    print_line(next_zeroed_register_file_nid);

    if (number_of_binaries == 0)
      print_break_comment("initializing sp");
    else
      print_aligned_break_comment("initializing registers", log_ten(NUMBEROFREGISTERS * 3 + 1) + 1);

    print_line(initial_register_file_nid);

    print_break_comment_for(core, "initialized register file");

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

void new_segmentation(uint64_t core) {
  uint64_t stack_end;
  uint64_t low_stack_address_space;
  uint64_t up_stack_address_space;

  if (core > 0)
    return;

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

void print_segmentation(uint64_t core) {
  if (core > 0)
    return;

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
  if (eval_constant_value(NID_STACK_END) > 0)
    return is_block_in_segment(start_nid, end_nid, NID_STACK_START, NID_STACK_END);
  else
    // comparing with end of stack segment is unnecessary since end wrapped around to zero
    return new_binary_boolean(OP_UGTE,
      start_nid,
      NID_STACK_START,
      "virtual address of start of block >= start of stack segment?");
}

void new_code_segment(uint64_t core) {
  uint64_t  number_of_hex_digits;
  uint64_t* vaddr_nid;
  uint64_t* ir_nid;
  uint64_t* code_segment_nid;

  if (core >= number_of_binaries) {
    state_code_segment_nid = new_input(OP_STATE, SID_CODE_STATE,
      format_comment("core-%lu-code-segment", core), "code segment");

    init_code_segment_nid = UNUSED;
    next_code_segment_nid = UNUSED;
  } else {
    state_zeroed_code_segment_nid = new_input(OP_STATE, SID_CODE_STATE,
      format_comment("core-%lu-code-segment", core), "code segment");

    init_zeroed_code_segment_nid = new_init(SID_CODE_STATE,
      state_zeroed_code_segment_nid, NID_CODE_WORD_0, "zeroing code segment");

    eval_init(init_zeroed_code_segment_nid);

    next_zeroed_code_segment_nid = new_next(SID_CODE_STATE,
      state_zeroed_code_segment_nid, state_zeroed_code_segment_nid, "read-only zeroed code segment");

    number_of_hex_digits = round_up(VIRTUAL_ADDRESS_SPACE, 4) / 4;

    initial_code_nid = UNUSED;

    initial_code_segment_nid = state_zeroed_code_segment_nid;

    reuse_lines = 0; // TODO: turn on via console argument

    pc = code_start;

    while (pc < code_start + code_size) {
      fetch();

      if (ir != 0) {
        // skipping zero as instruction
        vaddr_nid = new_constant(OP_CONSTH, SID_VIRTUAL_ADDRESS,
          pc, number_of_hex_digits, format_comment("vaddr 0x%lX", pc));

        ir_nid = new_constant(OP_CONST, SID_INSTRUCTION_WORD,
          ir, 32, format_comment("code 0x%04lX", ir));

        code_segment_nid =
          store_single_word_at_virtual_address(vaddr_nid, ir_nid, initial_code_segment_nid);

        if (initial_code_nid == UNUSED)
          initial_code_nid = code_segment_nid;

        if (initial_code_segment_nid != state_zeroed_code_segment_nid)
          // set successor for printing initial code segment iteratively to avoid stack overflow
          set_succ(initial_code_segment_nid, code_segment_nid);

        initial_code_segment_nid = code_segment_nid;

        // evaluate on-the-fly to avoid stack overflow
        if (eval_line(load_single_word_at_virtual_address(vaddr_nid, initial_code_segment_nid)) != ir) {
          printf("%s: initial code segment value mismatch @ 0x%lX\n", selfie_name, pc);

          exit(EXITCODE_SYSTEMERROR);
        }
      }

      pc = pc + INSTRUCTIONSIZE;
    }

    reuse_lines = 1;

    if (initial_code_segment_nid != state_zeroed_code_segment_nid) {
      state_code_segment_nid = new_input(OP_STATE, SID_CODE_STATE,
        format_comment("core-%lu-loaded-code-segment", core), "loaded code segment");

      init_code_segment_nid = new_init(SID_CODE_STATE,
        state_code_segment_nid, initial_code_segment_nid, "loaded code");

      eval_init(init_code_segment_nid);

      next_code_segment_nid = new_next(SID_CODE_STATE,
        state_code_segment_nid, state_code_segment_nid, "read-only code segment");
    } else {
      state_code_segment_nid = state_zeroed_code_segment_nid;
      init_code_segment_nid  = init_zeroed_code_segment_nid;
      next_code_segment_nid  = next_zeroed_code_segment_nid;
    }
  }

  set_for(core, state_code_segment_nids, state_code_segment_nid);
  set_for(core, next_code_segment_nids, next_code_segment_nid);
}

void print_code_segment(uint64_t core) {
  if (core >= number_of_binaries) {
    print_break_comment_for(core, "uninitialized code segment");

    print_line(state_code_segment_nid);
  } else {
    print_break_comment("zeroed code segment");

    print_line(init_zeroed_code_segment_nid);
    print_line(next_zeroed_code_segment_nid);

    if (initial_code_segment_nid != state_zeroed_code_segment_nid) {
      // conservatively estimating number of lines needed to store one byte
      print_aligned_break_comment("loading code", log_ten(code_size * 3) + 1);

      while (initial_code_nid != UNUSED) {
        print_line(initial_code_nid);

        initial_code_nid = get_succ(initial_code_nid);
      }

      print_break_comment_for(core, "loaded code segment");

      print_line(init_code_segment_nid);
      print_line(next_code_segment_nid);
    }
  }
}

void new_memory_state(uint64_t core) {
  uint64_t  number_of_hex_digits;
  uint64_t  vaddr;
  uint64_t  data;
  uint64_t* vaddr_nid;
  uint64_t* data_nid;
  uint64_t* main_memory_nid;

  set_for(core, state_main_memory_nids, state_main_memory_nid);

  if (SYNCHRONIZED_MEMORY) {
    if (core > 0)
      return;
  } else if (SHARED_MEMORY)
    if (core > 0)
      return;

  state_main_memory_nid = new_input(OP_STATE, SID_MEMORY_STATE,
    format_comment("core-%lu-zeroed-main-memory", core), "zeroed main memory");

  set_for(core, state_main_memory_nids, state_main_memory_nid);

  init_zeroed_main_memory_nid = new_init(SID_MEMORY_STATE,
    state_main_memory_nid, NID_MEMORY_WORD_0, "zeroing memory");

  eval_init(init_zeroed_main_memory_nid);

  if (number_of_binaries > 0) {
    number_of_hex_digits = round_up(MEMORY_ADDRESS_SPACE, 4) / 4;

    initial_data_nid  = UNUSED;
    initial_heap_nid  = UNUSED;
    initial_stack_nid = UNUSED;

    initial_main_memory_nid = state_main_memory_nid;

    reuse_lines = 0; // TODO: turn on via console argument

    vaddr = data_start;

    while (vaddr <= VIRTUALMEMORYSIZE * GIGABYTE - WORDSIZE) {
      if (vaddr == data_start + data_size)
        vaddr = heap_start;

      if (vaddr == heap_start + heap_size)
        vaddr = stack_start;

      if (is_virtual_address_mapped(get_pt(current_context), vaddr)) {
        // memory allocated but not yet mapped is assumed to be zeroed
        data = load_virtual_memory(get_pt(current_context), vaddr);

        if (data != 0) {
          // skipping zero as initial value
          vaddr_nid = new_constant(OP_CONSTH, SID_VIRTUAL_ADDRESS,
            vaddr, number_of_hex_digits, format_comment("vaddr 0x%lX", vaddr));

          data_nid = new_constant(OP_CONSTH, SID_MACHINE_WORD,
            data, 0, format_comment("data 0x%lX", data));

          main_memory_nid = store_machine_word_at_virtual_address(vaddr_nid, data_nid, initial_main_memory_nid);

          if (is_virtual_address_in_data_segment(vaddr)) {
            if (initial_data_nid == UNUSED)
              initial_data_nid = main_memory_nid;
          } else if (is_virtual_address_in_heap_segment(vaddr)) {
            if (initial_heap_nid == UNUSED)
              initial_heap_nid = main_memory_nid;
          } else if (is_virtual_address_in_stack_segment(vaddr)) {
            if (initial_stack_nid == UNUSED)
              initial_stack_nid = main_memory_nid;
          }

          if (initial_main_memory_nid != state_main_memory_nid)
            if (main_memory_nid != initial_data_nid)
              if (main_memory_nid != initial_heap_nid)
                if (main_memory_nid != initial_stack_nid)
                  set_succ(initial_main_memory_nid, main_memory_nid);

          initial_main_memory_nid = main_memory_nid;

          // evaluate on-the-fly to avoid stack overflow later
          if (eval_line(load_machine_word_at_virtual_address(vaddr_nid, initial_main_memory_nid)) != data) {
            printf("%s: initial main memory value mismatch @ 0x%lX\n", selfie_name, vaddr);

            exit(EXITCODE_SYSTEMERROR);
          }
        }
      }

      if (vaddr + WORDSIZE == 0)
        // check 32-bit overflow to terminate loop
        vaddr = HIGHESTVIRTUALADDRESS;
      else
        vaddr = vaddr + WORDSIZE;
    }

    reuse_lines = 1;

    if (initial_main_memory_nid != state_main_memory_nid) {
      next_zeroed_main_memory_nid = new_next(SID_MEMORY_STATE,
        state_main_memory_nid, state_main_memory_nid, "read-only zeroed main memory");

      state_main_memory_nid = new_input(OP_STATE, SID_MEMORY_STATE,
        format_comment("core-%lu-loaded-main-memory", core), "loaded main memory");

      set_for(core, state_main_memory_nids, state_main_memory_nid);

      init_main_memory_nid = new_init(SID_MEMORY_STATE,
        state_main_memory_nid, initial_main_memory_nid, "loaded data");

      eval_init(init_main_memory_nid);
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

  print_break_comment_for(core, "zeroed main memory");

  print_line(init_zeroed_main_memory_nid);

  if (number_of_binaries > 0)
    if (initial_main_memory_nid != state_main_memory_nid) {
      print_line(next_zeroed_main_memory_nid);

      if (initial_data_nid != UNUSED) {
        // conservatively estimating number of lines needed to store one byte
        print_aligned_break_comment("loaded data segment", log_ten(data_size * 3) + 1);

        while (initial_data_nid != UNUSED) {
          print_line(initial_data_nid);

          initial_data_nid = get_succ(initial_data_nid);
        }
      }

      if (initial_heap_nid != UNUSED) {
        print_aligned_break_comment("loaded heap segment", log_ten(heap_initial_size * 3) + 1);

        while (initial_heap_nid != UNUSED) {
          print_line(initial_heap_nid);

          initial_heap_nid = get_succ(initial_heap_nid);
        }
      }

      if (initial_stack_nid != UNUSED) {
        print_aligned_break_comment("loaded stack segment", log_ten(stack_initial_size * 3) + 1);

        while (initial_stack_nid != UNUSED) {
          print_line(initial_stack_nid);

          initial_stack_nid = get_succ(initial_stack_nid);
        }
      }

      print_break_comment_for(core, "loaded main memory");

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
  return eval_element_size(get_sid(memory_nid)) == 8;
}

uint64_t is_half_word_memory(uint64_t* memory_nid) {
  return eval_element_size(get_sid(memory_nid)) == HALFWORDSIZEINBITS;
}

uint64_t is_single_word_memory(uint64_t* memory_nid) {
  return eval_element_size(get_sid(memory_nid)) == SINGLEWORDSIZEINBITS;
}

uint64_t is_double_word_memory(uint64_t* memory_nid) {
  return eval_element_size(get_sid(memory_nid)) == DOUBLEWORDSIZEINBITS;
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
    get_power_of_two_size_in_bytes(eval_element_size(get_sid(memory_nid)));

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
    if (eval_constant_value(vaddr_nid) % SINGLEWORDSIZE == 0)
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
    if (eval_constant_value(vaddr_nid) % DOUBLEWORDSIZE == 0)
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

uint64_t* is_address_in_machine_word_in_code_segment(uint64_t* machine_word_nid) {
  uint64_t* vaddr_nid;

  vaddr_nid = cast_machine_word_to_virtual_address(machine_word_nid);

  return does_machine_word_work_as_virtual_address(machine_word_nid,
    is_block_in_code_segment(vaddr_nid, vaddr_nid));
}

uint64_t* is_address_in_machine_word_in_data_segment(uint64_t* machine_word_nid) {
  uint64_t* vaddr_nid;

  vaddr_nid = cast_machine_word_to_virtual_address(machine_word_nid);

  return does_machine_word_work_as_virtual_address(machine_word_nid,
    is_block_in_data_segment(vaddr_nid, vaddr_nid));
}

uint64_t* is_address_in_machine_word_in_heap_segment(uint64_t* machine_word_nid) {
  uint64_t* vaddr_nid;

  vaddr_nid = cast_machine_word_to_virtual_address(machine_word_nid);

  return does_machine_word_work_as_virtual_address(machine_word_nid,
    is_block_in_heap_segment(vaddr_nid, vaddr_nid));
}

uint64_t* is_address_in_machine_word_in_stack_segment(uint64_t* machine_word_nid) {
  uint64_t* vaddr_nid;

  vaddr_nid = cast_machine_word_to_virtual_address(machine_word_nid);

  return does_machine_word_work_as_virtual_address(machine_word_nid,
    is_block_in_stack_segment(vaddr_nid, vaddr_nid));
}

uint64_t* is_address_in_machine_word_in_main_memory(uint64_t* machine_word_nid) {
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

uint64_t* is_range_in_machine_word_in_heap_segment(uint64_t* machine_word_nid, uint64_t* range_nid) {
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

char* get_instruction_mnemonic(uint64_t instruction_ID) {
  return (char*) *(RISC_V_MNEMONICS + instruction_ID);
}

uint64_t is_R_type(uint64_t instruction_ID) {
  if (instruction_ID >= ID_ADD)
    if (instruction_ID <= ID_REMUW)
      return 1;

  return 0;
}

uint64_t is_I_type(uint64_t instruction_ID) {
  if (instruction_ID >= ID_JALR)
    if (instruction_ID <= ID_SRAIW)
      return 1;

  return 0;
}

uint64_t is_register_relative_I_type(uint64_t instruction_ID) {
  if (instruction_ID >= ID_JALR)
    if (instruction_ID <= ID_LD)
      return 1;

  return 0;
}

uint64_t is_shift_I_type(uint64_t instruction_ID) {
  if (instruction_ID >= ID_SLLI)
    if (instruction_ID <= ID_SRAIW)
      return 1;

  return 0;
}

uint64_t is_32_bit_shift_I_type(uint64_t instruction_ID) {
  if (instruction_ID >= ID_SLLIW)
    if (instruction_ID <= ID_SRAIW)
      return 1;

  return 0;
}

uint64_t is_S_type(uint64_t instruction_ID) {
  if (instruction_ID >= ID_SB)
    if (instruction_ID <= ID_SD)
      return 1;

  return 0;
}

uint64_t is_SB_type(uint64_t instruction_ID) {
  if (instruction_ID >= ID_BEQ)
    if (instruction_ID <= ID_BGEU)
      return 1;

  return 0;
}

uint64_t is_U_type(uint64_t instruction_ID) {
  if (instruction_ID >= ID_LUI)
    if (instruction_ID <= ID_AUIPC)
      return 1;

  return 0;
}

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

uint64_t* is_enabled(uint64_t* instruction_nid) {
  if (instruction_nid != NID_DISABLED)
    return new_binary_boolean(OP_NEQ, instruction_nid, NID_DISABLED, "is instruction enabled?");
  else
    return NID_FALSE;
}

uint64_t* is_illegal_shamt(uint64_t* ir_nid) {
  if (IS64BITTARGET)
    return decode_opcode(SID_BOOLEAN, ir_nid,
      NID_OP_IMM_32, "IMM-32?",
      decode_shift_RV64I(SID_BOOLEAN, ir_nid,
        NID_F7_SLL_SRL_ILLEGAL, is_enabled(NID_SLLIW), is_enabled(NID_SRLIW),
        NID_F7_SRA_ILLEGAL, is_enabled(NID_SRAIW), "there?",
        NID_FALSE),
      "illegal shamt there?",
      NID_FALSE);
  else
    return decode_opcode(SID_BOOLEAN, ir_nid,
      NID_OP_IMM, "IMM?",
      decode_shift_imm(SID_BOOLEAN, ir_nid,
        NID_F7_SLL_SRL_ILLEGAL, is_enabled(NID_SLLI), is_enabled(NID_SRLI),
        NID_F7_SRA_ILLEGAL, is_enabled(NID_SRAI), "there?",
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

uint64_t* is_division_remainder_by_zero(uint64_t* ir_nid, uint64_t* register_file_nid) {
  uint64_t* RV64M_nid;
  uint64_t* RV32M_nid;

  if (RISCU + RV32M + RV64M) {
    if (RISCU)
      RV32M_nid = decode_opcode(SID_BOOLEAN, ir_nid,
        NID_OP_OP, "OP?",
        decode_RV32M(SID_BOOLEAN, ir_nid,
          NID_FALSE, NID_FALSE, NID_FALSE, NID_FALSE,
          NID_FALSE, is_enabled(NID_DIVU),
          NID_FALSE, is_enabled(NID_REMU), "active?",
          NID_FALSE),
        "divu or remu active?",
        NID_FALSE);
    else {
      if (RV64M)
        RV64M_nid = decode_opcode(SID_BOOLEAN, ir_nid,
          NID_OP_OP_32, "OP-32?",
          decode_RV64M(SID_BOOLEAN, ir_nid,
            NID_FALSE,
            is_enabled(NID_DIVW), is_enabled(NID_DIVUW),
            is_enabled(NID_REMW), is_enabled(NID_REMUW), "active?",
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
            is_enabled(NID_DIV), is_enabled(NID_DIVU),
            is_enabled(NID_REM), is_enabled(NID_REMU), "active?",
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

uint64_t* is_signed_division_remainder_overflow(uint64_t* ir_nid, uint64_t* register_file_nid) {
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
              is_enabled(NID_DIVW), NID_FALSE,
              is_enabled(NID_REMW), NID_FALSE, "active?",
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
              is_enabled(NID_DIV), NID_FALSE,
              is_enabled(NID_REM), NID_FALSE, "active?",
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
  uint64_t* bltu_nid, uint64_t* bgeu_nid, char* comment,
  uint64_t* no_funct3_nid, uint64_t* other_opcode_nid) {
  if (RISCU)
    return decode_opcode(sid, ir_nid,
      NID_OP_BRANCH, "BRANCH?",
      decode_funct3(sid, ir_nid,
        NID_F3_BEQ, "BEQ?",
        beq_nid, format_comment("beq %s", (uint64_t) comment),
        no_funct3_nid),
      format_comment("branch %s", (uint64_t) comment),
      other_opcode_nid);

  return decode_opcode(sid, ir_nid,
    NID_OP_BRANCH, "BRANCH?",
    decode_funct3(sid, ir_nid,
      NID_F3_BEQ, "BEQ?",
      beq_nid, format_comment("beq %s", (uint64_t) comment),
      decode_funct3(sid, ir_nid,
        NID_F3_BNE, "BNE?",
        bne_nid, format_comment("bne %s", (uint64_t) comment),
        decode_funct3(sid, ir_nid,
          NID_F3_BLT, "BLT?",
          blt_nid, format_comment("blt %s", (uint64_t) comment),
          decode_funct3(sid, ir_nid,
            NID_F3_BGE, "BGE?",
            bge_nid, format_comment("bge %s", (uint64_t) comment),
            decode_funct3(sid, ir_nid,
              NID_F3_BLTU, "BLTU?",
              bltu_nid, format_comment("bltu %s", (uint64_t) comment),
              decode_funct3(sid, ir_nid,
                NID_F3_BGEU, "BGEU?",
                bgeu_nid, format_comment("bgeu %s", (uint64_t) comment),
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
  return new_ternary(OP_ITE, SID_INSTRUCTION_ID,
    new_binary_boolean(OP_EQ, ir_nid, NID_ECALL_I, "ir == ECALL?"),
    NID_ECALL,
    decode_imm(SID_INSTRUCTION_ID, ir_nid,
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
      "known?", NID_DISABLED,
      decode_op(SID_INSTRUCTION_ID, ir_nid,
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
        "known?", NID_DISABLED,
        decode_RV32M(SID_INSTRUCTION_ID, ir_nid,
          NID_MUL,
          NID_MULH,
          NID_MULHSU,
          NID_MULHU,
          NID_DIV,
          NID_DIVU,
          NID_REM,
          NID_REMU,
          "known?", NID_DISABLED),
        decode_RV64M(SID_INSTRUCTION_ID, ir_nid,
          NID_MULW,
          NID_DIVW,
          NID_DIVUW,
          NID_REMW,
          NID_REMUW,
          "known?", NID_DISABLED),
        decode_load(SID_INSTRUCTION_ID, ir_nid,
          NID_LD, NID_LWU,
          NID_LW,
          NID_LH, NID_LHU,
          NID_LB, NID_LBU,
          "known?", NID_DISABLED,
          decode_store(SID_INSTRUCTION_ID, ir_nid,
            NID_SD,
            NID_SW, NID_SH, NID_SB, "known?", NID_DISABLED,
            decode_branch(SID_INSTRUCTION_ID, ir_nid,
              NID_BEQ, NID_BNE,
              NID_BLT, NID_BGE,
              NID_BLTU, NID_BGEU,
              "known?", NID_DISABLED,
              decode_jal(SID_INSTRUCTION_ID, ir_nid,
                NID_JAL, "known?",
                decode_jalr(SID_INSTRUCTION_ID, ir_nid,
                  NID_JALR, "known?", NID_DISABLED,
                  decode_lui(SID_INSTRUCTION_ID, ir_nid,
                    NID_LUI, "known?",
                    decode_auipc(SID_INSTRUCTION_ID, ir_nid,
                      NID_AUIPC, "known?",
                      NID_DISABLED))))))))),
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
    is_address_in_machine_word_in_main_memory(get_rs1_value_plus_I_immediate(ir_nid, register_file_nid)),
    is_address_in_machine_word_in_main_memory(get_rs1_value_plus_I_immediate(ir_nid, register_file_nid)),
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

  uint64_t* register_data_flow_nid;

  opcode_nid = get_instruction_opcode(ir_nid);

  rd_nid       = get_instruction_rd(ir_nid);
  rd_value_nid = load_register_value(rd_nid, "current rd value", register_file_nid);

  register_data_flow_nid = new_binary_boolean(OP_AND,
    new_binary_boolean(OP_NEQ, rd_nid, NID_ZR, "rd != register zero?"),
    new_binary_boolean(OP_AND,
      new_binary_boolean(OP_NEQ, opcode_nid, NID_OP_STORE, "opcode != STORE?"),
      new_binary_boolean(OP_NEQ, opcode_nid, NID_OP_BRANCH, "opcode != BRANCH?"),
      "not STORE and not BRANCH?"), // redundant
    "rd != zero register and not STORE and not BRANCH?");

  rd_value_nid =
    imm_data_flow(ir_nid, register_file_nid,
      op_data_flow(ir_nid, register_file_nid,
        load_data_flow(ir_nid, register_file_nid, memory_nid,
          jal_data_flow(pc_nid, ir_nid,
            jalr_data_flow(pc_nid, ir_nid, register_file_nid,
              lui_data_flow(ir_nid,
                auipc_data_flow(pc_nid, ir_nid, rd_value_nid)))))));

  return new_ternary(OP_ITE, SID_REGISTER_STATE,
    register_data_flow_nid,
    store_register_value(rd_nid, rd_value_nid, "rd update", register_file_nid),
    register_file_nid,
    "register data flow");
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
    is_address_in_machine_word_in_main_memory(get_rs1_value_plus_S_immediate(ir_nid, register_file_nid)),
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

uint64_t* execute_branch(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* condition_nid) {
  return new_ternary(OP_ITE, SID_MACHINE_WORD,
    condition_nid,
    get_pc_value_plus_SB_immediate(pc_nid, ir_nid),
    get_pc_value_plus_4(pc_nid),
    "evaluate branch condition");
}

uint64_t* branch_control_flow(uint64_t* pc_nid, uint64_t* ir_nid, uint64_t* register_file_nid, uint64_t* other_control_flow_nid) {
  uint64_t* rs1_value_nid;
  uint64_t* rs2_value_nid;

  rs1_value_nid = load_register_value(get_instruction_rs1(ir_nid), "rs1 value", register_file_nid);
  rs2_value_nid = load_register_value(get_instruction_rs2(ir_nid), "rs2 value", register_file_nid);

  return decode_branch(SID_MACHINE_WORD, ir_nid,
    execute_branch(pc_nid, ir_nid,
      new_binary_boolean(OP_EQ, rs1_value_nid, rs2_value_nid, "rs1 value == rs2 value?")),
    execute_branch(pc_nid, ir_nid,
      new_binary_boolean(OP_NEQ, rs1_value_nid, rs2_value_nid, "rs1 value != rs2 value?")),
    execute_branch(pc_nid, ir_nid,
      new_binary_boolean(OP_SLT, rs1_value_nid, rs2_value_nid, "rs1 value < rs2 value?")),
    execute_branch(pc_nid, ir_nid,
      new_binary_boolean(OP_SGTE, rs1_value_nid, rs2_value_nid, "rs1 value >= rs2 value?")),
    execute_branch(pc_nid, ir_nid,
      new_binary_boolean(OP_ULT, rs1_value_nid, rs2_value_nid, "rs1 value < rs2 value (unsigned)?")),
    execute_branch(pc_nid, ir_nid,
      new_binary_boolean(OP_UGTE, rs1_value_nid, rs2_value_nid, "rs1 value >= rs2 value (unsigned)?")),
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

uint64_t is_compressed_instruction_ID(uint64_t instruction_ID) {
  if (instruction_ID >= ID_C_MV)
    if (instruction_ID <= ID_C_JAL)
      return 1;

  return 0;
}

uint64_t is_CR_type(uint64_t instruction_ID) {
  if (instruction_ID >= ID_C_MV)
    if (instruction_ID <= ID_C_JALR)
      return 1;

  return 0;
}

uint64_t is_jump_CR_type(uint64_t instruction_ID) {
  if (instruction_ID >= ID_C_JR)
    if (instruction_ID <= ID_C_JALR)
      return 1;

  return 0;
}

uint64_t is_CI_type(uint64_t instruction_ID) {
  if (instruction_ID >= ID_C_LI)
    if (instruction_ID <= ID_C_LDSP)
      return 1;

  return 0;
}

uint64_t is_CL_type(uint64_t instruction_ID) {
  if (instruction_ID >= ID_C_LW)
    if (instruction_ID <= ID_C_LD)
      return 1;

  return 0;
}

uint64_t is_CS_type(uint64_t instruction_ID) {
  if (instruction_ID >= ID_C_SW)
    if (instruction_ID <= ID_C_SDSP)
      return 1;

  return 0;
}

uint64_t is_register_CS_type(uint64_t instruction_ID) {
  if (instruction_ID >= ID_C_SUB)
    if (instruction_ID <= ID_C_SUBW)
      return 1;

  return 0;
}

uint64_t is_CB_type(uint64_t instruction_ID) {
  if (instruction_ID >= ID_C_BEQZ)
    if (instruction_ID <= ID_C_SRAI)
      return 1;

  return 0;
}

uint64_t is_CJ_type(uint64_t instruction_ID) {
  if (instruction_ID >= ID_C_J)
    if (instruction_ID <= ID_C_JAL)
      return 1;

  return 0;
}

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
    is_enabled(c_shift_nid),
    "compressed shift with illegal shamt?");
}

uint64_t* is_illegal_compressed_instruction_imm_shamt(uint64_t* c_ir_nid) {
  uint64_t* c_lui_nid;
  uint64_t* c_addi_nid;
  uint64_t* c_addi16sp_nid;
  uint64_t* c_addi4spn_nid;

  if (RVC) {
    c_lui_nid = new_binary_boolean(OP_AND,
      is_enabled(NID_C_LUI),
      new_binary_boolean(OP_EQ,
        get_compressed_instruction_CUI_immediate(c_ir_nid),
        NID_MACHINE_WORD_0,
        "CUI-immediate == 0?"),
      "c.lui with CUI-immediate == 0?");

    c_addi_nid = new_binary_boolean(OP_AND,
      is_enabled(NID_C_ADDI),
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
      is_enabled(NID_C_ADDI16SP),
      new_binary_boolean(OP_EQ,
        get_compressed_instruction_CI16SP_immediate(c_ir_nid),
        NID_MACHINE_WORD_0,
        "CI16SP-immediate == 0?"),
      "c.addi16sp with CI16SP-immediate == 0?");

    c_addi4spn_nid = new_binary_boolean(OP_AND,
      is_enabled(NID_C_ADDI4SPN),
      new_binary_boolean(OP_EQ,
        get_compressed_instruction_CIW_immediate(c_ir_nid),
        NID_MACHINE_WORD_0,
        "CIW-immediate == 0?"),
      "c.addi4spn with CIW-immediate == 0?");

    return new_binary_boolean(OP_AND,
      is_compressed_instruction(c_ir_nid),
      new_binary_boolean(OP_IMPLIES,
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
        "is either defined illegal compressed instruction or else has illegal immediate or shamt?"),
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
  uint64_t* c_beqz_nid, uint64_t* c_bnez_nid, char* comment,
  uint64_t* other_c_funct3_nid) {
  return decode_compressed_funct3(sid, c_ir_nid,
    NID_F3_C_BEQZ, "C.BEQZ?",
    c_beqz_nid, format_comment("c.beqz %s", (uint64_t) comment),
    decode_compressed_funct3(sid, c_ir_nid,
      NID_F3_C_BNEZ, "C.BNEZ?",
      c_bnez_nid, format_comment("c.bnez %s", (uint64_t) comment),
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
      decode_compressed_opcode(SID_INSTRUCTION_ID, c_ir_nid,
        NID_OP_C2, "C2?",
        decode_compressed_mv_add(SID_INSTRUCTION_ID, c_ir_nid,
          NID_C_MV, NID_C_ADD, "known?",
          decode_compressed_slli(SID_INSTRUCTION_ID, c_ir_nid,
            NID_C_SLLI, "known?",
            decode_compressed_load(SID_INSTRUCTION_ID, c_ir_nid,
              NID_C_LDSP, NID_C_LWSP, "known?",
              decode_compressed_store(SID_INSTRUCTION_ID, c_ir_nid,
                NID_C_SDSP, NID_C_SWSP, "known?",
                decode_compressed_nonzero_rs1_zero_rs2(SID_INSTRUCTION_ID, c_ir_nid,
                  decode_compressed_jr(SID_INSTRUCTION_ID, c_ir_nid,
                    NID_C_JR, "known?",
                    decode_compressed_jalr(SID_INSTRUCTION_ID, c_ir_nid,
                      NID_C_JALR, "known?",
                      NID_DISABLED)),
                  NID_DISABLED))))),
        "C2 compressed instruction known?",
        decode_compressed_opcode(SID_INSTRUCTION_ID, c_ir_nid,
          NID_OP_C0, "C0?",
          decode_compressed_addi4spn(SID_INSTRUCTION_ID, c_ir_nid,
            NID_C_ADDI4SPN, "known?",
          decode_compressed_load(SID_INSTRUCTION_ID, c_ir_nid,
            NID_C_LD, NID_C_LW, "known?",
            decode_compressed_store(SID_INSTRUCTION_ID, c_ir_nid,
              NID_C_SD, NID_C_SW, "known?",
              NID_DISABLED))),
          "C0 compressed instruction known?",
          decode_compressed_opcode(SID_INSTRUCTION_ID, c_ir_nid,
            NID_OP_C1, "C1?",
            decode_compressed_imm(SID_INSTRUCTION_ID, c_ir_nid,
              NID_C_LI, NID_C_LUI,
              NID_C_ADDI, NID_C_ADDIW, NID_C_ADDI16SP,
              NID_C_SRLI, NID_C_SRAI, NID_C_ANDI, "known?",
              decode_compressed_op(SID_INSTRUCTION_ID, c_ir_nid,
                NID_C_SUB, NID_C_XOR, NID_C_OR, NID_C_AND,
                NID_C_ADDW, NID_C_SUBW, "known?",
                decode_compressed_branch(SID_INSTRUCTION_ID, c_ir_nid,
                  NID_C_BEQZ, NID_C_BNEZ, "known?",
                  decode_compressed_j(SID_INSTRUCTION_ID, c_ir_nid,
                    NID_C_J, "known?",
                    decode_compressed_jal(SID_INSTRUCTION_ID, c_ir_nid,
                      NID_C_JAL, "known?",
                      NID_DISABLED))))),
            "C1 compressed instruction known?",
            NID_DISABLED)));
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
    return new_binary_boolean(OP_IMPLIES,
      is_compressed_instruction(c_ir_nid),
      decode_compressed_load_with_opcode(SID_BOOLEAN, c_ir_nid,
        is_sized_block_in_stack_segment(get_sp_value_plus_CI64_offset(c_ir_nid, register_file_nid), NID_VIRTUAL_DOUBLE_WORD_SIZE_MINUS_1),
        is_sized_block_in_stack_segment(get_sp_value_plus_CI32_offset(c_ir_nid, register_file_nid), NID_VIRTUAL_SINGLE_WORD_SIZE_MINUS_1),
        is_sized_block_in_main_memory(get_rs1_shift_value_plus_CL64_offset(c_ir_nid, register_file_nid), NID_VIRTUAL_DOUBLE_WORD_SIZE_MINUS_1),
        is_sized_block_in_main_memory(get_rs1_shift_value_plus_CL32_offset(c_ir_nid, register_file_nid), NID_VIRTUAL_SINGLE_WORD_SIZE_MINUS_1),
        "no-seg-faults",
        NID_TRUE,
        NID_TRUE),
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
  uint64_t* register_file_nid, uint64_t* memory_nid, uint64_t* other_register_data_flow_nid) {
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

    rs2_value_nid       = load_register_value(get_compressed_instruction_rs2(c_ir_nid), "compressed rs2 value", register_file_nid);
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
      load_double_word(get_sp_value_plus_CI64_offset(c_ir_nid, register_file_nid), memory_nid), // c.ldsp
      extend_single_word_to_machine_word(OP_SEXT, // c.lwsp
        load_single_word(get_sp_value_plus_CI32_offset(c_ir_nid, register_file_nid), memory_nid)),
      load_double_word(get_rs1_shift_value_plus_CL64_offset(c_ir_nid, register_file_nid), memory_nid), // c.ld
      extend_single_word_to_machine_word(OP_SEXT, // c.lw
        load_single_word(get_rs1_shift_value_plus_CL32_offset(c_ir_nid, register_file_nid), memory_nid)),
      get_pc_value_plus_2(pc_nid), // c.jal
      get_pc_value_plus_2(pc_nid), // c.jalr
      "register data flow",
      NID_MACHINE_WORD_0);

    return new_ternary(OP_ITE, SID_REGISTER_STATE,
      is_compressed_instruction(c_ir_nid),
      new_ternary(OP_ITE, SID_REGISTER_STATE,
        new_binary_boolean(OP_NEQ, rd_nid, NID_ZR, "rd != register zero?"),
        store_register_value(rd_nid, rd_value_nid,
          "compressed instruction rd update", register_file_nid),
        register_file_nid,
        "compressed instruction register data flow"),
      other_register_data_flow_nid,
      "compressed instruction and other register data flow");
  } else
    return other_register_data_flow_nid;
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
    return new_binary_boolean(OP_IMPLIES,
      is_compressed_instruction(c_ir_nid),
      decode_compressed_memory_data_flow(SID_BOOLEAN, c_ir_nid,
        is_sized_block_in_stack_segment(get_sp_value_plus_CSS64_offset(c_ir_nid, register_file_nid), NID_VIRTUAL_DOUBLE_WORD_SIZE_MINUS_1),
        is_sized_block_in_stack_segment(get_sp_value_plus_CSS32_offset(c_ir_nid, register_file_nid), NID_VIRTUAL_SINGLE_WORD_SIZE_MINUS_1),
        is_sized_block_in_main_memory(get_rs1_shift_value_plus_CS64_offset(c_ir_nid, register_file_nid), NID_VIRTUAL_DOUBLE_WORD_SIZE_MINUS_1),
        is_sized_block_in_main_memory(get_rs1_shift_value_plus_CS32_offset(c_ir_nid, register_file_nid), NID_VIRTUAL_SINGLE_WORD_SIZE_MINUS_1),
        "no-seg-faults",
        NID_TRUE),
      "no compressed store and other store segmentation faults");
  else
    return UNUSED;
}

uint64_t* core_compressed_memory_data_flow(uint64_t* c_ir_nid,
  uint64_t* register_file_nid, uint64_t* memory_nid, uint64_t* other_memory_data_flow_nid) {
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
      other_memory_data_flow_nid,
      "compressed instruction and other memory data flow");
  } else
    return other_memory_data_flow_nid;
}

uint64_t* get_pc_value_plus_CB_offset(uint64_t* pc_nid, uint64_t* c_ir_nid) {
  return new_binary(OP_ADD, SID_MACHINE_WORD,
    pc_nid,
    get_compressed_instruction_CB_offset(c_ir_nid),
    "pc value + CB-offset");
}

uint64_t* execute_compressed_branch(uint64_t* pc_nid, uint64_t* c_ir_nid, uint64_t* condition_nid) {
  return new_ternary(OP_ITE, SID_MACHINE_WORD,
    condition_nid,
    get_pc_value_plus_CB_offset(pc_nid, c_ir_nid),
    get_pc_value_plus_2(pc_nid),
    "evaluate compressed branch condition");
}

uint64_t* compressed_branch_control_flow(uint64_t* pc_nid, uint64_t* c_ir_nid, uint64_t* register_file_nid, uint64_t* other_control_flow_nid) {
  uint64_t* rs1_shift_value_nid;

  rs1_shift_value_nid = load_register_value(get_compressed_instruction_rs1_shift(c_ir_nid), "rs1' value", register_file_nid);

  return decode_compressed_branch(SID_MACHINE_WORD, c_ir_nid,
    execute_compressed_branch(pc_nid, c_ir_nid,
      new_binary_boolean(OP_EQ, rs1_shift_value_nid, NID_MACHINE_WORD_0, "rs1' value == 0?")),
    execute_compressed_branch(pc_nid, c_ir_nid,
      new_binary_boolean(OP_NEQ, rs1_shift_value_nid, NID_MACHINE_WORD_0, "rs1' value != 0?")),
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
  set_for(core, state_pc_nids, state_pc_nid);

  if (SYNCHRONIZED_PC)
    if (core > 0)
      return;

  if (core < number_of_binaries)
    initial_pc_nid = new_constant(OP_CONSTH, SID_MACHINE_WORD, get_pc(current_context), 8, "entry pc value");
  else
    initial_pc_nid = new_constant(OP_CONSTH, SID_MACHINE_WORD, code_start, 8, "initial pc value");

  state_pc_nid =
    new_input(OP_STATE, SID_MACHINE_WORD, format_comment("core-%lu-pc", core), "program counter");

  set_for(core, state_pc_nids, state_pc_nid);

  init_pc_nid = new_init(SID_MACHINE_WORD, state_pc_nid, initial_pc_nid, "initial value of pc");

  eval_init(init_pc_nid);
}

void print_core_state(uint64_t core) {
  if (SYNCHRONIZED_PC)
    if (core > 0)
      return;

  print_break_comment_for(core, "program counter");

  print_line(initial_pc_nid);
  print_line(init_pc_nid);
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

  if (core >= number_of_binaries) {
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
  print_segmentation(core);

  print_kernel_state(core);

  print_core_state(core);

  print_register_file_state(core);

  print_code_segment(core);

  print_memory_state(core);

  print_break_comment_line_for(core, "fetch instruction", eval_ir_nid);

  print_break_comment_line_for(core, "fetch compressed instruction", eval_c_ir_nid);

  print_break_comment_line_for(core, "decode instruction", eval_instruction_ID_nid);

  print_break_comment_line_for(core, "decode compressed instruction", eval_compressed_instruction_ID_nid);

  print_break_comment_line_for(core, "instruction control flow", eval_instruction_control_flow_nid);

  print_break_comment_line_for(core, "compressed instruction control flow",
    eval_compressed_instruction_control_flow_nid);

  print_break_comment_line_for(core, "update kernel state", next_program_break_nid);

  print_break_line(next_file_descriptor_nid);

  print_break_line_for(core, next_readable_bytes_nids);

  print_break_line_for(core, next_read_bytes_nids);

  print_break_comment_line_for(core, "kernel and instruction control flow", eval_control_flow_nid);

  print_break_comment_line_for(core, "update program counter", next_pc_nid);

  print_break_comment_line_for(core, "instruction register data flow",
    eval_instruction_register_data_flow_nid);

  print_break_comment_line_for(core, "compressed instruction register data flow",
    eval_compressed_instruction_register_data_flow_nid);

  print_break_comment_line_for(core, "kernel and instruction register data flow",
    eval_register_data_flow_nid);

  print_break_comment_line_for(core, "update register data flow", next_register_file_nid);

  print_break_comment_line_for(core, "instruction memory data flow",
    eval_instruction_memory_data_flow_nid);

  print_break_comment_line_for(core, "compressed instruction memory data flow",
    eval_compressed_instruction_memory_data_flow_nid);

  print_break_comment_line_for(core, "kernel and instruction memory data flow",
    eval_memory_data_flow_nid);

  print_break_comment_line_for(core, "update memory data flow", next_main_memory_nid);

  print_break_comment_for(core, "state properties");

  print_line_for(core, prop_illegal_instruction_nids);

  print_break_line_for(core, prop_illegal_compressed_instruction_nids);

  print_break_line_for(core, prop_is_instruction_known_nids);

  print_break_line_for(core, prop_next_fetch_unaligned_nids);

  print_break_line_for(core, prop_next_fetch_seg_faulting_nids);

  print_break_line_for(core, prop_is_syscall_id_known_nids);

  // optional exit properties

  print_break_line_for(core, prop_bad_exit_code_nids);

  if (core == number_of_cores - 1) {
    print_break_line(prop_exit_codes_nid);

    print_break_line(prop_all_cores_exited_nid);
  }

  // optional arithmetic properties

  print_break_line_for(core, prop_division_by_zero_nids);

  print_break_line_for(core, prop_signed_division_overflow_nids);

  // optional user code segmentation fault checks

  print_break_line_for(core, prop_load_seg_faulting_nids);

  print_break_line_for(core, prop_store_seg_faulting_nids);

  print_break_line_for(core, prop_compressed_load_seg_faulting_nids);

  print_break_line_for(core, prop_compressed_store_seg_faulting_nids);

  print_break_line_for(core, prop_stack_seg_faulting_nids);

  // optional kernel segmentation fault checks

  print_break_line_for(core, prop_brk_seg_faulting_nids);

  print_break_line_for(core, prop_openat_seg_faulting_nids);

  print_break_line_for(core, prop_read_seg_faulting_nids);

  print_break_line_for(core, prop_write_seg_faulting_nids);

  // synchronizing program counters

  print_break_line_for(core, sync_pc_nids);

  // synchronizing register files

  print_break_line_for(core, sync_register_file_nids);

  // synchronizing main memories

  print_break_line_for(core, sync_main_memory_nids);
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

  eval_control_flow_nid = new_ternary(OP_ITE, SID_MACHINE_WORD,
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

  eval_register_data_flow_nid = new_ternary(OP_ITE, SID_REGISTER_STATE,
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

  eval_memory_data_flow_nid = new_ternary(OP_ITE, SID_MEMORY_STATE,
    eval_still_reading_active_read_nid,
    store_byte(new_binary(OP_ADD, SID_MACHINE_WORD,
      a1_value_nid,
      read_bytes_nid,
      "a1 + number of already read_bytes"),
      new_input(OP_INPUT, SID_BYTE, "read-input-byte", "input byte by read system call"),
      memory_nid),
    memory_data_flow_nid,
    "memory data flow");
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

  if (core == number_of_cores - 1)
    next_program_break_nid =
      new_next(SID_VIRTUAL_ADDRESS,
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

  if (core == number_of_cores - 1)
    next_file_descriptor_nid =
      new_next(SID_MACHINE_WORD,
        file_descriptor_nid,
        next_file_descriptor_nid,
        "new file descriptor");

  // update read kernel state

  set_for(core, next_readable_bytes_nids,
    new_next(SID_MACHINE_WORD,
      readable_bytes_nid,
      new_ternary(OP_ITE, SID_MACHINE_WORD,
        still_reading_active_read_nid,
        new_unary(OP_DEC, SID_MACHINE_WORD,
          readable_bytes_nid,
          "decrement readable bytes"),
        readable_bytes_nid,
        "decrement readable bytes if system call is still reading"),
      "readable bytes"));

  set_for(core, next_read_bytes_nids,
    new_next(SID_MACHINE_WORD,
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
      "bytes already read in active read system call"));
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

  uint64_t* equal_a0_values_nid;

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

  set_for(core, prop_is_syscall_id_known_nids, state_property(core,
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
    format_comment("core-%lu unknown syscall ID", core)));

  if (check_seg_faults)
    set_for(core, prop_brk_seg_faulting_nids, state_property(core,
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
      format_comment("core-%lu possible brk segmentation fault", core)));

  // TODO: validate openat arguments other than filename

  if (check_seg_faults)
    set_for(core, prop_openat_seg_faulting_nids, state_property(core,
      UNUSED,
      new_binary_boolean(OP_AND,
        active_openat_nid,
        new_unary_boolean(OP_NOT,
          is_range_in_machine_word_in_heap_segment(a1_value_nid, NID_MAX_STRING_LENGTH),
          "is filename access not in heap segment?"),
        "openat system call filename access may cause segmentation fault"),
      format_comment("core-%lu-openat-seg-fault", core),
      format_comment("core-%lu possible openat segmentation fault", core)));

  // TODO: further validate read arguments

  if (check_seg_faults)
    set_for(core, prop_read_seg_faulting_nids, state_property(core,
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
            is_range_in_machine_word_in_heap_segment(a1_value_nid, a2_value_nid),
            "is read system call access not in heap segment?"),
          "may bytes to be read not be stored in heap segment?"),
        "storing bytes to be read may cause segmentation fault"),
      format_comment("core-%lu-read-seg-fault", core),
      format_comment("core-%lu possible read segmentation fault", core)));

  // TODO: further validate write arguments

  if (check_seg_faults)
    set_for(core, prop_write_seg_faulting_nids, state_property(core,
      UNUSED,
      new_binary_boolean(OP_AND,
        active_write_nid,
          new_binary_boolean(OP_AND,
            new_binary_boolean(OP_UGT, a2_value_nid, NID_MACHINE_WORD_0, "bytes to be written > 0?"),
            new_unary_boolean(OP_NOT,
              is_range_in_machine_word_in_heap_segment(a1_value_nid, a2_value_nid),
              "is write system call access not in heap segment?"),
          "may bytes to be written not be loaded from heap segment?"),
        "loading bytes to be written may cause segmentation fault"),
      format_comment("core-%lu-write-seg-fault", core),
      format_comment("core-%lu possible write segmentation fault", core)));

  if (check_bad_exit_code) {
    prop_bad_exit_code_nid = new_property(OP_BAD,
      new_binary_boolean(OP_AND,
        active_exit_nid,
        new_binary_boolean(OP_EQ,
          a0_value_nid,
          new_constant(OP_CONSTD, SID_MACHINE_WORD,
            bad_exit_code, 0, format_comment("bad exit code %ld", bad_exit_code)),
          "actual exit code == bad exit code?"),
        "active exit system call with bad exit code"),
      format_comment("core-%lu-bad-exit-code", core),
      format_comment("exit(%ld)", bad_exit_code));

    set_for(core, prop_bad_exit_code_nids, prop_bad_exit_code_nid);
  }

  if (check_exit_codes) {
    if (core == 0) {
      prop_active_exits_nid = active_exit_nid;

      prop_exit_codes_nid       = UNUSED;
      prop_all_cores_exited_nid = UNUSED;
    } else {
      prop_active_exits_nid = new_binary_boolean(OP_AND,
        prop_active_exits_nid,
        active_exit_nid,
        format_comment("up to core-%lu active exits?", core));

      equal_a0_values_nid = new_binary_boolean(OP_EQ,
        prop_previous_core_a0_value_nid,
        a0_value_nid,
        format_comment("previous core exit code == core-%lu exit code?", core));

      if (core == 1)
        prop_exit_codes_nid = equal_a0_values_nid;
      else
        prop_exit_codes_nid = new_binary_boolean(OP_AND,
          prop_exit_codes_nid,
          equal_a0_values_nid,
        format_comment("up to core-%lu same exit codes?", core));

      if (core == number_of_cores - 1) {
        prop_exit_codes_nid = state_property(core,
          new_binary_boolean(OP_IMPLIES,
            prop_active_exits_nid,
            prop_exit_codes_nid,
            "all cores should exit with the same exit code"),
          UNUSED,
          "exit-codes",
          "exit codes on all cores");

        if (number_of_binaries < number_of_cores)
          prop_all_cores_exited_nid = new_property(OP_BAD,
            prop_active_exits_nid,
            "all-cores-exited",
            "all cores exited");
      }
    }

    prop_previous_core_a0_value_nid = a0_value_nid;
  }
}

void rotor_combinational(uint64_t core, uint64_t* pc_nid, uint64_t* code_segment_nid, uint64_t* register_file_nid, uint64_t* memory_nid) {
  // fetch instruction

  eval_ir_nid = fetch_instruction(pc_nid, code_segment_nid);

  set_for(core, eval_ir_nids, eval_ir_nid);

  // fetch compressed instruction

  eval_c_ir_nid = fetch_compressed_instruction(pc_nid, code_segment_nid);

  set_for(core, eval_c_ir_nids, eval_c_ir_nid);

  // decode instruction

  eval_instruction_ID_nid = decode_instruction(eval_ir_nid);

  // decode compressed instruction

  eval_compressed_instruction_ID_nid = decode_compressed_instruction(eval_c_ir_nid);

  if (eval_compressed_instruction_ID_nid == UNUSED)
    set_for(core, eval_instruction_ID_nids, eval_instruction_ID_nid);
  else
    set_for(core, eval_instruction_ID_nids, new_ternary(OP_ITE, SID_INSTRUCTION_ID,
      is_compressed_instruction(eval_ir_nid),
      eval_compressed_instruction_ID_nid,
      eval_instruction_ID_nid,
      "is known uncompressed or compressed instruction?"));

  // instruction control flow

  eval_instruction_control_flow_nid =
    core_control_flow(pc_nid, eval_ir_nid, register_file_nid);

  // compressed instruction control flow

  eval_compressed_instruction_control_flow_nid =
    core_compressed_control_flow(pc_nid, eval_c_ir_nid,
      register_file_nid, eval_instruction_control_flow_nid);

  // instruction register data flow

  eval_instruction_register_data_flow_nid =
    core_register_data_flow(pc_nid, eval_ir_nid, register_file_nid, memory_nid);

  // compressed instruction register data flow

  eval_compressed_instruction_register_data_flow_nid =
    core_compressed_register_data_flow(pc_nid, eval_c_ir_nid,
      register_file_nid, memory_nid, eval_instruction_register_data_flow_nid);

  // instruction memory data flow

  eval_instruction_memory_data_flow_nid =
    core_memory_data_flow(eval_ir_nid, register_file_nid, memory_nid);

  // compressed instruction memory data flow

  eval_compressed_instruction_memory_data_flow_nid =
    core_compressed_memory_data_flow(eval_c_ir_nid,
      register_file_nid, memory_nid, eval_instruction_memory_data_flow_nid);
}

void rotor_sequential(uint64_t core, uint64_t* pc_nid, uint64_t* register_file_nid, uint64_t* memory_nid,
  uint64_t* control_flow_nid, uint64_t* register_data_flow_nid, uint64_t* memory_data_flow_nid) {
  uint64_t* sync_pc_nid;
  uint64_t* sync_register_file_nid;
  uint64_t* sync_main_memory_nid;

  // update control flow

  next_pc_nid = UNUSED;
  sync_pc_nid = UNUSED;

  if (SYNCHRONIZED_PC)
    if (core == 0) {
      next_pc_nid = new_next(SID_MACHINE_WORD, pc_nid, control_flow_nid, "program counter");

      eval_core_0_control_flow_nid = control_flow_nid;
    } else
      sync_pc_nid = new_property(OP_CONSTRAINT,
        new_binary_boolean(OP_EQ,
          control_flow_nid,
          eval_core_0_control_flow_nid,
          "new pc value == new core-0 pc value?"),
        format_comment("new-core-%lu-pc-value", core),
        "asserting new pc value == new core-0 pc value");
  else
    next_pc_nid = new_next(SID_MACHINE_WORD, pc_nid, control_flow_nid, "program counter");

  set_for(core, next_pc_nids, next_pc_nid);
  set_for(core, sync_pc_nids, sync_pc_nid);

  // update register data flow

  next_register_file_nid = UNUSED;
  sync_register_file_nid = UNUSED;

  if (SYNCHRONIZED_REGISTERS)
    if (core == 0) {
      next_register_file_nid = new_next(SID_REGISTER_STATE,
        register_file_nid, register_data_flow_nid, "register file");

      eval_core_0_register_data_flow_nid = register_data_flow_nid;
    } else
      sync_register_file_nid = new_property(OP_CONSTRAINT,
        new_binary_boolean(OP_EQ,
          register_data_flow_nid,
          eval_core_0_register_data_flow_nid,
          "new register data flow == new core-0 register data flow?"),
        format_comment("new-core-%lu-register-data-flow", core),
        "asserting new register data flow == new core-0 register data flow");
  else if (SHARED_REGISTERS) {
    if (core < number_of_cores - 1)
      state_register_file_nid = register_data_flow_nid;
    else
      next_register_file_nid = new_next(SID_REGISTER_STATE,
        get_for(0, state_register_file_nids), register_data_flow_nid, "register file");
  } else
    next_register_file_nid = new_next(SID_REGISTER_STATE,
      register_file_nid, register_data_flow_nid, "register file");

  set_for(core, next_register_file_nids, next_register_file_nid);
  set_for(core, sync_register_file_nids, sync_register_file_nid);

  // update memory data flow

  next_main_memory_nid = UNUSED;
  sync_main_memory_nid = UNUSED;

  if (SYNCHRONIZED_MEMORY)
    if (core == 0) {
      next_main_memory_nid = new_next(SID_MEMORY_STATE,
        memory_nid, memory_data_flow_nid, "main memory");

      eval_core_0_memory_data_flow_nid = memory_data_flow_nid;
    } else
      sync_main_memory_nid = new_property(OP_CONSTRAINT,
        new_binary_boolean(OP_EQ,
          memory_data_flow_nid,
          eval_core_0_memory_data_flow_nid,
          "new memory data flow == new core-0 memory data flow?"),
        format_comment("new-core-%lu-memory-data-flow", core),
        "asserting new memory data flow == new core-0 memory data flow");
  else if (SHARED_MEMORY) {
    if (core < number_of_cores - 1)
      state_main_memory_nid = memory_data_flow_nid;
    else
      next_main_memory_nid = new_next(SID_MEMORY_STATE,
        get_for(0, state_main_memory_nids), memory_data_flow_nid, "main memory");
  } else
    next_main_memory_nid = new_next(SID_MEMORY_STATE,
      memory_nid, memory_data_flow_nid, "main memory");

  set_for(core, next_main_memory_nids, next_main_memory_nid);
  set_for(core, sync_main_memory_nids, sync_main_memory_nid);
}

void rotor_properties(uint64_t core, uint64_t* ir_nid, uint64_t* c_ir_nid,
  uint64_t* instruction_ID_nids, uint64_t* control_flow_nid, uint64_t* register_file_nid) {
  // mandatory state properties

  set_for(core, prop_illegal_instruction_nids, state_property(core,
    UNUSED,
    is_illegal_shamt(ir_nid),
    format_comment("core-%lu-illegal-instruction", core),
    format_comment("core-%lu illegal instruction", core)));

  set_for(core, prop_illegal_compressed_instruction_nids, state_property(core,
    UNUSED,
    is_illegal_compressed_instruction_imm_shamt(c_ir_nid),
    format_comment("core-%lu-illegal-compressed-instruction", core),
    format_comment("core-%lu illegal compressed instruction", core)));

  set_for(core, prop_is_instruction_known_nids, state_property(core,
    is_enabled(get_for(core, instruction_ID_nids)),
    UNUSED,
    format_comment("core-%lu-known-instructions", core),
    format_comment("core-%lu known instructions", core)));

  set_for(core, prop_next_fetch_unaligned_nids, state_property(core,
    new_binary_boolean(OP_EQ,
      new_binary(OP_AND, SID_MACHINE_WORD,
        control_flow_nid,
        NID_INSTRUCTION_WORD_SIZE_MASK,
        "next pc alignment"),
      NID_MACHINE_WORD_0,
      "next pc unaligned"),
    UNUSED,
    format_comment("core-%lu-fetch-unaligned", core),
    format_comment("core-%lu imminent unaligned fetch", core)));

  set_for(core, prop_next_fetch_seg_faulting_nids, state_property(core,
    is_address_in_machine_word_in_code_segment(control_flow_nid),
    UNUSED,
    format_comment("core-%lu-fetch-seg-fault", core),
    format_comment("core-%lu imminent fetch segmentation fault", core)));

  // optional arithmetic properties

  if (check_division_by_zero)
    set_for(core, prop_division_by_zero_nids, state_property(core,
      UNUSED,
      is_division_remainder_by_zero(ir_nid, register_file_nid),
      format_comment("core-%lu-division-by-zero", core),
      format_comment("core-%lu division by zero", core)));

  if (check_division_overflow)
    set_for(core, prop_signed_division_overflow_nids, state_property(core,
      UNUSED,
      is_signed_division_remainder_overflow(ir_nid, register_file_nid),
      format_comment("core-%lu-signed-division-overflow", core),
      format_comment("core-%lu signed division overflow", core)));

  // segmentation faults in main memory

  if (check_seg_faults) {
    set_for(core, prop_load_seg_faulting_nids, state_property(core,
      load_no_seg_faults(ir_nid, register_file_nid),
      UNUSED,
      format_comment("core-%lu-load-seg-fault", core),
      format_comment("core-%lu load segmentation fault", core)));

    set_for(core, prop_store_seg_faulting_nids, state_property(core,
      store_no_seg_faults(ir_nid, register_file_nid),
      UNUSED,
      format_comment("core-%lu-store-seg-fault", core),
      format_comment("core-%lu store segmentation fault", core)));

    set_for(core, prop_compressed_load_seg_faulting_nids, state_property(core,
      compressed_load_no_seg_faults(c_ir_nid, register_file_nid),
      UNUSED,
      format_comment("core-%lu-compressed-load-seg-fault", core),
      format_comment("core-%lu compressed load segmentation fault", core)));

    set_for(core, prop_compressed_store_seg_faulting_nids, state_property(core,
      compressed_store_no_seg_faults(c_ir_nid, register_file_nid),
      UNUSED,
      format_comment("core-%lu-compressed-store-seg-fault", core),
      format_comment("core-%lu compressed store segmentation fault", core)));

    // TODO: check stack pointer segfault earlier upon sp update

    set_for(core, prop_stack_seg_faulting_nids, state_property(core,
      is_address_in_machine_word_in_stack_segment(load_register_value(NID_SP, "sp value", register_file_nid)),
      UNUSED,
      format_comment("core-%lu-stack-seg-fault", core),
      format_comment("core-%lu stack segmentation fault", core)));
  }
}

void load_binary(uint64_t binary) {
  if (binary < number_of_binaries) {
    restore_binary(binary);

    reset_interpreter();
    reset_profiler();
    reset_microkernel();

    current_context = create_context(MY_CONTEXT, 0);

    // assert: number_of_remaining_arguments() > 0

    boot_loader(current_context);

    restore_context(current_context);

    // assert: allowances are multiples of word size

    heap_initial_size = get_program_break(current_context) - get_heap_seg_start(current_context);

    if (heap_initial_size > heap_allowance)
      heap_allowance = round_up(heap_initial_size, PAGESIZE);

    heap_start = get_heap_seg_start(current_context);
    heap_size  = heap_allowance;

    stack_initial_size = VIRTUALMEMORYSIZE * GIGABYTE - *(get_regs(current_context) + REG_SP);

    if (stack_initial_size > stack_allowance)
      stack_allowance = round_up(stack_initial_size, PAGESIZE);

    stack_start = VIRTUALMEMORYSIZE * GIGABYTE - stack_allowance;
    stack_size  = stack_allowance;

    // assert: stack_start >= heap_start + heap_size > 0
  } else {
    code_start = 4096;
    code_size  = 7 * 4;

    data_start = 8192;
    data_size  = 0;

    heap_initial_size = 0;

    heap_start = 12288;
    heap_size  = heap_allowance;

    stack_initial_size = 0;

    stack_start = VIRTUALMEMORYSIZE * GIGABYTE - stack_allowance;
    stack_size  = stack_allowance;

    // assert: stack_start >= heap_start + heap_size > 0
  }
}

void model_rotor() {
  uint64_t i;
  uint64_t core;

  w = w
    + dprintf(output_fd, "; %s\n\n", SELFIE_URL)
    + dprintf(output_fd, "; BTOR2 file %s generated by %s\n\n", model_name, selfie_name);
  if (check_bad_exit_code == 0)
    w = w + dprintf(output_fd, "; with %s\n", bad_exit_code_check_option);
  if (check_exit_codes == 0)
    w = w + dprintf(output_fd, "; with %s\n", exit_codes_check_option);
  if (check_division_by_zero == 0)
    w = w + dprintf(output_fd, "; with %s\n", division_by_zero_check_option);
  if (check_division_overflow == 0)
    w = w + dprintf(output_fd, "; with %s\n", division_overflow_check_option);
  if (check_seg_faults == 0)
    w = w + dprintf(output_fd, "; with %s\n", seg_faults_check_option);
  w = w + dprintf(output_fd, "; with %s %lu\n", cores_option, number_of_cores);
  w = w + dprintf(output_fd, "; with %s %lu (%lu-bit virtual address space)\n",
    virtual_address_space_option, VIRTUAL_ADDRESS_SPACE, VIRTUAL_ADDRESS_SPACE);
  w = w + dprintf(output_fd, "; with %s %lu (%lu-bit code words)\n",
    code_word_size_option, CODEWORDSIZEINBITS, CODEWORDSIZEINBITS);
  w = w + dprintf(output_fd, "; with %s %lu (%lu-bit memory words)\n",
    memory_word_size_option, MEMORYWORDSIZEINBITS, MEMORYWORDSIZEINBITS);
  w = w + dprintf(output_fd, "; with %s %lu (%lu bytes initial heap size)\n",
    heap_allowance_option, heap_allowance, heap_initial_size);
  w = w + dprintf(output_fd, "; with %s %lu (%lu bytes initial stack size)\n\n",
    stack_allowance_option, stack_allowance, stack_initial_size);
  i = 0;
  while (i < number_of_binaries) {
    w = w + dprintf(output_fd, "; for RISC-V executable obtained from %s\n",
      get_for(i, binary_names));
    w = w + dprintf(output_fd, "; with %lu bytes of code and %lu bytes of data\n\n",
      get_for(i, code_sizes), get_for(i, data_sizes));
    i = i + 1;
  }
  if (number_of_binaries > 0) {
    w = w + dprintf(output_fd, "; RISC-V code invoked ");
    i = 1;
    if (i < number_of_remaining_arguments()) {
      w = w + dprintf(output_fd, "with console arguments:");
      while (i < number_of_remaining_arguments()) {
        w = w + dprintf(output_fd, " %s", (char*) *(remaining_arguments() + i));
        i = i + 1;
      }
    } else
      w = w + dprintf(output_fd, "without console arguments");
    w = w + dprintf(output_fd, "\n\n");
  }

  init_model();

  init_interface_sorts();
  init_interface_kernel();

  init_register_file_sorts();
  init_memory_sorts(max_code_size);

  print_interface_sorts();
  print_interface_kernel();

  print_register_sorts();
  print_memory_sorts();

  init_kernels(number_of_cores);
  init_register_files(number_of_cores);
  init_memories(number_of_cores);

  init_instruction_mnemonics();
  init_instruction_sorts();
  init_compressed_instruction_sorts();

  init_decoders(number_of_cores);
  init_cores(number_of_cores);

  init_properties(number_of_cores);

  core = 0;

  while (core < number_of_cores) {
    load_binary(core);

    new_segmentation(core);

    new_kernel_state(core, 1);

    new_core_state(core);

    new_register_file_state(core);

    new_code_segment(core);

    new_memory_state(core);

    rotor_combinational(core, state_pc_nid, state_code_segment_nid,
      state_register_file_nid, state_main_memory_nid);
    kernel_combinational(state_pc_nid, eval_ir_nid,
      eval_compressed_instruction_control_flow_nid,
      eval_compressed_instruction_register_data_flow_nid,
      eval_compressed_instruction_memory_data_flow_nid,
      next_program_break_nid, next_file_descriptor_nid,
      state_readable_bytes_nid, state_read_bytes_nid,
      state_register_file_nid, state_main_memory_nid);

    rotor_sequential(core, state_pc_nid,
      state_register_file_nid, state_main_memory_nid,
      eval_control_flow_nid,
      eval_register_data_flow_nid,
      eval_memory_data_flow_nid);
    kernel_sequential(core,
      state_program_break_nid, state_file_descriptor_nid,
      state_readable_bytes_nid, state_read_bytes_nid,
      eval_program_break_nid, eval_file_descriptor_nid,
      eval_still_reading_active_read_nid, eval_more_than_one_readable_byte_to_read_nid,
      eval_ir_nid, state_register_file_nid);

    rotor_properties(core,
      eval_ir_nid, eval_c_ir_nid,
      eval_instruction_ID_nids, eval_control_flow_nid,
      state_register_file_nid);
    kernel_properties(core,
      eval_ir_nid,
      state_read_bytes_nid,
      state_register_file_nid);

    output_model(core);

    core = core + 1;
  }
}

// -----------------------------------------------------------------
// ---------------------------- EMULATOR ---------------------------
// -----------------------------------------------------------------

void save_binary(uint64_t binary) {
  set_for(binary, binary_names, (uint64_t*) binary_name);

  set_for(binary, e_entries, (uint64_t*) e_entry);

  set_for(binary, code_binaries, (uint64_t*) code_binary);
  set_for(binary, data_binaries, (uint64_t*) data_binary);

  set_for(binary, code_starts, (uint64_t*) code_start);
  set_for(binary, code_sizes, (uint64_t*) code_size);
  set_for(binary, data_starts, (uint64_t*) data_start);
  set_for(binary, data_sizes, (uint64_t*) data_size);
}

void restore_binary(uint64_t binary) {
  binary_name = (char*) get_for(binary, binary_names);

  e_entry = (uint64_t) get_for(binary, e_entries);

  code_binary = get_for(binary, code_binaries);
  data_binary = get_for(binary, data_binaries);

  code_start = (uint64_t) get_for(binary, code_starts);
  code_size  = (uint64_t) get_for(binary, code_sizes);
  data_start = (uint64_t) get_for(binary, data_starts);
  data_size  = (uint64_t) get_for(binary, data_sizes);
}

void print_assembly(uint64_t core) {
  uint64_t pc;
  uint64_t ID;
  char* mnemonic;
  uint64_t* ir_nid;
  uint64_t* c_ir_nid;
  char* rd;
  char* rs1;
  char* rs2;
  uint64_t I_imm;
  uint64_t I_imm_32_bit;
  uint64_t shamt;
  uint64_t shamt_5_bit;
  uint64_t S_imm;
  uint64_t SB_imm;
  uint64_t U_imm;
  uint64_t UJ_imm;
  uint64_t imm_shamt;

  pc = eval_line_for(core, state_pc_nids);

  if (number_of_cores > 1)
    printf("core-%lu: ", core);

  printf("0x%lX: ", pc);

  ID = eval_line_for(core, eval_instruction_ID_nids);

  mnemonic = get_instruction_mnemonic(ID);

  ir_nid   = get_for(core, eval_ir_nids);
  c_ir_nid = get_for(core, eval_c_ir_nids);

  if (is_compressed_instruction_ID(ID) == 0) {
    rd  = get_register_name(eval_line(get_instruction_rd(ir_nid)));
    rs1 = get_register_name(eval_line(get_instruction_rs1(ir_nid)));
    rs2 = get_register_name(eval_line(get_instruction_rs2(ir_nid)));

    I_imm        = eval_line(get_instruction_I_immediate(ir_nid));
    I_imm_32_bit = eval_line(get_instruction_I_32_bit_immediate(ir_nid));

    shamt       = eval_line(get_instruction_shamt(ir_nid));
    shamt_5_bit = eval_line(get_instruction_5_bit_shamt(ir_nid));

    S_imm  = eval_line(get_instruction_S_immediate(ir_nid));
    SB_imm = eval_line(get_instruction_SB_immediate(ir_nid));
    U_imm  = eval_line(get_instruction_U_immediate(ir_nid));
    UJ_imm = eval_line(get_instruction_UJ_immediate(ir_nid));
  } else {
    rd  = get_register_name(eval_line(get_compressed_instruction_rd(c_ir_nid)));
    rs1 = get_register_name(eval_line(get_compressed_instruction_rs1(c_ir_nid)));
    rs2 = get_register_name(eval_line(get_compressed_instruction_rs2(c_ir_nid)));

    I_imm        = eval_line(get_compressed_instruction_CI_immediate(c_ir_nid));
    I_imm_32_bit = eval_line(get_compressed_instruction_CI_32_bit_immediate(c_ir_nid));

    shamt = eval_line(get_compressed_instruction_shamt(c_ir_nid));

    SB_imm = eval_line(get_compressed_instruction_CB_offset(c_ir_nid));
    UJ_imm = eval_line(get_compressed_instruction_CJ_offset(c_ir_nid));
    if (is_CR_type(ID)) {
      if (is_jump_CR_type(ID)) {
        if (ID == ID_C_JR)
          rd = get_register_name(REG_ZR);
        else if (ID == ID_C_JALR)
          rd = get_register_name(REG_RA);
        I_imm = 0;
        ID    = ID_JALR;
      } else {
        if (ID == ID_C_MV)
          rs1 = get_register_name(REG_ZR);
        else if (ID == ID_C_ADD)
          rs1 = rd;
        ID = ID_ADD;
      }
    } else if (is_CI_type(ID)) {
      rs1 = rd;
      if (ID == ID_C_LI) {
        rs1 = get_register_name(REG_ZR);
        ID  = ID_ADDI;
      } else if (ID == ID_C_LUI) {
        I_imm = eval_line(get_compressed_instruction_CUI_immediate(c_ir_nid));
        ID    = ID_LUI;
      } else if (ID == ID_C_ADDI)
        ID = ID_ADDI;
      else if (ID == ID_C_ADDIW)
        ID = ID_ADDIW;
      else if (ID == ID_C_ADDI16SP) {
        rd    = get_register_name(REG_SP);
        rs1   = rd;
        I_imm = eval_line(get_compressed_instruction_CI16SP_immediate(c_ir_nid));
        ID    = ID_ADDI;
      } else if (ID == ID_C_ADDI4SPN) {
        rd    = get_register_name(eval_line(get_compressed_instruction_rd_shift(c_ir_nid)));
        rs1   = get_register_name(REG_SP);
        I_imm = eval_line(get_compressed_instruction_CIW_immediate(c_ir_nid));
        ID    = ID_ADDI;
      } else if (ID == ID_C_SLLI)
        ID    = ID_SLLI;
      else {
        rs1 = get_register_name(REG_SP);
        if (ID == ID_C_LWSP) {
          I_imm = eval_line(get_compressed_instruction_CI32_offset(c_ir_nid));
          ID    = ID_LW;
        } else if (ID == ID_C_LDSP) {
          I_imm = eval_line(get_compressed_instruction_CI64_offset(c_ir_nid));
          ID    = ID_LD;
        }
      }
    } else if (is_CL_type(ID)) {
      rd  = get_register_name(eval_line(get_compressed_instruction_rd_shift(c_ir_nid)));
      rs1 = get_register_name(eval_line(get_compressed_instruction_rs1_shift(c_ir_nid)));
      if (ID == ID_C_LW) {
        I_imm = eval_line(get_compressed_instruction_CL32_offset(c_ir_nid));
        ID    = ID_LW;
      } else if (ID == ID_C_LD) {
        I_imm = eval_line(get_compressed_instruction_CL64_offset(c_ir_nid));
        ID    = ID_LD;
      }
    } else if (is_CS_type(ID)) {
      rd  = get_register_name(eval_line(get_compressed_instruction_rs1_shift(c_ir_nid)));
      rs1 = rd;
      rs2 = get_register_name(eval_line(get_compressed_instruction_rs2_shift(c_ir_nid)));
      if (ID == ID_C_SW) {
        S_imm = eval_line(get_compressed_instruction_CS32_offset(c_ir_nid));
        ID    = ID_SW;
      } else if (ID == ID_C_SD) {
        S_imm = eval_line(get_compressed_instruction_CS64_offset(c_ir_nid));
        ID    = ID_SD;
      } else if (is_register_CS_type(ID)) {
        if (ID == ID_C_SUB)
          ID = ID_SUB;
        else if (ID == ID_C_XOR)
          ID = ID_XOR;
        else if (ID == ID_C_OR)
          ID = ID_OR;
        else if (ID == ID_C_AND)
          ID = ID_AND;
        else if (ID == ID_C_ADDW)
          ID = ID_ADDW;
        else if (ID == ID_C_SUBW)
          ID = ID_SUBW;
      } else {
        rs1 = get_register_name(REG_SP);
        rs2 = get_register_name(eval_line(get_compressed_instruction_rs2(c_ir_nid)));
        if (ID == ID_C_SWSP) {
          S_imm = eval_line(get_compressed_instruction_CSS32_offset(c_ir_nid));
          ID    = ID_SW;
        } else if (ID == ID_C_SDSP) {
          S_imm = eval_line(get_compressed_instruction_CSS64_offset(c_ir_nid));
          ID    = ID_SD;
        }
      }
    } else if (is_CB_type(ID)) {
      rd  = get_register_name(eval_line(get_compressed_instruction_rs1_shift(c_ir_nid)));
      rs1 = rd;
      rs2 = get_register_name(REG_ZR);

      I_imm = eval_line(get_compressed_instruction_CB_offset(c_ir_nid));
      if (ID == ID_C_BEQZ)
        ID = ID_BEQ;
      else if (ID == ID_C_BNEZ)
        ID = ID_BNE;
      else if (ID == ID_C_ANDI)
        ID = ID_ANDI;
      else if (ID == ID_C_SRLI)
        ID = ID_C_SRLI;
      else if (ID == ID_C_SRAI)
        ID = ID_SRAI;
    } else if (is_CJ_type(ID)) {
      if (ID == ID_C_J)
        rd = get_register_name(REG_ZR);
      else if (ID == ID_C_JAL)
        rd = get_register_name(REG_RA);
      ID = ID_JAL;
    }
  }

  printf("%s", get_instruction_mnemonic(ID));

  if (is_R_type(ID))
    printf(" %s,%s,%s", rd, rs1, rs2);
  else if (is_I_type(ID)) {
    if (is_shift_I_type(ID))
      if (is_32_bit_shift_I_type(ID)) imm_shamt = shamt_5_bit; else imm_shamt = shamt;
    else
      if (ID == ID_ADDIW) imm_shamt = I_imm_32_bit; else imm_shamt = I_imm;
    if (is_register_relative_I_type(ID))
      printf(" %s,%ld(%s)", rd, imm_shamt, rs1);
    else if (is_shift_I_type(ID))
      printf(" %s,%s,0x%lX", rd, rs1, imm_shamt);
    else
      printf(" %s,%s,%ld", rd, rs1, imm_shamt);
  } else if (is_S_type(ID))
    printf(" %s,%ld(%s)", rs2, S_imm, rs1);
  else if (is_SB_type(ID))
    printf(" %s,%s,0x%lX <%ld>", rs1, rs2, pc + SB_imm,
      signed_division(SB_imm, INSTRUCTIONSIZE));
  else if (is_U_type(ID))
    printf(" %s,0x%lX", rd, U_imm);
  else if (ID == ID_JAL)
    printf(" %s,0x%lX <%ld>", rd, pc + UJ_imm,
      signed_division(UJ_imm, INSTRUCTIONSIZE));

  if (mnemonic != get_instruction_mnemonic(ID))
    printf(" (%s)", mnemonic);
}

void print_multicore_assembly() {
  uint64_t core;

  core = 0;

  while (core < number_of_cores) {
    print_assembly(core);

    core = core + 1;

    if (core < number_of_cores)
      printf("; ");
  }

  printf("\n");
}

uint64_t eval_properties(uint64_t core) {
  uint64_t halt;

  halt = 0;

  // mandatory state properties

  halt = halt + eval_property_for(core, prop_illegal_instruction_nids);
  halt = halt + eval_property_for(core, prop_illegal_compressed_instruction_nids);
  halt = halt + eval_property_for(core, prop_is_instruction_known_nids);
  halt = halt + eval_property_for(core, prop_next_fetch_unaligned_nids);
  halt = halt + eval_property_for(core, prop_next_fetch_seg_faulting_nids);
  halt = halt + eval_property_for(core, prop_is_syscall_id_known_nids);

  // optional exit properties

  halt = halt + eval_property_for(core, prop_bad_exit_code_nids);

  if (core == number_of_cores - 1) {
    // if property is falsified rotor terminates evaluation in current step
    are_exit_codes_different = are_exit_codes_different + eval_property(core, prop_exit_codes_nid);

    // if property is satisfied rotor terminates evaluation in current step
    eval_property(core, prop_all_cores_exited_nid);
  }

  // optional arithmetic properties

  halt = halt + eval_property_for(core, prop_division_by_zero_nids);
  halt = halt + eval_property_for(core, prop_signed_division_overflow_nids);

  // optional user code segmentation fault checks

  halt = halt + eval_property_for(core, prop_load_seg_faulting_nids);
  halt = halt + eval_property_for(core, prop_store_seg_faulting_nids);
  halt = halt + eval_property_for(core, prop_compressed_load_seg_faulting_nids);
  halt = halt + eval_property_for(core, prop_compressed_store_seg_faulting_nids);
  halt = halt + eval_property_for(core, prop_stack_seg_faulting_nids);

  // optional kernel segmentation fault checks

  halt = halt + eval_property_for(core, prop_brk_seg_faulting_nids);
  halt = halt + eval_property_for(core, prop_openat_seg_faulting_nids);
  halt = halt + eval_property_for(core, prop_read_seg_faulting_nids);
  halt = halt + eval_property_for(core, prop_write_seg_faulting_nids);

  // synchronizing program counters

  halt = halt + eval_property_for(core, sync_pc_nids);

  return halt != 0;
}

uint64_t eval_multicore_properties() {
  uint64_t halt;
  uint64_t core;

  halt = 0;

  core = 0;

  while (core < number_of_cores) {
    halt = halt + eval_properties(core);

    core = core + 1;
  }

  return halt != 0;
}

uint64_t eval_sequential(uint64_t core) {
  uint64_t halt;

  halt = 1;

  if (core == number_of_cores - 1) {
    halt = halt * eval_next(next_program_break_nid);
    halt = halt * eval_next(next_file_descriptor_nid);
  }

  halt = halt * eval_next_for(core, next_readable_bytes_nids);
  halt = halt * eval_next_for(core, next_read_bytes_nids);

  halt = halt * eval_next_for(core, next_pc_nids);

  halt = halt * eval_next_for(core, next_register_file_nids);
  halt = halt * eval_next_for(core, next_code_segment_nids);
  halt = halt * eval_next_for(core, next_main_memory_nids);

  return halt != 0;
}

uint64_t eval_multicore_sequential() {
  uint64_t halt;
  uint64_t core;

  halt = 1;

  core = 0;

  while (core < number_of_cores) {
    if (eval_sequential(core)) {
      printf("%s: %s called exit(%lu) on core-%lu @ 0x%lX after %lu steps", selfie_name,
        model_name,
        eval_line(load_register_value(NID_A0, "exit code", get_for(core, state_register_file_nids))),
        core,
        eval_line_for(core, state_pc_nids),
        next_step - current_offset);
      if (any_input) printf(" with input %lu\n", current_input); else printf("\n");
    } else
      halt = 0;

    core = core + 1;
  }

  return halt != 0;
}

void apply_sequential(uint64_t core) {
  if (core == number_of_cores - 1) {
    apply_next(next_program_break_nid);
    apply_next(next_file_descriptor_nid);
  }

  apply_next_for(core, next_readable_bytes_nids);
  apply_next_for(core, next_read_bytes_nids);

  apply_next_for(core, next_pc_nids);

  apply_next_for(core, next_register_file_nids);
  apply_next_for(core, next_code_segment_nids);
  apply_next_for(core, next_main_memory_nids);
}

void apply_multicore_sequential() {
  uint64_t core;

  core = 0;

  while (core < number_of_cores) {
    apply_sequential(core);

    core = core + 1;
  }
}

void save_states(uint64_t core) {
  if (core == number_of_cores - 1) {
    save_state(next_program_break_nid);
    save_state(next_file_descriptor_nid);
  }

  save_state_for(core, next_readable_bytes_nids);
  save_state_for(core, next_read_bytes_nids);

  save_state_for(core, next_pc_nids);

  save_state_for(core, next_register_file_nids);
  save_state_for(core, next_code_segment_nids);
  save_state_for(core, next_main_memory_nids);
}

void save_multicore_states() {
  uint64_t core;

  core = 0;

  while (core < number_of_cores) {
    save_states(core);

    core = core + 1;
  }
}

void restore_states(uint64_t core) {
  if (core == number_of_cores - 1) {
    restore_state(next_program_break_nid);
    restore_state(next_file_descriptor_nid);
  }

  restore_state_for(core, next_readable_bytes_nids);
  restore_state_for(core, next_read_bytes_nids);

  restore_state_for(core, next_pc_nids);

  restore_state_for(core, next_register_file_nids);
  restore_state_for(core, next_code_segment_nids);
  restore_state_for(core, next_main_memory_nids);
}

void restore_multicore_states() {
  uint64_t core;

  core = 0;

  while (core < number_of_cores) {
    restore_states(core);

    core = core + 1;
  }
}

void eval_multicore_states() {
  while (1) {
    if (output_assembly)
      print_multicore_assembly();

    if (eval_multicore_properties())
      return;

    if (eval_multicore_sequential()) {
      if (number_of_cores > 1) {
        printf("%s: %s called exit on all cores after %lu steps", selfie_name,
          model_name, next_step - current_offset);
        if (any_input) printf(" with input %lu\n", current_input); else printf("\n");
      }

      return;
    }

    if (current_step - current_offset >= 100000 - 1) {
      printf("%s: terminating %s after %lu steps", selfie_name,
        model_name, next_step - current_offset);
      if (any_input) printf(" with input %lu\n", current_input); else printf("\n");

      return;
    }

    if (first_input) {
      save_multicore_states();

      first_input = 0;
    }

    apply_multicore_sequential();

    current_step = next_step;

    next_step = next_step + 1;
  }
}

void eval_rotor() {
  if (number_of_binaries == number_of_cores) {
    printf("%s: ********************************************************************************\n", selfie_name);

    current_offset = 0;
    current_step   = 0;

    input_steps   = 0;
    current_input = 0;

    save_multicore_states();

    while (current_input < 256) {
      next_step = next_step + 1;

      first_input = 0;
      any_input   = 0;

      eval_multicore_states();

      if (min_steps > next_step - current_offset) {
        min_steps = next_step - current_offset;

        min_input = current_input;
      }

      if (max_steps < next_step - current_offset) {
        max_steps = next_step - current_offset;

        max_input = current_input;
      }

      if (any_input) {
        restore_multicore_states();

        current_offset = next_step - input_steps;
        current_step   = next_step;

        current_input = current_input + 1;
      } else {
        printf("%s: executed %lu instructions without input\n", selfie_name, max_steps);

        return;
      }
    }

    printf("%s: executed between %lu instructions with input %lu and %lu instructions with input %lu\n", selfie_name,
      min_steps, min_input, max_steps, max_input);

    if (check_exit_codes)
      if (number_of_binaries > 1) {
        if (are_exit_codes_different)
          printf("%s: exit codes are different for some input\n", selfie_name);
        else
          printf("%s: exit codes are equal for all considered inputs\n", selfie_name);
      }
  }
}

void disassemble_rotor(uint64_t core) {
  uint64_t* pc_nid;
  uint64_t* ir_nid;

  if (core < number_of_binaries) {
    printf("%s: ********************************************************************************\n", selfie_name);

    pc_nid = get_for(core, state_pc_nids);

    set_state(pc_nid, code_start);
    set_step(pc_nid, next_step);

    set_step(get_for(core, state_code_segment_nids), next_step);

    ir_nid = get_for(core, eval_ir_nids);

    current_step = next_step;

    while (get_state(pc_nid) < code_start + code_size) {
      next_step = next_step + 1;

      print_assembly(core);
      printf("\n");

      if (eval_line(is_compressed_instruction(ir_nid)))
        set_state(pc_nid, get_state(pc_nid) + 2);
      else
        set_state(pc_nid, get_state(pc_nid) + 4);

      set_step(pc_nid, next_step);

      set_step(get_for(core, state_code_segment_nids), next_step);

      current_step = next_step;
    }
  }
}

uint64_t rotor_arguments() {
  bad_exit_code_check_option = "-Pnobadexitcode";
  exit_codes_check_option    = "-Pnoexitcodes";

  division_by_zero_check_option  = "-Pnodivisionbyzero";
  division_overflow_check_option = "-Pnodivisionoverflow";

  seg_faults_check_option = "-Pnosegfaults";

  cores_option                   = "-cores";
  virtual_address_space_option   = "-virtualaddressspace";
  code_word_size_option          = "-codewordsize";
  memory_word_size_option        = "-memorywordsize";
  heap_allowance_option          = "-heapallowance";
  stack_allowance_option         = "-stackallowance";

  bad_exit_code = atoi(peek_argument(0));

  while (1) {
    if (number_of_remaining_arguments() > 1) {
      if (string_compare(peek_argument(1), "-m")) {
        evaluate_model = 1;

        get_argument();
      } else if (string_compare(peek_argument(1), "-d")) {
        evaluate_model  = 1;
        output_assembly = 1;

        get_argument();
      } else if (string_compare(peek_argument(1), "-s")) {
        disassemble_model = 1;

        get_argument();
      } else if (string_compare(peek_argument(1), "-l")) {
        get_argument();

        if (number_of_remaining_arguments() > 1) {
          if (number_of_binaries < MAX_BINARIES) {
            selfie_load(peek_argument(1));

            save_binary(number_of_binaries);

            number_of_binaries = number_of_binaries + 1;

            if (number_of_binaries > number_of_cores)
              number_of_cores = number_of_binaries;

            if (code_size > max_code_size)
              max_code_size = code_size;

            get_argument();
          } else
          return EXITCODE_BADARGUMENTS;
        } else
          return EXITCODE_BADARGUMENTS;
      } else if (string_compare(peek_argument(1), bad_exit_code_check_option)) {
        check_bad_exit_code = 0;

        get_argument();
      } else if (string_compare(peek_argument(1), exit_codes_check_option)) {
        check_exit_codes = 0;

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
          number_of_cores = atoi(peek_argument(1));

          if (number_of_cores < number_of_binaries)
            number_of_cores = number_of_binaries;

          get_argument();
        } else
          return EXITCODE_BADARGUMENTS;
      } else if (string_compare(peek_argument(1), virtual_address_space_option)) {
        get_argument();

        if (number_of_remaining_arguments() > 1) {
          VIRTUAL_ADDRESS_SPACE = atoi(peek_argument(1));

          get_argument();
        } else
          return EXITCODE_BADARGUMENTS;
      } else if (string_compare(peek_argument(1), code_word_size_option)) {
        get_argument();

        if (number_of_remaining_arguments() > 1) {
          CODEWORDSIZEINBITS = get_power_of_two_size_in_bytes(atoi(peek_argument(1))) * 8;

          get_argument();
        } else
          return EXITCODE_BADARGUMENTS;
      } else if (string_compare(peek_argument(1), memory_word_size_option)) {
        get_argument();

        if (number_of_remaining_arguments() > 1) {
          MEMORYWORDSIZEINBITS = get_power_of_two_size_in_bytes(atoi(peek_argument(1))) * 8;

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

        return EXITCODE_NOERROR;
      } else
        return EXITCODE_BADARGUMENTS;
    } else
      return EXITCODE_NOERROR;
  }
}

uint64_t selfie_model() {
  uint64_t exit_code;

  if (string_compare(argument, "-")) {
    if (number_of_remaining_arguments() > 0) {
      init_binaries();

      if (code_size > 0) {
        save_binary(0);

        number_of_binaries = 1;

        max_code_size = code_size;
      } else {
        number_of_binaries = 0;

        max_code_size = 7 * 4;
      }

      exit_code = rotor_arguments();

      if (exit_code != EXITCODE_NOERROR)
        return exit_code;

      if (number_of_binaries > 0) {
        init_memory(number_of_binaries);

        if (number_of_binaries < number_of_cores)
          model_name = replace_extension((char*) get_for(0, binary_names), "-synthesize", "btor2");
        else
          model_name = replace_extension((char*) get_for(0, binary_names), "-rotorized", "btor2");
      } else {
        if (IS64BITTARGET)
          model_name = "64-bit-riscv-machine-synthesize.btor2";
        else
          model_name = "32-bit-riscv-machine-synthesize.btor2";
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

      model_rotor();

      output_name = (char*) 0;
      output_fd   = 1;

      printf("%s: %lu characters of model formulae written into %s\n", selfie_name, w, model_name);

      if (evaluate_model)
        eval_rotor();

      if (disassemble_model)
        disassemble_rotor(0);

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