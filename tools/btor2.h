/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

BTOR2 is the library shared by rotor and bitr: the model data
structure (lines, sorts, constants, operators, states, properties),
the BTOR2 and SMT-LIB printer, and the concrete evaluator that runs
models step by step on bit vectors and arrays, including the
symbolic status needed for unrolling. Rotor generates models with
it, bitr parses models into it, see projects/reversible.md. Like
selfie.h it is included as library: gcc --include selfie.h
--include tools/btor2.h, or ./selfie -c selfie.h tools/btor2.h ...
*/

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------------     M O D E L     -----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t* allocate_line() {
  return smalloc(7 * sizeof(uint64_t*) + 3 * sizeof(char*) + 5 * sizeof(uint64_t));
}

uint64_t  get_nid(uint64_t* line)      { return *line; }
char*     get_op(uint64_t* line)       { return (char*)     *(line + 1); }
uint64_t* get_sid(uint64_t* line)      { return (uint64_t*) *(line + 2); }
uint64_t* get_arg1(uint64_t* line)     { return (uint64_t*) *(line + 3); }
uint64_t* get_arg2(uint64_t* line)     { return (uint64_t*) *(line + 4); }
uint64_t* get_arg3(uint64_t* line)     { return (uint64_t*) *(line + 5); }
char*     get_comment(uint64_t* line)  { return (char*)     *(line + 6); }
uint64_t* get_symbolic(uint64_t* line) { return (uint64_t*) *(line + 7); }
uint64_t  get_state(uint64_t* line)    { return *(line + 8); }
uint64_t  get_step(uint64_t* line)     { return *(line + 9); }
uint64_t  get_reuse(uint64_t* line)    { return *(line + 10); }
char*     get_prefix(uint64_t* line)   { return (char*) *(line + 11); }
uint64_t  get_sat(uint64_t* line)      { return *(line + 12); }
uint64_t* get_pred(uint64_t* line)     { return (uint64_t*) *(line + 13); }
uint64_t* get_succ(uint64_t* line)     { return (uint64_t*) *(line + 14); }

void set_nid(uint64_t* line, uint64_t nid)       { *line        = nid; }
void set_op(uint64_t* line, char* op)            { *(line + 1)  = (uint64_t) op; }
void set_sid(uint64_t* line, uint64_t* sid)      { *(line + 2)  = (uint64_t) sid; }
void set_arg1(uint64_t* line, uint64_t* arg1)    { *(line + 3)  = (uint64_t) arg1; }
void set_arg2(uint64_t* line, uint64_t* arg2)    { *(line + 4)  = (uint64_t) arg2; }
void set_arg3(uint64_t* line, uint64_t* arg3)    { *(line + 5)  = (uint64_t) arg3; }
void set_comment(uint64_t* line, char* comment)  { *(line + 6)  = (uint64_t) comment; }
void set_symbolic(uint64_t* line, uint64_t* nid) { *(line + 7)  = (uint64_t) nid; }
void set_state(uint64_t* line, uint64_t state)   { *(line + 8)  = state; }
void set_step(uint64_t* line, uint64_t step)     { *(line + 9)  = step; }
void set_reuse(uint64_t* line, uint64_t reuse)   { *(line + 10) = reuse; }
void set_prefix(uint64_t* line, char* prefix)    { *(line + 11) = (uint64_t) prefix; }
void set_sat(uint64_t* line, uint64_t sat)       { *(line + 12) = sat; }
void set_pred(uint64_t* line, uint64_t* pred)    { *(line + 13) = (uint64_t) pred; }
void set_succ(uint64_t* line, uint64_t* succ)    { *(line + 14) = (uint64_t) succ; }

uint64_t* allocate_lines(uint64_t number_of_lines);

uint64_t* get_for(uint64_t core, uint64_t* lines)            { return (uint64_t*) *(lines + core); }
void set_for(uint64_t core, uint64_t* lines, uint64_t* line) { *(lines + core) = (uint64_t) line; }

uint64_t  are_lines_equal(uint64_t* left_line, uint64_t* right_line);
uint64_t* find_equal_line(uint64_t* line);

uint64_t* new_line(char* op, uint64_t* sid, uint64_t* arg1, uint64_t* arg2, uint64_t* arg3, char* comment);

uint64_t* new_bitvec(uint64_t size_in_bits, char* comment);
uint64_t* new_array(uint64_t* size_sid, uint64_t* element_sid, char* comment);

uint64_t* new_constant(char* op, uint64_t* sid, uint64_t constant, char* comment);
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

uint64_t* NONSYMBOLIC = (uint64_t*) 0;
uint64_t* SYMBOLIC    = (uint64_t*) 1;

uint64_t SAT         = 1;
uint64_t SAT_UNKNOWN = 0;

char* BITVEC = (char*) 0;
char* ARRAY  = (char*) 0;

char* OP_SORT = (char*) 0;

char* OP_ZERO = (char*) 0;
char* OP_ONE  = (char*) 0;

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

char* PREFIX_SORT  = (char*) 0;
char* PREFIX_CONST = (char*) 0;
char* PREFIX_INPUT = (char*) 0;
char* PREFIX_EXP   = (char*) 0;
char* PREFIX_EVAL  = (char*) 0;

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

  OP_ZERO = "zero";
  OP_ONE  = "one";

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

  PREFIX_SORT  = "sort";
  PREFIX_CONST = "const";
  PREFIX_INPUT = "input";
  PREFIX_EXP   = "exp";
  PREFIX_EVAL  = "eval";
}

// -----------------------------------------------------------------
// ---------------------------- SYNTAX -----------------------------
// -----------------------------------------------------------------

uint64_t is_bitvector(uint64_t* line);
uint64_t is_array(uint64_t* line);

uint64_t is_constant_op(char* op);
uint64_t is_input_op(char* op);
uint64_t is_unary_op(char* op);
uint64_t is_property_op(char* op);

char* get_smt_op(uint64_t* line);

void declare_fun(uint64_t* line, uint64_t nid, char* type);
void define_fun(uint64_t* line, uint64_t nid, char* type);

uint64_t get_size_in_hex_digits(uint64_t size_in_bits);

void print_nid(uint64_t nid, uint64_t* line);

void print_comment(uint64_t* line);

uint64_t print_sort(uint64_t nid, uint64_t* line);

void print_boolean_and_constd(uint64_t* sid, uint64_t value);
uint64_t print_constant(uint64_t nid, uint64_t* line);

uint64_t print_input(uint64_t nid, uint64_t* line);

uint64_t print_ext(uint64_t nid, uint64_t* line);
uint64_t print_slice(uint64_t nid, uint64_t* line);

uint64_t print_unary_op(uint64_t nid, uint64_t* line);
uint64_t print_binary_op(uint64_t nid, uint64_t* line);
uint64_t print_ternary_op(uint64_t nid, uint64_t* line);

uint64_t has_symbolic_state(uint64_t* line);

uint64_t print_ite(uint64_t nid, uint64_t* line);

uint64_t print_constraint(uint64_t nid, uint64_t* line);

uint64_t print_propagated_constant(uint64_t nid, uint64_t* line);

uint64_t print_line_with_given_nid(uint64_t nid, uint64_t* line);
uint64_t print_line_once(uint64_t nid, uint64_t* line);

void print_line_advancing_nid(uint64_t* line);

void print_line(uint64_t* line);
void print_line_for(uint64_t core, uint64_t* lines);

void print_break();
void print_break_line(uint64_t* line);
void print_break_line_for(uint64_t core, uint64_t* lines);
void print_nobreak_comment(char* comment);
void print_break_comment(char* comment);
void print_nobreak_comment_for(uint64_t core, char* comment);
void print_break_comment_for(uint64_t core, char* comment);
void print_break_comment_line(char* comment, uint64_t* line);
void print_break_comment_line_for(uint64_t core, char* comment, uint64_t* lines);

void print_aligned_break_comment(char* comment, uint64_t alignment);

char* format_comment(char* comment, uint64_t value);

char* format_binary(uint64_t value, uint64_t alignment);
char* format_decimal(uint64_t value);
char* format_hexadecimal(uint64_t value);

char* format_comment_binary(char* comment, uint64_t value);

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t last_nid = 0; // last nid is 0

uint64_t current_nid = 1; // first nid is 1

uint64_t printing_comments             = 1;
uint64_t printing_reuse                = 0;
uint64_t printing_propagated_constants = 1;

uint64_t inputs_are_symbolic = 1; // inputs are always symbolic
uint64_t states_are_symbolic = 0; // states are originally not symbolic unless uninitialized

uint64_t w = 0; // number of written characters

uint64_t printing_only_sat = 0; // print only properties found satisfiable

uint64_t* smt_value_nid = (uint64_t*) 0; // state whose value SMT-LIB check-sat reports, if any

// sorts the evaluator must know: the Boolean sort, and arrays it never copies
// since they are read-only or input; set by the model generator or parser

uint64_t* SID_BOOLEAN = (uint64_t*) 0;

uint64_t* SID_INPUT_BUFFER = (uint64_t*) 0; // uninitialized input, read on demand
uint64_t* SID_CODE_STATE   = (uint64_t*) 0; // read-only code

uint64_t MAX_ARRAY_ADDRESS_SPACE = 32; // largest number of bits in array addresses

// -----------------------------------------------------------------
// -------------------------- SEMANTICS ----------------------------
// -----------------------------------------------------------------

uint64_t eval_bitvec_size(uint64_t* line);

void fit_bitvec_sort(uint64_t* sid, uint64_t value);
void signed_fit_bitvec_sort(uint64_t* sid, uint64_t value);

uint64_t eval_array_size(uint64_t* line);
uint64_t eval_element_size(uint64_t* line);

void fit_array_index_sort(uint64_t* array_sid, uint64_t index);
void fit_array_element_sort(uint64_t* array_sid, uint64_t value);

void match_sorts(uint64_t* sid1, uint64_t* sid2, char* comment);
void match_array_sorts(uint64_t* array_sid, uint64_t* index_sid, uint64_t* value_sid);

uint64_t* allocate_array(uint64_t* sid);

uint64_t read_array_raw(uint64_t* state_nid, uint64_t index);
uint64_t read_array(uint64_t* state_nid, uint64_t index);
void     write_array_raw(uint64_t* state_nid, uint64_t index, uint64_t value);
void     write_array(uint64_t* state_nid, uint64_t index, uint64_t value);

uint64_t is_symbolic_array_element(uint64_t* state_nid, uint64_t index);
void     set_symbolic_array_element(uint64_t* state_nid, uint64_t index, uint64_t is_symbolic);

uint64_t is_bitwise_logical_operator(char* op);
uint64_t is_logical_operator(char *op, uint64_t* sid);
uint64_t is_bitwise_operator(char* op);
uint64_t is_arithmetic_operator(char* op);
uint64_t is_comparison_operator(char* op);
uint64_t is_binary_operator(char* op);

uint64_t bitwise(uint64_t a, uint64_t b, uint64_t and_xor, uint64_t or_xor);
uint64_t bitwise_and(uint64_t a, uint64_t b);
uint64_t bitwise_or(uint64_t a, uint64_t b);
uint64_t bitwise_xor(uint64_t a, uint64_t b);

uint64_t arithmetic_right_shift(uint64_t n, uint64_t b, uint64_t size);
uint64_t signed_less_than_or_equal_to(uint64_t a, uint64_t b);

uint64_t get_cached_state(uint64_t* line);

uint64_t eval_constant_value(uint64_t* line);

uint64_t eval_ext_w(uint64_t* line);

uint64_t eval_slice_u(uint64_t* line);
uint64_t eval_slice_l(uint64_t* line);

uint64_t eval_input(uint64_t* line);

void propagate_symbolic_state(uint64_t* line, uint64_t* arg1, uint64_t* arg2, uint64_t* arg3);

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

uint64_t* memcopy(uint64_t* destination, uint64_t* source, uint64_t bytes);
uint64_t* copy_array(uint64_t* sid, uint64_t* source, uint64_t* destination);

void eval_init(uint64_t* line);

uint64_t eval_next(uint64_t* line);
uint64_t eval_next_for(uint64_t core, uint64_t* lines);
void apply_next(uint64_t* line);
void apply_next_for(uint64_t core, uint64_t* lines);

void save_state(uint64_t* line);
void save_state_for(uint64_t core, uint64_t* lines);
void restore_state(uint64_t* line);
void restore_state_for(uint64_t core, uint64_t* lines);
void reset_state(uint64_t* line);
void reset_state_for(uint64_t core, uint64_t* lines);

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

uint64_t printing_unrolled_model = 0; // indicates if model is unrolled

uint64_t printing_smt = 0; // indicates if targeting SMT-LIB instead of non-sequential BTOR2

uint64_t printing_explicit_constraints = 0;

uint64_t* eval_good_nid = (uint64_t*) 0;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------------     M O D E L     -----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t* allocate_lines(uint64_t number_of_lines) {
  return zmalloc(number_of_lines * sizeof(uint64_t*));
}

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
  set_symbolic(new_line, NONSYMBOLIC);
  set_state(new_line, 0);
  set_step(new_line, UNINITIALIZED);
  set_reuse(new_line, 0);
  set_prefix(new_line, (char*) 0);
  set_sat(new_line, SAT_UNKNOWN);
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

uint64_t* new_constant(char* op, uint64_t* sid, uint64_t constant, char* comment) {
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
  return new_line(OP_INIT, sid, state_nid, value_nid, UNUSED, comment);
}

uint64_t* new_next(uint64_t* sid, uint64_t* state_nid, uint64_t* value_nid, char* comment) {
  return new_line(OP_NEXT, sid, state_nid, value_nid, UNUSED, comment);
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

uint64_t is_property_op(char* op) {
  if (op == OP_BAD)
    return 1;
  else if (op == OP_CONSTRAINT)
    return 1;
  else
    return 0;
}

char* get_smt_op(uint64_t* line) {
  char* op;

  op = get_op(line);

  if (op == OP_SEXT)
    return "sign_extend";
  else if (op == OP_UEXT)
    return "zero_extend";
  else if (op == OP_SLICE)
    return "extract";
  else if (op == OP_NOT)
    return "bvnot";
  else if (op == OP_INC)
    return "bvinc";
  else if (op == OP_DEC)
    return "bvdec";
  else if (op == OP_NEG)
    return "bvneg";
  else if (op == OP_IMPLIES)
    return "=>";
  else if (op == OP_EQ)
    return "=";
  else if (op == OP_NEQ)
    return "distinct";
  else if (op == OP_SGT)
    return "bvsgt";
  else if (op == OP_UGT)
    return "bvugt";
  else if (op == OP_SGTE)
    return "bvsge";
  else if (op == OP_UGTE)
    return "bvuge";
  else if (op == OP_SLT)
    return "bvslt";
  else if (op == OP_ULT)
    return "bvult";
  else if (op == OP_SLTE)
    return "bvsle";
  else if (op == OP_ULTE)
    return "bvule";
  else if (op == OP_AND)
    return "bvand";
  else if (op == OP_OR)
    return "bvor";
  else if (op == OP_XOR)
    return "bvxor";
  else if (op == OP_SLL)
    return "bvshl";
  else if (op == OP_SRL)
    return "bvlshr";
  else if (op == OP_SRA)
    return "bvashr";
  else if (op == OP_ADD)
    return "bvadd";
  else if (op == OP_SUB)
    return "bvsub";
  else if (op == OP_MUL)
    return "bvmul";
  else if (op == OP_SDIV)
    return "bvsdiv";
  else if (op == OP_UDIV)
    return "bvudiv";
  else if (op == OP_SREM)
    return "bvsrem";
  else if (op == OP_UREM)
    return "bvurem";
  else if (op == OP_CONCAT)
    return "concat";
  else if (op == OP_READ)
    return "select";
  else if (op == OP_ITE)
    return "ite";
  else if (op == OP_WRITE)
    return "store";
  else
    return "unknown SMT-LIB operator";
}

void declare_fun(uint64_t* line, uint64_t nid, char* type) {
  set_nid(line, nid);
  set_prefix(line, type);
  w = w + dprintf(output_fd, "(declare-fun %s%lu () %s%lu)",
    get_prefix(line), get_nid(line),
    get_prefix(get_sid(line)), get_nid(get_sid(line)));
}

void define_fun(uint64_t* line, uint64_t nid, char* type) {
  set_nid(line, nid);
  set_prefix(line, type);
  w = w + dprintf(output_fd, "(define-fun %s%lu () %s%lu ",
    get_prefix(line), get_nid(line),
    get_prefix(get_sid(line)), get_nid(get_sid(line)));
}

uint64_t get_size_in_hex_digits(uint64_t size_in_bits) {
  if (size_in_bits % 4 == 0)
    return size_in_bits / 4;
  else
    return size_in_bits / 4 + 1;
}

void print_nid(uint64_t nid, uint64_t* line) {
  set_nid(line, nid);
  w = w + dprintf(output_fd, "%lu", nid);
}

void print_comment(uint64_t* line) {
  if (printing_comments) {
    if (or(get_comment(line) != NOCOMMENT, and(printing_reuse, get_reuse(line) > 0)))
      w = w + dprintf(output_fd, " ;");
    if (get_comment(line) != NOCOMMENT)
      w = w + dprintf(output_fd, " %s", get_comment(line));
    if (and(printing_reuse, get_reuse(line) > 0))
      w = w + dprintf(output_fd, " [reused %lu time(s)]", get_reuse(line));
  }
  w = w + dprintf(output_fd, "\n");
}

uint64_t print_sort(uint64_t nid, uint64_t* line) {
  if (is_array(line)) {
    nid = print_line_once(nid, get_arg2(line));
    nid = print_line_once(nid, get_arg3(line));
  }
  if (printing_smt) {
    set_nid(line, nid);
    set_prefix(line, PREFIX_SORT);
    w = w + dprintf(output_fd, "(define-sort %s%lu () ", get_prefix(line), get_nid(line));
    if (is_bitvector(line)) {
      if (line == SID_BOOLEAN)
        w = w + dprintf(output_fd, "Bool");
      else
        w = w + dprintf(output_fd, "(_ BitVec %lu)", eval_bitvec_size(line));
    } else
      // assert: array
      w = w + dprintf(output_fd, "(Array %s%lu %s%lu)",
        get_prefix(get_arg2(line)), get_nid(get_arg2(line)),
        get_prefix(get_arg3(line)), get_nid(get_arg3(line)));
    w = w + dprintf(output_fd, ")");
  } else {
    print_nid(nid, line);
    w = w + dprintf(output_fd, " %s", OP_SORT);
    if (is_bitvector(line))
      w = w + dprintf(output_fd, " %s %lu", BITVEC, eval_bitvec_size(line));
    else
      // assert: array
      w = w + dprintf(output_fd, " %s %lu %lu", ARRAY, get_nid(get_arg2(line)), get_nid(get_arg3(line)));
  }
  print_comment(line);
  return nid;
}

void print_boolean_and_constd(uint64_t* sid, uint64_t value) {
  if (printing_smt) {
    if (sid == SID_BOOLEAN)
      if (is_true(value)) w = w + dprintf(output_fd, "true"); else w = w + dprintf(output_fd, "false");
    else
      w = w + dprintf(output_fd, "(_ bv%lu %lu)", value, eval_bitvec_size(sid));
  } else {
    if (value == 0)
      w = w + dprintf(output_fd, " %s %lu", OP_ZERO, get_nid(sid));
    else if (value == 1)
      w = w + dprintf(output_fd, " %s %lu", OP_ONE, get_nid(sid));
    else
      w = w + dprintf(output_fd, " %s %lu %ld", OP_CONSTD, get_nid(sid), value);
  }
}

uint64_t print_constant(uint64_t nid, uint64_t* line) {
  uint64_t value;
  uint64_t size;
  nid = print_line_once(nid, get_sid(line));
  value = eval_constant_value(line);
  size = eval_bitvec_size(get_sid(line));
  if (printing_smt) {
    define_fun(line, nid, PREFIX_CONST);
    if (or(get_sid(line) == SID_BOOLEAN, get_op(line) == OP_CONSTD))
      print_boolean_and_constd(get_sid(line), value);
    else if (get_op(line) == OP_CONST)
      w = w + dprintf(output_fd, "#b%s", itoa(value, string_buffer, 2, 0, size));
    else
      // assert: get_op(line) == OP_CONSTH
      w = w + dprintf(output_fd, "#x%s", itoa(value, string_buffer, 16, 0, get_size_in_hex_digits(size)));
    w = w + dprintf(output_fd, ")");
  } else {
    print_nid(nid, line);
    if (get_op(line) == OP_CONSTD)
      print_boolean_and_constd(get_sid(line), value);
    else if (get_op(line) == OP_CONST)
      w = w + dprintf(output_fd, " %s %lu %s", get_op(line), get_nid(get_sid(line)),
        itoa(value, string_buffer, 2, 0, size));
    else
      // assert: get_op(line) == OP_CONSTH
      w = w + dprintf(output_fd, " %s %lu %s", get_op(line), get_nid(get_sid(line)),
        itoa(value, string_buffer, 16, 0, get_size_in_hex_digits(size)));
  }
  print_comment(line);
  return nid;
}

uint64_t print_input(uint64_t nid, uint64_t* line) {
  char* op;
  char* type;
  uint64_t* value_nid;
  op = get_op(line);
  type = PREFIX_INPUT;
  value_nid = (uint64_t*) 0; // avoids uninitialized use warning
  if (printing_unrolled_model) {
    if (op == OP_STATE) {
      if (get_symbolic(line) == SYMBOLIC)
        // replace uninitialized state variable with input
        op = OP_INPUT;
      else {
        // assert: get_symbolic(line) != NONSYMBOLIC
        value_nid = get_arg2(get_symbolic(line));
        if (and(is_array(get_sid(line)), is_bitvector(get_sid(value_nid))))
          // assert: get_op(get_symbolic(line)) == OP_INIT
          type = PREFIX_CONST; // initializing array with bitvector constant (zero)
        else {
          // initializing (init) or assigning (next)
          // bitvector with bitvector constant or
          // array with (non-zero) bitvector constants
          if (get_op(get_symbolic(line)) == OP_INIT) {
            nid = print_line_once(nid, value_nid);
            if (printing_comments)
              w = w + dprintf(output_fd, "; %s done\n", get_comment(get_symbolic(line)));
          } // else: assert: get_op(get_symbolic(line)) == OP_NEXT
          set_nid(line, get_nid(value_nid));
          set_prefix(line, get_prefix(value_nid));
          return nid - 1; // nid is not used
        }
      }
    }
  }
  nid = print_line_once(nid, get_sid(line));
  if (printing_smt)
    declare_fun(line, nid, type);
  else {
    print_nid(nid, line);
    w = w + dprintf(output_fd, " %s %lu %s", op, get_nid(get_sid(line)), (char*) get_arg1(line));
  }
  print_comment(line);
  if (type == PREFIX_CONST) {
    // initializing array with bitvector constant (zero)
    nid = print_line_once(nid + 1, value_nid);
    if (printing_smt) {
      w = w + dprintf(output_fd, "(assert (= %s%lu ((as const %s%lu) %s%lu)))",
        get_prefix(line), get_nid(line),
        get_prefix(get_sid(line)), get_nid(get_sid(line)),
        get_prefix(value_nid), get_nid(value_nid));
      nid = nid - 1; // nid is not used
    } else
      w = w + dprintf(output_fd, "%lu %s %lu %lu %lu",
        nid, OP_INIT, get_nid(get_sid(line)), get_nid(line), get_nid(value_nid));
    print_comment(get_symbolic(line));
  }
  return nid;
}

uint64_t print_ext(uint64_t nid, uint64_t* line) {
  nid = print_line_once(nid, get_sid(line));
  nid = print_line_once(nid, get_arg1(line));
  if (printing_smt) {
    define_fun(line, nid, PREFIX_EXP);
    w = w + dprintf(output_fd, "((_ %s %lu) %s%lu))",
      get_smt_op(line),
      eval_ext_w(line),
      get_prefix(get_arg1(line)), get_nid(get_arg1(line)));
  } else {
    print_nid(nid, line);
    w = w + dprintf(output_fd, " %s %lu %lu %lu",
      get_op(line), get_nid(get_sid(line)), get_nid(get_arg1(line)), eval_ext_w(line));
  }
  print_comment(line);
  return nid;
}

uint64_t print_slice(uint64_t nid, uint64_t* line) {
  nid = print_line_once(nid, get_sid(line));
  nid = print_line_once(nid, get_arg1(line));
  if (printing_smt) {
    define_fun(line, nid, PREFIX_EXP);
    w = w + dprintf(output_fd, "((_ %s %lu %lu) %s%lu))",
      get_smt_op(line),
      eval_slice_u(line),
      eval_slice_l(line),
      get_prefix(get_arg1(line)), get_nid(get_arg1(line)));
  } else {
    print_nid(nid, line);
    w = w + dprintf(output_fd, " %s %lu %lu %lu %lu",
      OP_SLICE, get_nid(get_sid(line)), get_nid(get_arg1(line)), eval_slice_u(line), eval_slice_l(line));
  }
  print_comment(line);
  return nid;
}

uint64_t print_unary_op(uint64_t nid, uint64_t* line) {
  char* op;
  op = get_op(line);
  nid = print_line_once(nid, get_sid(line));
  nid = print_line_once(nid, get_arg1(line));
  if (printing_smt) {
    define_fun(line, nid, PREFIX_EXP);
    if (op == OP_INC)
      // Z3 does not support bvinc
      w = w + dprintf(output_fd, "(bvadd %s%lu (_ bv1 %lu)))",
        get_prefix(get_arg1(line)), get_nid(get_arg1(line)),
        eval_bitvec_size(get_sid(line)));
    else if (op == OP_DEC)
      // Z3 does not support bvdec
      w = w + dprintf(output_fd, "(bvsub %s%lu (_ bv1 %lu)))",
        get_prefix(get_arg1(line)), get_nid(get_arg1(line)),
        eval_bitvec_size(get_sid(line)));
    else {
      if (or(op != OP_NOT, get_sid(line) != SID_BOOLEAN))
        op = get_smt_op(line);
      w = w + dprintf(output_fd, "(%s %s%lu))",
        op, get_prefix(get_arg1(line)), get_nid(get_arg1(line)));
    }
  } else {
    print_nid(nid, line);
    w = w + dprintf(output_fd, " %s %lu %lu",
      op, get_nid(get_sid(line)), get_nid(get_arg1(line)));
  }
  print_comment(line);
  return nid;
}

uint64_t print_binary_op(uint64_t nid, uint64_t* line) {
  nid = print_line_once(nid, get_sid(line));
  nid = print_line_once(nid, get_arg1(line));
  nid = print_line_once(nid, get_arg2(line));
  if (printing_smt) {
    define_fun(line, nid, PREFIX_EXP);
    if (and(or(get_op(line) == OP_AND, or(get_op(line) == OP_OR, get_op(line) == OP_XOR)),
      get_sid(line) == SID_BOOLEAN))
        w = w + dprintf(output_fd, "(%s", get_op(line));
    else
      w = w + dprintf(output_fd, "(%s", get_smt_op(line));
    w = w + dprintf(output_fd, " %s%lu %s%lu))",
      get_prefix(get_arg1(line)), get_nid(get_arg1(line)),
      get_prefix(get_arg2(line)), get_nid(get_arg2(line)));
  } else {
    print_nid(nid, line);
    w = w + dprintf(output_fd, " %s %lu %lu %lu",
      get_op(line), get_nid(get_sid(line)), get_nid(get_arg1(line)), get_nid(get_arg2(line)));
  }
  print_comment(line);
  return nid;
}

uint64_t print_ternary_op(uint64_t nid, uint64_t* line) {
  nid = print_line_once(nid, get_sid(line));
  nid = print_line_once(nid, get_arg1(line));
  nid = print_line_once(nid, get_arg2(line));
  nid = print_line_once(nid, get_arg3(line));
  if (printing_smt) {
    define_fun(line, nid, PREFIX_EXP);
    w = w + dprintf(output_fd, "(%s %s%lu %s%lu %s%lu))",
      get_smt_op(line),
      get_prefix(get_arg1(line)), get_nid(get_arg1(line)),
      get_prefix(get_arg2(line)), get_nid(get_arg2(line)),
      get_prefix(get_arg3(line)), get_nid(get_arg3(line)));
  } else {
    print_nid(nid, line);
    w = w + dprintf(output_fd, " %s %lu %lu %lu %lu",
      get_op(line), get_nid(get_sid(line)), get_nid(get_arg1(line)), get_nid(get_arg2(line)), get_nid(get_arg3(line)));
  }
  print_comment(line);
  return nid;
}

uint64_t has_symbolic_state(uint64_t* line) {
  if (line == UNUSED)
    return 0;
  else if (get_symbolic(line) == SYMBOLIC)
    return 1;
  else if (get_op(line) == OP_INPUT)
    return inputs_are_symbolic;
  else if (get_op(line) == OP_STATE) {
    if (states_are_symbolic)
      return 1;
    else
      // assert: get_symbolic(line) is init or next line
      // assert: get_arg2(get_symbolic(line)) != line
      return has_symbolic_state(get_arg2(get_symbolic(line)));
  } else
    return get_symbolic(line) != NONSYMBOLIC;
}

uint64_t print_ite(uint64_t nid, uint64_t* line) {
  if (printing_propagated_constants)
    if (not(has_symbolic_state(get_arg1(line)))) {
      // conjecture: happens only when printing unrolled model
      if (is_true(get_state(get_arg1(line)))) {
        nid = print_line_once(nid, get_arg2(line));
        set_nid(line, get_nid(get_arg2(line)));
        set_prefix(line, get_prefix(get_arg2(line)));
      } else {
        nid = print_line_once(nid, get_arg3(line));
        set_nid(line, get_nid(get_arg3(line)));
        set_prefix(line, get_prefix(get_arg3(line)));
      }
      if (printing_comments) w = w + dprintf(output_fd, "; %s checked\n", get_comment(line));
      return nid - 1; // nid is not used
    }
  return print_ternary_op(nid, line);
}

uint64_t print_constraint(uint64_t nid, uint64_t* line) {
  nid = print_line_once(nid, get_arg1(line));
  if (printing_smt) {
    if (get_op(line) == OP_BAD) w = w + dprintf(output_fd, "(push 1)\n");
    w = w + dprintf(output_fd, "(assert (= %s%lu true))", get_prefix(get_arg1(line)), get_nid(get_arg1(line)));
    print_comment(line);
    if (get_op(line) == OP_BAD) {
      w = w + dprintf(output_fd, "(check-sat)\n");
      if (smt_value_nid != UNUSED)
        w = w + dprintf(output_fd, "(get-value (%s%lu))\n",
          get_prefix(smt_value_nid), get_nid(smt_value_nid));
      w = w + dprintf(output_fd, "(pop 1)\n");
    }
    return nid - 1; // nid is not used
  } else {
    print_nid(nid, line);
    w = w + dprintf(output_fd, " %s %lu %s", get_op(line), get_nid(get_arg1(line)), (char*) get_arg2(line));
    if (printing_unrolled_model) w = w + dprintf(output_fd, "-%lu", current_step - current_offset);
    print_comment(line);
    return nid;
  }
}

uint64_t print_propagated_constant(uint64_t nid, uint64_t* line) {
  nid = print_line_once(nid, get_sid(line));
  if (printing_smt) {
    define_fun(line, nid, PREFIX_EVAL);
    print_boolean_and_constd(get_sid(line), get_state(line));
    w = w + dprintf(output_fd, ")");
  } else {
    print_nid(nid, line);
    print_boolean_and_constd(get_sid(line), get_state(line));
  }
  if (printing_comments) w = w + dprintf(output_fd, " ; %s propagated", get_comment(line));
  w = w + dprintf(output_fd, "\n");
  return nid;
}

uint64_t print_line_with_given_nid(uint64_t nid, uint64_t* line) {
  char* op;

  op = get_op(line);

  if (op == OP_SORT)
    return print_sort(nid, line);
  else if (is_constant_op(op))
    return print_constant(nid, line);
  else if (is_input_op(op))
    return print_input(nid, line);
  else if (op == OP_WRITE)
    return print_ternary_op(nid, line);
  else if (op == OP_ITE)
    return print_ite(nid, line);
  else if (op == OP_INIT)
    return print_binary_op(nid, line);
  else if (op == OP_NEXT)
    return print_binary_op(nid, line);
  else if (is_property_op(op))
    return print_constraint(nid, line);
  else {
    if (printing_propagated_constants)
      if (not(has_symbolic_state(line)))
        return print_propagated_constant(nid, line);

    if (op == OP_SEXT)
      return print_ext(nid, line);
    else if (op == OP_UEXT)
      return print_ext(nid, line);
    else if (op == OP_SLICE)
      return print_slice(nid, line);
    else if (is_unary_op(op))
      return print_unary_op(nid, line);
    else
      return print_binary_op(nid, line);
  }
}

uint64_t print_line_once(uint64_t nid, uint64_t* line) {
  if (get_nid(line) > last_nid)
    // print lines only once
    return nid;
  else if (get_nid(line) > 0) {
    // assert: only when printing unrolled model
    if (get_step(line) <= current_step)
      // print input, state, and stale lines only once
      return nid;
  }
  return print_line_with_given_nid(nid, line) + 1;
}

void print_line_advancing_nid(uint64_t* line) {
  current_nid = print_line_once(current_nid, line);
}

void print_line(uint64_t* line) {
  if (and(printing_only_sat,
    and(is_property_op(get_op(line)), get_sat(line) == SAT_UNKNOWN))) return;
  if (get_nid(line) > 0) {
    // print lines only once but mention reuse at top level
    w = w + dprintf(output_fd, "; reusing ");
    print_line_with_given_nid(get_nid(line), line);
  } else
    print_line_advancing_nid(line);
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
    if (and(printing_only_sat,
      and(is_property_op(get_op(line)), get_sat(line) == SAT_UNKNOWN))) return;
    print_break();
    print_line(line);
  }
}

void print_break_line_for(uint64_t core, uint64_t* lines) {
  print_break_line(get_for(core, lines));
}

void print_nobreak_comment(char* comment) {
  w = w + dprintf(output_fd, "\n; %s\n", comment);
}

void print_break_comment(char* comment) {
  print_nobreak_comment(comment);
  print_break();
}

void print_nobreak_comment_for(uint64_t core, char* comment) {
  w = w + dprintf(output_fd, "\n; core-%lu %s\n", core, comment);
}

void print_break_comment_for(uint64_t core, char* comment) {
  print_nobreak_comment_for(core, comment);
  print_break();
}

void print_break_comment_line(char* comment, uint64_t* line) {
  if (line != UNUSED) {
    print_break_comment(comment);
    print_line(line);
  }
}

void print_break_comment_line_for(uint64_t core, char* comment, uint64_t* lines) {
  if (get_for(core, lines) != UNUSED) {
    print_break_comment_for(core, comment);
    print_line(get_for(core, lines));
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

    if (get_step(line) == INITIALIZED)
      return size;
    else
      set_step(line, INITIALIZED);

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

    if (get_step(line) == INITIALIZED)
      return size;
    else
      set_step(line, INITIALIZED);

    if (size <= MAX_ARRAY_ADDRESS_SPACE)
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

    if (get_step(line) == INITIALIZED)
      return size;
    else
      set_step(line, INITIALIZED);

    if (size <= SIZEOFUINT64INBITS)
      return size;

    printf("%s: unsupported %lu-bit array element size error\n", selfie_name, size);
  } else
    printf("%s: evaluate element size of non-array error\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

void fit_array_index_sort(uint64_t* array_sid, uint64_t index) {
  if (is_array(array_sid)) {
    fit_bitvec_sort(get_arg2(array_sid), index);

    return;
  }

  printf("%s: non-array access @ 0x%lX index error\n", selfie_name, index);

  exit(EXITCODE_SYSTEMERROR);
}

void fit_array_element_sort(uint64_t* array_sid, uint64_t value) {
  if (is_array(array_sid)) {
    fit_bitvec_sort(get_arg3(array_sid), value);

    return;
  }

  printf("%s: non-array access with %lu value error\n", selfie_name, value);

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

uint64_t* allocate_array(uint64_t* sid) {
  // assert: element size of array <= sizeof(uint64_t)
  // allocate space for array as well as symbolic status of array elements
  return zmalloc(2 * two_to_the_power_of(eval_array_size(sid)) * sizeof(uint64_t));
}

uint64_t read_array_raw(uint64_t* state_nid, uint64_t index) {
  uint64_t* array;

  array = (uint64_t*) get_state(state_nid);

  if (array != (uint64_t*) 0) return *(array + index);

  printf("%s: reading from uninitialized state error\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t read_array(uint64_t* state_nid, uint64_t index) {
  uint64_t value;

  fit_array_index_sort(get_sid(state_nid), index);

  value = read_array_raw(state_nid, index);

  fit_array_element_sort(get_sid(state_nid), value);

  return value;
}

void write_array_raw(uint64_t* state_nid, uint64_t index, uint64_t value) {
  uint64_t* array;

  array = (uint64_t*) get_state(state_nid);

  if (array != (uint64_t*) 0) {
    // TODO: log writes and only apply with init and next
    *(array + index) = value;

    return;
  }

  printf("%s: writing to uninitialized state error\n", selfie_name);

  exit(EXITCODE_SYSTEMERROR);
}

void write_array(uint64_t* state_nid, uint64_t index, uint64_t value) {
  fit_array_index_sort(get_sid(state_nid), index);
  fit_array_element_sort(get_sid(state_nid), value);

  write_array_raw(state_nid, index, value);
}

uint64_t is_symbolic_array_element(uint64_t* state_nid, uint64_t index) {
  return is_true(read_array_raw(state_nid,
    index + two_to_the_power_of(eval_array_size(get_sid(state_nid)))));
}

void set_symbolic_array_element(uint64_t* state_nid, uint64_t index, uint64_t is_symbolic) {
  write_array_raw(state_nid,
    index + two_to_the_power_of(eval_array_size(get_sid(state_nid))),
    is_symbolic);
}

uint64_t is_bitwise_logical_operator(char* op) {
  if (op == OP_AND)
    return 1;
  else if (op == OP_OR)
    return 1;
  else if (op == OP_XOR)
    return 1;
  else
    return 0;
}

uint64_t is_logical_operator(char *op, uint64_t* sid) {
  if (op == OP_IMPLIES)
    return 1;
  else if (sid == SID_BOOLEAN)
    if (is_bitwise_logical_operator(op))
      return 1;

  return 0;
}

uint64_t is_bitwise_operator(char* op) {
  if (is_bitwise_logical_operator(op))
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

uint64_t is_binary_operator(char* op) {
  if (is_logical_operator(op, SID_BOOLEAN))
    return 1;
  else if (is_bitwise_operator(op))
    return 1;
  else if (is_arithmetic_operator(op))
    return 1;
  else if (is_comparison_operator(op))
    return 1;
  else
    return 0;
}

uint64_t bitwise(uint64_t a, uint64_t b, uint64_t and_xor, uint64_t or_xor) {
  uint64_t r;
  uint64_t i;

  if (a == b) {
    if (and_xor)
      if (or_xor)
        // exclusive or of equal operands
        return 0;

    return a;
  } else if (a < b)
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
      if (is_bitvector(get_sid(line))) {
        if (get_step(line) == current_step)
          return get_state(line);
      } else {
        // assert: array
        if (get_step(line) <= next_step)
          // TODO: log writes and only apply with init and next
          return (uint64_t) line;
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

    set_step(line, INITIALIZED);
  } else
    value = get_state(line);

  return value;
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
      input_steps = current_step - current_offset;

    set_state(line, current_input);
    set_step(line, next_step);

    if (not(any_input))
      first_input = 1;

    any_input = 1;

    return get_state(line);
  }

  printf("%s: unknown model operator %s\n", selfie_name, op);

  exit(EXITCODE_SYSTEMERROR);
}

void propagate_symbolic_state(uint64_t* line, uint64_t* arg1, uint64_t* arg2, uint64_t* arg3) {
  if (or(has_symbolic_state(arg1), or(has_symbolic_state(arg2), has_symbolic_state(arg3))))
    set_symbolic(line, SYMBOLIC);
  else
    set_symbolic(line, NONSYMBOLIC);
}

uint64_t eval_ext(uint64_t* line) {
  uint64_t* value_nid;
  uint64_t n;
  uint64_t w;
  uint64_t value;

  value_nid = get_arg1(line);

  n = eval_bitvec_size(get_sid(value_nid));

  w = eval_ext_w(line);

  if (eval_bitvec_size(get_sid(line)) == n + w) {
    value = eval_line(value_nid);

    if (n + w <= WORDSIZEINBITS)
      if (get_op(line) == OP_SEXT)
        set_state(line, sign_shrink(sign_extend(value, n), n + w));
      else
        // assert: unsigned extension
        set_state(line, value);
    else if (has_symbolic_state(value_nid))
      set_state(line, 0);
    else {
      // TODO: support of non-symbolic double machine words
      printf("%s: ext unsupported sort error: n==%lu, w==%lu\n", selfie_name, n, w);

      exit(EXITCODE_SYSTEMERROR);
    }

    propagate_symbolic_state(line, value_nid, NONSYMBOLIC, NONSYMBOLIC);

    set_step(line, next_step);

    return get_state(line);
  }

  printf("%s: ext sort mismatch error: n==%lu, w==%lu, m==%lu\n", selfie_name,
    n, w, eval_bitvec_size(get_sid(line)));

  exit(EXITCODE_SYSTEMERROR);
}

uint64_t eval_slice(uint64_t* line) {
  uint64_t* value_nid;
  uint64_t n;
  uint64_t u;
  uint64_t l;
  uint64_t value;

  value_nid = get_arg1(line);

  n = eval_bitvec_size(get_sid(value_nid));

  u = eval_slice_u(line);
  l = eval_slice_l(line);

  if (n > u)
    if (u >= l)
      if (eval_bitvec_size(get_sid(line)) == u - l + 1) {
        value = eval_line(value_nid);

        if (u < WORDSIZEINBITS)
          set_state(line, get_bits(value, l, u - l + 1));
        else if (has_symbolic_state(value_nid))
          set_state(line, 0);
        else {
          // TODO: support of non-symbolic double machine words
          printf("%s: slice unsupported sort error: n==%lu, u==%lu, l==%lu\n", selfie_name, n, u, l);

          exit(EXITCODE_SYSTEMERROR);
        }

        propagate_symbolic_state(line, value_nid, NONSYMBOLIC, NONSYMBOLIC);

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

  if (size <= WORDSIZEINBITS)
    //  TODO: support of non-symbolic double machine words
    if (size == left_size + right_size) {
      left_value  = eval_line(left_nid);
      right_value = eval_line(right_nid);

      set_state(line, left_shift(left_value, right_size) + right_value);

      propagate_symbolic_state(line, left_nid, right_nid, NONSYMBOLIC);

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

  if (eval_line(if_nid)) {
    set_state(line, eval_line(then_nid));

    if (has_symbolic_state(if_nid))
      eval_line(else_nid);
    else
      // lazy propagation of (unevaluated) symbolic value
      else_nid = UNUSED;
  } else {
    if (has_symbolic_state(if_nid))
      eval_line(then_nid);
    else
      // lazy propagation of (unevaluated) symbolic value
      then_nid = UNUSED;

    set_state(line, eval_line(else_nid));
  }

  propagate_symbolic_state(line, if_nid, then_nid, else_nid);

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
      // TODO: non-symbolic read after unrelated non-symbolic write is not detected
      if (get_step(state_nid) <= next_step) {
        index = eval_line(index_nid);

        propagate_symbolic_state(line, state_nid, index_nid, NONSYMBOLIC);

        if (get_sid(state_nid) != SID_INPUT_BUFFER) {
          // avoids reading illegal instruction from uninitialized code segment
          set_state(line, 1);

          if (not(has_symbolic_state(line))) {
            if (is_symbolic_array_element(state_nid, index))
              set_symbolic(line, SYMBOLIC);
            else
              // TODO: non-symbolic read after unrelated non-symbolic write may be incorrect
              set_state(line, read_array(state_nid, index));
          }
        } else {
          // input buffer is uninitialized, generate input
          if (input_steps == 0)
            // TODO: input is consumed more than once
            input_steps = current_step - current_offset;

          set_state(line, current_input);

          if (not(any_input))
            first_input = 1;

          any_input = 1;
        }

        set_step(line, next_step);

        return get_state(line);
      } else
        printf("%s: read updated state error\n", selfie_name);
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

          propagate_symbolic_state(line, state_nid, index_nid, NONSYMBOLIC);

          if (not(has_symbolic_state(line))) {
            if (has_symbolic_state(value_nid))
              set_symbolic_array_element(state_nid, index, 1);
            else {
              set_symbolic_array_element(state_nid, index, 0);

              write_array(state_nid, index, value);
            }
          }

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

    propagate_symbolic_state(line, value_nid, NONSYMBOLIC, NONSYMBOLIC);

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
  uint64_t* sid;
  uint64_t left_value;
  uint64_t right_value;
  uint64_t size;

  op = get_op(line);

  if (not(is_binary_operator(op))) {
    // else case exceeds selfie's branch limit
    printf("%s: unknown binary operator %s\n", selfie_name, op);

    exit(EXITCODE_SYSTEMERROR);
  }

  left_nid  = get_arg1(line);
  right_nid = get_arg2(line);

  match_sorts(get_sid(left_nid), get_sid(right_nid), "left and right operand");

  sid = get_sid(line);

  if (is_logical_operator(op, sid)) {
    match_sorts(get_sid(left_nid), SID_BOOLEAN, "logical operator");

    left_value = eval_line(left_nid);

    if (op == OP_IMPLIES) {
      if (not(left_value)) {
        set_state(line, 1);

        if (has_symbolic_state(left_nid))
          right_value = eval_line(right_nid);
        else
          // lazy evaluation of right operand and
          // lazy propagation of (unevaluated) symbolic value
          right_nid = UNUSED;
      } else {
        right_value = eval_line(right_nid);

        set_state(line, is_true(right_value));
      }
    } else {
      right_value = eval_line(right_nid);

      if (op == OP_AND) {
        set_state(line, and(left_value, right_value));

        if (not(has_symbolic_state(left_nid)))
          if (not(left_value))
            // lazy propagation of symbolic value
            right_nid = UNUSED;

        if (not(has_symbolic_state(right_nid)))
          if (not(right_value))
            // lazy propagation of symbolic value
            left_nid = UNUSED;
      } else if (op == OP_OR) {
        set_state(line, or(left_value, right_value));

        if (not(has_symbolic_state(left_nid)))
          if (is_true(left_value))
            // lazy propagation of symbolic value
            right_nid = UNUSED;

        if (not(has_symbolic_state(right_nid)))
          if (is_true(right_value))
            // lazy propagation of symbolic value
            left_nid = UNUSED;
      } else if (op == OP_XOR)
        set_state(line, xor(left_value, right_value));
    }
  } else {
    left_value  = eval_line(left_nid);
    right_value = eval_line(right_nid);

    size = eval_bitvec_size(get_sid(left_nid));

    if (is_bitwise_operator(op)) {
      match_sorts(sid, get_sid(left_nid), "bitwise operator");

      if (op == OP_AND)
        set_state(line, bitwise_and(left_value, right_value));
      else if (op == OP_OR)
        set_state(line, bitwise_or(left_value, right_value));
      else if (op == OP_XOR)
        set_state(line, bitwise_xor(left_value, right_value));
      else if (right_value < SIZEOFUINT64INBITS) {
        if (op == OP_SLL)
          set_state(line, sign_shrink(left_shift(left_value, right_value), size));
        else if (op == OP_SRL)
          set_state(line, right_shift(left_value, right_value));
        else if (op == OP_SRA)
          set_state(line, arithmetic_right_shift(left_value, right_value, size));
      } else if (or(has_symbolic_state(left_nid), has_symbolic_state(right_nid)))
        set_state(line, 0);
      else {
        printf("%s: non-symbolic %s by %lu bits\n", selfie_name, op, right_value);

        exit(EXITCODE_SYSTEMERROR);
      }
    } else if (is_arithmetic_operator(op)) {
      match_sorts(sid, get_sid(left_nid), "arithmetic operator");

      if (op == OP_ADD)
        set_state(line, sign_shrink(left_value + right_value, size));
      else if (op == OP_SUB)
        set_state(line, sign_shrink(left_value - right_value, size));
      else if (op == OP_MUL)
        set_state(line, sign_shrink(left_value * right_value, size));
      else if (right_value != 0) {
        if (op == OP_UDIV)
          set_state(line, left_value / right_value);
        else if (op == OP_UREM)
          set_state(line, left_value % right_value);
        else {
          left_value  = sign_extend(left_value, size);
          right_value = sign_extend(right_value, size);

          if (or(left_value != INT64_MIN, right_value != (uint64_t) -1)) {
            if (op == OP_SDIV)
              set_state(line, sign_shrink(signed_division(left_value, right_value), size));
            else if (op == OP_SREM)
              set_state(line,
                sign_shrink(left_value - signed_division(left_value, right_value) * right_value, size));
          } else if (or(has_symbolic_state(left_nid), has_symbolic_state(right_nid)))
            set_state(line, 0);
          else {
            printf("%s: non-symbolic %s overflow\n", selfie_name, op);

            exit(EXITCODE_SYSTEMERROR);
          }
        }
      } else if (or(has_symbolic_state(left_nid), has_symbolic_state(right_nid)))
        set_state(line, 0);
      else {
        printf("%s: non-symbolic %s by zero\n", selfie_name, op);

        exit(EXITCODE_SYSTEMERROR);
      }
    } else if (is_comparison_operator(op)) {
      match_sorts(sid, SID_BOOLEAN, "comparison operator");

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

  fit_bitvec_sort(sid, get_state(line));

  propagate_symbolic_state(line, left_nid, right_nid, NONSYMBOLIC);

  set_step(line, next_step);

  return get_state(line);
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

uint64_t* copy_array(uint64_t* sid, uint64_t* source, uint64_t* destination) {
  // copy array as well as symbolic status of array elements
  return memcopy(destination, source, 2 * two_to_the_power_of(eval_array_size(sid)) * sizeof(uint64_t));
}

void eval_init(uint64_t* line) {
  uint64_t* state_nid;
  uint64_t* state_sid;
  uint64_t* value_nid;
  uint64_t* source;
  uint64_t* destination;

  if (get_op(line) == OP_INIT)
    if (current_step == INITIALIZED)
      if (current_step == next_step) {
        if (get_step(line) == UNINITIALIZED) {
          state_nid = get_arg1(line);

          state_sid = get_sid(state_nid);

          if (get_op(state_nid) == OP_STATE) {
            if (get_step(state_nid) == UNINITIALIZED) {
              match_sorts(get_sid(line), state_sid, "init state");

              value_nid = get_arg2(line);

              if (is_bitvector(state_sid)) {
                match_sorts(state_sid, get_sid(value_nid), "init bitvector");

                set_state(state_nid, eval_line(value_nid));
                set_state(line, get_state(state_nid));
              } else {
                // assert: sid of state line is ARRAY
                if (is_bitvector(get_sid(value_nid))) {
                  match_sorts(get_arg3(state_sid), get_sid(value_nid), "init array element");

                  if (eval_line(value_nid) != 0) {
                    printf("%s: init non-zero array element error\n", selfie_name);

                    exit(EXITCODE_SYSTEMERROR);
                  }

                  set_state(state_nid, (uint64_t) allocate_array(state_sid));
                  set_state(line, (uint64_t) allocate_array(state_sid));
                } else {
                  // assert: sid of value line is ARRAY
                  match_sorts(state_sid, get_sid(value_nid), "init array");

                  value_nid = (uint64_t*) eval_line(value_nid);

                  if (get_state(state_nid) != get_state(value_nid)) {
                    set_state(state_nid, get_state(value_nid));
                    set_state(line, get_state(state_nid));

                    if (state_sid != SID_INPUT_BUFFER)
                      if (state_sid != SID_CODE_STATE) {
                        set_state(line, (uint64_t) allocate_array(state_sid));

                        source      = (uint64_t*) get_state(state_nid);
                        destination = (uint64_t*) get_state(line);

                        copy_array(state_sid, source, destination);
                      }

                    // TODO: reinitialize value state
                    set_state(value_nid, 0);
                  } else {
                    printf("%s: init reinitializing array error\n", selfie_name);

                    exit(EXITCODE_SYSTEMERROR);
                  }
                }
              }

              // state is only symbolic if the initial value is symbolic
              set_symbolic(state_nid, line);

              set_step(state_nid, INITIALIZED);
              set_step(line, INITIALIZED);

              return;
            } else
              printf("%s: init reinitializing state error\n", selfie_name);
          } else
            printf("%s: init %s error\n", selfie_name, get_op(state_nid));
        } else
          printf("%s: init reinitializing init error\n", selfie_name);

        exit(EXITCODE_SYSTEMERROR);
      }

  printf("%s: init error: %s\n", selfie_name, get_comment(line));

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
            if (get_step(state_nid) != UNINITIALIZED)
              if (get_step(state_nid) <= current_step) {
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

                // value_nid could have been altered above
                value_nid = get_arg2(line);

                if (state_nid != value_nid) {
                  if (printing_unrolled_model) {
                    w = w + dprintf(output_fd, "; next-start-%lu: %s\n\n", current_step - current_offset, get_comment(line));
                    print_line_advancing_nid(value_nid);
                    w = w + dprintf(output_fd, "\n; next-end-%lu: %s\n\n", current_step - current_offset, get_comment(line));
                  }

                  if (has_symbolic_state(value_nid))
                    return 0;
                }

                return no_update;
              } else
                printf("%s: next updated state error\n", selfie_name);
            else
              printf("%s: next uninitialized state error\n", selfie_name);
          } else
            printf("%s: next %s error\n", selfie_name, get_op(state_nid));

          exit(EXITCODE_SYSTEMERROR);
        }
      }

  printf("%s: next error: %s\n", selfie_name, get_comment(line));

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
    value_nid = get_arg2(line);

    if (is_bitvector(get_sid(state_nid)))
      set_state(state_nid, get_state(value_nid));
    // TODO: else log writes and only apply with init and next

    if (state_nid != value_nid) {
      // state is only symbolic if the next value is symbolic
      set_symbolic(state_nid, line);

      set_step(state_nid, next_step);

      if (printing_unrolled_model) {
        set_nid(state_nid, get_nid(value_nid));
        set_prefix(state_nid, get_prefix(value_nid));
      }
    } // else: symbolic state remains unchanged

    return;
  }

  printf("%s: apply error: %s\n", selfie_name, get_comment(line));

  exit(EXITCODE_SYSTEMERROR);
}

void apply_next_for(uint64_t core, uint64_t* lines) {
  if (get_for(core, lines) == UNUSED)
    return;
  else
    apply_next(get_for(core, lines));
}

void save_state(uint64_t* line) {
  uint64_t* state_nid;
  uint64_t* sid;
  uint64_t state;
  uint64_t* source;
  uint64_t* destination;

  // assert: next line
  state_nid = get_arg1(line);

  sid   = get_sid(state_nid);
  state = get_state(state_nid);

  if (is_bitvector(sid))
    set_state(line, state);
  else if (sid != SID_INPUT_BUFFER)
    if (sid != SID_CODE_STATE) {
      // assert: array
      source      = (uint64_t*) state;
      destination = (uint64_t*) get_state(line);

      if (destination == (uint64_t*) 0) {
        destination = allocate_array(sid);

        set_state(line, (uint64_t) destination);
      }

      copy_array(sid, source, destination);
    }

  set_symbolic(line, get_symbolic(state_nid));
}

void save_state_for(uint64_t core, uint64_t* lines) {
  if (get_for(core, lines) == UNUSED)
    return;
  else
    save_state(get_for(core, lines));
}

void restore_state(uint64_t* line) {
  uint64_t* state_nid;
  uint64_t* sid;
  uint64_t current_state;

  // assert: next line
  state_nid = get_arg1(line);

  sid = get_sid(state_nid);

  if (sid != SID_INPUT_BUFFER)
    if (sid != SID_CODE_STATE) {
      current_state = get_state(state_nid);

      set_state(state_nid, get_state(line));

      // keep current state to avoid reallocating arrays
      set_state(line, current_state);
    }

  set_symbolic(state_nid, get_symbolic(line));

  set_step(state_nid, next_step);

  set_step(line, next_step);
}

void restore_state_for(uint64_t core, uint64_t* lines) {
  if (get_for(core, lines) == UNUSED)
    return;
  else
    restore_state(get_for(core, lines));
}

void reset_state(uint64_t* line) {
  uint64_t* state_nid;
  uint64_t* sid;
  uint64_t state;
  uint64_t* source;
  uint64_t* destination;

  // assert: init line
  state_nid = get_arg1(line);

  sid = get_sid(state_nid);

  state = get_state(line);

  if (is_bitvector(sid))
    set_state(state_nid, state);
  else if (sid != SID_INPUT_BUFFER)
    if (sid != SID_CODE_STATE) {
      // assert: array
      source      = (uint64_t*) state;
      destination = (uint64_t*) get_state(state_nid);

      copy_array(sid, source, destination);
    }

  // state is only symbolic if the initial value is symbolic
  set_symbolic(state_nid, line);

  set_step(state_nid, next_step);
}

void reset_state_for(uint64_t core, uint64_t* lines) {
  if (get_for(core, lines) == UNUSED)
    return;
  else
    reset_state(get_for(core, lines));
}
