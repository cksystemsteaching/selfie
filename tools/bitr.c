/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

Bitr is a bounded model checker for BTOR2 models in C*, built up in
layers, see projects/reversible.md. It reads BTOR2 and nothing else:
models come from rotor or cellfie, programs and input enter only as
initial state through its loaders. This is the first layer (M4): a
parser for the BTOR2 subset rotor emits, loaders that put an ELF
binary into the code and data segments and a file onto the input
tape of a model, and a concrete simulator that runs a model step by
step until it halts, hits a bad state, or violates a constraint.
The model data structure and the evaluator are tools/btor2.h, shared
with rotor.

Usage: bitr model.btor2 [ -l binary ] [ -i file ] [ -k steps ] [ -p ]

-l loads the code and data of binary into the model's code and data
segment states, checking them against words the model holds already;
-i puts file onto the model's input tape (RISC-R) or input buffer
(RISC-U); -k bounds the number of steps; -p prints the program
counter at every step. Bitr reports the first bad state or violated
constraint and the number of instructions executed until then.
*/

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------------- BITR ------------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- PARSER -----------------------------
// -----------------------------------------------------------------

uint64_t* read_whole_file(char* name);

uint64_t  model_character();
void      next_model_character();
void      skip_blanks();
uint64_t  at_end_of_line();
void      skip_line();
char*     scan_token();
char*     scan_comment();

uint64_t  parse_decimal(char* token);
uint64_t  parse_hexadecimal(char* token);
uint64_t  parse_binary(char* token);

uint64_t* line_of_nid(uint64_t nid);
void      set_line_of_nid(uint64_t nid, uint64_t* line);
uint64_t* line_of_token(char* token);

char*     canonical_op(char* token);

void      parse_error(char* message);
void      parse_model();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t READ_CHUNK = 1048576; // 1MB per read

// ------------------------ GLOBAL VARIABLES -----------------------

char*    model_name = (char*) 0;

char*    model_text = (char*) 0; // model file in memory
uint64_t model_size = 0;         // in bytes
uint64_t model_pos  = 0;         // current character
uint64_t model_line = 1;         // current line number

uint64_t* nid_lines = (uint64_t*) 0; // line of each nid
uint64_t  nid_limit = 0;             // size of nid_lines
uint64_t  max_nid   = 0;

uint64_t* init_lines = (uint64_t*) 0; // init line of each state nid

uint64_t number_of_sorts      = 0;
uint64_t number_of_states     = 0;
uint64_t number_of_inits      = 0;
uint64_t number_of_nexts      = 0;
uint64_t number_of_bads       = 0;
uint64_t number_of_constraints = 0;

// -----------------------------------------------------------------
// ---------------------------- LOADERS ----------------------------
// -----------------------------------------------------------------

uint64_t* find_state(char* symbol);
uint64_t  array_elements(uint64_t* state_nid);
uint64_t  array_element_size(uint64_t* state_nid);

void load_words(uint64_t* state_nid, uint64_t start, uint64_t size, uint64_t binary);
void load_binary(char* name);
void load_input(char* name);

// ------------------------ GLOBAL VARIABLES -----------------------

char* binary_file = (char*) 0;
char* input_file  = (char*) 0;

uint64_t loaded_words   = 0;
uint64_t checked_words  = 0;
uint64_t mismatched_words = 0;

// -----------------------------------------------------------------
// --------------------------- SIMULATOR ---------------------------
// -----------------------------------------------------------------

void     init_states();
uint64_t check_properties();
uint64_t simulate();

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t max_steps   = 0; // bound on steps, 0 for none
uint64_t printing_pc = 0; // print pc at every step

uint64_t* pc_state_nid = (uint64_t*) 0;

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

uint64_t bitr();

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------------- PARSER -----------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t* read_whole_file(char* name) {
  uint64_t fd;
  uint64_t* buffer;
  uint64_t capacity;
  uint64_t* bigger;
  uint64_t bytes;

  // reads the file into a word-aligned buffer, model_size is its length in bytes

  fd = open_read_only(name);

  if (signed_less_than(fd, 0)) {
    printf("%s: could not open %s\n", selfie_name, name);

    exit(EXITCODE_IOERROR);
  }

  capacity = READ_CHUNK;
  buffer   = zmalloc(capacity + READ_CHUNK);

  model_size = 0;

  bytes = read(fd, buffer, READ_CHUNK);

  while (signed_less_than(0, bytes)) {
    model_size = model_size + bytes;

    if (model_size + READ_CHUNK > capacity) {
      bigger = zmalloc(2 * capacity + READ_CHUNK);

      memcopy(bigger, buffer, round_up(model_size, sizeof(uint64_t)));

      buffer   = bigger;
      capacity = 2 * capacity;
    }

    bytes = read(fd, (uint64_t*) ((uint64_t) buffer + model_size), READ_CHUNK);
  }

  return buffer;
}

uint64_t model_character() {
  if (model_pos < model_size)
    return load_character(model_text, model_pos);
  else
    return 0;
}

void next_model_character() {
  if (model_character() == 10)
    model_line = model_line + 1;

  model_pos = model_pos + 1;
}

void skip_blanks() {
  while (model_pos < model_size) {
    if (model_character() == 32)
      next_model_character();
    else if (model_character() == 9)
      next_model_character();
    else if (model_character() == 13)
      next_model_character();
    else
      return;
  }
}

uint64_t at_end_of_line() {
  if (model_pos >= model_size)
    return 1;
  else
    return model_character() == 10;
}

void skip_line() {
  while (not(at_end_of_line()))
    next_model_character();

  if (model_pos < model_size)
    next_model_character();
}

char* scan_token() {
  uint64_t start;
  uint64_t scanning;
  uint64_t c;
  uint64_t length;
  char* token;
  uint64_t i;

  // the next blank-separated token on the current line, or 0

  skip_blanks();

  start = model_pos;

  scanning = not(at_end_of_line());

  while (scanning) {
    c = model_character();

    if (c == 32)
      scanning = 0;
    else if (c == 9)
      scanning = 0;
    else if (c == 13)
      scanning = 0;
    else if (c == 59)
      // semicolon starts a comment
      scanning = 0;
    else {
      next_model_character();

      scanning = not(at_end_of_line());
    }
  }

  length = model_pos - start;

  if (length == 0)
    return (char*) 0;

  token = (char*) zmalloc(round_up(length + 1, sizeof(uint64_t)));

  i = 0;

  while (i < length) {
    store_character(token, i, load_character(model_text, start + i));

    i = i + 1;
  }

  return token;
}

char* scan_comment() {
  uint64_t start;
  uint64_t length;
  char* comment;
  uint64_t i;

  // the rest of the line after a semicolon, or 0

  skip_blanks();

  if (at_end_of_line())
    return (char*) 0;

  if (model_character() != 59)
    parse_error("comment expected");

  next_model_character();

  skip_blanks();

  start = model_pos;

  while (not(at_end_of_line()))
    next_model_character();

  length = model_pos - start;

  comment = (char*) zmalloc(round_up(length + 1, sizeof(uint64_t)));

  i = 0;

  while (i < length) {
    store_character(comment, i, load_character(model_text, start + i));

    i = i + 1;
  }

  return comment;
}

uint64_t parse_decimal(char* token) {
  uint64_t negative;
  uint64_t value;
  uint64_t i;
  uint64_t c;

  negative = 0;
  value    = 0;
  i        = 0;

  if (load_character(token, 0) == 45) {
    negative = 1;

    i = 1;
  }

  c = load_character(token, i);

  if (c == 0)
    parse_error("decimal number expected");

  while (c != 0) {
    if (c < 48)
      parse_error("decimal digit expected");
    else if (c > 57)
      parse_error("decimal digit expected");

    value = value * 10 + (c - 48);

    i = i + 1;

    c = load_character(token, i);
  }

  if (negative)
    return -value;
  else
    return value;
}

uint64_t parse_hexadecimal(char* token) {
  uint64_t value;
  uint64_t i;
  uint64_t c;

  value = 0;
  i     = 0;

  c = load_character(token, 0);

  if (c == 0)
    parse_error("hexadecimal number expected");

  while (c != 0) {
    if (c >= 48)
      if (c <= 57)
        value = value * 16 + (c - 48);
      else if (c >= 65)
        if (c <= 70)
          value = value * 16 + (c - 55);
        else if (c >= 97)
          if (c <= 102)
            value = value * 16 + (c - 87);
          else
            parse_error("hexadecimal digit expected");
        else
          parse_error("hexadecimal digit expected");
      else
        parse_error("hexadecimal digit expected");
    else
      parse_error("hexadecimal digit expected");

    i = i + 1;

    c = load_character(token, i);
  }

  return value;
}

uint64_t parse_binary(char* token) {
  uint64_t value;
  uint64_t i;
  uint64_t c;

  value = 0;
  i     = 0;

  c = load_character(token, 0);

  if (c == 0)
    parse_error("binary number expected");

  while (c != 0) {
    if (c == 48)
      value = value * 2;
    else if (c == 49)
      value = value * 2 + 1;
    else
      parse_error("binary digit expected");

    i = i + 1;

    c = load_character(token, i);
  }

  return value;
}

uint64_t* line_of_nid(uint64_t nid) {
  if (nid < nid_limit)
    if (nid > 0)
      return (uint64_t*) *(nid_lines + nid);

  return UNUSED;
}

void set_line_of_nid(uint64_t nid, uint64_t* line) {
  uint64_t* bigger;
  uint64_t  bigger_limit;

  if (nid == 0)
    parse_error("nid must be positive");

  if (nid >= nid_limit) {
    bigger_limit = nid_limit;

    if (bigger_limit == 0)
      bigger_limit = 1024;

    while (bigger_limit <= nid)
      bigger_limit = bigger_limit * 2;

    bigger = zmalloc(bigger_limit * sizeof(uint64_t*));

    if (nid_limit > 0)
      memcopy(bigger, nid_lines, nid_limit * sizeof(uint64_t*));

    nid_lines = bigger;

    bigger = zmalloc(bigger_limit * sizeof(uint64_t*));

    if (nid_limit > 0)
      memcopy(bigger, init_lines, nid_limit * sizeof(uint64_t*));

    init_lines = bigger;

    nid_limit = bigger_limit;
  }

  if (*(nid_lines + nid) != 0)
    parse_error("nid defined twice");

  *(nid_lines + nid) = (uint64_t) line;

  if (nid > max_nid)
    max_nid = nid;
}

uint64_t* line_of_token(char* token) {
  uint64_t* line;

  if (token == (char*) 0)
    parse_error("nid expected");

  line = line_of_nid(parse_decimal(token));

  if (line == UNUSED)
    parse_error("undefined nid");

  return line;
}

char* canonical_op(char* token) {
  if (string_compare(token, OP_SORT)) return OP_SORT;
  if (string_compare(token, OP_ZERO)) return OP_ZERO;
  if (string_compare(token, OP_ONE)) return OP_ONE;
  if (string_compare(token, OP_CONST)) return OP_CONST;
  if (string_compare(token, OP_CONSTD)) return OP_CONSTD;
  if (string_compare(token, OP_CONSTH)) return OP_CONSTH;
  if (string_compare(token, OP_INPUT)) return OP_INPUT;
  if (string_compare(token, OP_STATE)) return OP_STATE;
  if (string_compare(token, OP_INIT)) return OP_INIT;
  if (string_compare(token, OP_NEXT)) return OP_NEXT;
  if (string_compare(token, OP_SEXT)) return OP_SEXT;
  if (string_compare(token, OP_UEXT)) return OP_UEXT;
  if (string_compare(token, OP_SLICE)) return OP_SLICE;
  if (string_compare(token, OP_NOT)) return OP_NOT;
  if (string_compare(token, OP_INC)) return OP_INC;
  if (string_compare(token, OP_DEC)) return OP_DEC;
  if (string_compare(token, OP_NEG)) return OP_NEG;
  if (string_compare(token, OP_IMPLIES)) return OP_IMPLIES;
  if (string_compare(token, OP_EQ)) return OP_EQ;
  if (string_compare(token, OP_NEQ)) return OP_NEQ;
  if (string_compare(token, OP_SGT)) return OP_SGT;
  if (string_compare(token, OP_UGT)) return OP_UGT;
  if (string_compare(token, OP_SGTE)) return OP_SGTE;
  if (string_compare(token, OP_UGTE)) return OP_UGTE;
  if (string_compare(token, OP_SLT)) return OP_SLT;
  if (string_compare(token, OP_ULT)) return OP_ULT;
  if (string_compare(token, OP_SLTE)) return OP_SLTE;
  if (string_compare(token, OP_ULTE)) return OP_ULTE;
  if (string_compare(token, OP_AND)) return OP_AND;
  if (string_compare(token, OP_OR)) return OP_OR;
  if (string_compare(token, OP_XOR)) return OP_XOR;
  if (string_compare(token, OP_SLL)) return OP_SLL;
  if (string_compare(token, OP_SRL)) return OP_SRL;
  if (string_compare(token, OP_SRA)) return OP_SRA;
  if (string_compare(token, OP_ADD)) return OP_ADD;
  if (string_compare(token, OP_SUB)) return OP_SUB;
  if (string_compare(token, OP_MUL)) return OP_MUL;
  if (string_compare(token, OP_SDIV)) return OP_SDIV;
  if (string_compare(token, OP_UDIV)) return OP_UDIV;
  if (string_compare(token, OP_SREM)) return OP_SREM;
  if (string_compare(token, OP_UREM)) return OP_UREM;
  if (string_compare(token, OP_CONCAT)) return OP_CONCAT;
  if (string_compare(token, OP_READ)) return OP_READ;
  if (string_compare(token, OP_ITE)) return OP_ITE;
  if (string_compare(token, OP_WRITE)) return OP_WRITE;
  if (string_compare(token, OP_BAD)) return OP_BAD;
  if (string_compare(token, OP_CONSTRAINT)) return OP_CONSTRAINT;

  return (char*) 0;
}

void parse_error(char* message) {
  printf("%s: syntax error in %s in line %lu: %s\n", selfie_name, model_name, model_line, message);

  exit(EXITCODE_PARSERERROR);
}

void parse_model() {
  char* token;
  uint64_t nid;
  char* op;
  uint64_t* sid;
  uint64_t* line;
  uint64_t* arg1;
  uint64_t* arg2;
  uint64_t* arg3;
  uint64_t  value;
  uint64_t  u;
  uint64_t  l;
  char* symbol;
  char* comment;

  model_text = (char*) read_whole_file(model_name);
  model_pos  = 0;
  model_line = 1;

  // keep the model as written: no structural sharing
  reuse_lines = 0;

  while (model_pos < model_size) {
    skip_blanks();

    if (at_end_of_line()) {
      skip_line();
    } else if (model_character() == 59) {
      // comment line
      skip_line();
    } else {
      token = scan_token();

      nid = parse_decimal(token);

      token = scan_token();

      if (token == (char*) 0)
        parse_error("operator expected");

      op = canonical_op(token);

      if (op == (char*) 0)
        parse_error("unknown operator");

      line = UNUSED;

      if (op == OP_SORT) {
        token = scan_token();

        if (token == (char*) 0)
          parse_error("sort kind expected");

        if (string_compare(token, "bitvec")) {
          value = parse_decimal(scan_token());

          comment = scan_comment();

          line = new_bitvec(value, comment);

          if (value == 1)
            if (SID_BOOLEAN == UNUSED)
              SID_BOOLEAN = line;
        } else if (string_compare(token, "array")) {
          arg2 = line_of_token(scan_token());
          arg3 = line_of_token(scan_token());

          comment = scan_comment();

          line = new_array(arg2, arg3, comment);
        } else
          parse_error("bitvec or array expected");

        number_of_sorts = number_of_sorts + 1;
      } else if (or(is_constant_op(op), or(op == OP_ZERO, op == OP_ONE))) {
        sid = line_of_token(scan_token());

        if (op == OP_ZERO) {
          // zero and one are decimal constants in the model
          op = OP_CONSTD;

          value = 0;
        } else if (op == OP_ONE) {
          op = OP_CONSTD;

          value = 1;
        } else {
          token = scan_token();

          if (token == (char*) 0)
            parse_error("constant expected");

          if (op == OP_CONSTD)
            value = parse_decimal(token);
          else if (op == OP_CONSTH)
            value = parse_hexadecimal(token);
          else
            value = parse_binary(token);
        }

        comment = scan_comment();

        line = new_constant(op, sid, value, comment);
      } else if (is_input_op(op)) {
        sid = line_of_token(scan_token());

        symbol = scan_token();

        comment = scan_comment();

        line = new_input(op, sid, symbol, comment);

        if (op == OP_STATE)
          number_of_states = number_of_states + 1;
      } else if (op == OP_INIT) {
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());
        arg2 = line_of_token(scan_token());

        comment = scan_comment();

        line = new_init(sid, arg1, arg2, comment);

        if (get_op(arg1) != OP_STATE)
          parse_error("init of non-state");

        *(init_lines + get_nid(arg1)) = (uint64_t) line;

        number_of_inits = number_of_inits + 1;
      } else if (op == OP_NEXT) {
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());
        arg2 = line_of_token(scan_token());

        comment = scan_comment();

        line = new_next(sid, arg1, arg2, comment);

        number_of_nexts = number_of_nexts + 1;
      } else if (is_property_op(op)) {
        arg1 = line_of_token(scan_token());

        symbol = scan_token();

        comment = scan_comment();

        line = new_property(op, arg1, symbol, comment);

        if (op == OP_BAD)
          number_of_bads = number_of_bads + 1;
        else
          number_of_constraints = number_of_constraints + 1;
      } else if (op == OP_SEXT) {
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());

        value = parse_decimal(scan_token());

        comment = scan_comment();

        line = new_ext(op, sid, arg1, value, comment);
      } else if (op == OP_UEXT) {
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());

        value = parse_decimal(scan_token());

        comment = scan_comment();

        line = new_ext(op, sid, arg1, value, comment);
      } else if (op == OP_SLICE) {
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());

        u = parse_decimal(scan_token());
        l = parse_decimal(scan_token());

        comment = scan_comment();

        line = new_slice(sid, arg1, u, l, comment);
      } else if (is_unary_op(op)) {
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());

        comment = scan_comment();

        line = new_unary(op, sid, arg1, comment);
      } else if (op == OP_ITE) {
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());
        arg2 = line_of_token(scan_token());
        arg3 = line_of_token(scan_token());

        comment = scan_comment();

        line = new_ternary(op, sid, arg1, arg2, arg3, comment);
      } else if (op == OP_WRITE) {
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());
        arg2 = line_of_token(scan_token());
        arg3 = line_of_token(scan_token());

        comment = scan_comment();

        line = new_ternary(op, sid, arg1, arg2, arg3, comment);
      } else {
        // read, concat, and binary operators
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());
        arg2 = line_of_token(scan_token());

        comment = scan_comment();

        line = new_binary(op, sid, arg1, arg2, comment);
      }

      set_line_of_nid(nid, line);

      set_nid(line, nid);

      skip_line();
    }
  }

  printf("%s: %lu lines with %lu sorts, %lu states, %lu inits, %lu nexts, %lu bads, and %lu constraints parsed from %s\n", selfie_name,
    number_of_lines, number_of_sorts, number_of_states, number_of_inits, number_of_nexts, number_of_bads, number_of_constraints, model_name);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------------- LOADERS ----------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t* find_state(char* symbol) {
  uint64_t nid;
  uint64_t* line;

  // the state with the given symbol, or 0

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED)
      if (get_op(line) == OP_STATE)
        if ((char*) get_arg1(line) != (char*) 0)
          if (string_compare((char*) get_arg1(line), symbol))
            return line;

    nid = nid + 1;
  }

  return UNUSED;
}

uint64_t array_elements(uint64_t* state_nid) {
  return two_to_the_power_of(eval_array_size(get_sid(state_nid)));
}

uint64_t array_element_size(uint64_t* state_nid) {
  return eval_element_size(get_sid(state_nid));
}

void load_words(uint64_t* state_nid, uint64_t start, uint64_t size, uint64_t binary) {
  uint64_t element_bytes;
  uint64_t elements;
  uint64_t offset;
  uint64_t index;
  uint64_t word;

  // writes the words of a loaded code (binary == 1) or data (binary == 0)
  // segment of size bytes into the array state, element by element, and
  // checks the words the state already holds

  element_bytes = array_element_size(state_nid) / 8;
  elements      = array_elements(state_nid);

  offset = 0;

  while (offset < size) {
    index = offset / element_bytes;

    if (index >= elements) {
      printf("%s: %s does not fit the %lu elements of %s\n", selfie_name, binary_file, elements, (char*) get_arg1(state_nid));

      exit(EXITCODE_BADARGUMENTS);
    }

    if (binary)
      word = load_instruction(offset);
    else
      word = load_data(offset);

    if (read_array_raw(state_nid, index) != 0)
      if (read_array_raw(state_nid, index) != word)
        mismatched_words = mismatched_words + 1;

    if (read_array_raw(state_nid, index) == word)
      checked_words = checked_words + 1;

    write_array_raw(state_nid, index, word);

    loaded_words = loaded_words + 1;

    offset = offset + element_bytes;
  }

  // unused since linear addresses are relative to the segment start
  start = start + 0;
}

void load_binary(char* name) {
  uint64_t* code_nid;
  uint64_t* data_nid;

  // code and data of the binary go into the live code and data segment states;
  // a model generated for the binary holds the same words already, which checks
  // the loader against rotor's initialization, see projects/reversible.md

  selfie_load(name);

  code_nid = find_state("core-0-loaded-code-segment");

  if (code_nid == UNUSED)
    code_nid = find_state("core-0-code-segment");

  data_nid = find_state("core-0-loaded-data-segment");

  if (data_nid == UNUSED)
    data_nid = find_state("core-0-zeroed-data-segment");

  if (code_nid == UNUSED) {
    printf("%s: no code segment state in %s\n", selfie_name, model_name);

    exit(EXITCODE_BADARGUMENTS);
  }

  load_words(code_nid, code_start, code_size, 1);

  if (data_nid != UNUSED)
    load_words(data_nid, data_start, data_size, 0);

  printf("%s: %lu words of %s loaded into %s, %lu words agreed, %lu words mismatched\n", selfie_name,
    loaded_words, name, model_name, checked_words, mismatched_words);

  if (mismatched_words > 0)
    exit(EXITCODE_SYSTEMERROR);
}

void load_input(char* name) {
  uint64_t* tapes_nid;
  uint64_t* ends_nid;
  uint64_t* heads_nid;
  uint64_t* buffer_nid;
  uint64_t* buffer;
  uint64_t  size;
  uint64_t  tape_words;
  uint64_t  words;
  uint64_t  i;

  // the file goes onto the input tape of standard input, with its size as
  // the file end; a RISC-U model reads its first byte from the input buffer

  buffer = read_whole_file(name);
  size   = model_size;

  tapes_nid = find_state("input-tapes");
  ends_nid  = find_state("tape-ends");
  heads_nid = find_state("tape-heads");

  if (tapes_nid != UNUSED) {
    // words per tape: all tape words over the number of tapes
    tape_words = array_elements(tapes_nid) / array_elements(heads_nid);

    words = round_up(size, WORDSIZE) / WORDSIZE;

    if (words > tape_words) {
      // reads beyond the tape are bad states, so only the beginning matters
      printf("%s: only the first %lu of %lu words of %s fit the input tape in %s\n", selfie_name, tape_words, words, name, model_name);

      words = tape_words;
    }

    i = 0;

    while (i < words) {
      write_array_raw(tapes_nid, i, *(buffer + i));

      i = i + 1;
    }

    write_array_raw(ends_nid, 0, size);

    printf("%s: %lu bytes of %s put onto the input tape of %s\n", selfie_name, size, name, model_name);
  } else {
    buffer_nid = find_state("input-buffer");

    if (buffer_nid == UNUSED) {
      printf("%s: no input tape or buffer in %s\n", selfie_name, model_name);

      exit(EXITCODE_BADARGUMENTS);
    }

    if (size > 0)
      current_input = load_character((char*) buffer, 0);
    else
      current_input = 0;

    printf("%s: first byte %lu of %s put into the input buffer of %s\n", selfie_name, current_input, name, model_name);
  }
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// --------------------------- SIMULATOR ---------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

void init_states() {
  uint64_t nid;
  uint64_t* line;
  uint64_t* sid;
  uint64_t* init_nid;

  // states are initialized in the order of their nids, states without
  // init to zero; the input buffer of RISC-U models and the code segment
  // are arrays the evaluator never copies

  line = find_state("input-buffer");

  if (line != UNUSED)
    SID_INPUT_BUFFER = get_sid(line);

  line = find_state("core-0-code-segment");

  if (line != UNUSED)
    SID_CODE_STATE = get_sid(line);

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED)
      if (get_op(line) == OP_STATE) {
        init_nid = (uint64_t*) *(init_lines + nid);

        if (init_nid == UNUSED) {
          sid = get_sid(line);

          if (is_bitvector(sid))
            init_nid = new_init(sid, line, new_constant(OP_CONSTD, sid, 0, "zero"), "uninitialized state zeroed");
          else
            init_nid = new_init(sid, line, new_constant(OP_CONSTD, get_arg3(sid), 0, "zero"), "uninitialized state zeroed");
        }

        eval_init(init_nid);
      }

    nid = nid + 1;
  }

  pc_state_nid = find_state("core-0-pc");
}

uint64_t check_properties() {
  uint64_t nid;
  uint64_t* line;
  uint64_t  condition;

  // reports the first bad state or violated constraint, returns 1 if any

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED) {
      if (get_op(line) == OP_BAD) {
        condition = eval_line(get_arg1(line));

        if (condition) {
          printf("%s: bad %s after %lu instructions\n", selfie_name, (char*) get_arg2(line), current_step + 1);

          return 1;
        }
      } else if (get_op(line) == OP_CONSTRAINT) {
        condition = eval_line(get_arg1(line));

        if (not(condition)) {
          printf("%s: constraint %s violated after %lu instructions\n", selfie_name, (char*) get_arg2(line), current_step + 1);

          return 1;
        }
      }
    }

    nid = nid + 1;
  }

  return 0;
}

uint64_t simulate() {
  uint64_t nid;
  uint64_t* line;
  uint64_t  halt;

  // runs the model from its initial state until it halts, reaches a bad
  // state, or violates a constraint; the number of instructions executed
  // is the number of steps taken, counting the step a property stops

  printf("%s: ********************************************************************************\n", selfie_name);

  current_step = 0;
  next_step    = 0;

  while (1) {
    next_step = next_step + 1;

    if (printing_pc)
      if (pc_state_nid != UNUSED)
        printf("%s: pc 0x%lX at instruction %lu\n", selfie_name, get_state(pc_state_nid), current_step + 1);

    if (check_properties())
      return 1;

    if (max_steps > 0)
      if (current_step >= max_steps) {
        printf("%s: %lu instructions executed, bound reached\n", selfie_name, current_step);

        return 0;
      }

    halt = 1;

    nid = 1;

    while (nid <= max_nid) {
      line = line_of_nid(nid);

      if (line != UNUSED)
        if (get_op(line) == OP_NEXT)
          halt = halt * eval_next(line);

      nid = nid + 1;
    }

    if (halt) {
      printf("%s: halted after %lu instructions\n", selfie_name, current_step + 1);

      return 0;
    }

    nid = 1;

    while (nid <= max_nid) {
      line = line_of_nid(nid);

      if (line != UNUSED)
        if (get_op(line) == OP_NEXT)
          apply_next(line);

      nid = nid + 1;
    }

    current_step = next_step;
  }
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

uint64_t bitr() {
  if (number_of_remaining_arguments() == 0)
    return EXITCODE_BADARGUMENTS;

  model_name = get_argument();

  while (number_of_remaining_arguments() > 0) {
    get_argument();

    if (string_compare(argument, "-l")) {
      if (number_of_remaining_arguments() > 0)
        binary_file = get_argument();
      else
        return EXITCODE_BADARGUMENTS;
    } else if (string_compare(argument, "-i")) {
      if (number_of_remaining_arguments() > 0)
        input_file = get_argument();
      else
        return EXITCODE_BADARGUMENTS;
    } else if (string_compare(argument, "-k")) {
      if (number_of_remaining_arguments() > 0)
        max_steps = atoi(get_argument());
      else
        return EXITCODE_BADARGUMENTS;
    } else if (string_compare(argument, "-p"))
      printing_pc = 1;
    else
      return EXITCODE_BADARGUMENTS;
  }

  // concrete simulation: inputs and states are values, not symbols
  inputs_are_symbolic = 0;
  states_are_symbolic = 0;

  parse_model();

  init_states();

  if (binary_file != (char*) 0)
    load_binary(binary_file);

  if (input_file != (char*) 0)
    load_input(input_file);

  simulate();

  printf("%s: ################################################################################\n", selfie_name);

  return EXITCODE_NOERROR;
}

int main(int argc, char** argv) {
  uint64_t exit_code;

  init_selfie((uint64_t) argc, (uint64_t*) argv);

  init_library();
  init_system();
  init_target();
  init_kernel();

  // the loader uses selfie's binary loader
  init_register();
  init_interpreter();
  init_disassembler();

  init_model();

  exit_code = bitr();

  return exit_selfie(exit_code, " model.btor2 [ -l binary ] [ -i file ] [ -k steps ] [ -p ]");
}
