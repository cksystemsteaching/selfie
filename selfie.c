/*
Copyright (c) 2015-2018, the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

http://selfie.cs.uni-salzburg.at

The Selfie Project provides an educational platform for teaching
undergraduate and graduate students the design and implementation
of programming languages and runtime systems. The focus is on the
construction of compilers, libraries, operating systems, and even
virtual machine monitors. The common theme is to identify and
resolve self-reference in systems code which is seen as the key
challenge when teaching systems engineering, hence the name.

Selfie is a self-contained 64-bit, 10-KLOC C implementation of:

1. a self-compiling compiler called starc that compiles
   a tiny but still fast subset of C called C Star (C*) to
   a tiny and easy-to-teach subset of RISC-V called RISC-U,
2. a self-executing emulator called mipster that executes
   RISC-U code including itself when compiled with starc,
3. a self-hosting hypervisor called hypster that provides
   RISC-U virtual machines that can host all of selfie,
   that is, starc, mipster, and hypster itself,
4. a prototypical symbolic execution engine called monster
   that executes RISC-U code symbolically,
5. a simple SAT solver that reads CNF DIMACS files, and
6. a tiny C* library called libcstar utilized by selfie.

Selfie is implemented in a single (!) file and kept minimal for simplicity.
There is also a simple in-memory linker, a RISC-U disassembler, a profiler,
and a debugger with replay as well as minimal operating system support in
the form of RISC-V system calls built into the emulator.

C* is a tiny Turing-complete subset of C that includes dereferencing
(the * operator) but excludes composite data types, bitwise and Boolean
operators, and many other features. There are only unsigned 64-bit
integers and 64-bit pointers as well as character and string literals.
This choice turns out to be helpful for students to understand the
true role of composite data types such as arrays and records.
Bitwise operations are implemented in libcstar using unsigned integer
arithmetics helping students better understand arithmetic operators.
C* is supposed to be close to the minimum necessary for implementing
a self-compiling, single-pass, recursive-descent compiler. C* can be
taught in one to two weeks of classes depending on student background.

The compiler can readily be extended to compile features missing in C*
and to improve performance of the generated code. The compiler generates
RISC-U executables in ELF format that are compatible with the official
RISC-V toolchain. The mipster emulator can execute RISC-U executables
loaded from file but also from memory immediately after code generation
without going through the file system.

RISC-U is a tiny Turing-complete subset of the RISC-V instruction set.
It only features unsigned 64-bit integer arithmetic, double-word memory,
and simple control-flow instructions but neither bitwise nor byte- and
word-level instructions. RISC-U can be taught in one week of classes.

The emulator implements minimal operating system support that is meant
to be extended by students, first as part of the emulator, and then
ported to run on top of it, similar to an actual operating system or
virtual machine monitor. The fact that the emulator can execute itself
helps exposing the self-referential nature of that challenge. In fact,
selfie goes one step further by implementing microkernel functionality
as part of the emulator and a hypervisor that can run as part of the
emulator as well as on top of it, all with the same code.

Selfie is the result of many years of teaching systems engineering.
The design of the compiler is inspired by the Oberon compiler of
Professor Niklaus Wirth from ETH Zurich. RISC-U is inspired by the
RISC-V community around Professor David Patterson from UC Berkeley.
The design of the hypervisor is inspired by microkernels of
Professor Jochen Liedtke from University of Karlsruhe.
*/

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     L I B R A R Y     ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------- BUILTIN PROCEDURES ----------------------
// -----------------------------------------------------------------

 // selfie bootstraps int to uint64_t!
void exit(int code);

uint64_t read(uint64_t fd, uint64_t* buffer, uint64_t bytes_to_read);
uint64_t write(uint64_t fd, uint64_t* buffer, uint64_t bytes_to_write);
uint64_t open(uint64_t* filename, uint64_t flags, uint64_t mode);

// selfie bootstraps void* and unsigned long to uint64_t* and uint64_t, respectively!
void* malloc(unsigned long);

// -----------------------------------------------------------------
// ----------------------- LIBRARY PROCEDURES ----------------------
// -----------------------------------------------------------------

void init_library();
void reset_library();

uint64_t two_to_the_power_of(uint64_t p);
uint64_t ten_to_the_power_of(uint64_t p);

uint64_t left_shift(uint64_t n, uint64_t b);
uint64_t right_shift(uint64_t n, uint64_t b);

uint64_t get_bits(uint64_t n, uint64_t i, uint64_t b);
uint64_t get_low_word(uint64_t n);
uint64_t get_high_word(uint64_t n);

uint64_t absolute(uint64_t n);

uint64_t signed_less_than(uint64_t a, uint64_t b);
uint64_t signed_division(uint64_t a, uint64_t b);

uint64_t is_signed_integer(uint64_t n, uint64_t b);
uint64_t sign_extend(uint64_t n, uint64_t b);
uint64_t sign_shrink(uint64_t n, uint64_t b);

uint64_t  load_character(uint64_t* s, uint64_t i);
uint64_t* store_character(uint64_t* s, uint64_t i, uint64_t c);

uint64_t  string_length(uint64_t* s);
uint64_t* string_copy(uint64_t* s);
void      string_reverse(uint64_t* s);
uint64_t  string_compare(uint64_t* s, uint64_t* t);

uint64_t  atoi(uint64_t* s);
uint64_t* itoa(uint64_t n, uint64_t* s, uint64_t b, uint64_t a);

uint64_t fixed_point_ratio(uint64_t a, uint64_t b, uint64_t f);
uint64_t fixed_point_percentage(uint64_t r, uint64_t f);

void put_character(uint64_t c);

void print(uint64_t* s);
void println();

void print_character(uint64_t c);
void print_string(uint64_t* s);
void print_integer(uint64_t n);
void unprint_integer(uint64_t n);
void print_hexadecimal(uint64_t n, uint64_t a);
void print_octal(uint64_t n, uint64_t a);
void print_binary(uint64_t n, uint64_t a);

uint64_t print_format0(uint64_t* s, uint64_t i);
uint64_t print_format1(uint64_t* s, uint64_t i, uint64_t* a);

void printf1(uint64_t* s, uint64_t* a1);
void printf2(uint64_t* s, uint64_t* a1, uint64_t* a2);
void printf3(uint64_t* s, uint64_t* a1, uint64_t* a2, uint64_t* a3);
void printf4(uint64_t* s, uint64_t* a1, uint64_t* a2, uint64_t* a3, uint64_t* a4);
void printf5(uint64_t* s, uint64_t* a1, uint64_t* a2, uint64_t* a3, uint64_t* a4, uint64_t* a5);
void printf6(uint64_t* s, uint64_t* a1, uint64_t* a2, uint64_t* a3, uint64_t* a4, uint64_t* a5, uint64_t* a6);

uint64_t round_up(uint64_t n, uint64_t m);

uint64_t* smalloc(uint64_t size);
uint64_t* zalloc(uint64_t size);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t CHAR_EOF          =  -1; // end of file
uint64_t CHAR_BACKSPACE    =   8; // ASCII code 8  = backspace
uint64_t CHAR_TAB          =   9; // ASCII code 9  = tabulator
uint64_t CHAR_LF           =  10; // ASCII code 10 = line feed
uint64_t CHAR_CR           =  13; // ASCII code 13 = carriage return
uint64_t CHAR_SPACE        = ' ';
uint64_t CHAR_UNDERSCORE   = '_';
uint64_t CHAR_SINGLEQUOTE  =  39; // ASCII code 39 = '
uint64_t CHAR_DOUBLEQUOTE  = '"';
uint64_t CHAR_COMMA        = ',';
uint64_t CHAR_SEMICOLON    = ';';
uint64_t CHAR_LPARENTHESIS = '(';
uint64_t CHAR_RPARENTHESIS = ')';
uint64_t CHAR_LBRACE       = '{';
uint64_t CHAR_RBRACE       = '}';
uint64_t CHAR_PLUS         = '+';
uint64_t CHAR_DASH         = '-';
uint64_t CHAR_ASTERISK     = '*';
uint64_t CHAR_SLASH        = '/';
uint64_t CHAR_PERCENTAGE   = '%';
uint64_t CHAR_EQUAL        = '=';
uint64_t CHAR_EXCLAMATION  = '!';
uint64_t CHAR_LT           = '<';
uint64_t CHAR_GT           = '>';
uint64_t CHAR_BACKSLASH    =  92; // ASCII code 92 = backslash

uint64_t CPUBITWIDTH = 64;

uint64_t SIZEOFUINT64     = 8; // must be the same as REGISTERSIZE
uint64_t SIZEOFUINT64STAR = 8; // must be the same as REGISTERSIZE

uint64_t* power_of_two_table;

uint64_t INT64_MAX; // maximum numerical value of a signed 64-bit integer
uint64_t INT64_MIN; // minimum numerical value of a signed 64-bit integer

uint64_t UINT64_MAX; // maximum numerical value of an unsigned 64-bit integer

uint64_t MAX_FILENAME_LENGTH = 128;

uint64_t* character_buffer; // buffer for reading and writing characters
uint64_t* integer_buffer;   // buffer for printing integers
uint64_t* filename_buffer;  // buffer for opening files
uint64_t* binary_buffer;    // buffer for binary I/O

// flags for opening read-only files
// LINUX:       0 = 0x0000 = O_RDONLY (0x0000)
// MAC:         0 = 0x0000 = O_RDONLY (0x0000)
// WINDOWS: 32768 = 0x8000 = _O_BINARY (0x8000) | _O_RDONLY (0x0000)
// since LINUX/MAC do not seem to mind about _O_BINARY set
// we use the WINDOWS flags as default
uint64_t O_RDONLY = 32768;

// flags for opening write-only files
// MAC: 1537 = 0x0601 = O_CREAT (0x0200) | O_TRUNC (0x0400) | O_WRONLY (0x0001)
uint64_t MAC_O_CREAT_TRUNC_WRONLY = 1537;

// LINUX: 577 = 0x0241 = O_CREAT (0x0040) | O_TRUNC (0x0200) | O_WRONLY (0x0001)
uint64_t LINUX_O_CREAT_TRUNC_WRONLY = 577;

// WINDOWS: 33537 = 0x8301 = _O_BINARY (0x8000) | _O_CREAT (0x0100) | _O_TRUNC (0x0200) | _O_WRONLY (0x0001)
uint64_t WINDOWS_O_BINARY_CREAT_TRUNC_WRONLY = 33537;

// flags for rw-r--r-- file permissions
// 420 = 00644 = S_IRUSR (00400) | S_IWUSR (00200) | S_IRGRP (00040) | S_IROTH (00004)
// these flags seem to be working for LINUX, MAC, and WINDOWS
uint64_t S_IRUSR_IWUSR_IRGRP_IROTH = 420;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t number_of_written_characters = 0;

uint64_t* output_name = (uint64_t*) 0;
uint64_t  output_fd   = 1; // 1 is file descriptor of standard output

// ------------------------- INITIALIZATION ------------------------

void init_library() {
  uint64_t i;

  // powers of two table with CPUBITWIDTH entries for 2^0 to 2^(CPUBITWIDTH - 1)
  power_of_two_table = smalloc(CPUBITWIDTH * SIZEOFUINT64);

  *power_of_two_table = 1; // 2^0 == 1

  i = 1;

  while (i < CPUBITWIDTH) {
    // compute powers of two incrementally using this recurrence relation
    *(power_of_two_table + i) = *(power_of_two_table + (i - 1)) * 2;

    i = i + 1;
  }

  // compute 64-bit unsigned integer range using signed integer arithmetic
  UINT64_MAX = -1;

  // compute 64-bit signed integer range using unsigned integer arithmetic
  INT64_MAX = two_to_the_power_of(CPUBITWIDTH - 1) - 1;
  INT64_MIN = INT64_MAX + 1;

  // allocate and touch to make sure memory is mapped for read calls
  character_buffer  = smalloc(SIZEOFUINT64);
  *character_buffer = 0;

  // accommodate at least CPUBITWIDTH numbers for itoa, no mapping needed
  integer_buffer = smalloc(CPUBITWIDTH + 1);

  // does not need to be mapped
  filename_buffer = smalloc(MAX_FILENAME_LENGTH);

  // allocate and touch to make sure memory is mapped for read calls
  binary_buffer  = smalloc(SIZEOFUINT64);
  *binary_buffer = 0;
}

void reset_library() {
  number_of_written_characters = 0;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------    C O M P I L E R    ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- SCANNER ----------------------------
// -----------------------------------------------------------------

void init_scanner();
void reset_scanner();

void print_symbol(uint64_t symbol);
void print_line_number(uint64_t* message, uint64_t line);

void syntax_error_message(uint64_t* message);
void syntax_error_character(uint64_t character);
void syntax_error_identifier(uint64_t* expected);

void get_character();

uint64_t is_character_new_line();
uint64_t is_character_whitespace();

uint64_t find_next_character();

uint64_t is_character_letter();
uint64_t is_character_digit();
uint64_t is_character_letter_or_digit_or_underscore();
uint64_t is_character_not_double_quote_or_new_line_or_eof();

uint64_t identifier_string_match(uint64_t string_index);
uint64_t identifier_or_keyword();

void get_symbol();

void handle_escape_sequence();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t SYM_EOF = -1; // end of file

// C* symbols

uint64_t SYM_INTEGER      = 0;  // integer
uint64_t SYM_CHARACTER    = 1;  // character
uint64_t SYM_STRING       = 2;  // string
uint64_t SYM_IDENTIFIER   = 3;  // identifier
uint64_t SYM_UINT64       = 4;  // uint64_t
uint64_t SYM_IF           = 5;  // if
uint64_t SYM_ELSE         = 6;  // else
uint64_t SYM_VOID         = 7;  // void
uint64_t SYM_RETURN       = 8;  // return
uint64_t SYM_WHILE        = 9;  // while
uint64_t SYM_COMMA        = 10; // ,
uint64_t SYM_SEMICOLON    = 11; // ;
uint64_t SYM_LPARENTHESIS = 12; // (
uint64_t SYM_RPARENTHESIS = 13; // )
uint64_t SYM_LBRACE       = 14; // {
uint64_t SYM_RBRACE       = 15; // }
uint64_t SYM_PLUS         = 16; // +
uint64_t SYM_MINUS        = 17; // -
uint64_t SYM_ASTERISK     = 18; // *
uint64_t SYM_DIV          = 19; // /
uint64_t SYM_MOD          = 20; // %
uint64_t SYM_ASSIGN       = 21; // =
uint64_t SYM_EQUALITY     = 22; // ==
uint64_t SYM_NOTEQ        = 23; // !=
uint64_t SYM_LT           = 24; // <
uint64_t SYM_LEQ          = 25; // <=
uint64_t SYM_GT           = 26; // >
uint64_t SYM_GEQ          = 27; // >=

// symbols for bootstrapping

uint64_t SYM_INT      = 28; // int
uint64_t SYM_CHAR     = 29; // char
uint64_t SYM_UNSIGNED = 30; // unsigned

uint64_t* SYMBOLS; // strings representing symbols

uint64_t MAX_IDENTIFIER_LENGTH = 64;  // maximum number of characters in an identifier
uint64_t MAX_INTEGER_LENGTH    = 20;  // maximum number of characters in an unsigned integer
uint64_t MAX_STRING_LENGTH     = 128; // maximum number of characters in a string

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t line_number = 1; // current line number for error reporting

uint64_t* identifier = (uint64_t*) 0; // stores scanned identifier as string
uint64_t* integer    = (uint64_t*) 0; // stores scanned integer as string
uint64_t* string     = (uint64_t*) 0; // stores scanned string

uint64_t literal = 0; // stores numerical value of scanned integer or character

uint64_t integer_is_signed = 0; // enforce INT64_MIN limit if '-' was scanned before

uint64_t character; // most recently read character

uint64_t number_of_read_characters = 0;

uint64_t symbol; // most recently recognized symbol

uint64_t number_of_ignored_characters = 0;
uint64_t number_of_comments           = 0;
uint64_t number_of_scanned_symbols    = 0;

uint64_t* source_name = (uint64_t*) 0; // name of source file
uint64_t  source_fd   = 0;             // file descriptor of open source file

// ------------------------- INITIALIZATION ------------------------

void init_scanner () {
  SYMBOLS = smalloc((SYM_UNSIGNED + 1) * SIZEOFUINT64STAR);

  *(SYMBOLS + SYM_INTEGER)      = (uint64_t) "integer";
  *(SYMBOLS + SYM_CHARACTER)    = (uint64_t) "character";
  *(SYMBOLS + SYM_STRING)       = (uint64_t) "string";
  *(SYMBOLS + SYM_IDENTIFIER)   = (uint64_t) "identifier";
  *(SYMBOLS + SYM_UINT64)       = (uint64_t) "uint64_t";
  *(SYMBOLS + SYM_IF)           = (uint64_t) "if";
  *(SYMBOLS + SYM_ELSE)         = (uint64_t) "else";
  *(SYMBOLS + SYM_VOID)         = (uint64_t) "void";
  *(SYMBOLS + SYM_RETURN)       = (uint64_t) "return";
  *(SYMBOLS + SYM_WHILE)        = (uint64_t) "while";
  *(SYMBOLS + SYM_COMMA)        = (uint64_t) ",";
  *(SYMBOLS + SYM_SEMICOLON)    = (uint64_t) ";";
  *(SYMBOLS + SYM_LPARENTHESIS) = (uint64_t) "(";
  *(SYMBOLS + SYM_RPARENTHESIS) = (uint64_t) ")";
  *(SYMBOLS + SYM_LBRACE)       = (uint64_t) "{";
  *(SYMBOLS + SYM_RBRACE)       = (uint64_t) "}";
  *(SYMBOLS + SYM_PLUS)         = (uint64_t) "+";
  *(SYMBOLS + SYM_MINUS)        = (uint64_t) "-";
  *(SYMBOLS + SYM_ASTERISK)     = (uint64_t) "*";
  *(SYMBOLS + SYM_DIV)          = (uint64_t) "/";
  *(SYMBOLS + SYM_MOD)          = (uint64_t) "%";
  *(SYMBOLS + SYM_ASSIGN)       = (uint64_t) "=";
  *(SYMBOLS + SYM_EQUALITY)     = (uint64_t) "==";
  *(SYMBOLS + SYM_NOTEQ)        = (uint64_t) "!=";
  *(SYMBOLS + SYM_LT)           = (uint64_t) "<";
  *(SYMBOLS + SYM_LEQ)          = (uint64_t) "<=";
  *(SYMBOLS + SYM_GT)           = (uint64_t) ">";
  *(SYMBOLS + SYM_GEQ)          = (uint64_t) ">=";

  *(SYMBOLS + SYM_INT)      = (uint64_t) "int";
  *(SYMBOLS + SYM_CHAR)     = (uint64_t) "char";
  *(SYMBOLS + SYM_UNSIGNED) = (uint64_t) "unsigned";

  character = CHAR_EOF;
  symbol    = SYM_EOF;
}

void reset_scanner() {
  line_number = 1;

  number_of_read_characters = 0;

  get_character();

  number_of_ignored_characters = 0;
  number_of_comments           = 0;
  number_of_scanned_symbols    = 0;
}

// -----------------------------------------------------------------
// ------------------------- SYMBOL TABLE --------------------------
// -----------------------------------------------------------------

void reset_symbol_tables();

uint64_t hash(uint64_t* key);

void create_symbol_table_entry(uint64_t which, uint64_t* string, uint64_t line, uint64_t class, uint64_t type, uint64_t value, uint64_t address);

uint64_t* search_symbol_table(uint64_t* entry, uint64_t* string, uint64_t class);
uint64_t* search_global_symbol_table(uint64_t* string, uint64_t class);
uint64_t* get_scoped_symbol_table_entry(uint64_t* string, uint64_t class);

uint64_t is_undefined_procedure(uint64_t* entry);
uint64_t report_undefined_procedures();

// symbol table entry:
// +----+---------+
// |  0 | next    | pointer to next entry
// |  1 | string  | identifier string, big integer as string, string literal
// |  2 | line#   | source line number
// |  3 | class   | VARIABLE, BIGINT, STRING, PROCEDURE
// |  4 | type    | UINT64_T, UINT64STAR_T, VOID_T
// |  5 | value   | VARIABLE: initial value
// |  6 | address | VARIABLE, BIGINT, STRING: offset, PROCEDURE: address
// |  7 | scope   | REG_GP, REG_FP
// +----+---------+

uint64_t* get_next_entry(uint64_t* entry)  { return (uint64_t*) *entry; }
uint64_t* get_string(uint64_t* entry)      { return (uint64_t*) *(entry + 1); }
uint64_t  get_line_number(uint64_t* entry) { return             *(entry + 2); }
uint64_t  get_class(uint64_t* entry)       { return             *(entry + 3); }
uint64_t  get_type(uint64_t* entry)        { return             *(entry + 4); }
uint64_t  get_value(uint64_t* entry)       { return             *(entry + 5); }
uint64_t  get_address(uint64_t* entry)     { return             *(entry + 6); }
uint64_t  get_scope(uint64_t* entry)       { return             *(entry + 7); }

void set_next_entry(uint64_t* entry, uint64_t* next)   { *entry       = (uint64_t) next; }
void set_string(uint64_t* entry, uint64_t* identifier) { *(entry + 1) = (uint64_t) identifier; }
void set_line_number(uint64_t* entry, uint64_t line)   { *(entry + 2) = line; }
void set_class(uint64_t* entry, uint64_t class)        { *(entry + 3) = class; }
void set_type(uint64_t* entry, uint64_t type)          { *(entry + 4) = type; }
void set_value(uint64_t* entry, uint64_t value)        { *(entry + 5) = value; }
void set_address(uint64_t* entry, uint64_t address)    { *(entry + 6) = address; }
void set_scope(uint64_t* entry, uint64_t scope)        { *(entry + 7) = scope; }

// ------------------------ GLOBAL CONSTANTS -----------------------

// classes
uint64_t VARIABLE  = 1;
uint64_t BIGINT    = 2;
uint64_t STRING    = 3;
uint64_t PROCEDURE = 4;

// types
uint64_t UINT64_T     = 1;
uint64_t UINT64STAR_T = 2;
uint64_t VOID_T       = 3;

// symbol tables
uint64_t GLOBAL_TABLE  = 1;
uint64_t LOCAL_TABLE   = 2;
uint64_t LIBRARY_TABLE = 3;

// hash table size for global symbol table
uint64_t HASH_TABLE_SIZE = 1024;

// ------------------------ GLOBAL VARIABLES -----------------------

// table pointers
uint64_t* global_symbol_table  = (uint64_t*) 0;
uint64_t* local_symbol_table   = (uint64_t*) 0;
uint64_t* library_symbol_table = (uint64_t*) 0;

uint64_t number_of_global_variables = 0;
uint64_t number_of_procedures       = 0;
uint64_t number_of_strings          = 0;

uint64_t number_of_searches = 0;
uint64_t total_search_time  = 0;

// ------------------------- INITIALIZATION ------------------------

void reset_symbol_tables() {
  global_symbol_table  = (uint64_t*) zalloc(HASH_TABLE_SIZE * SIZEOFUINT64STAR);
  local_symbol_table   = (uint64_t*) 0;
  library_symbol_table = (uint64_t*) 0;

  number_of_global_variables = 0;
  number_of_procedures       = 0;
  number_of_strings          = 0;

  number_of_searches = 0;
  total_search_time  = 0;
}

// -----------------------------------------------------------------
// ---------------------------- PARSER -----------------------------
// -----------------------------------------------------------------

void reset_parser();

uint64_t is_not_rbrace_or_eof();
uint64_t is_expression();
uint64_t is_literal();
uint64_t is_star_or_div_or_modulo();
uint64_t is_plus_or_minus();
uint64_t is_comparison();

uint64_t look_for_factor();
uint64_t look_for_statement();
uint64_t look_for_type();

void save_temporaries();
void restore_temporaries(uint64_t number_of_temporaries);

void syntax_error_symbol(uint64_t expected);
void syntax_error_unexpected();
void print_type(uint64_t type);
void type_warning(uint64_t expected, uint64_t found);

uint64_t* get_variable_or_big_int(uint64_t* variable, uint64_t class);
void      load_upper_base_address(uint64_t* entry);
uint64_t  load_variable_or_big_int(uint64_t* variable, uint64_t class);
void      load_integer(uint64_t value);
void      load_string(uint64_t* string);

uint64_t help_call_codegen(uint64_t* entry, uint64_t* procedure);
void     help_procedure_prologue(uint64_t number_of_local_variable_bytes);
void     help_procedure_epilogue(uint64_t number_of_parameter_bytes);

uint64_t compile_call(uint64_t* procedure);
uint64_t compile_factor();
uint64_t compile_term();
uint64_t compile_simple_expression();
uint64_t compile_expression();
void     compile_while();
void     compile_if();
void     compile_return();
void     compile_statement();
uint64_t compile_type();
void     compile_variable(uint64_t offset);
uint64_t compile_initialization(uint64_t type);
void     compile_procedure(uint64_t* procedure, uint64_t type);
void     compile_cstar();

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t allocated_temporaries = 0; // number of allocated temporaries

uint64_t allocated_memory = 0; // number of bytes for global variables and strings

uint64_t return_branches = 0; // fixup chain for return statements

uint64_t return_type = 0; // return type of currently parsed procedure

uint64_t number_of_calls       = 0;
uint64_t number_of_assignments = 0;
uint64_t number_of_while       = 0;
uint64_t number_of_if          = 0;
uint64_t number_of_return      = 0;

// ------------------------- INITIALIZATION ------------------------

void reset_parser() {
  number_of_calls       = 0;
  number_of_assignments = 0;
  number_of_while       = 0;
  number_of_if          = 0;
  number_of_return      = 0;

  get_symbol();
}

// -----------------------------------------------------------------
// ---------------------- MACHINE CODE LIBRARY ---------------------
// -----------------------------------------------------------------

void emit_round_up(uint64_t reg, uint64_t m);
void emit_left_shift_by(uint64_t reg, uint64_t b);
void emit_program_entry();
void emit_bootstrapping();

// -----------------------------------------------------------------
// --------------------------- COMPILER ----------------------------
// -----------------------------------------------------------------

void selfie_compile();

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- REGISTER ---------------------------
// -----------------------------------------------------------------

void init_register();

uint64_t* get_register_name(uint64_t reg);
void      print_register_name(uint64_t reg);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t NUMBEROFREGISTERS   = 32;
uint64_t NUMBEROFTEMPORARIES = 7;

uint64_t REG_ZR  = 0;
uint64_t REG_RA  = 1;
uint64_t REG_SP  = 2;
uint64_t REG_GP  = 3;
uint64_t REG_TP  = 4;
uint64_t REG_T0  = 5;
uint64_t REG_T1  = 6;
uint64_t REG_T2  = 7;
uint64_t REG_FP  = 8;
uint64_t REG_S1  = 9;
uint64_t REG_A0  = 10;
uint64_t REG_A1  = 11;
uint64_t REG_A2  = 12;
uint64_t REG_A3  = 13;
uint64_t REG_A4  = 14;
uint64_t REG_A5  = 15;
uint64_t REG_A6  = 16;
uint64_t REG_A7  = 17;
uint64_t REG_S2  = 18;
uint64_t REG_S3  = 19;
uint64_t REG_S4  = 20;
uint64_t REG_S5  = 21;
uint64_t REG_S6  = 22;
uint64_t REG_S7  = 23;
uint64_t REG_S8  = 24;
uint64_t REG_S9  = 25;
uint64_t REG_S10 = 26;
uint64_t REG_S11 = 27;
uint64_t REG_T3  = 28;
uint64_t REG_T4  = 29;
uint64_t REG_T5  = 30;
uint64_t REG_T6  = 31;

uint64_t* REGISTERS; // strings representing registers

// ------------------------- INITIALIZATION ------------------------

void init_register() {
  REGISTERS = smalloc(NUMBEROFREGISTERS * SIZEOFUINT64STAR);

  *(REGISTERS + REG_ZR)  = (uint64_t) "$zero";
  *(REGISTERS + REG_RA)  = (uint64_t) "$ra";
  *(REGISTERS + REG_SP)  = (uint64_t) "$sp";
  *(REGISTERS + REG_GP)  = (uint64_t) "$gp";
  *(REGISTERS + REG_TP)  = (uint64_t) "$tp";
  *(REGISTERS + REG_T0)  = (uint64_t) "$t0";
  *(REGISTERS + REG_T1)  = (uint64_t) "$t1";
  *(REGISTERS + REG_T2)  = (uint64_t) "$t2";
  *(REGISTERS + REG_FP)  = (uint64_t) "$fp";
  *(REGISTERS + REG_S1)  = (uint64_t) "$s1";
  *(REGISTERS + REG_A0)  = (uint64_t) "$a0";
  *(REGISTERS + REG_A1)  = (uint64_t) "$a1";
  *(REGISTERS + REG_A2)  = (uint64_t) "$a2";
  *(REGISTERS + REG_A3)  = (uint64_t) "$a3";
  *(REGISTERS + REG_A4)  = (uint64_t) "$a4";
  *(REGISTERS + REG_A5)  = (uint64_t) "$a5";
  *(REGISTERS + REG_A6)  = (uint64_t) "$a6";
  *(REGISTERS + REG_A7)  = (uint64_t) "$a7";
  *(REGISTERS + REG_S2)  = (uint64_t) "$s2";
  *(REGISTERS + REG_S3)  = (uint64_t) "$s3";
  *(REGISTERS + REG_S4)  = (uint64_t) "$s4";
  *(REGISTERS + REG_S5)  = (uint64_t) "$s5";
  *(REGISTERS + REG_S6)  = (uint64_t) "$s6";
  *(REGISTERS + REG_S7)  = (uint64_t) "$s7";
  *(REGISTERS + REG_S8)  = (uint64_t) "$s8";
  *(REGISTERS + REG_S9)  = (uint64_t) "$s9";
  *(REGISTERS + REG_S10) = (uint64_t) "$s10";
  *(REGISTERS + REG_S11) = (uint64_t) "$s11";
  *(REGISTERS + REG_T3)  = (uint64_t) "$t3";
  *(REGISTERS + REG_T4)  = (uint64_t) "$t4";
  *(REGISTERS + REG_T5)  = (uint64_t) "$t5";
  *(REGISTERS + REG_T6)  = (uint64_t) "$t6";
}

// -----------------------------------------------------------------
// ------------------------ ENCODER/DECODER ------------------------
// -----------------------------------------------------------------

void check_immediate_range(uint64_t found, uint64_t bits);

uint64_t encode_r_format(uint64_t funct7, uint64_t rs2, uint64_t rs1, uint64_t funct3, uint64_t rd, uint64_t opcode);
uint64_t get_funct7(uint64_t instruction);
uint64_t get_rs2(uint64_t instruction);
uint64_t get_rs1(uint64_t instruction);
uint64_t get_funct3(uint64_t instruction);
uint64_t get_rd(uint64_t instruction);
uint64_t get_opcode(uint64_t instruction);
void     decode_r_format();

uint64_t encode_i_format(uint64_t immediate, uint64_t rs1, uint64_t funct3, uint64_t rd, uint64_t opcode);
uint64_t get_immediate_i_format(uint64_t instruction);
void     decode_i_format();

uint64_t encode_s_format(uint64_t immediate, uint64_t rs2, uint64_t rs1, uint64_t funct3, uint64_t opcode);
uint64_t get_immediate_s_format(uint64_t instruction);
void     decode_s_format();

uint64_t encode_b_format(uint64_t immediate, uint64_t rs2, uint64_t rs1, uint64_t funct3, uint64_t opcode);
uint64_t get_immediate_b_format(uint64_t instruction);
void     decode_b_format();

uint64_t encode_j_format(uint64_t immediate, uint64_t rd, uint64_t opcode);
uint64_t get_immediate_j_format(uint64_t instruction);
void     decode_j_format();

uint64_t encode_u_format(uint64_t immediate, uint64_t rd, uint64_t opcode);
uint64_t get_immediate_u_format(uint64_t instruction);
void     decode_u_format();

// ------------------------ GLOBAL CONSTANTS -----------------------

// opcodes
uint64_t OP_LD     = 3;   // 0000011, I format (LD)
uint64_t OP_IMM    = 19;  // 0010011, I format (ADDI, NOP)
uint64_t OP_SD     = 35;  // 0100011, S format (SD)
uint64_t OP_OP     = 51;  // 0110011, R format (ADD, SUB, MUL, DIVU, REMU, SLTU)
uint64_t OP_LUI    = 55;  // 0110111, U format (LUI)
uint64_t OP_BRANCH = 99;  // 1100011, B format (BEQ)
uint64_t OP_JALR   = 103; // 1100111, I format (JALR)
uint64_t OP_JAL    = 111; // 1101111, J format (JAL)
uint64_t OP_SYSTEM = 115; // 1110011, I format (ECALL)

// f3-codes
uint64_t F3_NOP   = 0; // 000
uint64_t F3_ADDI  = 0; // 000
uint64_t F3_ADD   = 0; // 000
uint64_t F3_SUB   = 0; // 000
uint64_t F3_MUL   = 0; // 000
uint64_t F3_DIVU  = 5; // 101
uint64_t F3_REMU  = 7; // 111
uint64_t F3_SLTU  = 3; // 011
uint64_t F3_LD    = 3; // 011
uint64_t F3_SD    = 3; // 011
uint64_t F3_BEQ   = 0; // 000
uint64_t F3_JALR  = 0; // 000
uint64_t F3_ECALL = 0; // 000

// f7-codes
uint64_t F7_ADD  = 0;  // 0000000
uint64_t F7_MUL  = 1;  // 0000001
uint64_t F7_SUB  = 32; // 0100000
uint64_t F7_DIVU = 1;  // 0000001
uint64_t F7_REMU = 1;  // 0000001
uint64_t F7_SLTU = 0;  // 0000000

// f12-codes (immediates)
uint64_t F12_ECALL = 0; // 000000000000

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t opcode = 0;
uint64_t rs1    = 0;
uint64_t rs2    = 0;
uint64_t rd     = 0;
uint64_t imm    = 0;
uint64_t funct3 = 0;
uint64_t funct7 = 0;

// -----------------------------------------------------------------
// ---------------------------- BINARY -----------------------------
// -----------------------------------------------------------------

void reset_instruction_counters();

uint64_t get_total_number_of_instructions();

void print_instruction_counter(uint64_t total, uint64_t counter, uint64_t* mnemonics);
void print_instruction_counters();

uint64_t load_instruction(uint64_t baddr);
void     store_instruction(uint64_t baddr, uint64_t instruction);

uint64_t load_data(uint64_t baddr);
void     store_data(uint64_t baddr, uint64_t data);

void emit_instruction(uint64_t instruction);

void emit_nop();

void emit_lui(uint64_t rd, uint64_t immediate);
void emit_addi(uint64_t rd, uint64_t rs1, uint64_t immediate);

void emit_add(uint64_t rd, uint64_t rs1, uint64_t rs2);
void emit_sub(uint64_t rd, uint64_t rs1, uint64_t rs2);
void emit_mul(uint64_t rd, uint64_t rs1, uint64_t rs2);
void emit_divu(uint64_t rd, uint64_t rs1, uint64_t rs2);
void emit_remu(uint64_t rd, uint64_t rs1, uint64_t rs2);
void emit_sltu(uint64_t rd, uint64_t rs1, uint64_t rs2);

void emit_ld(uint64_t rd, uint64_t rs1, uint64_t immediate);
void emit_sd(uint64_t rs1, uint64_t immediate, uint64_t rs2);

void emit_beq(uint64_t rs1, uint64_t rs2, uint64_t immediate);

void emit_jal(uint64_t rd, uint64_t immediate);
void emit_jalr(uint64_t rd, uint64_t rs1, uint64_t immediate);

void emit_ecall();

void fixup_relative_BFormat(uint64_t from_address);
void fixup_relative_JFormat(uint64_t from_address, uint64_t to_address);
void fixlink_relative(uint64_t from_address, uint64_t to_address);

void emit_data_word(uint64_t data, uint64_t offset, uint64_t source_line_number);
void emit_string_data(uint64_t* entry);

void emit_data_segment();

uint64_t* create_elf_header(uint64_t binary_length);
uint64_t  validate_elf_header(uint64_t* header);

uint64_t open_write_only(uint64_t* name);

void selfie_output();

uint64_t* touch(uint64_t* memory, uint64_t length);

void selfie_load();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t MAX_BINARY_LENGTH = 262144; // 256KB = MAX_CODE_LENGTH + MAX_DATA_LENGTH

uint64_t MAX_CODE_LENGTH = 245760; // 240KB
uint64_t MAX_DATA_LENGTH = 16384; // 16KB

uint64_t ELF_HEADER_LEN = 120; // = 64 + 56 bytes (file + program header)

// according to RISC-V pk
uint64_t ELF_ENTRY_POINT = 65536; // = 0x10000 (address of beginning of code)

// ------------------------ GLOBAL VARIABLES -----------------------

// instruction counters

uint64_t ic_lui   = 0;
uint64_t ic_addi  = 0;
uint64_t ic_add   = 0;
uint64_t ic_sub   = 0;
uint64_t ic_mul   = 0;
uint64_t ic_divu  = 0;
uint64_t ic_remu  = 0;
uint64_t ic_sltu  = 0;
uint64_t ic_ld    = 0;
uint64_t ic_sd    = 0;
uint64_t ic_beq   = 0;
uint64_t ic_jal   = 0;
uint64_t ic_jalr  = 0;
uint64_t ic_ecall = 0;

uint64_t* binary        = (uint64_t*) 0; // binary of code and data segments
uint64_t  binary_length = 0; // length of binary in bytes including data segment
uint64_t* binary_name   = (uint64_t*) 0; // file name of binary

uint64_t code_length = 0; // length of code segment in binary in bytes
uint64_t entry_point = 0; // beginning of code segment in virtual address space

uint64_t* code_line_number = (uint64_t*) 0; // code line number per emitted instruction
uint64_t* data_line_number = (uint64_t*) 0; // data line number per emitted data

uint64_t* assembly_name = (uint64_t*) 0; // name of assembly file
uint64_t  assembly_fd   = 0; // file descriptor of open assembly file

uint64_t* ELF_header = (uint64_t*) 0;

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emit_exit();
void implement_exit(uint64_t* context);

void emit_read();
void implement_read(uint64_t* context);

void emit_write();
void implement_write(uint64_t* context);

void     emit_open();
uint64_t down_load_string(uint64_t* table, uint64_t vstring, uint64_t* s);
void     implement_open(uint64_t* context);

void emit_malloc();
void implement_brk(uint64_t* context);

void emit_input();
void implement_input(uint64_t* context);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t debug_read       = 0;
uint64_t debug_write      = 0;
uint64_t debug_open       = 0;
uint64_t debug_brk        = 0;
uint64_t debug_end_point  = 0;
uint64_t no_concrete      = 0;
uint64_t print_branch     = 1;

uint64_t SYSCALL_EXIT  = 93;
uint64_t SYSCALL_READ  = 63;
uint64_t SYSCALL_WRITE = 64;
uint64_t SYSCALL_OPEN  = 1024;
uint64_t SYSCALL_BRK   = 214;
uint64_t SYSCALL_INPUT = 42;

// -----------------------------------------------------------------
// ----------------------- HYPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void      emit_switch();
void      do_switch(uint64_t* to_context, uint64_t timeout);
void      implement_switch();
uint64_t* mipster_switch(uint64_t* to_context, uint64_t timeout);

// ------------------------ GLOBAL CONSTANTS -----------------------

// TODO: fix this syscall for spike
uint64_t SYSCALL_SWITCH = 401;

uint64_t debug_switch = 0;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void init_memory(uint64_t megabytes);

uint64_t load_physical_memory(uint64_t* paddr);
void     store_physical_memory(uint64_t* paddr, uint64_t data);

uint64_t frame_for_page(uint64_t* table, uint64_t page);
uint64_t get_frame_for_page(uint64_t* table, uint64_t page);
uint64_t is_page_mapped(uint64_t* table, uint64_t page);

uint64_t is_valid_virtual_address(uint64_t vaddr);
uint64_t get_page_of_virtual_address(uint64_t vaddr);
uint64_t is_virtual_address_mapped(uint64_t* table, uint64_t vaddr);

uint64_t* tlb(uint64_t* table, uint64_t vaddr);

uint64_t load_virtual_memory(uint64_t* table, uint64_t vaddr);
void     store_virtual_memory(uint64_t* table, uint64_t vaddr, uint64_t data);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t debug_tlb = 0;

uint64_t MEGABYTE = 1048576; // 1MB

uint64_t VIRTUALMEMORYSIZE = 4294967296; // 4GB of virtual memory

uint64_t WORDSIZE       = 4; // in bytes
uint64_t WORDSIZEINBITS = 32;

uint64_t INSTRUCTIONSIZE = 4; // must be the same as WORDSIZE
uint64_t REGISTERSIZE    = 8; // must be twice of WORDSIZE

uint64_t PAGESIZE = 4096; // we use standard 4KB pages

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t page_frame_memory = 0; // size of memory for frames

// ------------------------- INITIALIZATION ------------------------

void init_memory(uint64_t megabytes) {
  if (megabytes > 4096)
    megabytes = 4096;

  page_frame_memory = megabytes * MEGABYTE;
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

void print_code_line_number_for_instruction(uint64_t a);
void print_code_context_for_instruction(uint64_t a);

void print_lui();
void print_lui_before();
void print_lui_after();
void do_lui();
void constrain_lui();

void print_addi();
void print_addi_before();
void print_addi_add_sub_mul_divu_remu_sltu_after();
void do_addi();
void constrain_addi();

void print_add_sub_mul_divu_remu_sltu(uint64_t *mnemonics);
void print_add_sub_mul_divu_remu_sltu_before();

void do_add();
void constrain_add();

void do_sub();
void constrain_sub();

void do_mul();
void constrain_mul();

void do_divu();
void constrain_divu();

void do_remu();
void constrain_remu_step_1();
void constrain_remu();

void do_sltu();
void constrain_sltu();
void backtrack_sltu();

void     print_ld();
void     print_ld_before();
void     print_ld_after(uint64_t vaddr);
uint64_t do_ld();
uint64_t constrain_ld();

void     print_sd();
void     print_sd_before();
void     print_sd_after(uint64_t vaddr);
uint64_t do_sd();
uint64_t constrain_sd();
void     backtrack_sd();

void print_beq();
void print_beq_before();
void print_beq_after();
void do_beq();

void print_jal();
void print_jal_before();
void print_jal_jalr_after();
void do_jal();
void constrain_jal_jalr();

void print_jalr();
void print_jalr_before();
void do_jalr();

void print_ecall();
void print_ecall_before();
void print_ecall_after();
void do_ecall();
void backtrack_ecall();

void print_data_line_number();
void print_data_context(uint64_t data);
void print_data(uint64_t data);
// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t MAX_REPLAY_LENGTH = 100;

// -----------------------------------------------------------------
// ------------------- SYMBOLIC EXECUTION ENGINE -------------------
// -----------------------------------------------------------------

void init_symbolic_engine();

void print_stype(uint64_t stype);
void print_symbolic_memory(uint64_t svc);
void print_symbolic_register(uint64_t reg);

//MSIID
//[in] a modular stride interval
//print a slide of concrete values: {start, start + s, [up, lo], end - s, end}
void print_concrete_bounds(uint64_t start, uint64_t end, uint64_t step);
void print_msiid(uint64_t start, uint64_t end, uint64_t st);

//error case
void print_over_approx();
void print_unreachable(uint64_t* label, uint64_t unreachable_pc);
void error_minuend(uint64_t* operand, uint64_t* operation);
void print_bad_expression();

//MSIID API
//[in] a modular stride interval
//[out] is a correct abstract value (end = start + i*s)
uint64_t is_erroneous(uint64_t start, uint64_t end, uint64_t step);
//[in] a start, step and MAX value
//[out] return a correct upper bound (up) such that up <= MAX (wrapped thinking)
uint64_t compute_upper_bound(uint64_t start, uint64_t step, uint64_t max);

//soundness and completness conditions
uint64_t add_sub_condition(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2);
uint64_t mul_condition(uint64_t lo, uint64_t up, uint64_t k);
uint64_t remu_condition(uint64_t lo, uint64_t up, uint64_t k);
uint64_t stride_remu_condition(uint64_t lo, uint64_t up, uint64_t step, uint64_t k);
uint64_t is_power_of_two(uint64_t n);
uint64_t gcd(uint64_t n1, uint64_t n2);

void addi_msiid(uint64_t src, uint64_t vaddr);
void add_msiid();
void sub_msiid();
void mul_msiid();
void divu_msiid();
void remu_msiid();
//stlu ?? (in constrain_memory)

//Pointers API
void addi_pointer(uint64_t src, uint64_t vaddr);
void add_pointer();
void sub_pointer();

//trace
uint64_t is_trace_space_available();
void ealloc();
void efree();

uint64_t is_symbolic_value(uint64_t type);
uint64_t is_safe_address(uint64_t vaddr, uint64_t reg);

uint64_t load_symbolic_memory(uint64_t* pt, uint64_t vaddr);
void store_symbolic_memory(uint64_t* pt, uint64_t stc, uint64_t vaddr, uint64_t type, uint64_t lo, uint64_t up, uint64_t step, uint64_t corr_id, uint64_t trb);

//constraints
void fill_constraint_buffer(uint64_t stc, uint64_t vaddr, uint64_t t, uint64_t h, uint64_t exp, uint64_t col, uint64_t cou, uint64_t f);
void store_propagate_constraint(uint64_t typ, uint64_t stc, uint64_t vaddr, uint64_t lo, uint64_t up, uint64_t step, uint64_t trb);
void store_constrained_memory(uint64_t type, uint64_t stc, uint64_t vaddr, uint64_t lo, uint64_t up, uint64_t step, uint64_t trb);
void store_register_memory(uint64_t reg, uint64_t value);

void constrain_memory(uint64_t mrvc, uint64_t from, uint64_t lo, uint64_t up, uint64_t trb);
void set_constraint(uint64_t reg, uint64_t stc, uint64_t vaddr, uint64_t start, uint64_t end, uint64_t step);
void set_correction(uint64_t reg, uint64_t hasmn, uint64_t expr, uint64_t colos, uint64_t coups, uint64_t operand);

//branch
void take_branch(uint64_t b, uint64_t how_many_more);
void create_constraints(uint64_t lo1, uint64_t up1, uint64_t s1, uint64_t lo2, uint64_t up2, uint64_t s2, uint64_t trb, uint64_t how_many_more);

//fuzzing input
uint64_t fuzz_lo(uint64_t value);
uint64_t fuzz_up(uint64_t value);

// ------------------------ GLOBAL CONSTANTS -----------------------
uint64_t MAX_TRACE_LENGTH = 100000;
uint64_t MAX_READ         = 10;     // read bound

uint64_t debug_symbolic = 0;

//Abstract Domain types
uint64_t CONCRETE_T   = 0;
uint64_t MSIID_T      = 1;
uint64_t ARRAY_T      = 2;
//uint64_t BITSVECT_T = 3;    next step
//uint64_t INCOMPLETE_T = 4;  next step

//reg_expr completness watchdog
uint64_t CONST_T = 0;
uint64_t SUM_T = 1;
uint64_t MUL_T = 2;
uint64_t DIV_T = 3;
uint64_t REM_T = 4;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t has_true_branch  = 1;
uint64_t has_false_branch = 1;

uint64_t tc = 0;        // current trace index
uint64_t mrvc_rs1 = 0;  // rs1's trace index before constraining
uint64_t mrvc_rs2 = 0;  // rs2's trace index before constraining

// trace entry:
// +----+---------+
// |  0 | pc      | pointer to instruction
// |  1 | tc      | previous value of vaddr
// ---------------------- register type
// |  2 | stc     | source index
// |  3 | vaddr   | virtual address
// |  4 | type    | CONCRETE_T, MSIID_T, ARRAY_T
// |  5 | alpha1  | CONCRETE_T: value, MSIID_T: starting value, ARRAY_T: pointer value
// |  6 | alpha2  | MSIID_T: ending value, ARRAY_T: base
// |  7 | alpha3  | MSIID_T: step, ARRAY_T: size
// |  8 | corrs   | MSIID_T: correction, remember the relationship betw. src address
// +----+---------+

// trace entry
uint64_t* pcs = (uint64_t*) 0;    // trace of program counter values
uint64_t* tcs = (uint64_t*) 0;    // trace of trace counters to previous values
// memory link
uint64_t* stcs = (uint64_t*) 0;   // trace of source indexes
uint64_t* vaddrs = (uint64_t*) 0; // trace of virtual addresses
// abstract
uint64_t* types     = (uint64_t*) 0;
uint64_t* alpha1s   = (uint64_t*) 0;
uint64_t* alpha2s   = (uint64_t*) 0;
uint64_t* alpha3s   = (uint64_t*) 0;
uint64_t* corrs     = (uint64_t*) 0;

// correction entry
uint64_t cc = 0;  // current correction index
uint64_t* hasmns    = (uint64_t*) 0;
uint64_t* exprs     = (uint64_t*) 0;
uint64_t* colos     = (uint64_t*) 0;
uint64_t* coups     = (uint64_t*) 0;
uint64_t* factors   = (uint64_t*) 0;

// buffer correction (used in constrain_memory): symbolic register tvp
uint64_t buffer_typ       =  0;
uint64_t buffer_vaddr     =  0;
uint64_t buffer_stc       =  0;
uint64_t buffer_hasmn     =  0;
uint64_t buffer_expr      =  0;
uint64_t buffer_colo      =  0;
uint64_t buffer_coup      =  0;
uint64_t buffer_factor    =  0;

// read history
uint64_t number_of_reads  = 0;     // number of reads
uint64_t rcc = 0;     // read current counter
uint64_t* stored_read_tcs    = (uint64_t*) 0;
uint64_t* stored_read_values = (uint64_t*) 0;

uint64_t  get_trace_pc(uint64_t index)     { return *(pcs + index);}
uint64_t  get_trace_tc(uint64_t index)     { return *(tcs + index);}
uint64_t  get_trace_src(uint64_t index)    { return *(stcs + index);}
uint64_t  get_trace_vaddr(uint64_t index)  { return *(vaddrs + index);}
uint64_t  get_trace_type(uint64_t index)   { return *(types + index);}
uint64_t  get_trace_a1(uint64_t index)     { return *(alpha1s + index);}
uint64_t  get_trace_a2(uint64_t index)     { return *(alpha2s + index);}
uint64_t  get_trace_a3(uint64_t index)     { return *(alpha3s + index);}
uint64_t  get_trace_corr(uint64_t index)   { return *(corrs + index);}

void  set_trace_pc(uint64_t index, uint64_t st_pc)        { *(pcs + index)      = st_pc;}
void  set_trace_tc(uint64_t index, uint64_t st_idx)       { *(tcs + index)      = st_idx;}
void  set_trace_src(uint64_t index, uint64_t st_src)      { *(stcs + index)     = st_src;}
void  set_trace_vaddr(uint64_t index, uint64_t st_vaddr)  { *(vaddrs + index)   = st_vaddr;}
void  set_trace_type(uint64_t index, uint64_t st_typ)     { *(types + index)    = st_typ;}
void  set_trace_a1(uint64_t index, uint64_t st_a1)        { *(alpha1s + index)  = st_a1;}
void  set_trace_a2(uint64_t index, uint64_t st_a2)        { *(alpha2s + index)  = st_a2;}
void  set_trace_a3(uint64_t index, uint64_t st_a3)        { *(alpha3s + index)  = st_a3;}
void  set_trace_corr(uint64_t index, uint64_t st_corr)    { *(corrs + index)    = st_corr;}

void print_trace();
void print_src_list(uint64_t idx);
uint64_t get_src_input(uint64_t idx); //witness

// registers
// abstract domains for tempory computations
uint64_t* reg_typ   = (uint64_t*) 0;  // type: memory range | integer interval
// abstract domain values (alpha)
uint64_t* reg_stc  = (uint64_t*) 0;     // source indexes (renaming)
uint64_t* reg_vaddr  = (uint64_t*) 0;   // vaddr of constrained memory
//uint64_t* reg_alpha1 = (uint64_t*) 0; // lower bound pt: value --> registers
uint64_t* reg_alpha2 = (uint64_t*) 0;   // upper bound | pt: start
uint64_t* reg_alpha3 = (uint64_t*) 0;   // step | pt: size

// MSIID_T Zone 1 (complete with correction)
// accumumated constraints
uint64_t* reg_hasmn   = (uint64_t*) 0;  // constraint has minuend
uint64_t* reg_expr    = (uint64_t*) 0;  // constraint can be corrected
uint64_t* reg_colos   = (uint64_t*) 0;  // offset on lower bound
uint64_t* reg_coups   = (uint64_t*) 0;  // offset on upper bound
uint64_t* reg_factor  = (uint64_t*) 0;  // constant operand in a mdr

// trace counter of most recent constraint
uint64_t mrcc = 0;

// fuzzing
uint64_t fuzz = 0; // power-of-two fuzzing factor for read calls

// line exit code
uint64_t last_jal_from = 0;

// ------------------------- INITIALIZATION ------------------------

void init_symbolic_engine() {
  uint64_t i;

  pcs     = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  tcs     = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  types   = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  stcs    = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  vaddrs  = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  alpha1s = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  alpha2s = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  alpha3s = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  corrs   = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);

  hasmns    = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  exprs     = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  colos     = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  coups     = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  factors   = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);

  stored_read_values = zalloc(MAX_READ * SIZEOFUINT64);
  stored_read_tcs    = zalloc(MAX_READ * SIZEOFUINT64);

  reg_typ       = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_stc       = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_vaddr     = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  //reg_alpha1  = zalloc(NUMBEROFREGISTERS * REGISTERSIZE); == registers
  reg_alpha2    = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_alpha3    = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_hasmn     = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_expr      = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_colos     = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_coups     = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_factor    = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);

  // initialise registers with concrete value (step 1) -->####
  i = 0;
  while (i < NUMBEROFREGISTERS) {
    *(reg_alpha3 + i) = 1;
    i = i + 1;
  }
}

// -----------------------------------------------------------------
// ----------------------- TAINT ANALYSIS  -------------------------
// -----------------------------------------------------------------

// ------------------------ GLOBAL CONSTANTS -----------------------
// ops
uint64_t ADD  = 0;
uint64_t SUB  = 1;
uint64_t MUL  = 2;
uint64_t DIVU = 3;
uint64_t REMU = 4;
uint64_t SLTU = 5;

//tables length
uint64_t MAXPROBLEMATICINSTR = 30;

uint64_t sdebug_context   = 0;
uint64_t sdebug_trace     = 0;
uint64_t sdebug_propagate = 0;

// ------------------------ GLOBAL VARIABLES -----------------------
uint64_t do_taint_flag = 0;

uint64_t* taints    = (uint64_t*) 0;         // trace of tainted addresses
uint64_t* minuends  = (uint64_t*) 0;         // trace of minuend addresses
uint64_t* has_steps = (uint64_t*) 0;         // trace of strides

uint64_t* reg_is_tainted   = (uint64_t*) 0;   // is register tainted
uint64_t* reg_is_minuend   = (uint64_t*) 0;   // is register tainted
uint64_t* reg_has_step     = (uint64_t*) 0;   // register step

uint64_t to_store_taint   = 0;                 // to store taint in trace
uint64_t to_store_minuend = 0;                 // to store minuend in trace
uint64_t to_store_step    = 0;                 // to store step in trace

// problematic instructions
uint64_t* minuends_pcs = (uint64_t*) 0;
uint64_t minuends_size = 0;

uint64_t* addsub_incompleteness_pcs = (uint64_t*) 0;
uint64_t addsub_size = 0;

uint64_t* both_symbolics_pcs = (uint64_t*) 0;
uint64_t  both_symbolics_size = 0;
// symbolic numerical statistics
// addi
uint64_t nb_addis = 0;
// add
uint64_t nb_addrs1  = 0;
uint64_t nb_addrs2  = 0;
uint64_t nb_addss   = 0;
// sub
uint64_t nb_subrs1  = 0;
uint64_t nb_subrs2  = 0;
uint64_t nb_subss   = 0;
// mul
uint64_t nb_mulrs1  = 0;
uint64_t nb_mulrs2  = 0;
uint64_t nb_mulss   = 0;
// div
uint64_t nb_divurs1 = 0;
uint64_t nb_divurs2 = 0;
uint64_t nb_divuss  = 0;
// mod
uint64_t nb_remurs1 = 0;
uint64_t nb_remurs2 = 0;
uint64_t nb_remuss  = 0;

uint64_t nb_slturs1 = 0;
uint64_t nb_slturs2 = 0;
uint64_t nb_sltuss  = 0;

void taint_unop();
void taint_binop(uint64_t op);
void incr_opss(uint64_t op);
void incr_oprs1(uint64_t op);
void incr_oprs2(uint64_t op);

void check_step();
void step_opss(uint64_t op);
void step_oprs1(uint64_t op);
void step_oprs2(uint64_t op);

void check_signed_mul();

void set_taint_memory(uint64_t is_taint, uint64_t is_minuend, uint64_t hasstep);
void store_taint_memory(uint64_t offset);

void push_new_entry(uint64_t hot_pc);
void push_new_entry_step(uint64_t hot_pc);
void push_new_symbollic_entry(uint64_t hot_pc);
// ------------------------- INITIALIZATION ------------------------

void init_taint_engine() {
  taints    = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  minuends  = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);
  has_steps  = zalloc(MAX_TRACE_LENGTH * SIZEOFUINT64);

  reg_is_tainted   = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_is_minuend   = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_has_step     = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);

  minuends_pcs              = zalloc(MAXPROBLEMATICINSTR * SIZEOFUINT64);
  addsub_incompleteness_pcs = zalloc(MAXPROBLEMATICINSTR * SIZEOFUINT64);
  both_symbolics_pcs        = zalloc(MAXPROBLEMATICINSTR * SIZEOFUINT64);
}
// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void init_interpreter();
void reset_interpreter();

void     print_register_hexadecimal(uint64_t reg);
void     print_register_octal(uint64_t reg);
uint64_t is_system_register(uint64_t reg);
void     print_register_value(uint64_t reg);

void print_exception(uint64_t exception, uint64_t faulting_page);
void throw_exception(uint64_t exception, uint64_t faulting_page);

void fetch();
void decode_execute();
void interrupt();

uint64_t* run_until_exception();

uint64_t instruction_with_max_counter(uint64_t* counters, uint64_t max);
uint64_t print_per_instruction_counter(uint64_t total, uint64_t* counters, uint64_t max);
void     print_per_instruction_profile(uint64_t* message, uint64_t total, uint64_t* counters);

void print_profile();

void selfie_disassemble(uint64_t verbose);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t EXCEPTION_NOEXCEPTION        = 0;
uint64_t EXCEPTION_PAGEFAULT          = 1;
uint64_t EXCEPTION_SYSCALL            = 2;
uint64_t EXCEPTION_TIMER              = 3;
uint64_t EXCEPTION_INVALIDADDRESS     = 4;
uint64_t EXCEPTION_DIVISIONBYZERO     = 5;
uint64_t EXCEPTION_UNKNOWNINSTRUCTION = 6;
uint64_t EXCEPTION_MAXTRACE           = 7;
uint64_t EXCEPTION_INCOMPLETENESS     = 8;

uint64_t* EXCEPTIONS; // strings representing exceptions

uint64_t debug_exception = 0;

// enables recording, disassembling, debugging, and symbolically executing code
uint64_t debug = 0;

uint64_t execute     = 0; // flag for executing code
uint64_t disassemble = 0; // flag for disassembling code
uint64_t symbolic    = 0; // flag for symbolically executing code
uint64_t backtrack   = 0; // flag for backtracking symbolic execution

uint64_t disassemble_verbose = 0; // flag for disassembling code in more detail

// number of instructions from context switch to timer interrupt
// CAUTION: avoid interrupting any kernel activities, keep TIMESLICE large
// TODO: implement proper interrupt controller to turn interrupts on and off
uint64_t TIMESLICE = 10000000;

uint64_t TIMEROFF = 0;

// ------------------------ GLOBAL VARIABLES -----------------------

// hardware thread state

uint64_t pc = 0; // program counter
uint64_t ir = 0; // instruction register

uint64_t* registers = (uint64_t*) 0; // general-purpose registers

uint64_t* pt = (uint64_t*) 0; // page table

// core state

uint64_t timer = 0; // counter for timer interrupt
uint64_t trap  = 0; // flag for creating a trap

// profile

uint64_t  calls               = 0;             // total number of executed procedure calls
uint64_t* calls_per_procedure = (uint64_t*) 0; // number of executed calls of each procedure

uint64_t  iterations          = 0;             // total number of executed loop iterations
uint64_t* iterations_per_loop = (uint64_t*) 0; // number of executed iterations of each loop

uint64_t* loads_per_instruction  = (uint64_t*) 0; // number of executed loads per load instruction
uint64_t* stores_per_instruction = (uint64_t*) 0; // number of executed stores per store instruction

// ------------------------- INITIALIZATION ------------------------

void init_interpreter() {
  EXCEPTIONS = smalloc((EXCEPTION_INCOMPLETENESS + 1) * SIZEOFUINT64STAR);

  *(EXCEPTIONS + EXCEPTION_NOEXCEPTION)        = (uint64_t) "no exception";
  *(EXCEPTIONS + EXCEPTION_PAGEFAULT)          = (uint64_t) "page fault";
  *(EXCEPTIONS + EXCEPTION_SYSCALL)            = (uint64_t) "syscall";
  *(EXCEPTIONS + EXCEPTION_TIMER)              = (uint64_t) "timer interrupt";
  *(EXCEPTIONS + EXCEPTION_INVALIDADDRESS)     = (uint64_t) "invalid address";
  *(EXCEPTIONS + EXCEPTION_DIVISIONBYZERO)     = (uint64_t) "division by zero";
  *(EXCEPTIONS + EXCEPTION_UNKNOWNINSTRUCTION) = (uint64_t) "unknown instruction";
  *(EXCEPTIONS + EXCEPTION_MAXTRACE)           = (uint64_t) "trace length exceeded";
  *(EXCEPTIONS + EXCEPTION_INCOMPLETENESS)      = (uint64_t) "incomplete abstraction";
}

void reset_interpreter() {
  pc = 0;
  ir = 0;

  registers = (uint64_t*) 0;

  pt = (uint64_t*) 0;

  trap = 0;

  timer = TIMEROFF;

  if (execute) {
    reset_instruction_counters();

    calls               = 0;
    calls_per_procedure = zalloc(MAX_CODE_LENGTH / INSTRUCTIONSIZE * SIZEOFUINT64);

    iterations          = 0;
    iterations_per_loop = zalloc(MAX_CODE_LENGTH / INSTRUCTIONSIZE * SIZEOFUINT64);

    loads_per_instruction  = zalloc(MAX_CODE_LENGTH / INSTRUCTIONSIZE * SIZEOFUINT64);
    stores_per_instruction = zalloc(MAX_CODE_LENGTH / INSTRUCTIONSIZE * SIZEOFUINT64);
  }
}

// -----------------------------------------------------------------
// ---------------------------- CONTEXTS ---------------------------
// -----------------------------------------------------------------

uint64_t* allocate_context(uint64_t* parent, uint64_t* vctxt, uint64_t* in);
uint64_t* find_context(uint64_t* parent, uint64_t* vctxt, uint64_t* in);
void      free_context(uint64_t* context);
uint64_t* delete_context(uint64_t* context, uint64_t* from);

// context struct:
// +----+----------------+
// |  0 | next context    | pointer to next context
// |  1 | prev context    | pointer to previous context
// |  2 | program counter | program counter
// |  3 | regs            | pointer to general purpose registers
// |  4 | page table      | pointer to page table
// |  5 | lo page         | lowest low unmapped page
// |  6 | me page         | highest low unmapped page
// |  7 | hi page         | highest high unmapped page
// |  8 | original break  | original end of data segment
// |  9 | program break   | end of data segment
// | 10 | exception       | exception ID
// | 11 | faulting page   | faulting page
// | 12 | exit code       | exit code
// | 13 | parent          | context that created this context
// | 14 | virtual context | virtual context address
// | 15 | name            | binary name loaded into context
// +----+-----------------+

uint64_t next_context(uint64_t* context)    { return (uint64_t) context; }
uint64_t prev_context(uint64_t* context)    { return (uint64_t) (context + 1); }
uint64_t program_counter(uint64_t* context) { return (uint64_t) (context + 2); }
uint64_t regs(uint64_t* context)            { return (uint64_t) (context + 3); }
uint64_t page_table(uint64_t* context)      { return (uint64_t) (context + 4); }
uint64_t lo_page(uint64_t* context)         { return (uint64_t) (context + 5); }
uint64_t me_page(uint64_t* context)         { return (uint64_t) (context + 6); }
uint64_t hi_page(uint64_t* context)         { return (uint64_t) (context + 7); }
uint64_t original_break(uint64_t* context)  { return (uint64_t) (context + 8); }
uint64_t program_break(uint64_t* context)   { return (uint64_t) (context + 9); }
uint64_t exception(uint64_t* context)       { return (uint64_t) (context + 10); }
uint64_t faulting_page(uint64_t* context)   { return (uint64_t) (context + 11); }
uint64_t exit_code(uint64_t* context)       { return (uint64_t) (context + 12); }
uint64_t parent(uint64_t* context)          { return (uint64_t) (context + 13); }
uint64_t virtual_context(uint64_t* context) { return (uint64_t) (context + 14); }
uint64_t name(uint64_t* context)            { return (uint64_t) (context + 15); }

uint64_t* get_next_context(uint64_t* context)    { return (uint64_t*) *context; }
uint64_t* get_prev_context(uint64_t* context)    { return (uint64_t*) *(context + 1); }
uint64_t  get_pc(uint64_t* context)              { return             *(context + 2); }
uint64_t* get_regs(uint64_t* context)            { return (uint64_t*) *(context + 3); }
uint64_t* get_pt(uint64_t* context)              { return (uint64_t*) *(context + 4); }
uint64_t  get_lo_page(uint64_t* context)         { return             *(context + 5); }
uint64_t  get_me_page(uint64_t* context)         { return             *(context + 6); }
uint64_t  get_hi_page(uint64_t* context)         { return             *(context + 7); }
uint64_t  get_original_break(uint64_t* context)  { return             *(context + 8); }
uint64_t  get_program_break(uint64_t* context)   { return             *(context + 9); }
uint64_t  get_exception(uint64_t* context)       { return             *(context + 10); }
uint64_t  get_faulting_page(uint64_t* context)   { return             *(context + 11); }
uint64_t  get_exit_code(uint64_t* context)       { return             *(context + 12); }
uint64_t* get_parent(uint64_t* context)          { return (uint64_t*) *(context + 13); }
uint64_t* get_virtual_context(uint64_t* context) { return (uint64_t*) *(context + 14); }
uint64_t* get_name(uint64_t* context)            { return (uint64_t*) *(context + 15); }
//symbolic exit code
uint64_t  get_exit_code_a2(uint64_t* context)    { return             *(context + 16); }
uint64_t  get_exit_code_a3(uint64_t* context)    { return             *(context + 17); }

void set_next_context(uint64_t* context, uint64_t* next)     { *context        = (uint64_t) next; }
void set_prev_context(uint64_t* context, uint64_t* prev)     { *(context + 1)  = (uint64_t) prev; }
void set_pc(uint64_t* context, uint64_t pc)                  { *(context + 2)  = pc; }
void set_regs(uint64_t* context, uint64_t* regs)             { *(context + 3)  = (uint64_t) regs; }
void set_pt(uint64_t* context, uint64_t* pt)                 { *(context + 4)  = (uint64_t) pt; }
void set_lo_page(uint64_t* context, uint64_t lo_page)        { *(context + 5)  = lo_page; }
void set_me_page(uint64_t* context, uint64_t me_page)        { *(context + 6)  = me_page; }
void set_hi_page(uint64_t* context, uint64_t hi_page)        { *(context + 7)  = hi_page; }
void set_original_break(uint64_t* context, uint64_t brk)     { *(context + 8)  = brk; }
void set_program_break(uint64_t* context, uint64_t brk)      { *(context + 9)  = brk; }
void set_exception(uint64_t* context, uint64_t exception)    { *(context + 10) = exception; }
void set_faulting_page(uint64_t* context, uint64_t page)     { *(context + 11) = page; }
void set_exit_code(uint64_t* context, uint64_t code)         { *(context + 12) = code; }
void set_parent(uint64_t* context, uint64_t* parent)         { *(context + 13) = (uint64_t) parent; }
void set_virtual_context(uint64_t* context, uint64_t* vctxt) { *(context + 14) = (uint64_t) vctxt; }
void set_name(uint64_t* context, uint64_t* name)             { *(context + 15) = (uint64_t) name; }
// symbolic exit code
void set_exit_code_a2(uint64_t* context, uint64_t code)      { *(context + 16) = code; }
void set_exit_code_a3(uint64_t* context, uint64_t code)      { *(context + 17) = code; }

// -----------------------------------------------------------------
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

void reset_microkernel();

uint64_t* create_context(uint64_t* parent, uint64_t* vctxt);

uint64_t* cache_context(uint64_t* vctxt);

void save_context(uint64_t* context);

void map_page(uint64_t* context, uint64_t page, uint64_t frame);

void restore_context(uint64_t* context);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t debug_create = 0;
uint64_t debug_map    = 0;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* current_context = (uint64_t*) 0; // context currently running

uint64_t* used_contexts = (uint64_t*) 0; // doubly-linked list of used contexts
uint64_t* free_contexts = (uint64_t*) 0; // singly-linked list of free contexts

// ------------------------- INITIALIZATION ------------------------

void reset_microkernel() {
  current_context = (uint64_t*) 0;

  while (used_contexts != (uint64_t*) 0)
    used_contexts = delete_context(used_contexts, used_contexts);
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

uint64_t pavailable();
uint64_t pexcess();
uint64_t pused();

uint64_t* palloc();
void      pfree(uint64_t* frame);

void map_and_store(uint64_t* context, uint64_t vaddr, uint64_t data);

void up_load_binary(uint64_t* context);

uint64_t up_load_string(uint64_t* context, uint64_t* s, uint64_t SP);
void     up_load_arguments(uint64_t* context, uint64_t argc, uint64_t* argv);

uint64_t handle_system_call(uint64_t* context);
uint64_t handle_page_fault(uint64_t* context);
uint64_t handle_division_by_zero(uint64_t* context);
uint64_t handle_max_trace(uint64_t* context);
uint64_t handle_timer(uint64_t* context);

uint64_t handle_exception(uint64_t* context);

uint64_t mipster(uint64_t* to_context);
uint64_t hypster(uint64_t* to_context);

uint64_t mixter(uint64_t* to_context, uint64_t mix);

uint64_t minmob(uint64_t* to_context);
void     map_unmapped_pages(uint64_t* context);
uint64_t minster(uint64_t* to_context);
uint64_t mobster(uint64_t* to_context);

void     backtrack_trace(uint64_t* context);
uint64_t monster(uint64_t* to_context);

uint64_t is_boot_level_zero();

uint64_t selfie_run(uint64_t machine);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t* MY_CONTEXT = (uint64_t*) 0;

uint64_t DONOTEXIT = 0;
uint64_t EXIT      = 1;

uint64_t EXITCODE_NOERROR                = 0;
uint64_t EXITCODE_BADARGUMENTS           = 1;
uint64_t EXITCODE_IOERROR                = 2;
uint64_t EXITCODE_SCANNERERROR           = 3;
uint64_t EXITCODE_PARSERERROR            = 4;
uint64_t EXITCODE_COMPILERERROR          = 5;
uint64_t EXITCODE_OUTOFVIRTUALMEMORY     = 6;
uint64_t EXITCODE_OUTOFPHYSICALMEMORY    = 7;
uint64_t EXITCODE_DIVISIONBYZERO         = 8;
uint64_t EXITCODE_UNKNOWNINSTRUCTION     = 9;
uint64_t EXITCODE_UNKNOWNSYSCALL         = 10;
uint64_t EXITCODE_MULTIPLEEXCEPTIONERROR = 11;
uint64_t EXITCODE_SYMBOLICEXECUTIONERROR = 12;
uint64_t EXITCODE_OUTOFTRACEMEMORY       = 13;
uint64_t EXITCODE_INCOMPLETENESS         = 14;
uint64_t EXITCODE_UNCAUGHTEXCEPTION      = 15;

uint64_t SYSCALL_BITWIDTH = 32; // integer bit width for system calls

uint64_t MIPSTER = 1;
uint64_t DIPSTER = 2;
uint64_t RIPSTER = 3;

uint64_t MONSTER = 4;

uint64_t MINSTER = 5;
uint64_t MOBSTER = 6;

uint64_t HYPSTER = 7;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t next_page_frame = 0;

uint64_t allocated_page_frame_memory = 0;
uint64_t free_page_frame_memory      = 0;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------   T H E O R E M  P R O V E R    ----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// -------------------------- SAT Solver ---------------------------
// -----------------------------------------------------------------

uint64_t clause_may_be_true(uint64_t* clause_address, uint64_t depth);
uint64_t instance_may_be_true(uint64_t depth);

uint64_t babysat(uint64_t depth);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t FALSE = 0;
uint64_t TRUE  = 1;

uint64_t UNSAT = 0;
uint64_t SAT   = 1;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* dimacs_name = (uint64_t*) 0;

uint64_t number_of_sat_variables = 0;

// number_of_sat_variables
uint64_t* sat_assignment = (uint64_t*) 0;

uint64_t number_of_sat_clauses = 0;

// number_of_sat_clauses * 2 * number_of_sat_variables
uint64_t* sat_instance = (uint64_t*) 0;

// -----------------------------------------------------------------
// ----------------------- DIMACS CNF PARSER -----------------------
// -----------------------------------------------------------------

void selfie_print_dimacs();

void     dimacs_find_next_character(uint64_t new_line);
void     dimacs_get_symbol();
void     dimacs_word(uint64_t* word);
uint64_t dimacs_number();
void     dimacs_get_clause(uint64_t clause);
void     dimacs_get_instance();

void selfie_load_dimacs();

void selfie_sat();

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

void init_selfie(uint64_t argc, uint64_t* argv);

uint64_t  number_of_remaining_arguments();
uint64_t* remaining_arguments();

uint64_t* peek_argument();
uint64_t* get_argument();
void      set_argument(uint64_t* argv);

void print_usage();

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t  selfie_argc = 0;
uint64_t* selfie_argv = (uint64_t*) 0;

uint64_t* selfie_name = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_selfie(uint64_t argc, uint64_t* argv) {
  selfie_argc = argc;
  selfie_argv = argv;

  selfie_name = get_argument();
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     L I B R A R Y     ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------- LIBRARY PROCEDURES ----------------------
// -----------------------------------------------------------------

uint64_t two_to_the_power_of(uint64_t p) {
  // assert: 0 <= p < CPUBITWIDTH
  return *(power_of_two_table + p);
}

uint64_t ten_to_the_power_of(uint64_t p) {
  // use recursion for simplicity and educational value
  // for p close to 0 performance is not relevant
  if (p == 0)
    return 1;
  else
    return ten_to_the_power_of(p - 1) * 10;
}

uint64_t left_shift(uint64_t n, uint64_t b) {
  // assert: 0 <= b < CPUBITWIDTH
  return n * two_to_the_power_of(b);
}

uint64_t right_shift(uint64_t n, uint64_t b) {
  // assert: 0 <= b < CPUBITWIDTH
  return n / two_to_the_power_of(b);
}

uint64_t get_bits(uint64_t n, uint64_t i, uint64_t b) {
  // assert: 0 < b <= i + b < CPUBITWIDTH
  if (i == 0)
    return n % two_to_the_power_of(b);
  else
    // shift to-be-loaded bits all the way to the left
    // to reset all bits to the left of them, then
    // shift to-be-loaded bits all the way to the right and return
    return right_shift(left_shift(n, CPUBITWIDTH - (i + b)), CPUBITWIDTH - b);
}

uint64_t get_low_word(uint64_t n) {
  return get_bits(n, 0, WORDSIZEINBITS);
}

uint64_t get_high_word(uint64_t n) {
  return get_bits(n, WORDSIZEINBITS, WORDSIZEINBITS);
}

uint64_t absolute(uint64_t n) {
  if (signed_less_than(n, 0))
    return -n;
  else
    return n;
}

uint64_t signed_less_than(uint64_t a, uint64_t b) {
  // INT64_MIN <= n <= INT64_MAX iff
  // INT64_MIN + INT64_MIN <= n + INT64_MIN <= INT64_MAX + INT64_MIN iff
  // -2^64 <= n + INT64_MIN <= 2^64 - 1 (sign-extended to 65 bits) iff
  // 0 <= n + INT64_MIN <= UINT64_MAX
  return a + INT64_MIN < b + INT64_MIN;
}

uint64_t signed_division(uint64_t a, uint64_t b) {
  // assert: b != 0
  // assert: a == INT64_MIN -> b != -1
  if (a == INT64_MIN)
    if (b == INT64_MIN)
      return 1;
    else if (signed_less_than(b, 0))
      return INT64_MIN / absolute(b);
    else
      return -(INT64_MIN / b);
  else if (b == INT64_MIN)
    return 0;
  else if (signed_less_than(a, 0))
    if (signed_less_than(b, 0))
      return absolute(a) / absolute(b);
    else
      return -(absolute(a) / b);
  else if (signed_less_than(b, 0))
    return -(a / absolute(b));
  else
    return a / b;
}

uint64_t is_signed_integer(uint64_t n, uint64_t b) {
  // assert: 0 < b <= CPUBITWIDTH
  if (n < two_to_the_power_of(b - 1))
    // assert: 0 <= n < 2^(b - 1)
    return 1;
  else if (n >= -two_to_the_power_of(b - 1))
    // assert: -2^(b - 1) <= n < 2^64
    return 1;
  else
    return 0;
}

uint64_t sign_extend(uint64_t n, uint64_t b) {
  // assert: 0 <= n <= 2^b
  // assert: 0 < b < CPUBITWIDTH
  if (n < two_to_the_power_of(b - 1))
    return n;
  else
    return n - two_to_the_power_of(b);
}

uint64_t sign_shrink(uint64_t n, uint64_t b) {
  // assert: -2^(b - 1) <= n < 2^(b - 1)
  // assert: 0 < b < CPUBITWIDTH
  return get_bits(n, 0, b);
}

uint64_t load_character(uint64_t* s, uint64_t i) {
  // assert: i >= 0
  uint64_t a;

  // a is the index of the double word where
  // the to-be-loaded i-th character in s is
  a = i / SIZEOFUINT64;

  // return i-th 8-bit character in s
  return get_bits(*(s + a), (i % SIZEOFUINT64) * 8, 8);
}

uint64_t* store_character(uint64_t* s, uint64_t i, uint64_t c) {
  // assert: i >= 0, 0 <= c < 2^8 (all characters are 8-bit)
  uint64_t a;

  // a is the index of the double word where
  // the with c to-be-overwritten i-th character in s is
  a = i / SIZEOFUINT64;

  // subtract the to-be-overwritten character to reset its bits in s
  // then add c to set its bits at the i-th position in s
  *(s + a) = (*(s + a) - left_shift(load_character(s, i), (i % SIZEOFUINT64) * 8)) + left_shift(c, (i % SIZEOFUINT64) * 8);

  return s;
}

uint64_t string_length(uint64_t* s) {
  uint64_t i;

  i = 0;

  while (load_character(s, i) != 0)
    i = i + 1;

  return i;
}

uint64_t* string_copy(uint64_t* s) {
  uint64_t l;
  uint64_t* t;
  uint64_t i;

  l = string_length(s);

  t = zalloc(l + 1);

  i = 0;

  while (i <= l) {
    store_character(t, i, load_character(s, i));

    i = i + 1;
  }

  return t;
}

void string_reverse(uint64_t* s) {
  uint64_t i;
  uint64_t j;
  uint64_t tmp;

  i = 0;
  j = string_length(s) - 1;

  while (i < j) {
    tmp = load_character(s, i);

    store_character(s, i, load_character(s, j));
    store_character(s, j, tmp);

    i = i + 1;
    j = j - 1;
  }
}

uint64_t string_compare(uint64_t* s, uint64_t* t) {
  uint64_t i;

  i = 0;

  while (1)
    if (load_character(s, i) == 0)
      if (load_character(t, i) == 0)
        return 1;
      else
        return 0;
    else if (load_character(s, i) == load_character(t, i))
      i = i + 1;
    else
      return 0;
}

uint64_t atoi(uint64_t* s) {
  uint64_t i;
  uint64_t n;
  uint64_t c;

  // the conversion of the ASCII string in s to its
  // numerical value n begins with the leftmost digit in s
  i = 0;

  // and the numerical value 0 for n
  n = 0;

  // load character (one byte) at index i in s from memory requires
  // bit shifting since memory access can only be done in double words
  c = load_character(s, i);

  // loop until s is terminated
  while (c != 0) {
    // the numerical value of ASCII-encoded decimal digits
    // is offset by the ASCII code of '0' (which is 48)
    c = c - '0';

    if (c > 9) {
      printf2((uint64_t*) "%s: cannot convert non-decimal number %s\n", selfie_name, s);

      exit(EXITCODE_BADARGUMENTS);
    }

    // assert: s contains a decimal number

    // use base 10 but detect wrap around
    if (n < UINT64_MAX / 10)
      n = n * 10 + c;
    else if (n == UINT64_MAX / 10)
      if (c <= UINT64_MAX % 10)
        n = n * 10 + c;
      else {
        // s contains a decimal number larger than UINT64_MAX
        printf2((uint64_t*) "%s: cannot convert out-of-bound number %s\n", selfie_name, s);

        exit(EXITCODE_BADARGUMENTS);
      }
    else {
      // s contains a decimal number larger than UINT64_MAX
      printf2((uint64_t*) "%s: cannot convert out-of-bound number %s\n", selfie_name, s);

      exit(EXITCODE_BADARGUMENTS);
    }

    // go to the next digit
    i = i + 1;

    // load character (one byte) at index i in s from memory requires
    // bit shifting since memory access can only be done in double words
    c = load_character(s, i);
  }

  return n;
}

uint64_t* itoa(uint64_t n, uint64_t* s, uint64_t b, uint64_t a) {
  // assert: b in {2,4,8,10,16}

  uint64_t i;
  uint64_t sign;

  // the conversion of the integer n to an ASCII string in s with
  // base b and alignment a begins with the leftmost digit in s
  i = 0;

  // for now assuming n is positive
  sign = 0;

  if (n == 0) {
    store_character(s, 0, '0');

    i = 1;
  } else if (signed_less_than(n, 0)) {
    if (b == 10) {
      // n is represented as two's complement
      // convert n to a positive number but remember the sign
      n = -n;

      sign = 1;
    }
  }

  while (n != 0) {
    if (n % b > 9)
      // the ASCII code of hexadecimal digits larger than 9
      // is offset by the ASCII code of 'A' (which is 65)
      store_character(s, i, n % b - 10 + 'A');
    else
      // the ASCII code of digits less than or equal to 9
      // is offset by the ASCII code of '0' (which is 48)
      store_character(s, i, n % b + '0');

    // convert n by dividing n with base b
    n = n / b;

    i = i + 1;
  }

  if (b == 10) {
    if (sign) {
      store_character(s, i, '-'); // negative decimal numbers start with -

      i = i + 1;
    }

    while (i < a) {
      store_character(s, i, ' '); // align with spaces

      i = i + 1;
    }
  } else {
    while (i < a) {
      store_character(s, i, '0'); // align with 0s

      i = i + 1;
    }

    if (b == 8) {
      store_character(s, i, '0'); // octal numbers start with 00
      store_character(s, i + 1, '0');

      i = i + 2;
    } else if (b == 16) {
      store_character(s, i, 'x'); // hexadecimal numbers start with 0x
      store_character(s, i + 1, '0');

      i = i + 2;
    }
  }

  store_character(s, i, 0); // null-terminated string

  // our numeral system is positional hindu-arabic, that is,
  // the weight of digits increases right to left, which means
  // that we need to reverse the string we computed above
  string_reverse(s);

  return s;
}

uint64_t fixed_point_ratio(uint64_t a, uint64_t b, uint64_t f) {
  // compute fixed point ratio with f fractional digits
  // multiply a/b with 10^f but avoid wrap around

  uint64_t p;

  p = f;

  while (p > 0) {
    if (a <= UINT64_MAX / ten_to_the_power_of(p)) {
      if (b / ten_to_the_power_of(f - p) != 0)
        return (a * ten_to_the_power_of(p)) / (b / ten_to_the_power_of(f - p));
    }

    p = p - 1;
  }

  return 0;
}

uint64_t fixed_point_percentage(uint64_t r, uint64_t f) {
  if (r != 0)
    // 10^4 (for 100.00%) * 10^f (for f fractional digits of r)
    return ten_to_the_power_of(4 + f) / r;
  else
    return 0;
}

void put_character(uint64_t c) {
  *character_buffer = c;

  // assert: character_buffer is mapped

  // try to write 1 character from character_buffer
  // into file with output_fd file descriptor
  if (write(output_fd, character_buffer, 1) == 1) {
    if (output_fd != 1)
      // count number of characters written to a file,
      // not the console which has file descriptor 1
      number_of_written_characters = number_of_written_characters + 1;
  } else {
    // write failed
    if (output_fd != 1) {
      // failed write was not to the console which has file descriptor 1
      // to report the error we may thus still write to the console
      output_fd = 1;

      printf2((uint64_t*) "%s: could not write character to output file %s\n", selfie_name, output_name);
    }

    exit(EXITCODE_IOERROR);
  }
}

void print(uint64_t* s) {
  uint64_t i;

  if (s == (uint64_t*) 0)
    print((uint64_t*) "NULL");
  else {
    i = 0;

    while (load_character(s, i) != 0) {
      put_character(load_character(s, i));

      i = i + 1;
    }
  }
}

void println() {
  put_character(CHAR_LF);
}

void print_character(uint64_t c) {
  put_character(CHAR_SINGLEQUOTE);

  if (c == CHAR_EOF)
    print((uint64_t*) "end of file");
  else if (c == CHAR_TAB)
    print((uint64_t*) "tabulator");
  else if (c == CHAR_LF)
    print((uint64_t*) "line feed");
  else if (c == CHAR_CR)
    print((uint64_t*) "carriage return");
  else
    put_character(c);

  put_character(CHAR_SINGLEQUOTE);
}

void print_string(uint64_t* s) {
  put_character(CHAR_DOUBLEQUOTE);

  print(s);

  put_character(CHAR_DOUBLEQUOTE);
}

void print_integer(uint64_t n) {
  print(itoa(n, integer_buffer, 10, 0));
}

void unprint_integer(uint64_t n) {
  n = string_length(itoa(n, integer_buffer, 10, 0));

  while (n > 0) {
    put_character(CHAR_BACKSPACE);

    n = n - 1;
  }
}

void print_hexadecimal(uint64_t n, uint64_t a) {
  print(itoa(n, integer_buffer, 16, a));
}

void print_octal(uint64_t n, uint64_t a) {
  print(itoa(n, integer_buffer, 8, a));
}

void print_binary(uint64_t n, uint64_t a) {
  print(itoa(n, integer_buffer, 2, a));
}

uint64_t print_format0(uint64_t* s, uint64_t i) {
  // print string s from index i on
  // ignore % formatting codes except for %%
  if (s == (uint64_t*) 0)
    return 0;
  else {
    while (load_character(s, i) != 0) {
      if (load_character(s, i) != '%') {
        put_character(load_character(s, i));

        i = i + 1;
      } else if (load_character(s, i + 1) == '%') {
        // for %% print just one %
        put_character('%');

        i = i + 2;
      } else {
        put_character(load_character(s, i));

        i = i + 1;
      }
    }

    return i;
  }
}

uint64_t print_format1(uint64_t* s, uint64_t i, uint64_t* a) {
  // print string s from index i on until next % formatting code except for %%
  // then print argument a according to the encountered % formatting code

  uint64_t p;

  if (s == (uint64_t*) 0)
    return 0;
  else {
    while (load_character(s, i) != 0) {
      if (load_character(s, i) != '%') {
        put_character(load_character(s, i));

        i = i + 1;
      } else if (load_character(s, i + 1) == 's') {
        print(a);

        return i + 2;
      } else if (load_character(s, i + 1) == 'c') {
        put_character((uint64_t) a);

        return i + 2;
      } else if (load_character(s, i + 1) == 'd') {
        print_integer((uint64_t) a);

        return i + 2;
      } else if (load_character(s, i + 1) == '.') {
        // for simplicity we support a single digit only
        p = load_character(s, i + 2) - '0';

        if (p < 10) {
          // the character at i + 2 is in fact a digit
          print_integer((uint64_t) a / ten_to_the_power_of(p));

          if (p > 0) {
            // using integer_buffer here is ok since we are not using print_integer
            itoa((uint64_t) a % ten_to_the_power_of(p), integer_buffer, 10, 0);
            p = p - string_length(integer_buffer);

            put_character('.');
            while (p > 0) {
              put_character('0');

              p = p - 1;
            }
            print(integer_buffer);
          }

          return i + 4;
        } else {
          put_character(load_character(s, i));

          i = i + 1;
        }
      } else if (load_character(s, i + 1) == 'p') {
        print_hexadecimal((uint64_t) a, SIZEOFUINT64STAR);

        return i + 2;
      } else if (load_character(s, i + 1) == 'x') {
        print_hexadecimal((uint64_t) a, 0);

        return i + 2;
      } else if (load_character(s, i + 1) == 'o') {
        print_octal((uint64_t) a, 0);

        return i + 2;
      } else if (load_character(s, i + 1) == 'b') {
        print_binary((uint64_t) a, 0);

        return i + 2;
      } else if (load_character(s, i + 1) == '%') {
        // for %% print just one %
        put_character('%');

        i = i + 2;
      } else {
        put_character(load_character(s, i));

        i = i + 1;
      }
    }

    return i;
  }
}

void printf1(uint64_t* s, uint64_t* a1) {
  print_format0(s, print_format1(s, 0, a1));
}

void printf2(uint64_t* s, uint64_t* a1, uint64_t* a2) {
  print_format0(s, print_format1(s, print_format1(s, 0, a1), a2));
}

void printf3(uint64_t* s, uint64_t* a1, uint64_t* a2, uint64_t* a3) {
  print_format0(s, print_format1(s, print_format1(s, print_format1(s, 0, a1), a2), a3));
}

void printf4(uint64_t* s, uint64_t* a1, uint64_t* a2, uint64_t* a3, uint64_t* a4) {
  print_format0(s, print_format1(s, print_format1(s, print_format1(s, print_format1(s, 0, a1), a2), a3), a4));
}

void printf5(uint64_t* s, uint64_t* a1, uint64_t* a2, uint64_t* a3, uint64_t* a4, uint64_t* a5) {
  print_format0(s, print_format1(s, print_format1(s, print_format1(s, print_format1(s, print_format1(s, 0, a1), a2), a3), a4), a5));
}

void printf6(uint64_t* s, uint64_t* a1, uint64_t* a2, uint64_t* a3, uint64_t* a4, uint64_t* a5, uint64_t* a6) {
  print_format0(s, print_format1(s, print_format1(s, print_format1(s, print_format1(s, print_format1(s, print_format1(s, 0, a1), a2), a3), a4), a5), a6));
}

uint64_t round_up(uint64_t n, uint64_t m) {
  if (n % m == 0)
    return n;
  else
    return n - n % m + m;
}

uint64_t* smalloc(uint64_t size) {
  // this procedure ensures a defined program exit,
  // if no memory can be allocated
  uint64_t* memory;

  memory = malloc(size);

  if (size == 0)
    // any address including null
    return memory;
  else if ((uint64_t) memory == 0) {
    printf1((uint64_t*) "%s: malloc out of memory\n", selfie_name);

    exit(EXITCODE_OUTOFVIRTUALMEMORY);
  }

  return memory;
}

uint64_t* zalloc(uint64_t size) {
  // this procedure is only executed at boot level zero
  // zalloc allocates size bytes rounded up to word size
  // and then zeroes that memory, similar to calloc, but
  // called zalloc to avoid redeclaring calloc
  uint64_t* memory;
  uint64_t  i;

  size = round_up(size, REGISTERSIZE);

  memory = smalloc(size);

  size = size / REGISTERSIZE;

  i = 0;

  while (i < size) {
    // erase memory by setting it to 0
    *(memory + i) = 0;

    i = i + 1;
  }

  return memory;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------    C O M P I L E R    ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- SCANNER ----------------------------
// -----------------------------------------------------------------

void print_symbol(uint64_t symbol) {
  put_character(CHAR_DOUBLEQUOTE);

  if (symbol == SYM_EOF)
    print((uint64_t*) "end of file");
  else
    print((uint64_t*) *(SYMBOLS + symbol));

  put_character(CHAR_DOUBLEQUOTE);
}

void print_line_number(uint64_t* message, uint64_t line) {
  printf4((uint64_t*) "%s: %s in %s in line %d: ", selfie_name, message, source_name, (uint64_t*) line);
}

void syntax_error_message(uint64_t* message) {
  print_line_number((uint64_t*) "syntax error", line_number);
  printf1((uint64_t*) "%s\n", message);
}

void syntax_error_character(uint64_t expected) {
  print_line_number((uint64_t*) "syntax error", line_number);
  print_character(expected);
  print((uint64_t*) " expected but ");
  print_character(character);
  print((uint64_t*) " found\n");
}

void syntax_error_identifier(uint64_t* expected) {
  print_line_number((uint64_t*) "syntax error", line_number);
  print_string(expected);
  print((uint64_t*) " expected but ");
  print_string(identifier);
  print((uint64_t*) " found\n");
}

void get_character() {
  uint64_t number_of_read_bytes;

  // assert: character_buffer is mapped

  // try to read 1 character into character_buffer
  // from file with source_fd file descriptor
  number_of_read_bytes = read(source_fd, character_buffer, 1);

  if (number_of_read_bytes == 1) {
    // store the read character in the global variable called character
    character = *character_buffer;

    number_of_read_characters = number_of_read_characters + 1;
  } else if (number_of_read_bytes == 0)
    // reached end of file
    character = CHAR_EOF;
  else {
    printf2((uint64_t*) "%s: could not read character from input file %s\n", selfie_name, source_name);

    exit(EXITCODE_IOERROR);
  }
}

uint64_t is_character_new_line() {
  if (character == CHAR_LF)
    return 1;
  else if (character == CHAR_CR)
    return 1;
  else
    return 0;
}

uint64_t is_character_whitespace() {
  if (character == CHAR_SPACE)
    return 1;
  else if (character == CHAR_TAB)
    return 1;
  else
    return is_character_new_line();
}

uint64_t find_next_character() {
  uint64_t in_single_line_comment;
  uint64_t in_multi_line_comment;

  // assuming we are not in a comment
  in_single_line_comment = 0;
  in_multi_line_comment  = 0;

  // read and discard all whitespace and comments until a character is found
  // that is not whitespace and does not occur in a comment, or the file ends
  while (1) {
    if (in_single_line_comment) {
      get_character();

      if (is_character_new_line())
        // single-line comments end with new line
        in_single_line_comment = 0;
      else if (character == CHAR_EOF)
        // or end of file
        return character;
      else
        // count the characters in comments as ignored characters
        number_of_ignored_characters = number_of_ignored_characters + 1;

    } else if (in_multi_line_comment) {
      get_character();

      if (character == CHAR_ASTERISK) {
        // look for '*/' and here count '*' as ignored character
        number_of_ignored_characters = number_of_ignored_characters + 1;

        get_character();

        if (character == CHAR_SLASH) {
          // multi-line comments end with "*/"
          in_multi_line_comment = 0;

          get_character();
        }
      }


      if (in_multi_line_comment) {
        // keep track of line numbers for error reporting and code annotation
        if (character == CHAR_LF)
          // only linefeeds count, not carriage returns
          line_number = line_number + 1;
        else if (character == CHAR_EOF) {
          // multi-line comment is not terminated
          syntax_error_message((uint64_t*) "runaway multi-line comment");

          exit(EXITCODE_SCANNERERROR);
        }
      }

      // count the characters in comments as ignored characters including '/' in '*/'
      number_of_ignored_characters = number_of_ignored_characters + 1;

    } else if (is_character_whitespace()) {
      if (character == CHAR_LF)
        line_number = line_number + 1;

      // also count line feed and carriage return as ignored characters
      number_of_ignored_characters = number_of_ignored_characters + 1;

      get_character();

    } else if (character == CHAR_SLASH) {
      get_character();

      if (character == CHAR_SLASH) {
        // "//" begins a comment
        in_single_line_comment = 1;

        // count both slashes as ignored characters
        number_of_ignored_characters = number_of_ignored_characters + 2;

        number_of_comments = number_of_comments + 1;
      } else if (character == CHAR_ASTERISK) {
        // "/*" begins a multi-line comment
        in_multi_line_comment = 1;

        // count both slash and asterisk as ignored characters
        number_of_ignored_characters = number_of_ignored_characters + 2;

        number_of_comments = number_of_comments + 1;
      } else {
        // while looking for "//" and "/*" we actually found '/'
        symbol = SYM_DIV;

        return character;
      }

    } else
      // character found that is not whitespace and not occurring in a comment
      return character;
  }
}

uint64_t is_character_letter() {
  // ASCII codes for lower- and uppercase letters are in contiguous intervals
  if (character >= 'a')
    if (character <= 'z')
      return 1;
    else
      return 0;
  else if (character >= 'A')
    if (character <= 'Z')
      return 1;
    else
      return 0;
  else
    return 0;
}

uint64_t is_character_digit() {
  // ASCII codes for digits are in a contiguous interval
  if (character >= '0')
    if (character <= '9')
      return 1;
    else
      return 0;
  else
    return 0;
}

uint64_t is_character_letter_or_digit_or_underscore() {
  if (is_character_letter())
    return 1;
  else if (is_character_digit())
    return 1;
  else if (character == CHAR_UNDERSCORE)
    return 1;
  else
    return 0;
}

uint64_t is_character_not_double_quote_or_new_line_or_eof() {
  if (character == CHAR_DOUBLEQUOTE)
    return 0;
  else if (is_character_new_line())
    return 0;
  else if (character == CHAR_EOF)
    return 0;
  else
    return 1;
}

uint64_t identifier_string_match(uint64_t keyword) {
  return string_compare(identifier, (uint64_t*) *(SYMBOLS + keyword));
}

uint64_t identifier_or_keyword() {
  if (identifier_string_match(SYM_UINT64))
    return SYM_UINT64;
  else if (identifier_string_match(SYM_IF))
    return SYM_IF;
  else if (identifier_string_match(SYM_ELSE))
    return SYM_ELSE;
  else if (identifier_string_match(SYM_VOID))
    return SYM_VOID;
  else if (identifier_string_match(SYM_RETURN))
    return SYM_RETURN;
  else if (identifier_string_match(SYM_WHILE))
    return SYM_WHILE;
  else if (identifier_string_match(SYM_INT))
    // selfie bootstraps int to uint64_t!
    return SYM_UINT64;
  else if (identifier_string_match(SYM_CHAR))
    // selfie bootstraps char to uint64_t!
    return SYM_UINT64;
  else if (identifier_string_match(SYM_UNSIGNED))
    // selfie bootstraps unsigned to uint64_t!
    return SYM_UINT64;
  else
    return SYM_IDENTIFIER;
}

void get_symbol() {
  uint64_t i;

  // reset previously scanned symbol
  symbol = SYM_EOF;

  if (find_next_character() != CHAR_EOF) {
    if (symbol != SYM_DIV) {
      // '/' may have already been recognized
      // while looking for whitespace and "//"
      if (is_character_letter()) {
        // accommodate identifier and null for termination
        identifier = smalloc(MAX_IDENTIFIER_LENGTH + 1);

        i = 0;

        while (is_character_letter_or_digit_or_underscore()) {
          if (i >= MAX_IDENTIFIER_LENGTH) {
            syntax_error_message((uint64_t*) "identifier too long");

            exit(EXITCODE_SCANNERERROR);
          }

          store_character(identifier, i, character);

          i = i + 1;

          get_character();
        }

        store_character(identifier, i, 0); // null-terminated string

        symbol = identifier_or_keyword();

        // dummy store to avoid potentially aliased constrained memory error ~~~~~??
        //character = character - 1;
        //character = character + 1;

      } else if (is_character_digit()) {
        // accommodate integer and null for termination
        integer = smalloc(MAX_INTEGER_LENGTH + 1);

        i = 0;

        while (is_character_digit()) {
          if (i >= MAX_INTEGER_LENGTH) {
            if (integer_is_signed)
              syntax_error_message((uint64_t*) "signed integer out of bound");
            else
              syntax_error_message((uint64_t*) "integer out of bound");

            exit(EXITCODE_SCANNERERROR);
          }

          store_character(integer, i, character);

          i = i + 1;

          get_character();
        }

        store_character(integer, i, 0); // null-terminated string

        literal = atoi(integer);

        if (integer_is_signed)
          if (literal > INT64_MIN) {
              syntax_error_message((uint64_t*) "signed integer out of bound");

              exit(EXITCODE_SCANNERERROR);
            }

        symbol = SYM_INTEGER;

      } else if (character == CHAR_SINGLEQUOTE) {
        get_character();

        literal = 0;

        if (character == CHAR_EOF) {
          syntax_error_message((uint64_t*) "reached end of file looking for a character literal");

          exit(EXITCODE_SCANNERERROR);
        } else
          literal = character;

        get_character();

        if (character == CHAR_SINGLEQUOTE)
          get_character();
        else if (character == CHAR_EOF) {
          syntax_error_character(CHAR_SINGLEQUOTE);

          exit(EXITCODE_SCANNERERROR);
        } else
          syntax_error_character(CHAR_SINGLEQUOTE);

        symbol = SYM_CHARACTER;

      } else if (character == CHAR_DOUBLEQUOTE) {
        get_character();

        // accommodate string and null for termination,
        // allocate zeroed memory since strings are emitted
        // in double words but may end non-word-aligned
        string = zalloc(MAX_STRING_LENGTH + 1);

        i = 0;

        while (is_character_not_double_quote_or_new_line_or_eof()) {
          if (i >= MAX_STRING_LENGTH) {
            syntax_error_message((uint64_t*) "string too long");

            exit(EXITCODE_SCANNERERROR);
          }

          if (character == CHAR_BACKSLASH)
            handle_escape_sequence();

          store_character(string, i, character);

          i = i + 1;

          get_character();
        }

        if (character == CHAR_DOUBLEQUOTE)
          get_character();
        else {
          syntax_error_character(CHAR_DOUBLEQUOTE);

          exit(EXITCODE_SCANNERERROR);
        }

        store_character(string, i, 0); // null-terminated string

        symbol = SYM_STRING;

      } else if (character == CHAR_COMMA) {
        get_character();

        symbol = SYM_COMMA;

      } else if (character == CHAR_SEMICOLON) {
        get_character();

        symbol = SYM_SEMICOLON;

      } else if (character == CHAR_LPARENTHESIS) {
        get_character();

        symbol = SYM_LPARENTHESIS;

      } else if (character == CHAR_RPARENTHESIS) {
        get_character();

        symbol = SYM_RPARENTHESIS;

      } else if (character == CHAR_LBRACE) {
        get_character();

        symbol = SYM_LBRACE;

      } else if (character == CHAR_RBRACE) {
        get_character();

        symbol = SYM_RBRACE;

      } else if (character == CHAR_PLUS) {
        get_character();

        symbol = SYM_PLUS;

      } else if (character == CHAR_DASH) {
        get_character();

        symbol = SYM_MINUS;

      } else if (character == CHAR_ASTERISK) {
        get_character();

        symbol = SYM_ASTERISK;

      } else if (character == CHAR_PERCENTAGE) {
        get_character();

        symbol = SYM_MOD;

      } else if (character == CHAR_EQUAL) {
        get_character();

        if (character == CHAR_EQUAL) {
          get_character();

          symbol = SYM_EQUALITY;
        } else
          symbol = SYM_ASSIGN;

      } else if (character == CHAR_EXCLAMATION) {
        get_character();

        if (character == CHAR_EQUAL)
          get_character();
        else
          syntax_error_character(CHAR_EQUAL);

        symbol = SYM_NOTEQ;

      } else if (character == CHAR_LT) {
        get_character();

        if (character == CHAR_EQUAL) {
          get_character();

          symbol = SYM_LEQ;
        } else
          symbol = SYM_LT;

      } else if (character == CHAR_GT) {
        get_character();

        if (character == CHAR_EQUAL) {
          get_character();

          symbol = SYM_GEQ;
        } else
          symbol = SYM_GT;

      } else {
        print_line_number((uint64_t*) "syntax error", line_number);
        print((uint64_t*) "found unknown character ");
        print_character(character);
        println();

        exit(EXITCODE_SCANNERERROR);
      }
    }

    number_of_scanned_symbols = number_of_scanned_symbols + 1;
  }
}

void handle_escape_sequence() {
  // ignoring the backslash
  number_of_ignored_characters = number_of_ignored_characters + 1;

  get_character();

  if (character == 'n')
    character = CHAR_LF;
  else if (character == 't')
    character = CHAR_TAB;
  else if (character == 'b')
    character = CHAR_BACKSPACE;
  else if (character == CHAR_SINGLEQUOTE)
    character = CHAR_SINGLEQUOTE;
  else if (character == CHAR_DOUBLEQUOTE)
    character = CHAR_DOUBLEQUOTE;
  else if (character == CHAR_PERCENTAGE)
    character = CHAR_PERCENTAGE;
  else if (character == CHAR_BACKSLASH)
    character = CHAR_BACKSLASH;
  else {
    syntax_error_message((uint64_t*) "unknown escape sequence found");

    exit(EXITCODE_SCANNERERROR);
  }
}

// -----------------------------------------------------------------
// ------------------------- SYMBOL TABLE --------------------------
// -----------------------------------------------------------------

uint64_t hash(uint64_t* key) {
  // assert: key != (uint64_t*) 0
  return (*key + (*key + (*key + (*key + (*key + *key / HASH_TABLE_SIZE) / HASH_TABLE_SIZE) / HASH_TABLE_SIZE) / HASH_TABLE_SIZE) / HASH_TABLE_SIZE) % HASH_TABLE_SIZE;
}

void create_symbol_table_entry(uint64_t which_table, uint64_t* string, uint64_t line, uint64_t class, uint64_t type, uint64_t value, uint64_t address) {
  uint64_t* new_entry;
  uint64_t* hashed_entry_address;

  new_entry = smalloc(2 * SIZEOFUINT64STAR + 6 * SIZEOFUINT64);

  set_string(new_entry, string);
  set_line_number(new_entry, line);
  set_class(new_entry, class);
  set_type(new_entry, type);
  set_value(new_entry, value);
  set_address(new_entry, address);

  // create entry at head of list of symbols
  if (which_table == GLOBAL_TABLE) {
    set_scope(new_entry, REG_GP);

    hashed_entry_address = global_symbol_table + hash(string);

    set_next_entry(new_entry, (uint64_t*) *hashed_entry_address);
    *hashed_entry_address = (uint64_t) new_entry;

    if (class == VARIABLE)
      number_of_global_variables = number_of_global_variables + 1;
    else if (class == PROCEDURE)
      number_of_procedures = number_of_procedures + 1;
    else if (class == STRING)
      number_of_strings = number_of_strings + 1;
  } else if (which_table == LOCAL_TABLE) {
    set_scope(new_entry, REG_FP);
    set_next_entry(new_entry, local_symbol_table);
    local_symbol_table = new_entry;
  } else {
    // library procedures
    set_scope(new_entry, REG_GP);
    set_next_entry(new_entry, library_symbol_table);
    library_symbol_table = new_entry;
  }
}

uint64_t* search_symbol_table(uint64_t* entry, uint64_t* string, uint64_t class) {
  number_of_searches = number_of_searches + 1;

  while (entry != (uint64_t*) 0) {
    total_search_time = total_search_time + 1;

    if (string_compare(string, get_string(entry)))
      if (class == get_class(entry))
        return entry;

    // keep looking
    entry = get_next_entry(entry);
  }

  return (uint64_t*) 0;
}

uint64_t* search_global_symbol_table(uint64_t* string, uint64_t class) {
  return search_symbol_table((uint64_t*) *(global_symbol_table + hash(string)), string, class);
}

uint64_t* get_scoped_symbol_table_entry(uint64_t* string, uint64_t class) {
  uint64_t* entry;

  if (class == VARIABLE)
    // local variables override global variables
    entry = search_symbol_table(local_symbol_table, string, VARIABLE);
  else if (class == PROCEDURE)
    // library procedures override declared or defined procedures
    entry = search_symbol_table(library_symbol_table, string, PROCEDURE);
  else
    entry = (uint64_t*) 0;

  if (entry == (uint64_t*) 0)
    return search_global_symbol_table(string, class);
  else
    return entry;
}

uint64_t is_undefined_procedure(uint64_t* entry) {
  uint64_t* library_entry;

  if (get_class(entry) == PROCEDURE) {
    // library procedures override declared or defined procedures
    library_entry = search_symbol_table(library_symbol_table, get_string(entry), PROCEDURE);

    if (library_entry != (uint64_t*) 0)
      // procedure is library procedure
      return 0;
    else if (get_address(entry) == 0)
      // procedure declared but not defined
      return 1;
    else if (get_opcode(load_instruction(get_address(entry))) == OP_JAL)
      // procedure called but not defined
      return 1;
  }

  return 0;
}

uint64_t report_undefined_procedures() {
  uint64_t undefined;
  uint64_t i;
  uint64_t* entry;

  undefined = 0;

  i = 0;

  while (i < HASH_TABLE_SIZE) {
    entry = (uint64_t*) *(global_symbol_table + i);

    while (entry != (uint64_t*) 0) {
      if (is_undefined_procedure(entry)) {
        undefined = 1;

        print_line_number((uint64_t*) "syntax error", get_line_number(entry));
        printf1((uint64_t*) "procedure %s undefined\n", get_string(entry));
      }

      // keep looking
      entry = get_next_entry(entry);
    }

    i = i + 1;
  }

  return undefined;
}

// -----------------------------------------------------------------
// ---------------------------- PARSER -----------------------------
// -----------------------------------------------------------------

uint64_t is_not_rbrace_or_eof() {
  if (symbol == SYM_RBRACE)
    return 0;
  else if (symbol == SYM_EOF)
    return 0;
  else
    return 1;
}

uint64_t is_expression() {
  if (symbol == SYM_MINUS)
    return 1;
  else if (symbol == SYM_LPARENTHESIS)
    return 1;
  else if (symbol == SYM_IDENTIFIER)
    return 1;
  else if (symbol == SYM_INTEGER)
    return 1;
  else if (symbol == SYM_ASTERISK)
    return 1;
  else if (symbol == SYM_STRING)
    return 1;
  else if (symbol == SYM_CHARACTER)
    return 1;
  else
    return 0;
}

uint64_t is_literal() {
  if (symbol == SYM_INTEGER)
    return 1;
  else if (symbol == SYM_CHARACTER)
    return 1;
  else
    return 0;
}

uint64_t is_star_or_div_or_modulo() {
  if (symbol == SYM_ASTERISK)
    return 1;
  else if (symbol == SYM_DIV)
    return 1;
  else if (symbol == SYM_MOD)
    return 1;
  else
    return 0;
}

uint64_t is_plus_or_minus() {
  if (symbol == SYM_MINUS)
    return 1;
  else if (symbol == SYM_PLUS)
    return 1;
  else
    return 0;
}

uint64_t is_comparison() {
  if (symbol == SYM_EQUALITY)
    return 1;
  else if (symbol == SYM_NOTEQ)
    return 1;
  else if (symbol == SYM_LT)
    return 1;
  else if (symbol == SYM_GT)
    return 1;
  else if (symbol == SYM_LEQ)
    return 1;
  else if (symbol == SYM_GEQ)
    return 1;
  else
    return 0;
}

uint64_t look_for_factor() {
  if (symbol == SYM_ASTERISK)
    return 0;
  else if (symbol == SYM_MINUS)
    return 0;
  else if (symbol == SYM_IDENTIFIER)
    return 0;
  else if (symbol == SYM_INTEGER)
    return 0;
  else if (symbol == SYM_CHARACTER)
    return 0;
  else if (symbol == SYM_STRING)
    return 0;
  else if (symbol == SYM_LPARENTHESIS)
    return 0;
  else if (symbol == SYM_EOF)
    return 0;
  else
    return 1;
}

uint64_t look_for_statement() {
  if (symbol == SYM_ASTERISK)
    return 0;
  else if (symbol == SYM_IDENTIFIER)
    return 0;
  else if (symbol == SYM_WHILE)
    return 0;
  else if (symbol == SYM_IF)
    return 0;
  else if (symbol == SYM_RETURN)
    return 0;
  else if (symbol == SYM_EOF)
    return 0;
  else
    return 1;
}

uint64_t look_for_type() {
  if (symbol == SYM_UINT64)
    return 0;
  else if (symbol == SYM_VOID)
    return 0;
  else if (symbol == SYM_EOF)
    return 0;
  else
    return 1;
}

void talloc() {
  // we use registers REG_T0-REG_T6 for temporaries
  if (allocated_temporaries < NUMBEROFTEMPORARIES)
    allocated_temporaries = allocated_temporaries + 1;
  else {
    syntax_error_message((uint64_t*) "out of registers");

    exit(EXITCODE_COMPILERERROR);
  }
}

uint64_t current_temporary() {
  if (allocated_temporaries > 0)
    if (allocated_temporaries < 4)
      return REG_TP + allocated_temporaries;
    else
      return REG_S11 + allocated_temporaries - 3;
  else {
    syntax_error_message((uint64_t*) "illegal register access");

    exit(EXITCODE_COMPILERERROR);
  }
}

uint64_t previous_temporary() {
  if (allocated_temporaries > 1)
    if (allocated_temporaries == 4)
      return REG_T2;
    else
      return current_temporary() - 1;
  else {
    syntax_error_message((uint64_t*) "illegal register access");

    exit(EXITCODE_COMPILERERROR);
  }
}

uint64_t next_temporary() {
  if (allocated_temporaries < NUMBEROFTEMPORARIES)
    if (allocated_temporaries == 3)
      return REG_T3;
    else
      return current_temporary() + 1;
  else {
    syntax_error_message((uint64_t*) "out of registers");

    exit(EXITCODE_COMPILERERROR);
  }
}

void tfree(uint64_t number_of_temporaries) {
  if (allocated_temporaries >= number_of_temporaries)
    allocated_temporaries = allocated_temporaries - number_of_temporaries;
  else {
    syntax_error_message((uint64_t*) "illegal register deallocation");

    exit(EXITCODE_COMPILERERROR);
  }
}

void save_temporaries() {
  while (allocated_temporaries > 0) {
    // push temporary onto stack
    emit_addi(REG_SP, REG_SP, -REGISTERSIZE);
    emit_sd(REG_SP, 0, current_temporary());

    tfree(1);
  }
}

void restore_temporaries(uint64_t number_of_temporaries) {
  while (allocated_temporaries < number_of_temporaries) {
    talloc();

    // restore temporary from stack
    emit_ld(current_temporary(), REG_SP, 0);
    emit_addi(REG_SP, REG_SP, REGISTERSIZE);
  }
}

void syntax_error_symbol(uint64_t expected) {
  print_line_number((uint64_t*) "syntax error", line_number);
  print_symbol(expected);
  print((uint64_t*) " expected but ");
  print_symbol(symbol);
  print((uint64_t*) " found\n");
}

void syntax_error_unexpected() {
  print_line_number((uint64_t*) "syntax error", line_number);
  print((uint64_t*) "unexpected symbol ");
  print_symbol(symbol);
  print((uint64_t*) " found\n");
}

void print_type(uint64_t type) {
  if (type == UINT64_T)
    print((uint64_t*) "uint64_t");
  else if (type == UINT64STAR_T)
    print((uint64_t*) "uint64_t*");
  else if (type == VOID_T)
    print((uint64_t*) "void");
  else
    print((uint64_t*) "unknown");
}

void type_warning(uint64_t expected, uint64_t found) {
  print_line_number((uint64_t*) "warning", line_number);
  print((uint64_t*) "type mismatch, ");
  print_type(expected);
  print((uint64_t*) " expected but ");
  print_type(found);
  print((uint64_t*) " found\n");
}

uint64_t* get_variable_or_big_int(uint64_t* variable_or_big_int, uint64_t class) {
  uint64_t* entry;

  if (class == BIGINT)
    return search_global_symbol_table(variable_or_big_int, class);
  else {
    entry = get_scoped_symbol_table_entry(variable_or_big_int, class);

    if (entry == (uint64_t*) 0) {
      print_line_number((uint64_t*) "syntax error", line_number);
      printf1((uint64_t*) "%s undeclared\n", variable_or_big_int);

      exit(EXITCODE_PARSERERROR);
    }

    return entry;
  }
}

void load_upper_base_address(uint64_t* entry) {
  uint64_t lower;
  uint64_t upper;

  // assert: n = allocated_temporaries

  lower = get_bits(get_address(entry),  0, 12);
  upper = get_bits(get_address(entry), 12, 20);

  if (lower >= two_to_the_power_of(11))
    // add 1 which is effectively 2^12 to cancel sign extension of lower
    upper = upper + 1;

  talloc();

  // calculate upper part of base address relative to global or frame pointer
  emit_lui(current_temporary(), sign_extend(upper, 20));
  emit_add(current_temporary(), get_scope(entry), current_temporary());

  // assert: allocated_temporaries == n + 1
}

uint64_t load_variable_or_big_int(uint64_t* variable_or_big_int, uint64_t class) {
  uint64_t* entry;
  uint64_t offset;

  // assert: n = allocated_temporaries

  entry = get_variable_or_big_int(variable_or_big_int, class);

  offset = get_address(entry);

  if (is_signed_integer(offset, 12)) {
    talloc();

    emit_ld(current_temporary(), get_scope(entry), offset);
  } else {
    load_upper_base_address(entry);

    emit_ld(current_temporary(), current_temporary(), sign_extend(get_bits(offset, 0, 12), 12));
  }

  // assert: allocated_temporaries == n + 1

  return get_type(entry);
}

void load_integer(uint64_t value) {
  uint64_t lower;
  uint64_t upper;
  uint64_t* entry;

  // assert: n = allocated_temporaries

  if (is_signed_integer(value, 12)) {
    // integers greater than or equal to -2^11 and less than 2^11
    // are loaded with one addi into a register

    talloc();

    emit_addi(current_temporary(), REG_ZR, value);

  } else if (is_signed_integer(value, 32)) {
    // integers greater than or equal to -2^31 and less than 2^31
    // are loaded with one lui and one addi into a register plus
    // an additional sub to cancel sign extension if necessary

    lower = get_bits(value,  0, 12);
    upper = get_bits(value, 12, 20);

    talloc();

    if (lower >= two_to_the_power_of(11)) {
      // add 1 which is effectively 2^12 to cancel sign extension of lower
      upper = upper + 1;

      // assert: 0 < upper <= 2^(32-12)
      emit_lui(current_temporary(), sign_extend(upper, 20));

      if (upper == two_to_the_power_of(19))
        // upper overflowed, cancel sign extension
        emit_sub(current_temporary(), REG_ZR, current_temporary());
    } else
      // assert: 0 < upper < 2^(32-12)
      emit_lui(current_temporary(), sign_extend(upper, 20));

    emit_addi(current_temporary(), current_temporary(), sign_extend(lower, 12));

  } else {
    // integers less than -2^31 or greater than or equal to 2^31 are stored in data segment
    entry = search_global_symbol_table(integer, BIGINT);

    if (entry == (uint64_t*) 0) {
      allocated_memory = allocated_memory + REGISTERSIZE;

      create_symbol_table_entry(GLOBAL_TABLE, integer, line_number, BIGINT, UINT64_T, value, -allocated_memory);
    }

    load_variable_or_big_int(integer, BIGINT);
  }

  // assert: allocated_temporaries == n + 1
}

void load_string(uint64_t* string) {
  uint64_t length;

  // assert: n = allocated_temporaries

  length = string_length(string) + 1;

  allocated_memory = allocated_memory + round_up(length, REGISTERSIZE);

  create_symbol_table_entry(GLOBAL_TABLE, string, line_number, STRING, UINT64STAR_T, 0, -allocated_memory);

  load_integer(-allocated_memory);

  emit_add(current_temporary(), REG_GP, current_temporary());

  // assert: allocated_temporaries == n + 1
}

uint64_t help_call_codegen(uint64_t* entry, uint64_t* procedure) {
  uint64_t type;

  if (entry == (uint64_t*) 0) {
    // procedure never called nor declared nor defined

    // default return type is "int"
    type = UINT64_T;

    create_symbol_table_entry(GLOBAL_TABLE, procedure, line_number, PROCEDURE, type, 0, binary_length);

    emit_jal(REG_RA, 0);

  } else {
    type = get_type(entry);

    if (get_address(entry) == 0) {
      // procedure declared but never called nor defined
      set_address(entry, binary_length);

      emit_jal(REG_RA, 0);
    } else if (get_opcode(load_instruction(get_address(entry))) == OP_JAL) {
      // procedure called and possibly declared but not defined

      // create fixup chain using absolute address
      emit_jal(REG_RA, get_address(entry));
      set_address(entry, binary_length - INSTRUCTIONSIZE);
    } else
      // procedure defined, use relative address
      emit_jal(REG_RA, get_address(entry) - binary_length);
  }

  return type;
}

void help_procedure_prologue(uint64_t number_of_local_variable_bytes) {
  // allocate memory for return address
  emit_addi(REG_SP, REG_SP, -REGISTERSIZE);

  // save return address
  emit_sd(REG_SP, 0, REG_RA);

  // allocate memory for caller's frame pointer
  emit_addi(REG_SP, REG_SP, -REGISTERSIZE);

  // save caller's frame pointer
  emit_sd(REG_SP, 0, REG_FP);

  // set callee's frame pointer
  emit_addi(REG_FP, REG_SP, 0);

  // allocate memory for callee's local variables
  if (number_of_local_variable_bytes > 0) {
    if (is_signed_integer(-number_of_local_variable_bytes, 12))
      emit_addi(REG_SP, REG_SP, -number_of_local_variable_bytes);
    else {
      load_integer(-number_of_local_variable_bytes);

      emit_add(REG_SP, REG_SP, current_temporary());

      tfree(1);
    }
  }
}

void help_procedure_epilogue(uint64_t number_of_parameter_bytes) {
  // deallocate memory for callee's frame pointer and local variables
  emit_addi(REG_SP, REG_FP, 0);

  // restore caller's frame pointer
  emit_ld(REG_FP, REG_SP, 0);

  // deallocate memory for caller's frame pointer
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  // restore return address
  emit_ld(REG_RA, REG_SP, 0);

  // deallocate memory for return address and parameters
  emit_addi(REG_SP, REG_SP, REGISTERSIZE + number_of_parameter_bytes);

  // return
  emit_jalr(REG_ZR, REG_RA, 0);
}

uint64_t compile_call(uint64_t* procedure) {
  uint64_t* entry;
  uint64_t number_of_temporaries;
  uint64_t type;

  // assert: n = allocated_temporaries

  entry = get_scoped_symbol_table_entry(procedure, PROCEDURE);

  number_of_temporaries = allocated_temporaries;

  save_temporaries();

  // assert: allocated_temporaries == 0

  if (is_expression()) {
    compile_expression();

    // TODO: check if types/number of parameters is correct

    // push first parameter onto stack
    emit_addi(REG_SP, REG_SP, -REGISTERSIZE);
    emit_sd(REG_SP, 0, current_temporary());

    tfree(1);

    while (symbol == SYM_COMMA) {
      get_symbol();

      compile_expression();

      // push more parameters onto stack
      emit_addi(REG_SP, REG_SP, -REGISTERSIZE);
      emit_sd(REG_SP, 0, current_temporary());

      tfree(1);
    }

    if (symbol == SYM_RPARENTHESIS) {
      get_symbol();

      type = help_call_codegen(entry, procedure);
    } else {
      syntax_error_symbol(SYM_RPARENTHESIS);

      type = UINT64_T;
    }
  } else if (symbol == SYM_RPARENTHESIS) {
    get_symbol();

    type = help_call_codegen(entry, procedure);
  } else {
    syntax_error_symbol(SYM_RPARENTHESIS);

    type = UINT64_T;
  }

  // assert: allocated_temporaries == 0

  restore_temporaries(number_of_temporaries);

  number_of_calls = number_of_calls + 1;

  // assert: allocated_temporaries == n

  return type;
}

uint64_t compile_factor() {
  uint64_t has_cast;
  uint64_t cast;
  uint64_t type;
  uint64_t negative;
  uint64_t dereference;
  uint64_t* variable_or_procedure_name;

  // assert: n = allocated_temporaries

  while (look_for_factor()) {
    syntax_error_unexpected();

    if (symbol == SYM_EOF)
      exit(EXITCODE_PARSERERROR);
    else
      get_symbol();
  }

  // optional: [ cast ]
  if (symbol == SYM_LPARENTHESIS) {
    get_symbol();

    // cast: "(" "uint64_t" [ "*" ] ")"
    if (symbol == SYM_UINT64) {
      has_cast = 1;

      cast = compile_type();

      if (symbol == SYM_RPARENTHESIS)
        get_symbol();
      else
        syntax_error_symbol(SYM_RPARENTHESIS);

    // not a cast: "(" expression ")"
    } else {
      type = compile_expression();

      if (symbol == SYM_RPARENTHESIS)
        get_symbol();
      else
        syntax_error_symbol(SYM_RPARENTHESIS);

      // assert: allocated_temporaries == n + 1

      return type;
    }
  } else
    has_cast = 0;

  // optional: -
  if (symbol == SYM_MINUS) {
    negative = 1;

    integer_is_signed = 1;

    get_symbol();

    integer_is_signed = 0;
  } else
    negative = 0;

  // optional: dereference
  if (symbol == SYM_ASTERISK) {
    dereference = 1;

    get_symbol();
  } else
    dereference = 0;

  // identifier or call?
  if (symbol == SYM_IDENTIFIER) {
    variable_or_procedure_name = identifier;

    get_symbol();

    if (symbol == SYM_LPARENTHESIS) {
      get_symbol();

      // procedure call: identifier "(" ... ")"
      type = compile_call(variable_or_procedure_name);

      talloc();

      // retrieve return value
      emit_addi(current_temporary(), REG_A0, 0);

      // reset return register to initial return value
      // for missing return expressions
      emit_addi(REG_A0, REG_ZR, 0);
    } else
      // variable access: identifier
      type = load_variable_or_big_int(variable_or_procedure_name, VARIABLE);

  // integer?
  } else if (symbol == SYM_INTEGER) {
    load_integer(literal);

    get_symbol();

    type = UINT64_T;

  // character?
  } else if (symbol == SYM_CHARACTER) {
    talloc();

    emit_addi(current_temporary(), REG_ZR, literal);

    get_symbol();

    type = UINT64_T;

  // string?
  } else if (symbol == SYM_STRING) {
    load_string(string);

    get_symbol();

    type = UINT64STAR_T;

  //  "(" expression ")"
  } else if (symbol == SYM_LPARENTHESIS) {
    get_symbol();

    type = compile_expression();

    if (symbol == SYM_RPARENTHESIS)
      get_symbol();
    else
      syntax_error_symbol(SYM_RPARENTHESIS);
  } else {
    syntax_error_unexpected();

    type = UINT64_T;
  }

  if (dereference) {
    if (type != UINT64STAR_T)
      type_warning(UINT64STAR_T, type);

    // dereference
    emit_ld(current_temporary(), current_temporary(), 0);

    type = UINT64_T;
  }

  if (negative) {
    if (type != UINT64_T) {
      type_warning(UINT64_T, type);

      type = UINT64_T;
    }

    emit_sub(current_temporary(), REG_ZR, current_temporary());
  }

  // assert: allocated_temporaries == n + 1

  if (has_cast)
    return cast;
  else
    return type;
}

uint64_t compile_term() {
  uint64_t ltype;
  uint64_t operator_symbol;
  uint64_t rtype;

  // assert: n = allocated_temporaries

  ltype = compile_factor();

  // assert: allocated_temporaries == n + 1

  // * / or % ?
  while (is_star_or_div_or_modulo()) {
    operator_symbol = symbol;

    get_symbol();

    rtype = compile_factor();

    // assert: allocated_temporaries == n + 2

    if (ltype != rtype)
      type_warning(ltype, rtype);

    if (operator_symbol == SYM_ASTERISK)
      emit_mul(previous_temporary(), previous_temporary(), current_temporary());
    else if (operator_symbol == SYM_DIV)
      emit_divu(previous_temporary(), previous_temporary(), current_temporary());
    else if (operator_symbol == SYM_MOD)
      emit_remu(previous_temporary(), previous_temporary(), current_temporary());

    tfree(1);
  }

  // assert: allocated_temporaries == n + 1

  return ltype;
}

uint64_t compile_simple_expression() {
  uint64_t ltype;
  uint64_t operator_symbol;
  uint64_t rtype;

  // assert: n = allocated_temporaries

  ltype = compile_term();

  // assert: allocated_temporaries == n + 1

  // + or - ?
  while (is_plus_or_minus()) {
    operator_symbol = symbol;

    get_symbol();

    rtype = compile_term();

    // assert: allocated_temporaries == n + 2

    if (operator_symbol == SYM_PLUS) {
      if (ltype == UINT64STAR_T) {
        if (rtype == UINT64_T)
          // UINT64STAR_T + UINT64_T
          // pointer arithmetic: factor of 2^3 of integer operand
          emit_left_shift_by(current_temporary(), 3);
        else
          // UINT64STAR_T + UINT64STAR_T
          syntax_error_message((uint64_t*) "(uint64_t*) + (uint64_t*) is undefined");
      } else if (rtype == UINT64STAR_T) {
        // UINT64_T + UINT64STAR_T
        // pointer arithmetic: factor of 2^3 of integer operand
        emit_left_shift_by(previous_temporary(), 3);

        ltype = UINT64STAR_T;
      }

      emit_add(previous_temporary(), previous_temporary(), current_temporary());

    } else if (operator_symbol == SYM_MINUS) {
      if (ltype == UINT64STAR_T) {
        if (rtype == UINT64_T) {
          // UINT64STAR_T - UINT64_T
          // pointer arithmetic: factor of 2^3 of integer operand
          emit_left_shift_by(current_temporary(), 3);
          emit_sub(previous_temporary(), previous_temporary(), current_temporary());
        } else {
          // UINT64STAR_T - UINT64STAR_T
          // pointer arithmetic: (left_term - right_term) / SIZEOFUINT64
          emit_sub(previous_temporary(), previous_temporary(), current_temporary());
          emit_addi(current_temporary(), REG_ZR, SIZEOFUINT64);
          emit_divu(previous_temporary(), previous_temporary(), current_temporary());

          ltype = UINT64_T;
        }
      } else if (rtype == UINT64STAR_T)
        // UINT64_T - UINT64STAR_T
        syntax_error_message((uint64_t*) "(uint64_t) - (uint64_t*) is undefined");
      else
        // UINT64_T - UINT64_T
        emit_sub(previous_temporary(), previous_temporary(), current_temporary());
    }

    tfree(1);
  }

  // assert: allocated_temporaries == n + 1

  return ltype;
}

uint64_t compile_expression() {
  uint64_t ltype;
  uint64_t operator_symbol;
  uint64_t rtype;

  // assert: n = allocated_temporaries

  ltype = compile_simple_expression();

  // assert: allocated_temporaries == n + 1

  //optional: ==, !=, <, >, <=, >= simple_expression
  if (is_comparison()) {
    operator_symbol = symbol;

    get_symbol();

    rtype = compile_simple_expression();

    // assert: allocated_temporaries == n + 2

    if (ltype != rtype)
      type_warning(ltype, rtype);

    if (operator_symbol == SYM_EQUALITY) {
      // a == b iff unsigned b - a < 1
      emit_sub(previous_temporary(), current_temporary(), previous_temporary());
      emit_addi(current_temporary(), REG_ZR, 1);
      emit_sltu(previous_temporary(), previous_temporary(), current_temporary());

      tfree(1);

    } else if (operator_symbol == SYM_NOTEQ) {
      // a != b iff unsigned 0 < b - a
      emit_sub(previous_temporary(), current_temporary(), previous_temporary());

      tfree(1);

      emit_sltu(current_temporary(), REG_ZR, current_temporary());

    } else if (operator_symbol == SYM_LT) {
      // a < b
      emit_sltu(previous_temporary(), previous_temporary(), current_temporary());

      tfree(1);

    } else if (operator_symbol == SYM_GT) {
      // a > b iff b < a
      emit_sltu(previous_temporary(), current_temporary(), previous_temporary());

      tfree(1);

    } else if (operator_symbol == SYM_LEQ) {
      // a <= b iff 1 - (b < a)
      emit_sltu(previous_temporary(), current_temporary(), previous_temporary());
      emit_addi(current_temporary(), REG_ZR, 1);
      emit_sub(previous_temporary(), current_temporary(), previous_temporary());

      tfree(1);

    } else if (operator_symbol == SYM_GEQ) {
      // a >= b iff 1 - (a < b)
      emit_sltu(previous_temporary(), previous_temporary(), current_temporary());
      emit_addi(current_temporary(), REG_ZR, 1);
      emit_sub(previous_temporary(), current_temporary(), previous_temporary());

      tfree(1);
    }
  }

  // assert: allocated_temporaries == n + 1

  return ltype;
}

void compile_while() {
  uint64_t jump_back_to_while;
  uint64_t branch_forward_to_end;

  // assert: allocated_temporaries == 0

  jump_back_to_while = binary_length;

  branch_forward_to_end = 0;

  // while ( expression )
  if (symbol == SYM_WHILE) {
    get_symbol();

    if (symbol == SYM_LPARENTHESIS) {
      get_symbol();

      compile_expression();

      // we do not know where to branch, fixup later
      branch_forward_to_end = binary_length;

      emit_beq(current_temporary(), REG_ZR, 0);

      tfree(1);

      if (symbol == SYM_RPARENTHESIS) {
        get_symbol();

        // zero or more statements: { statement }
        if (symbol == SYM_LBRACE) {
          get_symbol();

          while (is_not_rbrace_or_eof())
            compile_statement();

          if (symbol == SYM_RBRACE)
            get_symbol();
          else {
            syntax_error_symbol(SYM_RBRACE);

            exit(EXITCODE_PARSERERROR);
          }
        } else
          // only one statement without {}
          compile_statement();
      } else
        syntax_error_symbol(SYM_RPARENTHESIS);
    } else
      syntax_error_symbol(SYM_LPARENTHESIS);
  } else
    syntax_error_symbol(SYM_WHILE);

  // we use JAL for the unconditional jump back to the loop condition because:
  // 1. the RISC-V doc recommends to do so to not disturb branch prediction
  // 2. GCC also uses JAL for the unconditional back jump of a while loop
  emit_jal(REG_ZR, jump_back_to_while - binary_length);

  if (branch_forward_to_end != 0)
    // first instruction after loop body will be generated here
    // now we have the address for the conditional branch from above
    fixup_relative_BFormat(branch_forward_to_end);

  // assert: allocated_temporaries == 0

  number_of_while = number_of_while + 1;
}

void compile_if() {
  uint64_t branch_forward_to_else_or_end;
  uint64_t jump_forward_to_end;

  // assert: allocated_temporaries == 0

  // if ( expression )
  if (symbol == SYM_IF) {
    get_symbol();

    if (symbol == SYM_LPARENTHESIS) {
      get_symbol();

      compile_expression();

      // if the "if" case is not true we branch to "else" (if provided)
      branch_forward_to_else_or_end = binary_length;

      emit_beq(current_temporary(), REG_ZR, 0);

      tfree(1);

      if (symbol == SYM_RPARENTHESIS) {
        get_symbol();

        // zero or more statements: { statement }
        if (symbol == SYM_LBRACE) {
          get_symbol();

          while (is_not_rbrace_or_eof())
            compile_statement();

          if (symbol == SYM_RBRACE)
            get_symbol();
          else {
            syntax_error_symbol(SYM_RBRACE);

            exit(EXITCODE_PARSERERROR);
          }
        } else
        // only one statement without {}
          compile_statement();

        //optional: else
        if (symbol == SYM_ELSE) {
          get_symbol();

          // if the "if" case was true we skip the "else" case
          // by unconditionally jumping to the end
          jump_forward_to_end = binary_length;

          emit_jal(REG_ZR, 0);

          // if the "if" case was not true we branch here
          fixup_relative_BFormat(branch_forward_to_else_or_end);

          // zero or more statements: { statement }
          if (symbol == SYM_LBRACE) {
            get_symbol();

            while (is_not_rbrace_or_eof())
              compile_statement();

            if (symbol == SYM_RBRACE)
              get_symbol();
            else {
              syntax_error_symbol(SYM_RBRACE);

              exit(EXITCODE_PARSERERROR);
            }

          // only one statement without {}
          } else
            compile_statement();

          // if the "if" case was true we unconditionally jump here
          fixup_relative_JFormat(jump_forward_to_end, binary_length);
        } else
          // if the "if" case was not true we branch here
          fixup_relative_BFormat(branch_forward_to_else_or_end);
      } else
        syntax_error_symbol(SYM_RPARENTHESIS);
    } else
      syntax_error_symbol(SYM_LPARENTHESIS);
  } else
    syntax_error_symbol(SYM_IF);

  // assert: allocated_temporaries == 0

  number_of_if = number_of_if + 1;
}

void compile_return() {
  uint64_t type;

  // assert: allocated_temporaries == 0

  if (symbol == SYM_RETURN)
    get_symbol();
  else
    syntax_error_symbol(SYM_RETURN);

  // optional: expression
  if (symbol != SYM_SEMICOLON) {
    type = compile_expression();

    if (type != return_type)
      type_warning(return_type, type);

    // save value of expression in return register
    emit_addi(REG_A0, current_temporary(), 0);

    tfree(1);
  } else if (return_type != VOID_T)
    type_warning(return_type, VOID_T);

  // jump to procedure epilogue through fixup chain using absolute address
  emit_jal(REG_ZR, return_branches);

  // new head of fixup chain
  return_branches = binary_length - INSTRUCTIONSIZE;

  // assert: allocated_temporaries == 0

  number_of_return = number_of_return + 1;
}

void compile_statement() {
  uint64_t ltype;
  uint64_t rtype;
  uint64_t* variable_or_procedure_name;
  uint64_t* entry;
  uint64_t offset;

  // assert: allocated_temporaries == 0

  while (look_for_statement()) {
    syntax_error_unexpected();

    if (symbol == SYM_EOF)
      exit(EXITCODE_PARSERERROR);
    else
      get_symbol();
  }

  // ["*"]
  if (symbol == SYM_ASTERISK) {
    get_symbol();

    // "*" identifier
    if (symbol == SYM_IDENTIFIER) {
      ltype = load_variable_or_big_int(identifier, VARIABLE);

      if (ltype != UINT64STAR_T)
        type_warning(UINT64STAR_T, ltype);

      get_symbol();

      // "*" identifier "="
      if (symbol == SYM_ASSIGN) {
        get_symbol();

        rtype = compile_expression();

        if (rtype != UINT64_T)
          type_warning(UINT64_T, rtype);

        emit_sd(previous_temporary(), 0, current_temporary());

        tfree(2);

        number_of_assignments = number_of_assignments + 1;
      } else {
        syntax_error_symbol(SYM_ASSIGN);

        tfree(1);
      }

      if (symbol == SYM_SEMICOLON)
        get_symbol();
      else
        syntax_error_symbol(SYM_SEMICOLON);

    // "*" "(" expression ")"
    } else if (symbol == SYM_LPARENTHESIS) {
      get_symbol();

      ltype = compile_expression();

      if (ltype != UINT64STAR_T)
        type_warning(UINT64STAR_T, ltype);

      if (symbol == SYM_RPARENTHESIS) {
        get_symbol();

        // "*" "(" expression ")" "="
        if (symbol == SYM_ASSIGN) {
          get_symbol();

          rtype = compile_expression();

          if (rtype != UINT64_T)
            type_warning(UINT64_T, rtype);

          emit_sd(previous_temporary(), 0, current_temporary());

          tfree(2);

          number_of_assignments = number_of_assignments + 1;
        } else {
          syntax_error_symbol(SYM_ASSIGN);

          tfree(1);
        }

        if (symbol == SYM_SEMICOLON)
          get_symbol();
        else
          syntax_error_symbol(SYM_SEMICOLON);
      } else
        syntax_error_symbol(SYM_RPARENTHESIS);
    } else
      syntax_error_symbol(SYM_LPARENTHESIS);
  }
  // identifier "=" expression | call
  else if (symbol == SYM_IDENTIFIER) {
    variable_or_procedure_name = identifier;

    get_symbol();

    // procedure call
    if (symbol == SYM_LPARENTHESIS) {
      get_symbol();

      compile_call(variable_or_procedure_name);

      // reset return register to initial return value
      // for missing return expressions
      emit_addi(REG_A0, REG_ZR, 0);

      if (symbol == SYM_SEMICOLON)
        get_symbol();
      else
        syntax_error_symbol(SYM_SEMICOLON);

    // identifier = expression
    } else if (symbol == SYM_ASSIGN) {
      entry = get_variable_or_big_int(variable_or_procedure_name, VARIABLE);

      ltype = get_type(entry);

      get_symbol();

      rtype = compile_expression();

      if (ltype != rtype)
        type_warning(ltype, rtype);

      offset = get_address(entry);

      if (is_signed_integer(offset, 12)) {
        emit_sd(get_scope(entry), offset, current_temporary());

        tfree(1);
      } else {
        load_upper_base_address(entry);

        emit_sd(current_temporary(), sign_extend(get_bits(offset, 0, 12), 12), previous_temporary());

        tfree(2);
      }

      number_of_assignments = number_of_assignments + 1;

      if (symbol == SYM_SEMICOLON)
        get_symbol();
      else
        syntax_error_symbol(SYM_SEMICOLON);
    } else
      syntax_error_unexpected();
  }
  // while statement?
  else if (symbol == SYM_WHILE) {
    compile_while();
  }
  // if statement?
  else if (symbol == SYM_IF) {
    compile_if();
  }
  // return statement?
  else if (symbol == SYM_RETURN) {
    compile_return();

    if (symbol == SYM_SEMICOLON)
      get_symbol();
    else
      syntax_error_symbol(SYM_SEMICOLON);
  }
}

uint64_t compile_type() {
  uint64_t type;

  type = UINT64_T;

  if (symbol == SYM_UINT64) {
    get_symbol();

    while (symbol == SYM_ASTERISK) {
      // we tolerate pointer to pointers for bootstrapping
      type = UINT64STAR_T;

      get_symbol();
    }
  } else
    syntax_error_symbol(SYM_UINT64);

  return type;
}

void compile_variable(uint64_t offset) {
  uint64_t type;

  type = compile_type();

  if (symbol == SYM_IDENTIFIER) {
    // TODO: check if identifier has already been declared
    create_symbol_table_entry(LOCAL_TABLE, identifier, line_number, VARIABLE, type, 0, offset);

    get_symbol();
  } else {
    syntax_error_symbol(SYM_IDENTIFIER);

    create_symbol_table_entry(LOCAL_TABLE, (uint64_t*) "missing variable name", line_number, VARIABLE, type, 0, offset);
  }
}

uint64_t compile_initialization(uint64_t type) {
  uint64_t initial_value;
  uint64_t has_cast;
  uint64_t cast;

  initial_value = 0;

  has_cast = 0;

  if (symbol == SYM_ASSIGN) {
    get_symbol();

    // optional: [ cast ]
    if (symbol == SYM_LPARENTHESIS) {
      has_cast = 1;

      get_symbol();

      cast = compile_type();

      if (symbol == SYM_RPARENTHESIS)
        get_symbol();
      else
        syntax_error_symbol(SYM_RPARENTHESIS);
    }

    // optional: -
    if (symbol == SYM_MINUS) {
      integer_is_signed = 1;

      get_symbol();

      integer_is_signed = 0;

      initial_value = -literal;
    } else
      initial_value = literal;

    if (is_literal())
      get_symbol();
    else
      syntax_error_unexpected();

    if (symbol == SYM_SEMICOLON)
      get_symbol();
    else
      syntax_error_symbol(SYM_SEMICOLON);
  } else
    syntax_error_symbol(SYM_ASSIGN);

  if (has_cast) {
    if (type != cast)
      type_warning(type, cast);
  } else if (type != UINT64_T)
    type_warning(type, UINT64_T);

  return initial_value;
}

void compile_procedure(uint64_t* procedure, uint64_t type) {
  uint64_t is_undefined;
  uint64_t number_of_parameters;
  uint64_t parameters;
  uint64_t number_of_local_variable_bytes;
  uint64_t* entry;

  // assuming procedure is undefined
  is_undefined = 1;

  number_of_parameters = 0;

  // try parsing formal parameters
  if (symbol == SYM_LPARENTHESIS) {
    get_symbol();

    if (symbol != SYM_RPARENTHESIS) {
      compile_variable(0);

      number_of_parameters = 1;

      while (symbol == SYM_COMMA) {
        get_symbol();

        compile_variable(0);

        number_of_parameters = number_of_parameters + 1;
      }

      entry = local_symbol_table;

      parameters = 0;

      while (parameters < number_of_parameters) {
        // 8 bytes offset to skip frame pointer and link
        set_address(entry, parameters * REGISTERSIZE + 2 * REGISTERSIZE);

        parameters = parameters + 1;

        entry = get_next_entry(entry);
      }

      if (symbol == SYM_RPARENTHESIS)
        get_symbol();
      else
        syntax_error_symbol(SYM_RPARENTHESIS);
    } else
      get_symbol();
  } else
    syntax_error_symbol(SYM_LPARENTHESIS);

  entry = search_global_symbol_table(procedure, PROCEDURE);

  if (symbol == SYM_SEMICOLON) {
    // this is a procedure declaration
    if (entry == (uint64_t*) 0)
      // procedure never called nor declared nor defined
      create_symbol_table_entry(GLOBAL_TABLE, procedure, line_number, PROCEDURE, type, 0, 0);
    else if (get_type(entry) != type)
      // procedure already called, declared, or even defined
      // check return type but otherwise ignore
      type_warning(get_type(entry), type);

    get_symbol();

  } else if (symbol == SYM_LBRACE) {
    // this is a procedure definition
    if (entry == (uint64_t*) 0)
      // procedure never called nor declared nor defined
      create_symbol_table_entry(GLOBAL_TABLE, procedure, line_number, PROCEDURE, type, 0, binary_length);
    else {
      // procedure already called or declared or defined
      if (get_address(entry) != 0) {
        // procedure already called or defined
        if (get_opcode(load_instruction(get_address(entry))) == OP_JAL)
          // procedure already called but not defined
          fixlink_relative(get_address(entry), binary_length);
        else
          // procedure already defined
          is_undefined = 0;
      }

      if (is_undefined) {
        // procedure already called or declared but not defined
        set_line_number(entry, line_number);

        if (get_type(entry) != type)
          type_warning(get_type(entry), type);

        set_type(entry, type);
        set_address(entry, binary_length);

        if (string_compare(procedure, (uint64_t*) "main")) {
          // first source containing main procedure provides binary name
          binary_name = source_name;

          // account for initial call to main procedure
          number_of_calls = number_of_calls + 1;
        }
      } else {
        // procedure already defined
        print_line_number((uint64_t*) "warning", line_number);
        printf1((uint64_t*) "redefinition of procedure %s ignored\n", procedure);
      }
    }

    get_symbol();

    number_of_local_variable_bytes = 0;

    while (symbol == SYM_UINT64) {
      number_of_local_variable_bytes = number_of_local_variable_bytes + REGISTERSIZE;

      // offset of local variables relative to frame pointer is negative
      compile_variable(-number_of_local_variable_bytes);

      if (symbol == SYM_SEMICOLON)
        get_symbol();
      else
        syntax_error_symbol(SYM_SEMICOLON);
    }

    help_procedure_prologue(number_of_local_variable_bytes);

    // create a fixup chain for return statements
    return_branches = 0;

    return_type = type;

    while (is_not_rbrace_or_eof())
      compile_statement();

    return_type = 0;

    if (symbol == SYM_RBRACE)
      get_symbol();
    else {
      syntax_error_symbol(SYM_RBRACE);

      exit(EXITCODE_PARSERERROR);
    }

    fixlink_relative(return_branches, binary_length);

    return_branches = 0;

    help_procedure_epilogue(number_of_parameters * REGISTERSIZE);

  } else
    syntax_error_unexpected();

  local_symbol_table = (uint64_t*) 0;

  // assert: allocated_temporaries == 0
}

void compile_cstar() {
  uint64_t type;
  uint64_t* variable_or_procedure_name;
  uint64_t current_line_number;
  uint64_t initial_value;
  uint64_t* entry;

  while (symbol != SYM_EOF) {
    while (look_for_type()) {
      syntax_error_unexpected();

      if (symbol == SYM_EOF)
        exit(EXITCODE_PARSERERROR);
      else
        get_symbol();
    }

    if (symbol == SYM_VOID) {
      // void identifier ...
      // procedure declaration or definition
      get_symbol();

      if (symbol == SYM_ASTERISK) {
        // we tolerate void* return types for bootstrapping
        get_symbol();

        type = UINT64STAR_T;
      } else
        type = VOID_T;

      if (symbol == SYM_IDENTIFIER) {
        variable_or_procedure_name = identifier;

        get_symbol();

        compile_procedure(variable_or_procedure_name, type);
      } else
        syntax_error_symbol(SYM_IDENTIFIER);
    } else {
      type = compile_type();

      if (symbol == SYM_IDENTIFIER) {
        variable_or_procedure_name = identifier;

        get_symbol();

        if (symbol == SYM_LPARENTHESIS)
          // type identifier "(" ...
          // procedure declaration or definition
          compile_procedure(variable_or_procedure_name, type);
        else {
          current_line_number = line_number;

          if (symbol == SYM_SEMICOLON) {
            // type identifier ";" ...
            // global variable declaration
            get_symbol();

            initial_value = 0;
          } else
            // type identifier "=" ...
            // global variable definition
            initial_value = compile_initialization(type);

          entry = search_global_symbol_table(variable_or_procedure_name, VARIABLE);

          if (entry == (uint64_t*) 0) {
            allocated_memory = allocated_memory + REGISTERSIZE;

            create_symbol_table_entry(GLOBAL_TABLE, variable_or_procedure_name, current_line_number, VARIABLE, type, initial_value, -allocated_memory);
          } else {
            // global variable already declared or defined
            print_line_number((uint64_t*) "warning", current_line_number);
            printf1((uint64_t*) "redefinition of global variable %s ignored\n", variable_or_procedure_name);
          }
        }
      } else
        syntax_error_symbol(SYM_IDENTIFIER);
    }
  }
}

// -----------------------------------------------------------------
// ------------------------ MACHINE CODE LIBRARY -------------------
// -----------------------------------------------------------------

void emit_round_up(uint64_t reg, uint64_t m) {
  talloc();

  // computes value(reg) + m - 1 - (value(reg) + m - 1) % m
  emit_addi(reg, reg, m - 1);
  emit_addi(current_temporary(), REG_ZR, m);
  emit_remu(current_temporary(), reg, current_temporary());
  emit_sub(reg, reg, current_temporary());

  tfree(1);
}

void emit_left_shift_by(uint64_t reg, uint64_t b) {
  // assert: 0 <= b < 11

  // load multiplication factor less than 2^11 to avoid sign extension
  emit_addi(next_temporary(), REG_ZR, two_to_the_power_of(b));
  emit_mul(reg, reg, next_temporary());
}

void emit_program_entry() {
  uint64_t i;

  i = 0;

  // allocate space for machine initialization code,
  // emit exactly 20 NOPs with source code line 1
  while (i < 20) {
    emit_nop();

    i = i + 1;
  }
}

void emit_bootstrapping() {
  /*
      1. initialize global pointer
      2. initialize malloc's _bump pointer
      3. push argv pointer onto stack
      4. call main procedure
      5. proceed to exit procedure
  */
  uint64_t gp;
  uint64_t padding;
  uint64_t* entry;

  // calculate the global pointer value
  gp = ELF_ENTRY_POINT + binary_length + allocated_memory;

  // make sure gp is double-word-aligned
  padding = gp % REGISTERSIZE;
  gp      = gp + padding;

  if (padding != 0)
    emit_nop();

  // no more allocation in code segment from now on
  code_length = binary_length;

  // reset code emission to program entry
  binary_length = 0;

  // assert: emitting no more than 20 instructions

  if (report_undefined_procedures()) {
    // if there are undefined procedures just exit
    // by loading exit code 0 into return register
    emit_addi(REG_A0, REG_ZR, 0);
  } else {
    // avoid sign extension that would result in an additional sub instruction
    if (gp < two_to_the_power_of(31) - two_to_the_power_of(11))
      // assert: generates no more than two instructions
      load_integer(gp);
    else {
      syntax_error_message((uint64_t*) "maximum program break exceeded");

      exit(EXITCODE_COMPILERERROR);
    }

    // initialize global pointer
    emit_addi(REG_GP, current_temporary(), 0);

    tfree(1);

    // retrieve current program break in return register
    emit_addi(REG_A0, REG_ZR, 0);
    emit_addi(REG_A7, REG_ZR, SYSCALL_BRK);
    emit_ecall();

    // align current program break for double-word access
    emit_round_up(REG_A0, SIZEOFUINT64);

    // set program break to aligned program break
    emit_addi(REG_A7, REG_ZR, SYSCALL_BRK);
    emit_ecall();

    // look up global variable _bump for storing malloc's bump pointer
    // copy "_bump" string into zeroed double word to obtain unique hash
    entry = search_global_symbol_table(string_copy((uint64_t*) "_bump"), VARIABLE);

    // store aligned program break in _bump
    emit_sd(get_scope(entry), get_address(entry), REG_A0);

    // reset return register to initial return value
    emit_addi(REG_A0, REG_ZR, 0);

    // assert: stack is set up with argv pointer still missing
    //
    //    $sp
    //     |
    //     V
    // | argc | argv[0] | argv[1] | ... | argv[n]

    talloc();

    // first obtain pointer to argv
    //
    //    $sp + REGISTERSIZE
    //            |
    //            V
    // | argc | argv[0] | argv[1] | ... | argv[n]
    emit_addi(current_temporary(), REG_SP, REGISTERSIZE);

    // then push argv pointer onto the stack
    //      ______________
    //     |              V
    // | &argv | argc | argv[0] | argv[1] | ... | argv[n]
    emit_addi(REG_SP, REG_SP, -REGISTERSIZE);
    emit_sd(REG_SP, 0, current_temporary());

    tfree(1);

    // assert: global, _bump, and stack pointers are set up
    //         with all other non-temporary registers zeroed

    // copy "main" string into zeroed double word to obtain unique hash
    entry = get_scoped_symbol_table_entry(string_copy((uint64_t*) "main"), PROCEDURE);

    help_call_codegen(entry, (uint64_t*) "main");
  }

  // we exit with exit code in return register pushed onto the stack
  emit_addi(REG_SP, REG_SP, -REGISTERSIZE);
  emit_sd(REG_SP, 0, REG_A0);

  // wrapper code for exit must follow here

  // discount NOPs in profile that were generated for program entry
  ic_addi = ic_addi - binary_length / INSTRUCTIONSIZE;

  // restore original binary length
  binary_length = code_length;
}

// -----------------------------------------------------------------
// --------------------------- COMPILER ----------------------------
// -----------------------------------------------------------------

void selfie_compile() {
  uint64_t link;
  uint64_t number_of_source_files;

  // link until next console option
  link = 1;

  number_of_source_files = 0;

  source_name = (uint64_t*) "library";

  binary_name = source_name;

  // allocate memory for storing binary
  binary       = smalloc(MAX_BINARY_LENGTH);
  binary_length = 0;

  // reset code length
  code_length = 0;

  // allocate zeroed memory for storing source code line numbers
  code_line_number = zalloc(MAX_CODE_LENGTH / INSTRUCTIONSIZE * SIZEOFUINT64);
  data_line_number = zalloc(MAX_DATA_LENGTH / REGISTERSIZE * SIZEOFUINT64);

  reset_symbol_tables();
  reset_instruction_counters();

  emit_program_entry();

  // emit system call wrappers
  // exit code must be first
  emit_exit();
  emit_read();
  emit_write();
  emit_open();
  emit_malloc();
  emit_switch();
  emit_input();

  // implicitly declare main procedure in global symbol table
  // copy "main" string into zeroed double word to obtain unique hash
  create_symbol_table_entry(GLOBAL_TABLE, string_copy((uint64_t*) "main"), 0, PROCEDURE, UINT64_T, 0, 0);

  while (link) {
    if (number_of_remaining_arguments() == 0)
      link = 0;
    else if (load_character(peek_argument(), 0) == '-')
      link = 0;
    else {
      source_name = get_argument();

      number_of_source_files = number_of_source_files + 1;

      printf2((uint64_t*) "%s: selfie compiling %s with starc\n", selfie_name, source_name);

      // assert: source_name is mapped and not longer than MAX_FILENAME_LENGTH

      source_fd = sign_extend(open(source_name, O_RDONLY, 0), SYSCALL_BITWIDTH);

      if (signed_less_than(source_fd, 0)) {
        printf2((uint64_t*) "%s: could not open input file %s\n", selfie_name, source_name);

        exit(EXITCODE_IOERROR);
      }

      reset_scanner();
      reset_parser();

      compile_cstar();

      printf4((uint64_t*) "%s: %d characters read in %d lines and %d comments\n", selfie_name,
        (uint64_t*) number_of_read_characters,
        (uint64_t*) line_number,
        (uint64_t*) number_of_comments);

      printf4((uint64_t*) "%s: with %d(%.2d%%) characters in %d actual symbols\n", selfie_name,
        (uint64_t*) (number_of_read_characters - number_of_ignored_characters),
        (uint64_t*) fixed_point_percentage(fixed_point_ratio(number_of_read_characters, number_of_read_characters - number_of_ignored_characters, 4), 4),
        (uint64_t*) number_of_scanned_symbols);

      printf4((uint64_t*) "%s: %d global variables, %d procedures, %d string literals\n", selfie_name,
        (uint64_t*) number_of_global_variables,
        (uint64_t*) number_of_procedures,
        (uint64_t*) number_of_strings);

      printf6((uint64_t*) "%s: %d calls, %d assignments, %d while, %d if, %d return\n", selfie_name,
        (uint64_t*) number_of_calls,
        (uint64_t*) number_of_assignments,
        (uint64_t*) number_of_while,
        (uint64_t*) number_of_if,
        (uint64_t*) number_of_return);
    }
  }

  if (number_of_source_files == 0)
    printf1((uint64_t*) "%s: nothing to compile, only library generated\n", selfie_name);

  emit_bootstrapping();

  emit_data_segment();

  ELF_header = create_elf_header(binary_length);

  entry_point = ELF_ENTRY_POINT;

  printf3((uint64_t*) "%s: symbol table search time was %d iterations on average and %d in total\n", selfie_name, (uint64_t*) (total_search_time / number_of_searches), (uint64_t*) total_search_time);

  printf4((uint64_t*) "%s: %d bytes generated with %d instructions and %d bytes of data\n", selfie_name,
    (uint64_t*) binary_length,
    (uint64_t*) (code_length / INSTRUCTIONSIZE),
    (uint64_t*) (binary_length - code_length));

  print_instruction_counters();
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// --------------------------- REGISTER ----------------------------
// -----------------------------------------------------------------

uint64_t* get_register_name(uint64_t reg) {
  return (uint64_t*) *(REGISTERS + reg);
}

void print_register_name(uint64_t reg) {
  print(get_register_name(reg));
}

// -----------------------------------------------------------------
// ------------------------ ENCODER/DECODER ------------------------
// -----------------------------------------------------------------

void check_immediate_range(uint64_t immediate, uint64_t bits) {
  if (is_signed_integer(immediate, bits) == 0) {
    print_line_number((uint64_t*) "encoding error", line_number);
    printf3((uint64_t*) "%d expected between %d and %d\n",
      (uint64_t*) immediate,
      (uint64_t*) -two_to_the_power_of(bits - 1),
      (uint64_t*) two_to_the_power_of(bits - 1) - 1);

    exit(EXITCODE_COMPILERERROR);
  }
}

// RISC-V R Format
// ----------------------------------------------------------------
// |        7         |  5  |  5  |  3   |        5        |  7   |
// +------------------+-----+-----+------+-----------------+------+
// |      funct7      | rs2 | rs1 |funct3|       rd        |opcode|
// +------------------+-----+-----+------+-----------------+------+
// |31              25|24 20|19 15|14  12|11              7|6    0|
// ----------------------------------------------------------------

uint64_t encode_r_format(uint64_t funct7, uint64_t rs2, uint64_t rs1, uint64_t funct3, uint64_t rd, uint64_t opcode) {
  // assert: 0 <= funct7 < 2^7
  // assert: 0 <= rs2 < 2^5
  // assert: 0 <= rs1 < 2^5
  // assert: 0 <= funct3 < 2^3
  // assert: 0 <= rd < 2^5
  // assert: 0 <= opcode < 2^7

  return left_shift(left_shift(left_shift(left_shift(left_shift(funct7, 5) + rs2, 5) + rs1, 3) + funct3, 5) + rd, 7) + opcode;
}

uint64_t get_funct7(uint64_t instruction) {
  return get_bits(instruction, 25, 7);
}

uint64_t get_rs2(uint64_t instruction) {
  return get_bits(instruction, 20, 5);
}

uint64_t get_rs1(uint64_t instruction) {
  return get_bits(instruction, 15, 5);
}

uint64_t get_funct3(uint64_t instruction) {
  return get_bits(instruction, 12, 3);
}

uint64_t get_rd(uint64_t instruction) {
  return get_bits(instruction, 7, 5);
}

uint64_t get_opcode(uint64_t instruction) {
  return get_bits(instruction, 0, 7);
}

void decode_r_format() {
  funct7 = get_funct7(ir);
  rs2    = get_rs2(ir);
  rs1    = get_rs1(ir);
  funct3 = get_funct3(ir);
  rd     = get_rd(ir);
  imm    = 0;
}

// RISC-V I Format
// ----------------------------------------------------------------
// |           12           |  5  |  3   |        5        |  7   |
// +------------------------+-----+------+-----------------+------+
// |    immediate[11:0]     | rs1 |funct3|       rd        |opcode|
// +------------------------+-----+------+-----------------+------+
// |31                    20|19 15|14  12|11              7|6    0|
// ----------------------------------------------------------------

uint64_t encode_i_format(uint64_t immediate, uint64_t rs1, uint64_t funct3, uint64_t rd, uint64_t opcode) {
  // assert: -2^11 <= immediate < 2^11
  // assert: 0 <= rs1 < 2^5
  // assert: 0 <= funct3 < 2^3
  // assert: 0 <= rd < 2^5
  // assert: 0 <= opcode < 2^7

  check_immediate_range(immediate, 12);

  immediate = sign_shrink(immediate, 12);

  return left_shift(left_shift(left_shift(left_shift(immediate, 5) + rs1, 3) + funct3, 5) + rd, 7) + opcode;
}

uint64_t get_immediate_i_format(uint64_t instruction) {
  return sign_extend(get_bits(instruction, 20, 12), 12);
}

void decode_i_format() {
  funct7 = 0;
  rs2    = 0;
  rs1    = get_rs1(ir);
  funct3 = get_funct3(ir);
  rd     = get_rd(ir);
  imm    = get_immediate_i_format(ir);
}

// RISC-V S Format
// ----------------------------------------------------------------
// |        7         |  5  |  5  |  3   |        5        |  7   |
// +------------------+-----+-----+------+-----------------+------+
// |    imm1[11:5]    | rs2 | rs1 |funct3|    imm2[4:0]    |opcode|
// +------------------+-----+-----+------+-----------------+------+
// |31              25|24 20|19 15|14  12|11              7|6    0|
// ----------------------------------------------------------------

uint64_t encode_s_format(uint64_t immediate, uint64_t rs2, uint64_t rs1, uint64_t funct3, uint64_t opcode) {
  // assert: -2^11 <= immediate < 2^11
  // assert: 0 <= rs2 < 2^5
  // assert: 0 <= rs1 < 2^5
  // assert: 0 <= funct3 < 2^3
  // assert: 0 <= opcode < 2^7
  uint64_t imm1;
  uint64_t imm2;

  check_immediate_range(immediate, 12);

  immediate = sign_shrink(immediate, 12);

  imm1 = get_bits(immediate, 5, 7);
  imm2 = get_bits(immediate, 0, 5);

  return left_shift(left_shift(left_shift(left_shift(left_shift(imm1, 5) + rs2, 5) + rs1, 3) + funct3, 5) + imm2, 7) + opcode;
}

uint64_t get_immediate_s_format(uint64_t instruction) {
  uint64_t imm1;
  uint64_t imm2;

  imm1 = get_bits(instruction, 25, 7);
  imm2 = get_bits(instruction,  7, 5);

  return sign_extend(left_shift(imm1, 5) + imm2, 12);
}

void decode_s_format() {
  funct7 = 0;
  rs2    = get_rs2(ir);
  rs1    = get_rs1(ir);
  funct3 = get_funct3(ir);
  rd     = 0;
  imm    = get_immediate_s_format(ir);
}

// RISC-V B Format
// ----------------------------------------------------------------
// |        7         |  5  |  5  |  3   |        5        |  7   |
// +------------------+-----+-----+------+-----------------+------+
// |imm1[12]imm2[10:5]| rs2 | rs1 |funct3|imm3[4:1]imm4[11]|opcode|
// +------------------+-----+-----+------+-----------------+------+
// |31              25|24 20|19 15|14  12|11              7|6    0|
// ----------------------------------------------------------------

uint64_t encode_b_format(uint64_t immediate, uint64_t rs2, uint64_t rs1, uint64_t funct3, uint64_t opcode) {
  // assert: -2^12 <= immediate < 2^12
  // assert: 0 <= rs2 < 2^5
  // assert: 0 <= rs1 < 2^5
  // assert: 0 <= funct3 < 2^3
  // assert: 0 <= opcode < 2^7
  uint64_t imm1;
  uint64_t imm2;
  uint64_t imm3;
  uint64_t imm4;

  check_immediate_range(immediate, 13);

  immediate = sign_shrink(immediate, 13);

  // LSB of immediate is lost
  imm1 = get_bits(immediate, 12, 1);
  imm2 = get_bits(immediate,  5, 6);
  imm3 = get_bits(immediate,  1, 4);
  imm4 = get_bits(immediate, 11, 1);

  return left_shift(left_shift(left_shift(left_shift(left_shift(left_shift(left_shift(imm1, 6) + imm2, 5) + rs2, 5) + rs1, 3) + funct3, 4) + imm3, 1) + imm4, 7) + opcode;
}

uint64_t get_immediate_b_format(uint64_t instruction) {
  uint64_t imm1;
  uint64_t imm2;
  uint64_t imm3;
  uint64_t imm4;

  imm1 = get_bits(instruction, 31, 1);
  imm2 = get_bits(instruction, 25, 6);
  imm3 = get_bits(instruction,  8, 4);
  imm4 = get_bits(instruction,  7, 1);

  // reassemble immediate and add trailing zero
  return sign_extend(left_shift(left_shift(left_shift(left_shift(imm1, 1) + imm4, 6) + imm2, 4) + imm3, 1), 13);
}

void decode_b_format() {
  funct7 = 0;
  rs2    = get_rs2(ir);
  rs1    = get_rs1(ir);
  funct3 = get_funct3(ir);
  rd     = 0;
  imm    = get_immediate_b_format(ir);
}

// RISC-V J Format
// ----------------------------------------------------------------
// |                  20                 |        5        |  7   |
// +-------------------------------------+-----------------+------+
// |imm1[20]imm2[10:1]imm3[11]imm4[19:12]|       rd        |opcode|
// +-------------------------------------+-----------------+------+
// |31                                 12|11              7|6    0|
// ----------------------------------------------------------------

uint64_t encode_j_format(uint64_t immediate, uint64_t rd, uint64_t opcode) {
  // assert: -2^20 <= immediate < 2^20
  // assert: 0 <= rd < 2^5
  // assert: 0 <= opcode < 2^7
  uint64_t imm1;
  uint64_t imm2;
  uint64_t imm3;
  uint64_t imm4;

  check_immediate_range(immediate, 21);

  immediate = sign_shrink(immediate, 21);

  // LSB of immediate is lost
  imm1 = get_bits(immediate, 20,  1);
  imm2 = get_bits(immediate,  1, 10);
  imm3 = get_bits(immediate, 11,  1);
  imm4 = get_bits(immediate, 12,  8);

  return left_shift(left_shift(left_shift(left_shift(left_shift(imm1, 10) + imm2, 1) + imm3, 8) + imm4, 5) + rd, 7) + opcode;
}

uint64_t get_immediate_j_format(uint64_t instruction) {
  uint64_t imm1;
  uint64_t imm2;
  uint64_t imm3;
  uint64_t imm4;

  imm1 = get_bits(instruction, 31,  1);
  imm2 = get_bits(instruction, 21, 10);
  imm3 = get_bits(instruction, 20,  1);
  imm4 = get_bits(instruction, 12,  8);

  // reassemble immediate and add trailing zero
  return sign_extend(left_shift(left_shift(left_shift(left_shift(imm1, 8) + imm4, 1) + imm3, 10) + imm2, 1), 21);
}

void decode_j_format() {
  funct7 = 0;
  rs2    = 0;
  rs1    = 0;
  funct3 = 0;
  rd     = get_rd(ir);
  imm    = get_immediate_j_format(ir);
}

// RISC-V U Format
// ----------------------------------------------------------------
// |                  20                 |        5        |  7   |
// +-------------------------------------+-----------------+------+
// |           immediate[19:0]           |       rd        |opcode|
// +-------------------------------------+-----------------+------+
// |31                                 12|11              7|6    0|
// ----------------------------------------------------------------

uint64_t encode_u_format(uint64_t immediate, uint64_t rd, uint64_t opcode) {
  // assert: -2^19 <= immediate < 2^19
  // assert: 0 <= rd < 2^5
  // assert: 0 <= opcode < 2^7

  check_immediate_range(immediate, 20);

  immediate = sign_shrink(immediate, 20);

  return left_shift(left_shift(immediate, 5) + rd, 7) + opcode;
}

uint64_t get_immediate_u_format(uint64_t instruction) {
  return sign_extend(get_bits(instruction, 12, 20), 20);
}

void decode_u_format() {
  funct7 = 0;
  rs2    = 0;
  rs1    = 0;
  funct3 = 0;
  rd     = get_rd(ir);
  imm    = get_immediate_u_format(ir);
}

// -----------------------------------------------------------------
// ---------------------------- BINARY -----------------------------
// -----------------------------------------------------------------

void reset_instruction_counters() {
  ic_lui   = 0;
  ic_addi  = 0;
  ic_add   = 0;
  ic_sub   = 0;
  ic_mul   = 0;
  ic_divu  = 0;
  ic_remu  = 0;
  ic_sltu  = 0;
  ic_ld    = 0;
  ic_sd    = 0;
  ic_beq   = 0;
  ic_jal   = 0;
  ic_jalr  = 0;
  ic_ecall = 0;
}

uint64_t get_total_number_of_instructions() {
  return ic_lui + ic_addi + ic_add + ic_sub + ic_mul + ic_divu + ic_remu + ic_sltu + ic_ld + ic_sd + ic_beq + ic_jal + ic_jalr + ic_ecall;
}

void print_instruction_counter(uint64_t total, uint64_t counter, uint64_t* mnemonics) {
  printf3((uint64_t*)
    "%s: %d(%.2d%%)",
    mnemonics,
    (uint64_t*) counter,
    (uint64_t*) fixed_point_percentage(fixed_point_ratio(total, counter, 4), 4));
}

void print_instruction_counters() {
  uint64_t ic;

  ic = get_total_number_of_instructions();

  printf1((uint64_t*) "%s: init:    ", selfie_name);
  print_instruction_counter(ic, ic_lui, (uint64_t*) "lui");
  print((uint64_t*) ", ");
  print_instruction_counter(ic, ic_addi, (uint64_t*) "addi");
  println();

  printf1((uint64_t*) "%s: memory:  ", selfie_name);
  print_instruction_counter(ic, ic_ld, (uint64_t*) "ld");
  print((uint64_t*) ", ");
  print_instruction_counter(ic, ic_sd, (uint64_t*) "sd");
  println();

  printf1((uint64_t*) "%s: compute: ", selfie_name);
  print_instruction_counter(ic, ic_add, (uint64_t*) "add");
  print((uint64_t*) ", ");
  print_instruction_counter(ic, ic_sub, (uint64_t*) "sub");
  print((uint64_t*) ", ");
  print_instruction_counter(ic, ic_mul, (uint64_t*) "mul");
  print((uint64_t*) ", ");
  print_instruction_counter(ic, ic_divu, (uint64_t*) "divu");
  print((uint64_t*) ", ");
  print_instruction_counter(ic, ic_remu, (uint64_t*) "remu");
  println();

  printf1((uint64_t*) "%s: control: ", selfie_name);
  print_instruction_counter(ic, ic_sltu, (uint64_t*) "sltu");
  print((uint64_t*) ", ");
  print_instruction_counter(ic, ic_beq, (uint64_t*) "beq");
  print((uint64_t*) ", ");
  print_instruction_counter(ic, ic_jal, (uint64_t*) "jal");
  print((uint64_t*) ", ");
  print_instruction_counter(ic, ic_jalr, (uint64_t*) "jalr");
  print((uint64_t*) ", ");
  print_instruction_counter(ic, ic_ecall, (uint64_t*) "ecall");
  println();
}

uint64_t load_instruction(uint64_t baddr) {
  if (baddr % REGISTERSIZE == 0)
    return get_low_word(*(binary + baddr / REGISTERSIZE));
  else
    return get_high_word(*(binary + baddr / REGISTERSIZE));
}

void store_instruction(uint64_t baddr, uint64_t instruction) {
  uint64_t temp;

  if (baddr >= MAX_CODE_LENGTH) {
    syntax_error_message((uint64_t*) "maximum code length exceeded");

    exit(EXITCODE_COMPILERERROR);
  }

  temp = *(binary + baddr / REGISTERSIZE);

  if (baddr % REGISTERSIZE == 0)
    // replace low word
    temp = left_shift(get_high_word(temp), WORDSIZEINBITS) + instruction;
  else
    // replace high word
    temp = left_shift(instruction, WORDSIZEINBITS) + get_low_word(temp);

  *(binary + baddr / REGISTERSIZE) = temp;
}

uint64_t load_data(uint64_t baddr) {
  return *(binary + baddr / REGISTERSIZE);
}

void store_data(uint64_t baddr, uint64_t data) {
  if (baddr >= MAX_CODE_LENGTH + MAX_DATA_LENGTH) {
    syntax_error_message((uint64_t*) "maximum data length exceeded");

    exit(EXITCODE_COMPILERERROR);
  }

  *(binary + baddr / REGISTERSIZE) = data;
}

void emit_instruction(uint64_t instruction) {
  store_instruction(binary_length, instruction);

  if (*(code_line_number + binary_length / INSTRUCTIONSIZE) == 0)
    *(code_line_number + binary_length / INSTRUCTIONSIZE) = line_number;

  binary_length = binary_length + INSTRUCTIONSIZE;
}

void emit_nop() {
  emit_instruction(encode_i_format(0, REG_ZR, F3_NOP, REG_ZR, OP_IMM));

  ic_addi = ic_addi + 1;
}

void emit_lui(uint64_t rd, uint64_t immediate) {
  emit_instruction(encode_u_format(immediate, rd, OP_LUI));

  ic_lui = ic_lui + 1;
}

void emit_addi(uint64_t rd, uint64_t rs1, uint64_t immediate) {
  emit_instruction(encode_i_format(immediate, rs1, F3_ADDI, rd, OP_IMM));

  ic_addi = ic_addi + 1;
}

void emit_add(uint64_t rd, uint64_t rs1, uint64_t rs2) {
  emit_instruction(encode_r_format(F7_ADD, rs2, rs1, F3_ADD, rd, OP_OP));

  ic_add = ic_add + 1;
}

void emit_sub(uint64_t rd, uint64_t rs1, uint64_t rs2) {
  emit_instruction(encode_r_format(F7_SUB, rs2, rs1, F3_SUB, rd, OP_OP));

  ic_sub = ic_sub + 1;
}

void emit_mul(uint64_t rd, uint64_t rs1, uint64_t rs2) {
  emit_instruction(encode_r_format(F7_MUL, rs2, rs1, F3_MUL, rd, OP_OP));

  ic_mul = ic_mul + 1;
}

void emit_divu(uint64_t rd, uint64_t rs1, uint64_t rs2) {
  emit_instruction(encode_r_format(F7_DIVU, rs2, rs1, F3_DIVU, rd, OP_OP));

  ic_divu = ic_divu + 1;
}

void emit_remu(uint64_t rd, uint64_t rs1, uint64_t rs2) {
  emit_instruction(encode_r_format(F7_REMU, rs2, rs1, F3_REMU, rd, OP_OP));

  ic_remu = ic_remu + 1;
}

void emit_sltu(uint64_t rd, uint64_t rs1, uint64_t rs2) {
  emit_instruction(encode_r_format(F7_SLTU, rs2, rs1, F3_SLTU, rd, OP_OP));

  ic_sltu = ic_sltu + 1;
}

void emit_ld(uint64_t rd, uint64_t rs1, uint64_t immediate) {
  emit_instruction(encode_i_format(immediate, rs1, F3_LD, rd, OP_LD));

  ic_ld = ic_ld + 1;
}

void emit_sd(uint64_t rs1, uint64_t immediate, uint64_t rs2) {
  emit_instruction(encode_s_format(immediate, rs2, rs1, F3_SD, OP_SD));

  ic_sd = ic_sd + 1;
}

void emit_beq(uint64_t rs1, uint64_t rs2, uint64_t immediate) {
  emit_instruction(encode_b_format(immediate, rs2, rs1, F3_BEQ, OP_BRANCH));

  ic_beq = ic_beq + 1;
}

void emit_jal(uint64_t rd, uint64_t immediate) {
  emit_instruction(encode_j_format(immediate, rd, OP_JAL));

  ic_jal = ic_jal + 1;
}

void emit_jalr(uint64_t rd, uint64_t rs1, uint64_t immediate) {
  emit_instruction(encode_i_format(immediate, rs1, F3_JALR, rd, OP_JALR));

  ic_jalr = ic_jalr + 1;
}

void emit_ecall() {
  emit_instruction(encode_i_format(F12_ECALL, REG_ZR, F3_ECALL, REG_ZR, OP_SYSTEM));

  ic_ecall = ic_ecall + 1;
}

void fixup_relative_BFormat(uint64_t from_address) {
  uint64_t instruction;

  instruction = load_instruction(from_address);

  store_instruction(from_address,
    encode_b_format(binary_length - from_address,
      get_rs2(instruction),
      get_rs1(instruction),
      get_funct3(instruction),
      get_opcode(instruction)));
}

void fixup_relative_JFormat(uint64_t from_address, uint64_t to_address) {
  uint64_t instruction;

  instruction = load_instruction(from_address);

  store_instruction(from_address,
    encode_j_format(to_address - from_address,
      get_rd(instruction),
      get_opcode(instruction)));
}

void fixlink_relative(uint64_t from_address, uint64_t to_address) {
  uint64_t previous_address;

  while (from_address != 0) {
    previous_address = get_immediate_j_format(load_instruction(from_address));

    fixup_relative_JFormat(from_address, to_address);

    from_address = previous_address;
  }
}

void emit_data_word(uint64_t data, uint64_t offset, uint64_t source_line_number) {
  // assert: offset < 0

  store_data(binary_length + offset, data);

  if (data_line_number != (uint64_t*) 0)
    *(data_line_number + (allocated_memory + offset) / REGISTERSIZE) = source_line_number;
}

void emit_string_data(uint64_t* entry) {
  uint64_t* s;
  uint64_t i;
  uint64_t l;

  s = get_string(entry);

  i = 0;

  l = round_up(string_length(s) + 1, REGISTERSIZE);

  while (i < l) {
    emit_data_word(*s, get_address(entry) + i, get_line_number(entry));

    s = s + 1;

    i = i + REGISTERSIZE;
  }
}

void emit_data_segment() {
  uint64_t i;
  uint64_t* entry;

  binary_length = binary_length + allocated_memory;

  i = 0;

  while (i < HASH_TABLE_SIZE) {
    entry = (uint64_t*) *(global_symbol_table + i);

    // copy initial values of global variables, big integers and strings
    while ((uint64_t) entry != 0) {
      if (get_class(entry) == VARIABLE)
        emit_data_word(get_value(entry), get_address(entry), get_line_number(entry));
      else if (get_class(entry) == BIGINT)
        emit_data_word(get_value(entry), get_address(entry), get_line_number(entry));
      else if (get_class(entry) == STRING)
        emit_string_data(entry);

      entry = get_next_entry(entry);
    }

    i = i + 1;
  }

  allocated_memory = 0;
}

uint64_t* create_elf_header(uint64_t binary_length) {
  uint64_t* header;

  // store all numbers necessary to create a minimal and valid
  // ELF64 header including the program header
  header = smalloc(ELF_HEADER_LEN);

  // RISC-U ELF64 file header:
  *(header + 0) = 127                               // magic number part 0 is 0x7F
                + left_shift((uint64_t) 'E', 8)     // magic number part 1
                + left_shift((uint64_t) 'L', 16)    // magic number part 2
                + left_shift((uint64_t) 'F', 24)    // magic number part 3
                + left_shift(2, 32)                 // file class is ELFCLASS64
                + left_shift(1, 40)                 // object file data structures endianess is ELFDATA2LSB
                + left_shift(1, 48);                // version of the object file format
  *(header + 1) = 0;                                // ABI version and start of padding bytes
  *(header + 2) = 2                                 // object file type is ET_EXEC
                + left_shift(243, 16)               // target architecture is RV64
                + left_shift(1, 32);                // version of the object file format
  *(header + 3) = ELF_ENTRY_POINT;                  // entry point address
  *(header + 4) = 8 * SIZEOFUINT64;                 // program header offset
  *(header + 5) = 0;                                // section header offset
  *(header + 6) = left_shift(8 * SIZEOFUINT64, 32)  // elf header size
                + left_shift(7 * SIZEOFUINT64, 48); // size of program header entry
  *(header + 7) = 1;                                // number of program header entries

  // RISC-U ELF64 program header table:
  *(header + 8)  = 1                              // type of segment is LOAD
                 + left_shift(7, 32);             // segment attributes is RWX
  *(header + 9)  = ELF_HEADER_LEN + SIZEOFUINT64; // segment offset in file
  *(header + 10) = ELF_ENTRY_POINT;               // virtual address in memory
  *(header + 11) = 0;                             // physical address (reserved)
  *(header + 12) = binary_length;                 // size of segment in file
  *(header + 13) = binary_length;                 // size of segment in memory
  *(header + 14) = PAGESIZE;                      // alignment of segment

  return header;
}

uint64_t validate_elf_header(uint64_t* header) {
  uint64_t  new_entry_point;
  uint64_t  new_binary_length;
  uint64_t  position;
  uint64_t* valid_header;

  new_entry_point   = *(header + 10);
  new_binary_length = *(header + 12);

  if (new_binary_length != *(header + 13))
    // segment size in file is not the same as segment size in memory
    return 0;

  if (new_entry_point > VIRTUALMEMORYSIZE - PAGESIZE - new_binary_length)
    // binary does not fit into virtual address space
    return 0;

  valid_header = create_elf_header(new_binary_length);

  position = 0;

  while (position < ELF_HEADER_LEN / SIZEOFUINT64) {
    if (*(header + position) != *(valid_header + position))
      return 0;

    position = position + 1;
  }

  entry_point   = new_entry_point;
  binary_length = new_binary_length;

  return 1;
}

uint64_t open_write_only(uint64_t* name) {
  // we try opening write-only files using platform-specific flags
  // to make selfie platform-independent, this may nevertheless
  // not always work and require intervention
  uint64_t fd;

  // try Mac flags
  fd = sign_extend(open(name, MAC_O_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH), SYSCALL_BITWIDTH);

  if (signed_less_than(fd, 0)) {
    // try Linux flags
    fd = sign_extend(open(name, LINUX_O_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH), SYSCALL_BITWIDTH);

    if (signed_less_than(fd, 0))
      // try Windows flags
      fd = sign_extend(open(name, WINDOWS_O_BINARY_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH), SYSCALL_BITWIDTH);
  }

  return fd;
}

void selfie_output() {
  uint64_t fd;

  binary_name = get_argument();

  if (binary_length == 0) {
    printf2((uint64_t*) "%s: nothing to emit to output file %s\n", selfie_name, binary_name);

    return;
  }

  // assert: binary_name is mapped and not longer than MAX_FILENAME_LENGTH

  fd = open_write_only(binary_name);

  if (signed_less_than(fd, 0)) {
    printf2((uint64_t*) "%s: could not create binary output file %s\n", selfie_name, binary_name);

    exit(EXITCODE_IOERROR);
  }

  // assert: ELF_header is mapped

  // first write ELF header
  if (write(fd, ELF_header, ELF_HEADER_LEN) != ELF_HEADER_LEN) {
    printf2((uint64_t*) "%s: could not write ELF header of binary output file %s\n", selfie_name, binary_name);

    exit(EXITCODE_IOERROR);
  }

  // then write code length
  *binary_buffer = code_length;

  if (write(fd, binary_buffer, SIZEOFUINT64) != SIZEOFUINT64) {
    printf2((uint64_t*) "%s: could not write code length of binary output file %s\n", selfie_name, binary_name);

    exit(EXITCODE_IOERROR);
  }

  // assert: binary is mapped

  // then write binary
  if (write(fd, binary, binary_length) != binary_length) {
    printf2((uint64_t*) "%s: could not write binary into binary output file %s\n", selfie_name, binary_name);

    exit(EXITCODE_IOERROR);
  }

  printf5((uint64_t*) "%s: %d bytes with %d instructions and %d bytes of data written into %s\n",
    selfie_name,
    (uint64_t*) (ELF_HEADER_LEN + SIZEOFUINT64 + binary_length),
    (uint64_t*) (code_length / INSTRUCTIONSIZE),
    (uint64_t*) (binary_length - code_length),
    binary_name);
}

uint64_t* touch(uint64_t* memory, uint64_t length) {
  uint64_t* m;
  uint64_t n;

  m = memory;

  if (length > 0)
    // touch memory at beginning
    n = *m;

  while (length > PAGESIZE) {
    length = length - PAGESIZE;

    m = m + PAGESIZE / REGISTERSIZE;

    // touch every following page
    n = *m;
  }

  if (length > 0) {
    m = m + (length - 1) / REGISTERSIZE;

    // touch at end
    n = *m;
  }

  // avoids unused warning for n
  n = 0; n = n + 1;

  return memory;
}

void selfie_load() {
  uint64_t fd;
  uint64_t number_of_read_bytes;

  binary_name = get_argument();

  // assert: binary_name is mapped and not longer than MAX_FILENAME_LENGTH

  fd = sign_extend(open(binary_name, O_RDONLY, 0), SYSCALL_BITWIDTH);

  if (signed_less_than(fd, 0)) {
    printf2((uint64_t*) "%s: could not open input file %s\n", selfie_name, binary_name);

    exit(EXITCODE_IOERROR);
  }

  // make sure binary is mapped for reading into it
  binary = touch(smalloc(MAX_BINARY_LENGTH), MAX_BINARY_LENGTH);

  binary_length = 0;
  code_length   = 0;
  entry_point   = 0;

  // no source line numbers in binaries
  code_line_number = (uint64_t*) 0;
  data_line_number = (uint64_t*) 0;

  // make sure ELF_header is mapped for reading into it
  ELF_header = touch(smalloc(ELF_HEADER_LEN), ELF_HEADER_LEN);

  // read ELF_header first
  number_of_read_bytes = read(fd, ELF_header, ELF_HEADER_LEN);

  if (number_of_read_bytes == ELF_HEADER_LEN) {
    if (validate_elf_header(ELF_header)) {
      // now read code length
      number_of_read_bytes = read(fd, binary_buffer, SIZEOFUINT64);

      if (number_of_read_bytes == SIZEOFUINT64) {
        code_length = *binary_buffer;

        if (binary_length <= MAX_BINARY_LENGTH) {
          // now read binary including global variables and strings
          number_of_read_bytes = sign_extend(read(fd, binary, binary_length), SYSCALL_BITWIDTH);

          if (signed_less_than(0, number_of_read_bytes)) {
            // check if we are really at EOF
            if (read(fd, binary_buffer, SIZEOFUINT64) == 0) {
              printf5((uint64_t*) "%s: %d bytes with %d instructions and %d bytes of data loaded from %s\n",
                selfie_name,
                (uint64_t*) (ELF_HEADER_LEN + SIZEOFUINT64 + binary_length),
                (uint64_t*) (code_length / INSTRUCTIONSIZE),
                (uint64_t*) (binary_length - code_length),
                binary_name);

              return;
            }
          }
        }
      }
    }
  }

  printf2((uint64_t*) "%s: failed to load code from input file %s\n", selfie_name, binary_name);

  exit(EXITCODE_IOERROR);
}

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emit_exit() {
  create_symbol_table_entry(LIBRARY_TABLE, (uint64_t*) "exit", 0, PROCEDURE, VOID_T, 0, binary_length);

  // load signed 32-bit integer argument for exit
  emit_ld(REG_A0, REG_SP, 0);

  // remove the argument from the stack
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  // load the correct syscall number and invoke syscall
  emit_addi(REG_A7, REG_ZR, SYSCALL_EXIT);

  emit_ecall();

  // never returns here
}

void print_witness() {
  uint64_t idx;
  uint64_t input_idx;
  idx = tc;

  while (idx != 0) {
    if (get_trace_type(idx) != CONCRETE_T) { //look for the first symbolic value into the trace
      //get the most recent value
      input_idx = load_virtual_memory(pt, get_trace_vaddr(get_src_input(idx)));
      print((uint64_t*) "Symbolic values witness:\n");
      print_msiid(get_trace_a1(input_idx), get_trace_a2(input_idx), get_trace_a3(input_idx));
      printf2((uint64_t*) " for variable: %x at index [%d]\n", (uint64_t*) get_trace_vaddr(input_idx), (uint64_t*) input_idx);
      if (sdebug_context)
        print_src_list(idx);
      return;
    }
    idx = idx - 1;
  }
  print((uint64_t*) "No symbolic values: concrete execution?\n");
}

void print_end_point_status(uint64_t* context, uint64_t start, uint64_t end, uint64_t step) {
  printf3((uint64_t*) "%s: %s reaching end point at: %p", selfie_name, get_name(context), (uint64_t*) (last_jal_from - entry_point));
  print_code_line_number_for_instruction(last_jal_from - entry_point);
  printf3((uint64_t*) " with exit code <%d,%d,%d>\n", (uint64_t*) start, (uint64_t*) end, (uint64_t*) step);
  printf1((uint64_t*) "%d instructions executed for the path.\n", (uint64_t*) get_total_number_of_instructions());
  //witness
  print_witness();

  if (sdebug_trace)
    print_trace();

  //correct value (msiid)
  if(step != 0) {
    print_concrete_bounds(start, end, step);
    println();
  }
}

void implement_exit(uint64_t* context) {
  if (disassemble) {
    print((uint64_t*) "(exit): ");
    print_register_hexadecimal(REG_A0);
    print((uint64_t*) " |- ->\n");
  }

  if (symbolic) {
    set_exit_code(context, *(registers + REG_A0));
    set_exit_code_a2(context, *(reg_alpha2 + REG_A0));
    set_exit_code_a3(context, *(reg_alpha3 + REG_A0));
    return;
  }

  set_exit_code(context, sign_shrink(*(get_regs(context) + REG_A0), SYSCALL_BITWIDTH));
  printf4((uint64_t*)
    "%s: %s exiting with exit code %d and %.2dMB mallocated memory\n",
    selfie_name,
    get_name(context),
    (uint64_t*) sign_extend(get_exit_code(context), SYSCALL_BITWIDTH),
    (uint64_t*) fixed_point_ratio(get_program_break(context) - get_original_break(context), MEGABYTE, 2));
}

void emit_read() {
  create_symbol_table_entry(LIBRARY_TABLE, (uint64_t*) "read", 0, PROCEDURE, UINT64_T, 0, binary_length);

  emit_ld(REG_A2, REG_SP, 0); // size
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A1, REG_SP, 0); // *buffer
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A0, REG_SP, 0); // fd
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_addi(REG_A7, REG_ZR, SYSCALL_READ);

  emit_ecall();

  // jump back to caller, return value is in REG_A0
  emit_jalr(REG_ZR, REG_RA, 0);
}

uint64_t init_type(uint64_t lo, uint64_t up) {
  if (lo == up) return CONCRETE_T;
  return MSIID_T;
}

void implement_read(uint64_t* context) {
  // parameters
  uint64_t fd;
  uint64_t vbuffer;
  uint64_t size;

  // local variables
  uint64_t read_total;
  uint64_t bytes_to_read;
  uint64_t failed;
  uint64_t* buffer;
  uint64_t actually_read;
  uint64_t value;
  uint64_t lo;
  uint64_t up;
  uint64_t mrvc;

  if (disassemble) {
    print((uint64_t*) "(read): ");
    print_register_value(REG_A0);
    print((uint64_t*) ",");
    print_register_hexadecimal(REG_A1);
    print((uint64_t*) ",");
    print_register_value(REG_A2);
    print((uint64_t*) " |- ");
    print_register_value(REG_A0);
  }

  fd      = *(get_regs(context) + REG_A0);
  vbuffer = *(get_regs(context) + REG_A1);
  size    = *(get_regs(context) + REG_A2);

  if (debug_read)
    printf4((uint64_t*) "%s: trying to read %d bytes from file with descriptor %d into buffer at virtual address %p\n", selfie_name, (uint64_t*) size, (uint64_t*) fd, (uint64_t*) vbuffer);

  read_total   = 0;
  bytes_to_read = SIZEOFUINT64;

  failed = 0;

  while (size > 0) {
    if (is_valid_virtual_address(vbuffer)) {
      if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
        buffer = tlb(get_pt(context), vbuffer);

        if (size < bytes_to_read)
          bytes_to_read = size;

        if (symbolic) {
          if (is_trace_space_available()) {

            //bound
            if (number_of_reads < MAX_READ) {
              if (rcc > 0) {
                // do not read but reuse value, lower and upper bound
                value = *(stored_read_values + (number_of_reads - rcc));
                lo = fuzz_lo(value);
                up = fuzz_up(value);

                actually_read = bytes_to_read;
                rcc = rcc - 1;

                if (debug_read)
                  printf4((uint64_t*) "%s: storing %d, %d at read index %d\n", selfie_name, (uint64_t*) lo, (uint64_t*) up, (uint64_t*) rcc);
              } else {
                // save mrvc in buffer
                mrvc = load_physical_memory(buffer);

                // caution: read only overwrites bytes_to_read number of bytes
                // we therefore need to restore the actual value in buffer
                // to preserve the original read semantics
                if (number_of_reads > 0)
                  store_physical_memory(buffer, *(stored_read_values + (number_of_reads - 1)));
                else
                  store_physical_memory(buffer, 0);

                actually_read = sign_extend(read(fd, buffer, bytes_to_read), SYSCALL_BITWIDTH);

                // retrieve read value
                value = load_physical_memory(buffer);

                // fuzz read value
                lo = fuzz_lo(value);
                up = fuzz_up(value);

                // the witness needs the the previous read's last mrvc
                if (number_of_reads > 0)
                  *(stored_read_tcs + (number_of_reads - 1)) = mrvc;

                *(stored_read_tcs + number_of_reads)     = tc; //??
                *(stored_read_values + number_of_reads)  = value;
                number_of_reads = number_of_reads + 1;

                // restore mrvc in buffer
                store_physical_memory(buffer, mrvc);
                if (debug_read)
                  printf5((uint64_t*) "%s: storing %d, %d at read index %d and index %d\n", selfie_name, (uint64_t*) lo, (uint64_t*) up, (uint64_t*) number_of_reads, (uint64_t*) mrvc);
              }
            } else {
              value = SYM_EOF;
              lo    = SYM_EOF;
              up    = SYM_EOF;
              actually_read = 0;

              if (debug_read)
                printf3((uint64_t*) "%s: max number of reads reached, storing %d, %d\n", selfie_name, (uint64_t*) lo, (uint64_t*) up);
            }

            if (do_taint_flag) set_taint_memory(1, 0, 1);
            if (mrcc == 0)
              store_symbolic_memory(get_pt(context), 0, vbuffer, init_type(lo, up), lo, up, 1, -1,  0);
            else
              store_symbolic_memory(get_pt(context), 0, vbuffer, init_type(lo, up), lo, up, 1, -1, tc);

              if (debug_read)
                print_symbolic_memory(load_symbolic_memory(get_pt(context), vbuffer));

          } else {
            actually_read = 0;

            throw_exception(EXCEPTION_MAXTRACE, 0);
          }
        } else
          actually_read = sign_extend(read(fd, buffer, bytes_to_read), SYSCALL_BITWIDTH);

        if (actually_read == bytes_to_read) {
          read_total = read_total + actually_read;

          size = size - actually_read;

          if (size > 0)
            vbuffer = vbuffer + SIZEOFUINT64;
        } else {
          if (signed_less_than(0, actually_read))
            read_total = read_total + actually_read;

          size = 0;
        }
      } else {
        failed = 1;

        size = 0;

        if (debug_read)
          printf2((uint64_t*) "%s: reading into virtual address %p failed because the address is unmapped\n", selfie_name, (uint64_t*) vbuffer);
      }
    } else {
      failed = 1;

      size = 0;

      if (debug_read)
        printf2((uint64_t*) "%s: reading into virtual address %p failed because the address is invalid\n", selfie_name, (uint64_t*) vbuffer);
    }
  }

  if (failed == 0)
    *(get_regs(context) + REG_A0) = read_total;
  else
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);

  if (symbolic) {
    *(reg_typ + REG_A0)     = CONCRETE_T;
    *(registers + REG_A0)   = *(get_regs(context) + REG_A0);
    *(reg_alpha2 + REG_A0)  = *(get_regs(context) + REG_A0);
  }

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);

  if (debug_read)
    printf3((uint64_t*) "%s: actually read %d bytes from file with descriptor %d\n", selfie_name, (uint64_t*) read_total, (uint64_t*) fd);

  if (disassemble) {
    print((uint64_t*) " -> ");
    print_register_value(REG_A0);
    println();
  }
}

void emit_write() {
  create_symbol_table_entry(LIBRARY_TABLE, (uint64_t*) "write", 0, PROCEDURE, UINT64_T, 0, binary_length);

  emit_ld(REG_A2, REG_SP, 0); // size
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A1, REG_SP, 0); // *buffer
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A0, REG_SP, 0); // fd
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_addi(REG_A7, REG_ZR, SYSCALL_WRITE);

  emit_ecall();

  emit_jalr(REG_ZR, REG_RA, 0);
}

void implement_write(uint64_t* context) {
  // parameters
  uint64_t fd;
  uint64_t vbuffer;
  uint64_t size;

  // local variables
  uint64_t written_total;
  uint64_t bytes_to_write;
  uint64_t failed;
  uint64_t* buffer;
  uint64_t actually_written;

  if (disassemble) {
    print((uint64_t*) "(write): ");
    print_register_value(REG_A0);
    print((uint64_t*) ",");
    print_register_hexadecimal(REG_A1);
    print((uint64_t*) ",");
    print_register_value(REG_A2);
    print((uint64_t*) " |- ");
    print_register_value(REG_A0);
  }

  fd      = *(get_regs(context) + REG_A0);
  vbuffer = *(get_regs(context) + REG_A1);
  size    = *(get_regs(context) + REG_A2);

  if (debug_write)
    printf4((uint64_t*) "%s: trying to write %d bytes from buffer at virtual address %p into file with descriptor %d\n", selfie_name, (uint64_t*) size, (uint64_t*) vbuffer, (uint64_t*) fd);

  written_total = 0;
  bytes_to_write = SIZEOFUINT64;

  failed = 0;

  while (size > 0) {
    if (is_valid_virtual_address(vbuffer)) {
      if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
        buffer = tlb(get_pt(context), vbuffer);

        if (size < bytes_to_write)
          bytes_to_write = size;

        if (symbolic)
          // TODO: What should symbolically executed code output?
          // buffer points to a trace counter that refers to the actual value
          // actually_written = sign_extend(write(fd, values + load_physical_memory(buffer), bytes_to_write), SYSCALL_BITWIDTH);
          actually_written = bytes_to_write;
        else
          actually_written = sign_extend(write(fd, buffer, bytes_to_write), SYSCALL_BITWIDTH);

        if (actually_written == bytes_to_write) {
          written_total = written_total + actually_written;

          size = size - actually_written;

          if (size > 0)
            vbuffer = vbuffer + SIZEOFUINT64;
        } else {
          if (signed_less_than(0, actually_written))
            written_total = written_total + actually_written;

          size = 0;
        }
      } else {
        failed = 1;

        size = 0;

        if (debug_write)
          printf2((uint64_t*) "%s: writing into virtual address %p failed because the address is unmapped\n", selfie_name, (uint64_t*) vbuffer);
      }
    } else {
      failed = 1;

      size = 0;

      if (debug_write)
        printf2((uint64_t*) "%s: writing into virtual address %p failed because the address is invalid\n", selfie_name, (uint64_t*) vbuffer);
    }
  }

  if (failed == 0)
    *(get_regs(context) + REG_A0) = written_total;
  else
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);

  if (symbolic) {
    *(reg_typ + REG_A0)     = CONCRETE_T;
    *(registers + REG_A0)   = *(get_regs(context) + REG_A0);
    *(reg_alpha2 + REG_A0)  = *(get_regs(context) + REG_A0);
  }

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);

  if (debug_write)
    printf3((uint64_t*) "%s: actually wrote %d bytes into file with descriptor %d\n", selfie_name, (uint64_t*) written_total, (uint64_t*) fd);

  if (disassemble) {
    print((uint64_t*) " -> ");
    print_register_value(REG_A0);
    println();
  }
}

void emit_open() {
  create_symbol_table_entry(LIBRARY_TABLE, (uint64_t*) "open", 0, PROCEDURE, UINT64_T, 0, binary_length);

  emit_ld(REG_A2, REG_SP, 0); // mode
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A1, REG_SP, 0); // flags
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A0, REG_SP, 0); // filename
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_addi(REG_A7, REG_ZR, SYSCALL_OPEN);

  emit_ecall();

  emit_jalr(REG_ZR, REG_RA, 0);
}

uint64_t down_load_string(uint64_t* table, uint64_t vaddr, uint64_t* s) {
  uint64_t mrvc;
  uint64_t i;
  uint64_t j;

  i = 0;

  while (i < MAX_FILENAME_LENGTH / SIZEOFUINT64) {
    if (is_valid_virtual_address(vaddr)) {
      if (is_virtual_address_mapped(table, vaddr)) {
        if (symbolic) {
          mrvc = load_symbolic_memory(table, vaddr);

          *(s + i) = get_trace_a1(mrvc);

          if (is_symbolic_value(get_trace_type(mrvc))) {
            printf1((uint64_t*) "%s: detected symbolic value ", selfie_name);
            print_symbolic_memory(mrvc);
            print((uint64_t*) " in filename of open call\n");

            exit(EXITCODE_SYMBOLICEXECUTIONERROR);
          }
        } else
          *(s + i) = load_virtual_memory(table, vaddr);

        j = 0;

        // check if string ends in the current machine word
        while (j < SIZEOFUINT64) {
          if (load_character(s + i, j) == 0)
            return 1;

          j = j + 1;
        }

        // advance to the next machine word in virtual memory
        vaddr = vaddr + SIZEOFUINT64;

        // advance to the next machine word in our memory
        i = i + 1;
      } else if (debug_open)
        printf2((uint64_t*) "%s: opening file with name at virtual address %p failed because the address is unmapped\n", selfie_name, (uint64_t*) vaddr);
    } else if (debug_open)
      printf2((uint64_t*) "%s: opening file with name at virtual address %p failed because the address is invalid\n", selfie_name, (uint64_t*) vaddr);
  }

  return 0;
}

void implement_open(uint64_t* context) {
  // parameters
  uint64_t vfilename;
  uint64_t flags;
  uint64_t mode;

  // return value
  uint64_t fd;

  if (disassemble) {
    print((uint64_t*) "(open): ");
    print_register_hexadecimal(REG_A0);
    print((uint64_t*) ",");
    print_register_hexadecimal(REG_A1);
    print((uint64_t*) ",");
    print_register_octal(REG_A2);
    print((uint64_t*) " |- ");
    print_register_value(REG_A0);
  }

  vfilename = *(get_regs(context) + REG_A0);
  flags     = *(get_regs(context) + REG_A1);
  mode      = *(get_regs(context) + REG_A2);

  if (down_load_string(get_pt(context), vfilename, filename_buffer)) {
    fd = sign_extend(open(filename_buffer, flags, mode), SYSCALL_BITWIDTH);

    *(get_regs(context) + REG_A0) = fd;

    if (debug_open)
      printf5((uint64_t*) "%s: opened file %s with flags %x and mode %o returning file descriptor %d\n", selfie_name, filename_buffer, (uint64_t*) flags, (uint64_t*) mode, (uint64_t*) fd);
  } else {
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);

    if (debug_open)
      printf2((uint64_t*) "%s: opening file with name at virtual address %p failed because the name is too long\n", selfie_name, (uint64_t*) vfilename);
  }

  if (symbolic) {
    *(reg_typ + REG_A0)     = CONCRETE_T;
    *(reg_alpha2 + REG_A0)  = *(get_regs(context) + REG_A0);
  }

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);

  if (disassemble) {
    print((uint64_t*) " -> ");
    print_register_value(REG_A0);
    println();
  }
}

void emit_malloc() {
  uint64_t* entry;

  create_symbol_table_entry(LIBRARY_TABLE, (uint64_t*) "malloc", 0, PROCEDURE, UINT64STAR_T, 0, binary_length);

  // on boot levels higher than zero, zalloc falls back to malloc
  // assuming that page frames are zeroed on boot level zero
  create_symbol_table_entry(LIBRARY_TABLE, (uint64_t*) "zalloc", 0, PROCEDURE, UINT64STAR_T, 0, binary_length);

  // allocate memory in data segment for recording state of
  // malloc (bump pointer) in compiler-declared global variable
  allocated_memory = allocated_memory + REGISTERSIZE;

  // define global variable _bump for storing malloc's bump pointer
  // copy "_bump" string into zeroed double word to obtain unique hash
  create_symbol_table_entry(GLOBAL_TABLE, string_copy((uint64_t*) "_bump"), 1, VARIABLE, UINT64_T, 0, -allocated_memory);

  // do not account for _bump as global variable
  number_of_global_variables = number_of_global_variables - 1;

  entry = search_global_symbol_table(string_copy((uint64_t*) "_bump"), VARIABLE);

  // allocate register for size parameter
  talloc();

  emit_ld(current_temporary(), REG_SP, 0); // size
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  // round up size to double-word alignment
  emit_round_up(current_temporary(), SIZEOFUINT64);

  // allocate register to compute new bump pointer
  talloc();

  // get current _bump which will be returned upon success
  emit_ld(current_temporary(), get_scope(entry), get_address(entry));

  // call brk syscall to set new program break to _bump + size
  emit_add(REG_A0, current_temporary(), previous_temporary());
  emit_addi(REG_A7, REG_ZR, SYSCALL_BRK);
  emit_ecall();

  // return 0 if memory allocation failed, that is,
  // if new program break is still _bump and size !=0
  emit_beq(REG_A0, current_temporary(), 2 * INSTRUCTIONSIZE);
  emit_beq(REG_ZR, REG_ZR, 4 * INSTRUCTIONSIZE);
  emit_beq(REG_ZR, previous_temporary(), 3 * INSTRUCTIONSIZE);
  emit_addi(REG_A0, REG_ZR, 0);
  emit_beq(REG_ZR, REG_ZR, 3 * INSTRUCTIONSIZE);

  // if memory was successfully allocated
  // set _bump to new program break
  // and then return original _bump
  emit_sd(get_scope(entry), get_address(entry), REG_A0);
  emit_addi(REG_A0, current_temporary(), 0);

  tfree(2);

  emit_jalr(REG_ZR, REG_RA,0);
}

void implement_brk(uint64_t* context) {
  // parameter
  uint64_t program_break;

  // local variables
  uint64_t previous_program_break;
  uint64_t valid;
  uint64_t size;

  if (disassemble) {
    print((uint64_t*) "(brk): ");
    print_register_hexadecimal(REG_A0);
  }

  program_break = *(get_regs(context) + REG_A0);

  previous_program_break = get_program_break(context);

  valid = 0;

  if (program_break >= previous_program_break)
    if (program_break < *(get_regs(context) + REG_SP))
      if (program_break % SIZEOFUINT64 == 0)
        valid = 1;

  if (valid) {
    if (disassemble)
      print((uint64_t*) " |- ->\n");

    if (debug_brk)
      printf2((uint64_t*) "%s: setting program break to %p\n", selfie_name, (uint64_t*) program_break);

    set_program_break(context, program_break);

    if (symbolic) {
      size = program_break - previous_program_break;

      // interval is memory range, not symbolic value
      *(reg_typ + REG_A0) = ARRAY_T;
      // remember start and size of memory block for checking memory safety
      *(reg_alpha2 + REG_A0)  = previous_program_break;
      *(reg_alpha3 + REG_A0)  = size;

      if (mrcc > 0) {
        if (is_trace_space_available()) {
          set_taint_memory(0, 0, 1);
          // since there has been branching record malloc using vaddr == 0
          store_symbolic_memory(get_pt(context), 0, 0, ARRAY_T, previous_program_break, previous_program_break, size, -1, tc);
        }
        else {
          throw_exception(EXCEPTION_MAXTRACE, 0);
          return;
        }
      }
    }
  } else {
    // error returns current program break
    program_break = previous_program_break;

    if (debug_brk)
      printf2((uint64_t*) "%s: retrieving current program break %p\n", selfie_name, (uint64_t*) program_break);

    if (disassemble) {
      print((uint64_t*) " |- ");
      print_register_hexadecimal(REG_A0);
    }

    *(get_regs(context) + REG_A0) = program_break;

    if (disassemble) {
      print((uint64_t*) " -> ");
      print_register_hexadecimal(REG_A0);
      println();
    }

    if (symbolic) {
      *(reg_typ + REG_A0) = CONCRETE_T;
      *(reg_alpha2 + REG_A0) = program_break;
      *(reg_alpha3 + REG_A0) = 1;
    }
  }

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}


// -----------------------------------------------------------------
// ----------------------- HYPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emit_switch() {
  create_symbol_table_entry(LIBRARY_TABLE, (uint64_t*) "hypster_switch", 0, PROCEDURE, UINT64STAR_T, 0, binary_length);

  emit_ld(REG_A1, REG_SP, 0); // number of instructions to execute
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A0, REG_SP, 0); // context to which we switch
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_addi(REG_A7, REG_ZR, SYSCALL_SWITCH);

  emit_ecall();

  // save context from which we are switching here in return register
  emit_addi(REG_A0, REG_A1, 0);

  emit_jalr(REG_ZR, REG_RA, 0);
}

void do_switch(uint64_t* to_context, uint64_t timeout) {
  uint64_t* from_context;

  from_context = current_context;

  restore_context(to_context);

  // restore machine state
  pc        = get_pc(to_context);
  registers = get_regs(to_context);
  pt        = get_pt(to_context);

  // use REG_A1 instead of REG_A0 to avoid race condition with interrupt
  if (get_parent(from_context) != MY_CONTEXT)
    *(registers + REG_A1) = (uint64_t) get_virtual_context(from_context);
  else
    *(registers + REG_A1) = (uint64_t) from_context;

  current_context = to_context;

  timer = timeout;

  if (debug_switch) {
    printf3((uint64_t*) "%s: switched from context %p to context %p", selfie_name, from_context, to_context);
    if (timer != TIMEROFF)
      printf1((uint64_t*) " to execute %d instructions", (uint64_t*) timer);
    println();
  }
}

void implement_switch() {
  if (disassemble) {
    print((uint64_t*) "(switch): ");
    print_register_hexadecimal(REG_A0);
    print((uint64_t*) ",");
    print_register_value(REG_A1);
    print((uint64_t*) " |- ");
    print_register_value(REG_A1);
  }

  save_context(current_context);

  // cache context on my boot level before switching
  do_switch(cache_context((uint64_t*) *(registers + REG_A0)), *(registers + REG_A1));

  if (disassemble) {
    print((uint64_t*) " -> ");
    print_register_hexadecimal(REG_A1);
    println();
  }
}

uint64_t* mipster_switch(uint64_t* to_context, uint64_t timeout) {
  do_switch(to_context, timeout);

  run_until_exception();

  save_context(current_context);

  return current_context;
}

uint64_t* hypster_switch(uint64_t* to_context, uint64_t timeout) {
  // this procedure is only executed at boot level zero
  return mipster_switch(to_context, timeout);
}

void emit_input() {
  create_symbol_table_entry(LIBRARY_TABLE, (uint64_t*) "input", 0, PROCEDURE, UINT64_T, 0, binary_length);

  emit_ld(REG_A2, REG_SP, 0); // step
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A1, REG_SP, 0); // end
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A0, REG_SP, 0); // start
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_addi(REG_A7, REG_ZR, SYSCALL_INPUT);

  emit_ecall();

  emit_jalr(REG_ZR, REG_RA, 0);
}

// set [start, end, step] in return reg
void implement_input(uint64_t* context) {
  uint64_t start;
  uint64_t end;
  uint64_t step;

  start   = *(get_regs(context) + REG_A0);
  end     = *(get_regs(context) + REG_A1);
  step    = *(get_regs(context) + REG_A2);

  if (symbolic) {

    *(reg_typ + REG_A0)     = MSIID_T;
    *(registers + REG_A0)   = start;
    *(reg_alpha2 + REG_A0)  = end;
    *(reg_alpha3 + REG_A0)  = step;

    set_pc(context, get_pc(context) + INSTRUCTIONSIZE);

  } else {
    print(selfie_name);
    print((uint64_t*) ": input syscall during concrete execution ");
    println();
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

uint64_t load_physical_memory(uint64_t* paddr) {
  return *paddr;
}

void store_physical_memory(uint64_t* paddr, uint64_t data) {
  *paddr = data;
}

uint64_t frame_for_page(uint64_t* table, uint64_t page) {
  return (uint64_t) (table + page);
}

uint64_t get_frame_for_page(uint64_t* table, uint64_t page) {
  return *(table + page);
}

uint64_t is_page_mapped(uint64_t* table, uint64_t page) {
  if (get_frame_for_page(table, page) != 0)
    return 1;
  else
    return 0;
}

uint64_t is_valid_virtual_address(uint64_t vaddr) {
  if (vaddr < VIRTUALMEMORYSIZE)
    // memory must be word-addressed for lack of byte-sized data type
    if (vaddr % REGISTERSIZE == 0)
      return 1;

  return 0;
}

uint64_t get_page_of_virtual_address(uint64_t vaddr) {
  return vaddr / PAGESIZE;
}

uint64_t is_virtual_address_mapped(uint64_t* table, uint64_t vaddr) {
  // assert: is_valid_virtual_address(vaddr) == 1

  return is_page_mapped(table, get_page_of_virtual_address(vaddr));
}

uint64_t* tlb(uint64_t* table, uint64_t vaddr) {
  uint64_t page;
  uint64_t frame;
  uint64_t paddr;

  // assert: is_valid_virtual_address(vaddr) == 1
  // assert: is_virtual_address_mapped(table, vaddr) == 1

  page = get_page_of_virtual_address(vaddr);

  frame = get_frame_for_page(table, page);

  // map virtual address to physical address
  paddr = vaddr - page * PAGESIZE + frame;

  if (debug_tlb)
    printf5((uint64_t*) "%s: tlb access:\n vaddr: %p\n page:  %p\n frame: %p\n paddr: %p\n", selfie_name, (uint64_t*) vaddr, (uint64_t*) (page * PAGESIZE), (uint64_t*) frame, (uint64_t*) paddr);

  return (uint64_t*) paddr;
}

uint64_t load_virtual_memory(uint64_t* table, uint64_t vaddr) {
  // assert: is_valid_virtual_address(vaddr) == 1
  // assert: is_virtual_address_mapped(table, vaddr) == 1

  return load_physical_memory(tlb(table, vaddr));
}

void store_virtual_memory(uint64_t* table, uint64_t vaddr, uint64_t data) {
  // assert: is_valid_virtual_address(vaddr) == 1
  // assert: is_virtual_address_mapped(table, vaddr) == 1

  store_physical_memory(tlb(table, vaddr), data);
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

void print_code_line_number_for_instruction(uint64_t a) {
  if (code_line_number != (uint64_t*) 0)
    printf1((uint64_t*) "(~%d)", (uint64_t*) *(code_line_number + a / INSTRUCTIONSIZE));
}

void print_code_context_for_instruction(uint64_t a) {
  if (execute) {
    printf2((uint64_t*) "%s: $pc=%x", binary_name, (uint64_t*) a);
    print_code_line_number_for_instruction(a - entry_point);
  } else {
    printf1((uint64_t*) "%x", (uint64_t*) a);
    if (disassemble_verbose) {
      print_code_line_number_for_instruction(a);
      printf1((uint64_t*) ": %p", (uint64_t*) ir);
    }
  }
  print((uint64_t*) ": ");
}

void print_lui() {
  print_code_context_for_instruction(pc);
  printf2((uint64_t*) "lui %s,%x", get_register_name(rd), (uint64_t*) sign_shrink(imm, 20));
}

void print_lui_before() {
  print((uint64_t*) ": |- ");
  print_register_hexadecimal(rd);
}

void print_lui_after() {
  print((uint64_t*) " -> ");
  print_register_hexadecimal(rd);
}

void do_lui() {
  // load upper immediate

  if (rd != REG_ZR)
    // semantics of lui
    *(registers + rd) = left_shift(imm, 12);

  pc = pc + INSTRUCTIONSIZE;

  ic_lui = ic_lui + 1;
}

uint64_t flag_round(uint64_t reg_from, uint64_t lower_flag) {
  if (*(reg_expr + reg_from) < lower_flag)
    return lower_flag;
  return *(reg_expr + reg_from);
}

void print_bad_expression() {
  printf2((uint64_t*) "%s: : detected bad expression at %x", selfie_name, (uint64_t*) pc);
  print_code_line_number_for_instruction(pc - entry_point);
  println();
}

void constrain_lui() {
  if (rd != REG_ZR) {

    if (do_taint_flag) {
      *(reg_is_tainted + rd) = 0;
      *(reg_is_minuend + rd) = 0;
      *(reg_has_step + rd)   = 1;
    }

    // interval semantics of lui
    // *(registers + rd) = left_shift(imm, 12);
    // *(reg_alpha2 + rd) = left_shift(imm, 12);

    // rd has no constraint
    *(reg_typ + rd) = CONCRETE_T;
    set_correction(rd, 0, 0, 0, 0, 0);
    set_constraint(rd, 0, 0, left_shift(imm, 12), left_shift(imm, 12), 1);
  }

  pc = pc + INSTRUCTIONSIZE;
  ic_lui = ic_lui + 1;
}

void print_addi() {
  print_code_context_for_instruction(pc);

  if (rd == REG_ZR)
    if (rs1 == REG_ZR)
      if (imm == 0) {
        print((uint64_t*) "nop");

        return;
      }

  printf3((uint64_t*) "addi %s,%s,%d", get_register_name(rd), get_register_name(rs1), (uint64_t*) imm);
}

void print_addi_before() {
  print((uint64_t*) ": ");
  print_register_value(rs1);
  print((uint64_t*) " |- ");
  print_register_value(rd);
}

void print_addi_add_sub_mul_divu_remu_sltu_after() {
  print((uint64_t*) " -> ");
  print_register_value(rd);
}

void do_addi() {
  // add immediate

  if (rd != REG_ZR)
    // semantics of addi
    *(registers + rd) = *(registers + rs1) + imm;

  pc = pc + INSTRUCTIONSIZE;

  ic_addi = ic_addi + 1;
}

uint64_t is_from_return(uint64_t reg) {
  if (*(reg_stc + reg))
    return reg == REG_A0;
  return 0;
}

void addi_pointer(uint64_t src, uint64_t vaddr) {
  // rd has no constraint if rs1 is memory range
  *(reg_typ + rd) = *(reg_typ + rs1);
  set_correction(rd, 0, 0, 0, 0, 0);
  set_constraint(rd, src, vaddr, *(registers + rs1) + imm, *(reg_alpha2 + rs1), *(reg_alpha3 + rs1));
}

void addi_msiid(uint64_t src, uint64_t vaddr) {
  // rs1 constraint has already minuend and cannot have another addend
  if (*(reg_hasmn + rs1)) error_minuend((uint64_t*) "left",(uint64_t*) "addi");

  *(reg_typ + rd) = *(reg_typ + rs1);
  // rd inherits rs1 constraint
  set_correction(rd, 0, flag_round(rs1, SUM_T), *(reg_colos + rs1) + imm, *(reg_coups + rs1) + imm, *(reg_factor + rs1));

  // interval semantics of addi
  // *(registers + rd) = *(registers + rs1) + imm;
  // *(reg_alpha2 + rd) = *(reg_alpha2 + rs1) + imm;

  set_constraint(rd, src, vaddr, *(registers + rs1) + imm, *(reg_alpha2 + rs1) + imm, *(reg_alpha3 + rs1));
}

void constrain_addi() {
  uint64_t src;
  uint64_t vaddr;

  if (rd != REG_ZR) {
    if (do_taint_flag) taint_unop();

    // context-sensitivity
    if (is_from_return(rs1)) {
        //reduce the src depence list
        if (*(reg_stc + rs1)) {
          vaddr = get_trace_vaddr(*(reg_stc + rs1));
          src   = get_trace_src(*(reg_stc + rs1));
        } else {
          vaddr = *(reg_vaddr + rs1);
          src   = *(reg_stc + rs1);
        }
    } else {
        vaddr = *(reg_vaddr + rs1);
        src   = *(reg_stc + rs1);
    }

    if (*(reg_typ + rs1) == ARRAY_T)
      addi_pointer(src, vaddr);
    else if (*(reg_typ + rs1) == MSIID_T)
      addi_msiid(src, vaddr);
    else { //concrete
      // rd has no constraint if rs1 has none
      *(reg_typ + rd) = CONCRETE_T;
      set_correction(rd, 0, 0, 0, 0, 0);
      set_constraint(rd, *(reg_stc + rs1), *(reg_vaddr + rs1), *(registers + rs1) + imm, *(reg_alpha2 + rs1) + imm, 1);
    }
  }

  pc = pc + INSTRUCTIONSIZE;
  ic_addi = ic_addi + 1;
}

void print_add_sub_mul_divu_remu_sltu(uint64_t *mnemonics) {
  print_code_context_for_instruction(pc);
  printf4((uint64_t*) "%s %s,%s,%s", mnemonics, get_register_name(rd), get_register_name(rs1), get_register_name(rs2));
}

void print_add_sub_mul_divu_remu_sltu_before() {
  print((uint64_t*) ": ");
  print_register_value(rs1);
  print((uint64_t*) ",");
  print_register_value(rs2);
  print((uint64_t*) " |- ");
  print_register_value(rd);
}

void do_add() {
  if (rd != REG_ZR)
    // semantics of add
    *(registers + rd) = *(registers + rs1) + *(registers + rs2);

  pc = pc + INSTRUCTIONSIZE;

  ic_add = ic_add + 1;
}

void pointer_error() {
  // adding two pointers is undefined
  printf2((uint64_t*) "%s: undefined addition of two pointers at %x", selfie_name, (uint64_t*) pc);
  print_code_line_number_for_instruction(pc - entry_point);
  println();

  exit(EXITCODE_SYMBOLICEXECUTIONERROR);
}

uint64_t which_type(uint64_t reg1, uint64_t reg2) {
  if (*(reg_typ + reg1)) return *(reg_typ + reg1);
  return *(reg_typ + reg2);
}

void check_add_sub_step(uint64_t reg_min, uint64_t reg_max, uint64_t gcd_step) {
  uint64_t i_max;
  if (*(reg_alpha3 + reg_min) == gcd_step) {
    i_max = (*(reg_alpha2 + reg_min) - *(registers + reg_min)) / *(reg_alpha3 + reg_min);

    if (i_max < *(reg_alpha3 + reg_max) / gcd_step - 1) {
      //now: exit analysis (two "incompatible" symbolic values addition [max bound too small])
      print_over_approx((uint64_t*) "add");
      throw_exception(EXCEPTION_INCOMPLETENESS, 0);
    }
  } else {
    //now: exit analysis (two "incompatible" symbolic values addition [no multiple step])
    print_over_approx((uint64_t*) "add");
    throw_exception(EXCEPTION_INCOMPLETENESS, 0);
  }
}

void error_minuend(uint64_t* operand, uint64_t* operation) {
  printf4((uint64_t*) "%s: detected invalid minuend expression in %s operand of %s at %x", selfie_name, operand, operation, (uint64_t*) pc);
  print_code_line_number_for_instruction(pc - entry_point);
  println();

  throw_exception(EXCEPTION_INCOMPLETENESS, 0);
  //exit(EXITCODE_SYMBOLICEXECUTIONERROR);
}

void add_pointer() {
  if (*(reg_typ + rs1)) {
    if (*(reg_typ + rs2))
      pointer_error();

    *(reg_typ + rd) = ARRAY_T;
    set_correction(rd, 0, 0, 0, 0, 0);
    set_constraint(rd, 0, 0, *(registers + rs1) + *(registers + rs2), *(reg_alpha2 + rs1), *(reg_alpha3 + rs1));
  } else {
    *(reg_typ + rd) = ARRAY_T;
    set_correction(rd, 0, 0, 0, 0, 0);
    set_constraint(rd, 0, 0, *(registers + rs1) + *(registers + rs2), *(reg_alpha2 + rs2), *(reg_alpha3 + rs2));
  }
}

void add_msiid() {
  uint64_t add_los;
  uint64_t add_ups;
  uint64_t add_steps;

  //integer abstract domain
  //domain-overflow?
    if (add_sub_condition(*(registers + rs1), *(reg_alpha2 + rs1), *(registers + rs2), *(reg_alpha2 + rs2))) {
      add_los = *(registers + rs1) + *(registers + rs2);
      add_ups = *(reg_alpha2 + rs1) + *(reg_alpha2 + rs2);
    } else {
      //now: exit analysis (result too big for the abstract domain)

      //add_los = 0;
      //add_ups = UINT64_MAX;
      //*(reg_alpha3 + rd) = 1;
      print_over_approx((uint64_t*) "add");
      throw_exception(EXCEPTION_INCOMPLETENESS, 0);
      return;
    }

    //typ is MSIID_T or 0 (concrete)
    //interval add semantics
    if (*(reg_typ + rs1)) {
      if (*(reg_typ + rs2)) {

        // s + s
        add_steps = gcd(*(reg_alpha3 + rs1), *(reg_alpha3 + rs2));
        if (*(reg_alpha3 + rs1) < *(reg_alpha3 + rs2))
          check_add_sub_step(rs1, rs2, add_steps);
        else if (*(reg_alpha3 + rs1) > *(reg_alpha3 + rs2))
          check_add_sub_step(rs2, rs1, add_steps);

        // we cannot keep track of more than one constraint for add but
        // need to warn about their earlier presence if used in comparisons
        if (*(reg_expr + rs1) > 1) {
          //now: expression not managed -> fail
          print_bad_expression();
          throw_exception(EXCEPTION_INCOMPLETENESS, 0);
          //setMeta(rd, *(reg_typ + rs1), 0, fail_t); //TODO: minuend? / iscorrect rs2?
        } else
          *(reg_typ + rd) = *(reg_typ + rs1); //TODO: minuend? / iscorrect rs2?

        set_correction(rd, 0, SUM_T, 0, 0, *(reg_factor + rs1)); //TODO: manage witness
        set_constraint(rd, 0, 0, add_los, add_ups, add_steps);
      } else if (*(reg_hasmn + rs1))
          // rs1 constraint has already minuend and cannot have another addend
          error_minuend((uint64_t*) "left", (uint64_t*) "add");
        else {
          // rd inherits rs1 constraint since rs2 has none
          // s + c
          if (*(reg_expr + rs1) > 1) {
            //now: expression not managed -> fail
            print_bad_expression();
            throw_exception(EXCEPTION_INCOMPLETENESS, 0);
          }
          else
            *(reg_typ + rd) = *(reg_typ + rs1);

        set_correction(rd, 0, SUM_T, *(reg_colos + rs1) + *(registers + rs2), *(reg_coups + rs1) + *(reg_alpha2 + rs2), *(reg_factor + rs1));
        set_constraint(rd, *(reg_stc + rs1), *(reg_vaddr + rs1), add_los, add_ups, *(reg_alpha3 + rs1)); //interval add semantics
      }
  } else if (*(reg_typ + rs2)) {
    if (*(reg_hasmn + rs2))
      // rs2 constraint has already minuend and cannot have another addend
      error_minuend((uint64_t*) "right", (uint64_t*) "add");
    else {
      // rd inherits rs2 constraint since rs1 has none
      // c + s
      *(reg_typ + rd) = *(reg_typ + rs2);
      set_correction(rd, 0, flag_round(rs2, SUM_T), *(registers + rs1) + *(reg_colos + rs2), *(reg_alpha2 + rs1) + *(reg_coups + rs2), *(reg_factor + rs2));
      set_constraint(rd, *(reg_stc + rs2), *(reg_vaddr + rs2), add_los, add_ups, *(reg_alpha3 + rs2)); //interval add semantics
    }
  }
}

void constrain_add() {
  uint64_t stype;

  if (rd == REG_ZR)
    return;

  if (do_taint_flag) taint_binop(ADD);
  stype = which_type(rs1, rs2);

  //pointer abstract domain
  if (stype == ARRAY_T)
    add_pointer();
  else if (stype == MSIID_T)
    add_msiid();
  // if (stype == incomplete_t) { --> next step
  //   print_bad_expression();
  //   throw_exception(EXCEPTION_INCOMPLETENESS, 0);
  //   return;
  // }
  else {
    // rd has no constraint if both rs1 and rs2 have no constraints
    // c + c
    *(reg_typ + rd) = CONCRETE_T;
    set_correction(rd, 0, 0, 0, 0, 0);
    set_constraint(rd, 0, 0, *(registers + rs1) + *(registers + rs2), *(reg_alpha2 + rs1) + *(reg_alpha2 + rs2), 1);
  }

  pc = pc + INSTRUCTIONSIZE;
  ic_add = ic_add + 1;
}

void do_sub() {
  if (rd != REG_ZR)
    // semantics of sub
    *(registers + rd) = *(registers + rs1) - *(registers + rs2);

  pc = pc + INSTRUCTIONSIZE;

  ic_sub = ic_sub + 1;
}

void sub_2pointer() {
  if (*(reg_alpha2 + rs1) == *(reg_alpha2 + rs2))
    if (*(reg_alpha3 + rs1) == *(reg_alpha3 + rs2)) {
      return; //ok
    }
  // subtracting incompatible pointers
  throw_exception(EXCEPTION_INVALIDADDRESS, 0);
}

void sub_pointer() {
  uint64_t rd_val;
  rd_val = *(registers + rs1) - *(registers + rs2);

  if (*(reg_typ + rs1)) {
    if (*(reg_typ + rs2)) {
      sub_2pointer();
      // rd has no constraint if rs1 and rs2 are memory range
      *(reg_typ + rd) = CONCRETE_T;
      set_correction(rd, 0, 0, 0, 0, 0);
      set_constraint(rd, 0, 0, rd_val, rd_val, 1);
    } else {
    *(reg_typ + rd) = ARRAY_T;
    set_correction(rd, 0, 0, 0, 0, 0);
    set_constraint(rd, 0, 0, rd_val, *(reg_alpha2 + rs1), *(reg_alpha3 + rs1));
    }
  } else {
    *(reg_typ + rd) = ARRAY_T;
    set_correction(rd, 0, 0, 0, 0, 0);
    set_constraint(rd, 0, 0, rd_val, *(reg_alpha2 + rs2), *(reg_alpha3 + rs2));
  }
}

void sub_msiid() {
  uint64_t sub_los;
  uint64_t sub_ups;
  uint64_t sub_steps;

  //integer abstract domain
  //domain-overflow?
  if (add_sub_condition(*(registers + rs1), *(reg_alpha2 + rs1), *(registers + rs2), *(reg_alpha2 + rs2))) {
    sub_los = *(registers + rs1) - *(reg_alpha2 + rs2);
    sub_ups = *(reg_alpha2 + rs1) - *(registers + rs2);
  } else {
    //now: exit analysis (result too big for the abstract domain)

    //add_los = 0;
    //add_ups = UINT64_MAX;
    //*(reg_alpha3 + rd) = 1;
    print_over_approx((uint64_t*) "sub");
    throw_exception(EXCEPTION_INCOMPLETENESS, 0);
    return;
  }

  //typ is MSIID_T or 0 (concrete)
  //interval sub semantics
  if (*(reg_typ + rs1)) {
    if (*(reg_typ + rs2)) {

      // s - s
      sub_steps = gcd(*(reg_alpha3 + rs1), *(reg_alpha3 + rs2));
      if (*(reg_alpha3 + rs1) < *(reg_alpha3 + rs2))
          check_add_sub_step(rs1, rs2, sub_steps);
      else if (*(reg_alpha3 + rs1) > *(reg_alpha3 + rs2))
          check_add_sub_step(rs2, rs1, sub_steps);

    // we cannot keep track of more than one constraint for sub but
    // need to warn about their earlier presence if used in comparisons
    if (*(reg_expr + rs1) > 1) {
      //now: expression not managed -> fail
      print_bad_expression();
      throw_exception(EXCEPTION_INCOMPLETENESS, 0);
      //setMeta(rd, *(reg_typ + rs1), 0, fail_t); //TODO: minuend? / iscorrect rs2?
    } else
      *(reg_typ + rd) =  *(reg_typ + rs1);

    set_correction(rd, 0, SUM_T, 0, 0, *(reg_factor + rs1)); //TODO: manage witness
    set_constraint(rd, 0, 0, sub_los, sub_ups, sub_steps);
    } else if (*(reg_hasmn + rs1))
        // rs1 constraint has already minuend and cannot have another addend
            error_minuend((uint64_t*) "left", (uint64_t*) "sub");
          else {
            // rd inherits rs1 constraint since rs2 has none
            // s - c
            if (*(reg_expr + rs1) > 1) {
              //now: expression not managed -> fail
              print_bad_expression();
              throw_exception(EXCEPTION_INCOMPLETENESS, 0);
            } else
              *(reg_typ + rd) = *(reg_typ + rs1);

            set_correction(rd, 0, SUM_T, *(reg_colos + rs1) - *(reg_alpha2 + rs2), *(reg_coups + rs1) - *(registers + rs2), *(reg_factor + rs1));
            set_constraint(rd, *(reg_stc + rs1), *(reg_vaddr + rs1), sub_los, sub_ups, *(reg_alpha3 + rs1)); //interval sub semantics
          }
  } else if (*(reg_typ + rs2)) {
    if (*(reg_hasmn + rs2))
      // rs2 constraint has already minuend and cannot have another addend
      error_minuend((uint64_t*) "right", (uint64_t*) "sub");
    else {
      // rd inherits rs2 constraint since rs1 has none
      // c - s
      *(reg_typ + rd) = *(reg_typ + rs2);
      set_correction(rd, 1, flag_round(rs2, SUM_T), *(registers + rs1) - *(reg_coups + rs2), *(reg_alpha2 + rs1) - *(reg_colos + rs2), *(reg_factor + rs2));
      set_constraint(rd, *(reg_stc + rs2), *(reg_vaddr + rs2), sub_los, sub_ups, *(reg_alpha3 + rs2)); //interval sub semantics
    }
  }
}

void constrain_sub() {
  uint64_t stype;

  if (rd == REG_ZR)
    return;

  if (do_taint_flag) taint_binop(SUB);
  stype = which_type(rs1, rs2);

  //pointer abstract domain
  if (stype == ARRAY_T)
    sub_pointer();
  else if (stype == MSIID_T)
    sub_msiid();
  // if (stype == incomplete_t) {
  //   print_bad_expression();
  //   throw_exception(EXCEPTION_INCOMPLETENESS, 0);
  //   return;
  // }
  else {
    // rd has no constraint if both rs1 and rs2 have no constraints
    // c - c
    *(reg_typ + rd) = CONCRETE_T;
    set_correction(rd, 0, 0, 0, 0, 0);
    set_constraint(rd, 0, 0, *(registers + rs1) - *(reg_alpha2 + rs2), *(reg_alpha2 + rs1) - *(registers + rs2), 1);
  }

  pc = pc + INSTRUCTIONSIZE;
  ic_sub = ic_sub + 1;
}

void do_mul() {
  if (rd != REG_ZR)
    // semantics of mul
    *(registers + rd) = *(registers + rs1) * *(registers + rs2);

  // TODO: 128-bit resolution currently not supported

  pc = pc + INSTRUCTIONSIZE;

  ic_mul = ic_mul + 1;
}

uint64_t check_mul_condition(uint64_t reg_int, uint64_t reg_k) {
  if (mul_condition(*(registers + reg_int), *(reg_alpha2 + reg_int), *(registers + reg_k))) {
    //now: exit analysis (result too big for the abstract domain)

    // TODO: improve
    //*(reg_alpha3 + rd) = 1;
    //*(registers + rd)   = 0;
    //*(reg_alpha2 + rd)   = UINT64_MAX;

    //TODO: raise the overflow if the incomplete part interval is used
    //print_over_approx((uint64_t*) "mul");
    //throw_exception(EXCEPTION_INCOMPLETENESS, 0);
    return 0;
  } else {
    if (*(reg_alpha3 + reg_int) * *(registers + reg_k) < *(reg_alpha3 + reg_int)) {
      if (*(registers + reg_k) != 0) {
        //now: exit analysis (step overflow)

        // TODO: improve
        //*(reg_alpha3 + rd) = 1;
        //*(registers + rd)   = 0;
        //*(reg_alpha2 + rd)   = UINT64_MAX;
        print_over_approx((uint64_t*) "step mul");
        throw_exception(EXCEPTION_INCOMPLETENESS, 0);
        return 0;
      }
    }
  }
  return 1;
}

uint64_t can_mul_correction(uint64_t exp) {
  if (exp == CONST_T) return 1;
  if (exp == MUL_T)   return 1; // allow sequence of mul
  return 0;
}


void mul_msiid() {
  uint64_t mul_los;
  uint64_t mul_ups;

  mul_los = *(registers + rs1) * *(registers + rs2);
  mul_ups = *(reg_alpha2 + rs1) * *(reg_alpha2 + rs2);

  //interval mul semantics
  if (*(reg_typ + rs1)) {
    if (*(reg_typ + rs2)) {
      // s * s
      // non-linear expressions are not supported
      printf2((uint64_t*) "%s: detected non-linear expression in mul at %x", selfie_name, (uint64_t*) pc);
      print_code_line_number_for_instruction(pc - entry_point);
      println();

      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    } else if (*(reg_hasmn + rs1))
        // rs1 constraint has already minuend and cannot have another addend
        error_minuend((uint64_t*) "left", (uint64_t*) "mul");
      else {
        // rd inherits rs1 constraint since rs2 has none
        // assert: rs2 interval is singleton
        // s * c

        if (check_mul_condition(rs1, rs2) == 0) {
          // next step
          // it is a potentiial bitVects value (detected with MUL_T during division)
          //setMeta(rd, incomplete_t, 0, MUL_T);
          print_over_approx((uint64_t*) "mul");
          throw_exception(EXCEPTION_INCOMPLETENESS, 0);
        } else if (can_mul_correction(*(reg_expr + rs1)) == 0) {
              //now: expression not managed -> fail
              print_bad_expression();
              throw_exception(EXCEPTION_INCOMPLETENESS, 0);
          } else {
            *(reg_typ + rd) = MSIID_T;

            if (*(reg_factor + rs1) == 0)
              set_correction(rd, 0, MUL_T, *(reg_colos + rs1), *(reg_coups + rs1), *(registers + rs2));
            else  //cumul factors
              set_correction(rd, 0, MUL_T, *(reg_colos + rs1), *(reg_coups + rs1), *(reg_factor + rs1) * *(registers + rs2));
            set_constraint(rd, *(reg_stc + rs1), *(reg_vaddr + rs1), mul_los, mul_ups, *(reg_alpha3 + rs1) * *(registers + rs2)); //interval mul semantics

            // print((uint64_t*) " ~~~~ mul ~~~~ *");
            // print_integer(*(registers + rs2));
            // print((uint64_t*) " = ");
            // print_integer(*(reg_typ + rd));
            // print_msiid(*(registers + rd), *(reg_alpha2 + rd), *(reg_alpha3 + rd));
            // println();
          }
      }
  } else if (*(reg_typ + rs2)) {
    if (*(reg_hasmn + rs2))
      // rs2 constraint has already minuend and cannot have another addend
      error_minuend((uint64_t*) "right", (uint64_t*) "mul");
    else {
      // rd inherits rs2 constraint since rs1 has none
      // assert: rs1 interval is singleton
      // c * s
      if (check_mul_condition(rs2, rs1) == 0) {
        // next step
        // it is a potentiial bitVects value (detected with MUL_T during division)
        //setMeta(rd, incomplete_t, 0, MUL_T);
        print_over_approx((uint64_t*) "mul");
        throw_exception(EXCEPTION_INCOMPLETENESS, 0);
      } else if (*(reg_expr + rs1) > 0) {
          //now: expression not managed -> fail
          print_bad_expression();
          throw_exception(EXCEPTION_INCOMPLETENESS, 0);
        } else {
          *(reg_typ + rd) = MSIID_T;
          set_correction(rd, 0, MUL_T, *(reg_colos + rs2), *(reg_coups + rs2), *(registers + rs1));
          set_constraint(rd, *(reg_stc + rs2), *(reg_vaddr + rs2), mul_los, mul_ups, *(reg_alpha3 + rs2) * *(registers + rs1)); //interval mul semantics
      }
    }
  }

  //cast into concrete value 0 in case of * 0
  if (*(reg_alpha3 + rd) == 0) {
    *(reg_typ + rd) = CONCRETE_T;
    set_correction(rd, 0, 0, 0, 0, 0);
    set_constraint(rd, *(reg_stc + rd), *(reg_vaddr + rd), mul_los, mul_ups, 1);
  }
}

void constrain_mul() {
  uint64_t stype;

  if (rd == REG_ZR)
    return;

  if (do_taint_flag) taint_binop(MUL);
  stype = which_type(rs1, rs2);

  // next step
  // if (stype == incomplete_t) {
  //   print_bad_expression();
  //   throw_exception(EXCEPTION_INCOMPLETENESS, 0);
  //   return;
  // }

  if (stype == ARRAY_T)
    pointer_error();
  else if (stype == MSIID_T)
    mul_msiid();
  else {
    // rd has no constraint if both rs1 and rs2 have no constraints
    // c * c
    *(reg_typ + rd) = CONCRETE_T;
    set_correction(rd, 0, 0, 0, 0, 0);
    set_constraint(rd, 0, 0, *(registers + rs1) * *(registers + rs2), *(reg_alpha2 + rs1) * *(reg_alpha2 + rs2), 1);
  }

  pc = pc + INSTRUCTIONSIZE;
  ic_mul = ic_mul + 1;
}

void do_divu() {
  // division unsigned

  if (*(registers + rs2) != 0) {
    if (rd != REG_ZR)
      // semantics of divu
      *(registers + rd) = *(registers + rs1) / *(registers + rs2);

    pc = pc + INSTRUCTIONSIZE;

    ic_divu = ic_divu + 1;
  } else
    throw_exception(EXCEPTION_DIVISIONBYZERO, 0);
}

uint64_t check_divu_step() {
  // set the result step to 1 if divisor greater than s1
  if (*(reg_alpha3 + rs1) < *(registers + rs2)) {
    if (*(registers + rs2) % *(reg_alpha3 + rs1) != 0) {
      //now: exit analysis (step no multiple)

      print_over_approx((uint64_t*) "divu1");
      throw_exception(EXCEPTION_INCOMPLETENESS, 0);
      return 0;
    }
    return 1;
  } else {
    if (*(reg_alpha3 + rs1) % *(registers + rs2) != 0) {
      //now: exit analysis (step no multiple)

      print_over_approx((uint64_t*) "divu2");
      throw_exception(EXCEPTION_INCOMPLETENESS, 0);
      return 0;
    }
    return *(reg_alpha3 + rs1) / *(registers + rs2);
  }
}

void divu_msiid() {
  uint64_t div_los;
  uint64_t div_ups;
  uint64_t div_steps;
  uint64_t prev_step;
  uint64_t max;
  uint64_t expr;

  div_los = *(registers + rs1) / *(reg_alpha2 + rs2);
  div_ups = *(reg_alpha2 + rs1) / *(registers + rs2);
  prev_step = *(reg_alpha3 + rs1);

  //interval divu semantics
  if (*(reg_typ + rs1)) {
    if (*(reg_typ + rs2)) {
      // s / s
      // non-linear expressions are not supported
      printf2((uint64_t*) "%s: detected non-linear expression in divu at %x", selfie_name, (uint64_t*) pc);
      print_code_line_number_for_instruction(pc - entry_point);
      println();
      exit(EXITCODE_SYMBOLICEXECUTIONERROR);

    } else if (*(reg_hasmn + rs1))
        // rs1 constraint has already minuend and cannot have another addend
        error_minuend((uint64_t*) "left", (uint64_t*) "divu");
      else {
        // rd inherits rs1 constraint since rs2 has none
        // assert: rs2 interval is singleton
        // s / c

        if (*(reg_expr + rs1) > 0) {
          //now: expression not managed -> fail
          print_bad_expression();
          throw_exception(EXCEPTION_INCOMPLETENESS, 0);
        } else
          expr = DIV_T;

        // step computation
        div_steps = check_divu_step();
        if (div_steps == 0) return; //incomplete

          // interval semantics of divu
        if (*(registers + rs1) > *(reg_alpha2 + rs1)) {
          // rs1 constraint is wrapped: [lo, UINT64_MAX] U [0, up]

          // lo/k == up/k (or) up/k + step_rd
          if (div_los != div_ups)
            if (div_los > div_ups + div_steps) {
              //now: exit analysis (wrap interval division: not close)
              print_over_approx((uint64_t*) "divu3");
              throw_exception(EXCEPTION_INCOMPLETENESS, 0);
              return;
            }
          //exact computation of rd ms-interval
          max = compute_upper_bound(*(registers + rs1), prev_step, UINT64_MAX);

          set_correction(rd, 0, expr, *(reg_colos + rs1), *(reg_coups + rs1), *(registers + rs2));
          set_constraint(rd, *(reg_stc + rs1), *(reg_vaddr + rs1), (max + prev_step) / *(registers + rs2), max / *(reg_alpha2 + rs2), div_steps);
        } else {
          // rs1 constraint is not wrapped
          set_correction(rd, 0, expr, *(reg_colos + rs1), *(reg_coups + rs1), *(registers + rs2));
          set_constraint(rd, *(reg_stc + rs1), *(reg_vaddr + rs1), div_los, div_ups, div_steps);
        }

        if (*(registers + rd) == *(reg_alpha2 + rd))
          *(reg_typ + rd) = CONCRETE_T;
        else
          *(reg_typ + rd) = *(reg_typ + rs1);
      }
    } else if (*(reg_typ + rs2)) {
      printf2((uint64_t*) "%s: detected division of constant by interval at %x", selfie_name, (uint64_t*) pc);
      print_code_line_number_for_instruction(pc - entry_point);
      println();
      throw_exception(EXCEPTION_INCOMPLETENESS, 0);
    }
}

void constrain_divu() {
  uint64_t stype;

  if (*(registers + rs2) != 0) {
    if (*(reg_alpha2 + rs2) >= *(registers + rs2))  {

      // 0 is not in interval
      if (rd == REG_ZR)
        return;

      if (do_taint_flag) taint_binop(DIVU);
      stype = which_type(rs1, rs2);

      if (stype == ARRAY_T)
        pointer_error();
      else if (stype == MSIID_T)
        divu_msiid();
      else {
        // rd has no constraint if both rs1 and rs2 have no constraints
        // c / c
        *(reg_typ + rd) = CONCRETE_T;
        set_correction(rd, 0, 0, 0, 0, 0);
        set_constraint(rd, 0, 0, *(registers + rs1) / *(reg_alpha2 + rs2), *(reg_alpha2 + rs1) / *(registers + rs2), 1);
      }
    //next step
    // if (*(reg_alpha3 + rs1) > 1) { //create k-MSIID (previously mult)
    //   if (prev_step < div_steps) {
    //     print_over_approx((uint64_t*) "div");
    //     throw_exception(EXCEPTION_INCOMPLETENESS, 0);
    //   } else {
    //     setMeta(rd, bitsVect_t, 0, 0);
    //     set_correction(rd, 0, 0, 0); //reset correction
    //
    //     print((uint64_t*) "~~~~ ");
    //     print_integer(*(reg_typ + rs1));
    //     print_msiid(*(registers + rs1), *(reg_alpha2 + rs1), *(reg_alpha3 + rs1));
    //
    //     if(*(reg_typ + rs1) == incomplete_t)
    //       div_ups = compute_upper_bound(*(registers + rs1), prev_step, UINT64_MAX) / *(registers + rs2);
    //
    //     set_constraint(rd, *(reg_stc + rs1), *(reg_vaddr + rs1), div_los,  div_ups, UINT64_MAX / *(registers + rs2)); //bitVects <l,u,umax> (step always 1)
    //
    //     print((uint64_t*) "~~~~ divu ~~~~ /");
    //     print_integer(*(registers + rs2));
    //     print((uint64_t*) " = ");
    //     print_integer(*(reg_typ + rd));
    //     print_msiid(*(registers + rd), *(reg_alpha2 + rd), *(reg_alpha3 + rd));
    //     println();
    //
    //     return;
    //   }
    // }
    pc = pc + INSTRUCTIONSIZE;
    ic_divu = ic_divu + 1;
    } else  // 0 is in interval
      throw_exception(EXCEPTION_DIVISIONBYZERO, 0);
  } else
    throw_exception(EXCEPTION_DIVISIONBYZERO, 0);
}

void do_remu() {
  // remainder unsigned

  if (*(registers + rs2) != 0) {
    if (rd != REG_ZR)
      // semantics of remu
      *(registers + rd) = *(registers + rs1) % *(registers + rs2);

    pc = pc + INSTRUCTIONSIZE;

    ic_remu = ic_remu + 1;
  } else
    throw_exception(EXCEPTION_DIVISIONBYZERO, 0);
}

void constrain_remu_step_1() {
  uint64_t lo;
  uint64_t up;
  uint64_t divisor;
  uint64_t remu_case;
  uint64_t wrap_remu_case;
  uint64_t expr;

  // interval semantics of remu
  lo      = *(registers + rs1);
  up      = *(reg_alpha2 + rs1);
  divisor = *(registers + rs2);

  if (*(reg_expr + rs1) > 0) {
    //now: expression not managed -> fail
    print_bad_expression();
    throw_exception(EXCEPTION_INCOMPLETENESS, 0);
    return;
  } else
    expr = REM_T;

  if (lo <= up) {
    // rs1 interval is not wrapped
    remu_case = remu_condition(lo, up, divisor);

    if (remu_case == 0) {
      //case [0]
      lo = lo % divisor;
      up = up % divisor;

    } else {
      //other cases [0, k-1]
      lo = 0;
      up = divisor - 1;

      if (remu_case == 1) {
        //case[1] the result is not an ms-interval
        //now: exit analysis
        print_over_approx((uint64_t*) "rem1_1");
        throw_exception(EXCEPTION_INCOMPLETENESS, 0);
      }
    }
  } else {
    // [up, lo] interval is wrapped
    wrap_remu_case = remu_condition(lo, UINT64_MAX, divisor);  // [lo, UINT64_MAX]
    if (remu_condition(0, up, divisor) == 2) {  // [0, up]
      lo = 0;
      up = divisor - 1;
    } else if (wrap_remu_case == 2) {
      lo = 0;
      up = divisor - 1;
    } else if (wrap_remu_case == 0) {
      // REM_Typ1 == 0 and wrap_remu_case == 0
      if (up % divisor >= UINT64_MAX % divisor) {
        // up >= UMAX [k]
        lo = 0;
        up = up % divisor;
      } else if (up % divisor + 1 >= lo % divisor) {
        // up < UMAX [k] and up + 1 >= lo [k]
        lo = 0;
        up = UINT64_MAX % divisor;
      } else {
        // up < UMAX [k] and up + 1 < lo [k] (not an ms-interval)
        lo = 0;
        up = UINT64_MAX % divisor;

        printf2((uint64_t*) "%s: detected not handled remu at %x", selfie_name, (uint64_t*) pc);
        print_code_line_number_for_instruction(pc - entry_point);
        println();
        //now: exit analysis
        throw_exception(EXCEPTION_INCOMPLETENESS, 0);
      }
    } else {
      // REM_Typ1 == 0 and {wrap_remu_case == 1 (impossible)}
      if (up % divisor + 1 >= lo % divisor) {
        // up >= lo and lo != k [k + 1]
        lo = 0;
        up = divisor - 1;
      } else {
        // up < lo or lo == k [k + 1] (not an ms-interval)
        lo = 0;
        up = divisor - 1;

        //now: exit analysis
        print_over_approx((uint64_t*) "rem1_^2");
        throw_exception(EXCEPTION_INCOMPLETENESS, 0);
      }
    }
  }

  // rd inherits rs1 constraint since rs2 has none
  // assert: rs2 interval is singleton
  set_correction(rd, 0, expr, *(reg_colos + rs1), *(reg_coups + rs1), *(registers + rs2));
  set_constraint(rd, *(reg_stc + rs1), *(reg_vaddr + rs1), lo, up, 1);

  if (*(registers + rd) == *(reg_alpha2 + rd))
    *(reg_typ + rd) = CONCRETE_T;
  else
    *(reg_typ + rd) = MSIID_T;
  //else
  //  setMeta(rd, bitsVect_t, 0, expr);
}

void remu_msiid() {
  uint64_t lo;
  uint64_t up;
  uint64_t divisor;
  uint64_t step;
  uint64_t gcd_step_k;
  uint64_t remu_case;
  uint64_t lcm;
  uint64_t expr;

  if (*(reg_expr + rs1) > 0) {
    //now: expression not managed -> fail
    print_bad_expression();
    throw_exception(EXCEPTION_INCOMPLETENESS, 0);
  } else
    expr = REM_T;

  if (*(reg_hasmn + rs1)) {
    // rs1 constraint has already minuend and cannot have another divisor
    printf2((uint64_t*) "%s: detected invalid minuend expression in left operand of remu at %x", selfie_name, (uint64_t*) pc);
    print_code_line_number_for_instruction(pc - entry_point);
    println();
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  // interval semantics of remu
  // s % c
  lo      = *(registers + rs1);
  up      = *(reg_alpha2 + rs1);
  divisor = *(registers + rs2);
  step    = *(reg_alpha3 + rs1);

  //special case when step is 1
  if (step == 1) {
    constrain_remu_step_1();
    return;
  }

  if (lo <= up) {
    // rs1 interval is not wrapped
    remu_case = stride_remu_condition(lo, up, step, divisor);

    if (remu_case == 0) {
      //case [1] lo/div ==  up/div
      lo = lo % divisor;
      up = up % divisor;
      //same step

    } else if (remu_case == 1) {
      //case [2]: rem_up-rem_lo < lcm and rem_up = rem_lo + 1 (result not an ms-interval)
      up = (lo + ((divisor - 1 - lo % divisor) / step) * step) % divisor;
      lo = (lo + ((divisor - 1 - lo % divisor) / step + 1) * step) % divisor;
      //same step

      //now: exit analysis
      print_over_approx((uint64_t*) "rem1");
      throw_exception(EXCEPTION_INCOMPLETENESS, 0);
    } else {
      //case[3, 4 and 5]
      if (remu_case == 10) {
        //case [5] rem_up > rem_lo and rem_up - rem_lo < lcm - step (result not an ms-interval)
        //now: exit analysis
        print_over_approx((uint64_t*) "rem10");
        throw_exception(EXCEPTION_INCOMPLETENESS, 0);
      }
      //case [3 (>) and 4 (=)] rem_up > rem_lo and rem_up - rem_lo => lcm - step (complete gcd_step_k ms-interval)
      gcd_step_k = gcd(step, divisor);
      lo = lo % divisor - ( (lo % divisor) / gcd_step_k) * gcd_step_k;
      up = compute_upper_bound(lo, gcd_step_k, divisor - 1);
      step = gcd_step_k;
    }
  } else if (is_power_of_two(divisor)) {
    // rs1 interval is wrapped and divisor == 2^i
    gcd_step_k = gcd(step, divisor);
    lcm = (step * divisor) / gcd_step_k;

    if (up - lo < lcm - step) {
      // rs1 interval is too small the result is not an ms-interval
      //now: exit analysis
      print_over_approx((uint64_t*) "rem^2");
      throw_exception(EXCEPTION_INCOMPLETENESS, 0);
    }

    lo = lo % divisor - ( (lo % divisor) / gcd_step_k) * gcd_step_k;
    up = compute_upper_bound(lo, gcd_step_k, divisor-1);
    step = gcd_step_k;

  } else {
    //case wrapped and k != 2^i not handled
    printf3((uint64_t*) "%s: detected wrapped remu with %d divisor at %x", selfie_name, (uint64_t *) *(reg_alpha2 + rs2), (uint64_t*) pc);
    print_code_line_number_for_instruction(pc - entry_point);
    println();
    throw_exception(EXCEPTION_INCOMPLETENESS, 0);
    //exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  set_correction(rd, 0, expr, *(reg_colos + rs1), *(reg_coups + rs1), *(registers + rs2));
  set_constraint(rd, *(reg_stc + rs1), *(reg_vaddr + rs1), lo, up, step);

  if (*(registers + rd) == *(reg_alpha2 + rd))
    *(reg_typ + rd) = CONCRETE_T;
  else
    *(reg_typ + rd) = *(reg_typ + rs1);
}

void constrain_remu() {
  uint64_t stype;

  if (*(registers + rs2) != 0) {

    if (*(reg_typ + rs2) != CONCRETE_T) {
      // rs2 is not concrete
      printf2((uint64_t*) "%s: constrained memory location in right operand of remu at %x", selfie_name, (uint64_t*) pc);
      print_code_line_number_for_instruction(pc - entry_point);
      println();
      throw_exception(EXCEPTION_INCOMPLETENESS, 0);
      //exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      return;
    }

    if (rd == REG_ZR)
      return;

    if (do_taint_flag) taint_binop(REMU);
    stype = which_type(rs1, rs2);

    if (stype == ARRAY_T)
      pointer_error();
    else if (stype == MSIID_T) {
      remu_msiid();
    } else {
      // rd has no constraint if both rs1 and rs2 have no constraints
      // c % c
      *(reg_typ + rd) = CONCRETE_T;
      set_correction(rd, 0, 0, 0, 0, 0);
      set_constraint(rd, 0, 0, *(registers + rs1) % *(registers + rs2), *(reg_alpha2 + rs1) % *(reg_alpha2 + rs2), 1);
    }
    // next step
    // if (stype == incomplete_t) {
    //   print_bad_expression();
    //   throw_exception(EXCEPTION_INCOMPLETENESS, 0);
    //   return;
    // }

    pc = pc + INSTRUCTIONSIZE;
    ic_remu = ic_remu + 1;
  } else
    throw_exception(EXCEPTION_DIVISIONBYZERO, 0);
}

void do_sltu() {
  // set on less than unsigned

  if (rd != REG_ZR) {
    // semantics of sltu
    if (*(registers + rs1) < *(registers + rs2))
      *(registers + rd) = 1;
    else
      *(registers + rd) = 0;
  }

  pc = pc + INSTRUCTIONSIZE;

  ic_sltu = ic_sltu + 1;
}

void constrain_sltu() {
  // interval semantics of sltu
  if (rd != REG_ZR) {

    if (do_taint_flag) taint_binop(SLTU);

    if (*(reg_typ + rs1) == MSIID_T) {
      if (*(reg_vaddr + rs1) == 0) {
        // constrained memory at vaddr 0 means that there is more than
        // one constrained memory location in the sltu operand
        printf3((uint64_t*) "%s: %d constrained memory locations in left sltu operand at %x", selfie_name, (uint64_t*) *(reg_typ + rs1), (uint64_t*) pc);
        print_code_line_number_for_instruction(pc - entry_point);
        println();
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }
    }

    if (*(reg_typ + rs2) == MSIID_T) {
      if (*(reg_vaddr + rs2) == 0) {
        // constrained memory at vaddr 0 means that there is more than
        // one constrained memory location in the sltu operand
        printf3((uint64_t*) "%s: %d constrained memory locations in right sltu operand at %x", selfie_name, (uint64_t*) *(reg_typ + rs2), (uint64_t*) pc);
        print_code_line_number_for_instruction(pc - entry_point);
        println();
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }
    }

    // number of constraints given a stlu (detect unreachable case)
    has_true_branch  = 0;
    has_false_branch = 0;

    // remember the true value before constraining (lost if wrapped interval)
     if (*(reg_typ + rs1) == MSIID_T)
       mrvc_rs1 = load_virtual_memory(pt, *(reg_vaddr + rs1));
     if (*(reg_typ + rs2) == MSIID_T)
       mrvc_rs2 = load_virtual_memory(pt, *(reg_vaddr + rs2));

    // take local copy of mrcc to make sure that alias check considers old mrcc
    if (*(reg_typ + rs1) == ARRAY_T)
      if (*(reg_typ + rs2) == ARRAY_T)
        create_constraints(*(registers + rs1), *(registers + rs1), 1, *(registers + rs2), *(registers + rs2), 1, mrcc, 0);
      else
        create_constraints(*(registers + rs1), *(registers + rs1), 1, *(registers + rs2), *(reg_alpha2 + rs2), *(reg_alpha3 + rs2), mrcc, 0);
    else if (*(reg_typ + rs2) == ARRAY_T)
        create_constraints(*(registers + rs1), *(reg_alpha2 + rs1), *(reg_alpha3 + rs1), *(registers + rs2), *(registers + rs2), 1, mrcc, 0);
    else
        create_constraints(*(registers + rs1), *(reg_alpha2 + rs1), *(reg_alpha3 + rs1), *(registers + rs2), *(reg_alpha2 + rs2), *(reg_alpha3 + rs2), mrcc, 0);
  }

  pc = pc + INSTRUCTIONSIZE;
  ic_sltu = ic_sltu + 1;
}

void backtrack_sltu() {
  uint64_t vaddr;

  if (debug_symbolic) {
    printf1((uint64_t*) "%s: backtracking sltu ", selfie_name);
    print_symbolic_memory(tc);
  }

  vaddr = get_trace_vaddr(tc);

  if (vaddr < NUMBEROFREGISTERS) {
    if (vaddr > 0) {
      // the register is identified by vaddr
      *(registers + vaddr) = get_trace_a1(tc);

      *(reg_typ + vaddr) = get_trace_type(tc);
      set_correction(vaddr, 0, 0, 0, 0, 0);
      set_constraint(vaddr, get_trace_src(tc), 0, get_trace_a1(tc), get_trace_a2(tc), get_trace_a3(tc));

      // restoring mrcc
      mrcc = get_trace_tc(tc);

      if (vaddr != REG_FP)
        if (vaddr != REG_SP) {
          // stop backtracking and try next case
          pc = pc + INSTRUCTIONSIZE;

          ic_sltu = ic_sltu + 1;
        }
    }
  } else
    store_virtual_memory(pt, vaddr, get_trace_tc(tc));

  efree();
}

void print_ld() {
  print_code_context_for_instruction(pc);
  printf3((uint64_t*) "ld %s,%d(%s)", get_register_name(rd), (uint64_t*) imm, get_register_name(rs1));
}

void print_ld_before() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  print((uint64_t*) ": ");
  print_register_hexadecimal(rs1);

  if (is_valid_virtual_address(vaddr))
    if (is_virtual_address_mapped(pt, vaddr)) {
      if (is_system_register(rd))
        printf2((uint64_t*) ",mem[%x]=%x |- ", (uint64_t*) vaddr, (uint64_t*) load_virtual_memory(pt, vaddr));
      else
        printf2((uint64_t*) ",mem[%x]=%d |- ", (uint64_t*) vaddr, (uint64_t*) load_virtual_memory(pt, vaddr));
      print_register_value(rd);

      return;
    }

  print((uint64_t*) " |-");
}

void print_ld_after(uint64_t vaddr) {
  if (is_valid_virtual_address(vaddr))
    if (is_virtual_address_mapped(pt, vaddr)) {
      print((uint64_t*) " -> ");
      print_register_value(rd);
      printf1((uint64_t*) "=mem[%x]", (uint64_t*) vaddr);
    }
}

uint64_t do_ld() {
  uint64_t vaddr;
  uint64_t a;

  // load double word

  vaddr = *(registers + rs1) + imm;

  if (is_valid_virtual_address(vaddr)) {
    if (is_virtual_address_mapped(pt, vaddr)) {
      if (rd != REG_ZR)
        // semantics of ld
        *(registers + rd) = load_virtual_memory(pt, vaddr);

      // keep track of instruction address for profiling loads
      a = (pc - entry_point) / INSTRUCTIONSIZE;

      pc = pc + INSTRUCTIONSIZE;

      // keep track of number of loads in total
      ic_ld = ic_ld + 1;

      // and individually
      *(loads_per_instruction + a) = *(loads_per_instruction + a) + 1;
    } else
      throw_exception(EXCEPTION_PAGEFAULT, get_page_of_virtual_address(vaddr));
  } else
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);

  return vaddr;
}

uint64_t constrain_ld() {
  uint64_t vaddr;
  uint64_t mrvc;
  uint64_t a;

  // load double word

  vaddr = *(registers + rs1) + imm;

  if (is_safe_address(vaddr, rs1)) {
    if (is_virtual_address_mapped(pt, vaddr)) {
      if (rd != REG_ZR) {
        mrvc = load_symbolic_memory(pt, vaddr);

        // interval semantics of ld
        // assert: vaddr == getTraceVaddr(mrvc)
        if (is_symbolic_value(get_trace_type(mrvc))) {
            *(reg_typ + rd) = get_trace_type(mrvc);
            set_constraint(rd, get_trace_src(mrvc), vaddr, get_trace_a1(mrvc), get_trace_a2(mrvc), get_trace_a3(mrvc));

            if (get_trace_type(mrvc) == MSIID_T) {
              if (*(reg_alpha3 + rd) == 0) {
                printf2((uint64_t*) "%s: detected step 0 at %x", selfie_name, (uint64_t*) pc);
                print_code_line_number_for_instruction(pc - entry_point);
                println();
                exit(EXITCODE_SYMBOLICEXECUTIONERROR);
              }
            }
        } else {
            *(reg_typ + rd) = get_trace_type(mrvc);
            set_constraint(rd, 0, 0, get_trace_a1(mrvc), get_trace_a2(mrvc), 1);
        }

        if (do_taint_flag) {
          *(reg_is_tainted + rd)   = *(taints + mrvc);
          *(reg_is_minuend + rd)   = *(minuends + mrvc);
          *(reg_has_step + rd)     = *(has_steps + mrvc);
        }
        set_correction(rd, 0, 0, 0, 0, 0);
      }

      // keep track of instruction address for profiling loads
      a = (pc - entry_point) / INSTRUCTIONSIZE;

      pc = pc + INSTRUCTIONSIZE;
      ic_ld = ic_ld + 1;
      // keep track of number of loads per instruction
      a = (pc - entry_point) / INSTRUCTIONSIZE;

      *(loads_per_instruction + a) = *(loads_per_instruction + a) + 1;
    } else
      throw_exception(EXCEPTION_PAGEFAULT, get_page_of_virtual_address(vaddr));
  } else
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);

  return vaddr;
}

void print_sd() {
  print_code_context_for_instruction(pc);
  printf3((uint64_t*) "sd %s,%d(%s)", get_register_name(rs2), (uint64_t*) imm, get_register_name(rs1));
}

void print_sd_before() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  print((uint64_t*) ": ");
  print_register_hexadecimal(rs1);

  if (is_valid_virtual_address(vaddr))
    if (is_virtual_address_mapped(pt, vaddr)) {
      print((uint64_t*) ",");
      print_register_value(rs2);
      if (is_system_register(rd))
        printf2((uint64_t*) " |- mem[%x]=%x", (uint64_t*) vaddr, (uint64_t*) load_virtual_memory(pt, vaddr));
      else
        printf2((uint64_t*) " |- mem[%x]=%d", (uint64_t*) vaddr, (uint64_t*) load_virtual_memory(pt, vaddr));

      return;
    }

  print((uint64_t*) " |-");
}

void print_sd_after(uint64_t vaddr) {
  if (is_valid_virtual_address(vaddr))
    if (is_virtual_address_mapped(pt, vaddr)) {
      printf1((uint64_t*) " -> mem[%x]=", (uint64_t*) vaddr);
      print_register_value(rs2);
    }
}

uint64_t do_sd() {
  uint64_t vaddr;
  uint64_t a;

  // store double word

  vaddr = *(registers + rs1) + imm;

  if (is_valid_virtual_address(vaddr)) {
    if (is_virtual_address_mapped(pt, vaddr)) {
      // semantics of sd
      store_virtual_memory(pt, vaddr, *(registers + rs2));

      // keep track of instruction address for profiling stores
      a = (pc - entry_point) / INSTRUCTIONSIZE;

      pc = pc + INSTRUCTIONSIZE;

      // keep track of number of stores in total
      ic_sd = ic_sd + 1;

      // and individually
      *(stores_per_instruction + a) = *(stores_per_instruction + a) + 1;
    } else
      throw_exception(EXCEPTION_PAGEFAULT, get_page_of_virtual_address(vaddr));
  } else
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);

  return vaddr;
}

uint64_t has_correction(uint64_t reg) {
  if ( *(reg_expr + reg) > SUM_T)       return 1;
  if ( *(reg_expr + reg) == CONCRETE_T) return 0;
  if ( *(reg_colos + reg) == 0)         return *(reg_coups + reg);
  return 1;
}

uint64_t is_renamming(uint64_t vaddr, uint64_t reg) {
  if (vaddr == *(registers + REG_SP)) //also match last local variable accesses
   if (reg == REG_SP)
    return 1;                         //SD $ti 0($sp)
  return 0;
}

uint64_t constrain_sd() {
  uint64_t stc;
  uint64_t vaddr;
  uint64_t a;
  uint64_t context;
  uint64_t corr_value;
  context = 0;
  corr_value = -1;

  // store double word

  vaddr = *(registers + rs1) + imm;

  if (is_safe_address(vaddr, rs1)) {
    if (is_virtual_address_mapped(pt, vaddr)) {
      // interval semantics of sd
      if (*(reg_typ + rs2) == MSIID_T) {
        if (*(reg_vaddr + rs2) == 0) {
          // constrained memory at vaddr 0 means that:
          // [read syscall] there is more than
          //                one constrained memory location in the sd operand
          // [input syscall] just return from the input call
          printf2((uint64_t*) "%s: constrained memory locations in sd operand at %x", selfie_name, (uint64_t*) pc);
          print_code_line_number_for_instruction(pc - entry_point);
          println();
          //exit(EXITCODE_SYMBOLICEXECUTIONERROR);
        }

        //call renaming management
        if (is_renamming(vaddr, rs1)) {
          //TODO: problem with save_tempories?
          if(*(reg_vaddr + rs2)) {
            stc = load_virtual_memory(pt, *(reg_vaddr + rs2));

            if (has_correction(rs2)) { //if has co
              // allocate correction entry
              *(hasmns + cc)  = *(reg_hasmn + rs2);
              *(exprs + cc)   = *(reg_expr + rs2);
              *(colos + cc)   = *(reg_colos + rs2);
              *(coups + cc)   = *(reg_coups + rs2);
              *(factors + cc) = *(reg_factor + rs2);
              corr_value      = cc;
              cc = cc + 1;
            }
          } else
            stc = 0; //first return from input syscall

          if (sdebug_context) {
            context = 1;
            printf2((uint64_t*) "%s: symbolic argument at %d", selfie_name, (uint64_t*) pc);
            print_code_line_number_for_instruction(pc - entry_point);
            print((uint64_t*) " from ");
            print_symbolic_register(rs2);
            if (corr_value != (uint64_t) -1)
              printf5((uint64_t*) " with correction (%d,%d,[%d,%d],%d)",
              (uint64_t*) *(hasmns + corr_value),
              (uint64_t*) *(exprs + corr_value),
              (uint64_t*) *(colos + corr_value),
              (uint64_t*) *(coups + corr_value),
              (uint64_t*) *(factors + corr_value));

            println();
          }
        } else
          stc = *(reg_stc + rs2);
      } else
        stc = *(reg_stc + rs2);

      if (do_taint_flag) set_taint_memory(*(reg_is_tainted + rs2), *(reg_is_minuend + rs2), *(reg_has_step + rs2));
      store_symbolic_memory(pt, stc, vaddr,  *(reg_typ + rs2), *(registers + rs2), *(reg_alpha2 + rs2), *(reg_alpha3 + rs2), corr_value, mrcc);

      if (context) {
        printf1((uint64_t*) "%s: ", selfie_name);
        print_symbolic_memory(load_symbolic_memory(pt, vaddr));
        println();
      }

      pc = pc + INSTRUCTIONSIZE;
      ic_sd = ic_sd + 1;
      // keep track of number of stores per instruction
      a = (pc - entry_point) / INSTRUCTIONSIZE;

      *(stores_per_instruction + a) = *(stores_per_instruction + a) + 1;
    } else
      throw_exception(EXCEPTION_PAGEFAULT, get_page_of_virtual_address(vaddr));
  } else
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);

  return vaddr;
}

void backtrack_sd() {
  if (debug_symbolic) {
    printf1((uint64_t*) "%s: backtracking sd ", selfie_name);
    print_symbolic_memory(tc);
  }

  store_virtual_memory(pt, get_trace_vaddr(tc), get_trace_tc(tc));

  efree();
}

void print_beq() {
  print_code_context_for_instruction(pc);
  printf4((uint64_t*) "beq %s,%s,%d[%x]", get_register_name(rs1), get_register_name(rs2), (uint64_t*) signed_division(imm, INSTRUCTIONSIZE), (uint64_t*) (pc + imm));
}

void print_beq_before() {
  print((uint64_t*) ": ");
  print_register_value(rs1);
  print((uint64_t*) ",");
  print_register_value(rs2);
  printf1((uint64_t*) " |- $pc=%x", (uint64_t*) pc);
}

void print_beq_after() {
  printf1((uint64_t*) " -> $pc=%x", (uint64_t*) pc);
}

void test_unreachable_branch(uint64_t* label, uint64_t unreach_pc) {
  if (debug_end_point) {
    if (has_true_branch == 0)
      print_unreachable(label, unreach_pc);
    if (has_false_branch == 0)
      print_unreachable(label, unreach_pc);
  }
  has_true_branch = 1;
  has_false_branch = 1; // prevent from another raises by the same beq
}

void do_beq() {
  // branch on equal

  // semantics of beq
  if (*(registers + rs1) == *(registers + rs2)) {
    if (print_branch)
      test_unreachable_branch((uint64_t*) "true", pc + INSTRUCTIONSIZE);
    else
      print_branch = 1;
    pc = pc + imm;
  }
  else {
    if (print_branch)
      test_unreachable_branch((uint64_t*) "false", pc + imm);
    else
      print_branch = 1;
    pc = pc + INSTRUCTIONSIZE;
  }

  ic_beq = ic_beq + 1;
}

void print_jal() {
  print_code_context_for_instruction(pc);
  printf3((uint64_t*) "jal %s,%d[%x]", get_register_name(rd), (uint64_t*) signed_division(imm, INSTRUCTIONSIZE), (uint64_t*) (pc + imm));
}

void print_jal_before() {
  print((uint64_t*) ": |- ");
  if (rd != REG_ZR) {
    print_register_hexadecimal(rd);
    print((uint64_t*) ",");
  }
  printf1((uint64_t*) "$pc=%x", (uint64_t*) pc);
}

void print_jal_jalr_after() {
  print_beq_after();
  if (rd != REG_ZR) {
    print((uint64_t*) ",");
    print_register_hexadecimal(rd);
  }
}

void do_jal() {
  uint64_t a;

  // jump and link

  if (rd != REG_ZR) {
    // first link
    *(registers + rd) = pc + INSTRUCTIONSIZE;

    // then jump for procedure calls
    pc = pc + imm;

    // prologue address for profiling procedure calls
    a = (pc - entry_point) / INSTRUCTIONSIZE;

    // keep track of number of procedure calls in total
    calls = calls + 1;

    // and individually
    *(calls_per_procedure + a) = *(calls_per_procedure + a) + 1;
  } else if (signed_less_than(imm, 0)) {
    // jump backwards to check for another loop iteration
    pc = pc + imm;

    // first loop instruction address for profiling loop iterations
    a = (pc - entry_point) / INSTRUCTIONSIZE;

    // keep track of number of loop iterations in total
    iterations = iterations + 1;

    *(iterations_per_loop + a) = *(iterations_per_loop + a) + 1;
  } else {
    // save last exit line
    last_jal_from = pc;

    // just jump forward
    pc = pc + imm;
  }

  ic_jal = ic_jal + 1;
}

void constrain_jal_jalr() {
  if (rd != REG_ZR) {
    *(reg_alpha2 + rd) = *(registers + rd);
  }
}

void print_jalr() {
  print_code_context_for_instruction(pc);
  printf3((uint64_t*) "jalr %s,%d(%s)", get_register_name(rd), (uint64_t*) signed_division(imm, INSTRUCTIONSIZE), get_register_name(rs1));
}

void print_jalr_before() {
  print((uint64_t*) ": ");
  print_register_hexadecimal(rs1);
  print((uint64_t*) " |- ");
  if (rd != REG_ZR) {
    print_register_hexadecimal(rd);
    print((uint64_t*) ",");
  }
  printf1((uint64_t*) "$pc=%x", (uint64_t*) pc);
}

void do_jalr() {
  uint64_t next_pc;

  // jump and link register

  if (rd == REG_ZR)
    // fast path: just return by jumping rs1-relative with LSB reset
    pc = left_shift(right_shift(*(registers + rs1) + imm, 1), 1);
  else {
    // slow path: first prepare jump, then link, just in case rd == rs1

    // prepare jump with LSB reset
    next_pc = left_shift(right_shift(*(registers + rs1) + imm, 1), 1);

    // link to next instruction
    *(registers + rd) = pc + INSTRUCTIONSIZE;

    // jump
    pc = next_pc;
  }

  ic_jalr = ic_jalr + 1;
}

void print_ecall() {
  print_code_context_for_instruction(pc);
  print((uint64_t*) "ecall");
}

void print_ecall_before() {
  print((uint64_t*) ": |- ");
  print_register_hexadecimal(REG_A0);
}

void print_ecall_after() {
  print((uint64_t*) " -> ");
  print_register_hexadecimal(REG_A0);
}

void do_ecall() {
  ic_ecall = ic_ecall + 1;

if (*(registers + REG_A7) == SYSCALL_SWITCH)
    if (symbolic) {
      printf1((uint64_t*) "%s: context switching during symbolic execution is unsupported\n", selfie_name);

      exit(EXITCODE_BADARGUMENTS);
    } else {
      pc = pc + INSTRUCTIONSIZE;

      implement_switch();
    }
  else
    // all system calls other than switch are handled by exception
    throw_exception(EXCEPTION_SYSCALL, 0);
}

void backtrack_ecall() {
  if (debug_symbolic) {
    printf1((uint64_t*) "%s: backtracking ecall ", selfie_name);
    print_symbolic_memory(tc);
  }

  if (get_trace_vaddr(tc) == 0) {
    // backtracking malloc
    if (get_program_break(current_context) == get_trace_a2(tc) + get_trace_a3(tc))
      set_program_break(current_context, get_trace_a2(tc));
    else {
      printf1((uint64_t*) "%s: malloc backtracking error at ", selfie_name);
      print_symbolic_memory(tc);
      printf4((uint64_t*) " with current program break %x unequal %x which is previous program break %x plus size %d\n",
        (uint64_t*) get_program_break(current_context),
        (uint64_t*) (get_trace_a2(tc) + get_trace_a3(tc)),
        (uint64_t*) get_trace_a2(tc),
        (uint64_t*) get_trace_a3(tc));

      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  } else {
    // backtracking read
    rcc = rcc + 1;
    store_virtual_memory(pt, get_trace_vaddr(tc), get_trace_tc(tc));
  }
  efree();
}

void print_data_line_number() {
  if (data_line_number != (uint64_t*) 0)
    printf1((uint64_t*) "(~%d)", (uint64_t*) *(data_line_number + (pc - code_length) / REGISTERSIZE));
}

void print_data_context(uint64_t data) {
  printf1((uint64_t*) "%x", (uint64_t*) pc);

  if (disassemble_verbose) {
    print_data_line_number();
    print((uint64_t*) ": ");
    print_hexadecimal(data, SIZEOFUINT64 * 2);
    print((uint64_t*) " ");
  } else
    print((uint64_t*) ": ");
}

void print_data(uint64_t data) {
  print_data_context(data);
  printf1((uint64_t*) ".quad %x", (uint64_t*) data);
}

// -----------------------------------------------------------------
// ------------------- SYMBOLIC EXECUTION ENGINE -------------------
// -----------------------------------------------------------------

void print_stype(uint64_t stype) {
  if (stype == CONCRETE_T)
    print_character('C');
  else if (stype == MSIID_T)
    print_character('M');
  else if (stype == ARRAY_T)
    print_character('A');
  else
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
}

void print_symbolic_register(uint64_t reg) {
  print_register_name(reg);
  print((uint64_t*) "=");
  printf1((uint64_t*) "{@%x", (uint64_t*) *(reg_vaddr + reg));
  if (*(reg_typ + reg))
    if (*(registers + reg) == *(reg_alpha2 + reg))
      printf1((uint64_t*) "(%d)}", (uint64_t*) *(registers + reg));
    else
      printf3((uint64_t*) "(%d,%d,%d)}", (uint64_t*) *(registers + reg), (uint64_t*) *(reg_alpha2 + reg), (uint64_t*) *(reg_alpha3 + reg));
  else if (*(registers + reg) == *(reg_alpha2 + reg))
    printf1((uint64_t*) "[%d]}", (uint64_t*) *(registers + reg));
  else
    printf3((uint64_t*) "[%d,%d,%d]}", (uint64_t*) *(registers + reg), (uint64_t*) *(reg_alpha2 + reg), (uint64_t*) *(reg_alpha3 + reg));
  if (*(reg_stc + reg) != 0) {
    printf1((uint64_t*) "::@%d", (uint64_t*) *(reg_stc + reg));
    printf5((uint64_t*) "<%d,%d,[%d,%d],%d>\n",
    (uint64_t*) *(reg_hasmn + reg),
    (uint64_t*) *(reg_expr + reg),
    (uint64_t*) *(reg_colos + reg),
    (uint64_t*) *(reg_coups + reg),
    (uint64_t*) *(reg_factor + reg));
  }
}

void print_symbolic_memory(uint64_t svc) {
  printf3((uint64_t*) "@%d{@%d@%x", (uint64_t*) svc, (uint64_t*) get_trace_tc(svc), (uint64_t*) get_trace_pc(svc));
  if (get_trace_pc(svc) >= entry_point)
    print_code_line_number_for_instruction(get_trace_pc(svc) - entry_point);
  if (get_trace_vaddr(svc) == 0) {
    printf3((uint64_t*) ";%x=%x=malloc(%d)}", (uint64_t*) get_trace_a1(svc), (uint64_t*) get_trace_a2(svc), (uint64_t*) get_trace_a3(svc));
    return;
  } else if (get_trace_vaddr(svc) < NUMBEROFREGISTERS)
    printf2((uint64_t*) ";%s=%d", get_register_name(get_trace_vaddr(svc)), (uint64_t*) get_trace_a1(svc));
  else
    printf2((uint64_t*) ";%x=%d", (uint64_t*) get_trace_vaddr(svc), (uint64_t*) get_trace_a1(svc));
  if (get_trace_type(svc))
    if (get_trace_a1(svc) == get_trace_a2(svc))
      printf1((uint64_t*) "(%d)}", (uint64_t*) get_trace_a1(svc));
    else
      printf3((uint64_t*) "(%d,%d,%d)}", (uint64_t*) get_trace_a1(svc), (uint64_t*) get_trace_a2(svc), (uint64_t*) get_trace_a3(svc));
  else if (get_trace_a1(svc) == get_trace_a2(svc))
    printf1((uint64_t*) "[%d]}", (uint64_t*) get_trace_a1(svc));
  else
    printf3((uint64_t*) "[%d,%d,%d]}", (uint64_t*) get_trace_a1(svc), (uint64_t*) get_trace_a2(svc), (uint64_t*) get_trace_a3(svc));
  if (get_trace_src(svc) != 0) {
    printf1((uint64_t*) "::@%d", (uint64_t*) get_trace_src(svc));
    if (get_trace_corr(svc) != (uint64_t) -1)
      printf5((uint64_t*) "<%d,%d,[%d,%d],%d>\n",
      (uint64_t*) *(hasmns + get_trace_corr(svc)),
      (uint64_t*) *(exprs + get_trace_corr(svc)),
      (uint64_t*) *(colos + get_trace_corr(svc)),
      (uint64_t*) *(coups + get_trace_corr(svc)),
      (uint64_t*) *(factors + get_trace_corr(svc)));
    else
      print((uint64_t*) "<==>\n");
  } else
    println();
}

void print_over_approx(uint64_t* which) {
  printf3((uint64_t*) "%s: : over-approximation applied in %s at %x\n", selfie_name, which, (uint64_t*) (pc - entry_point));
}

uint64_t print_on_diff(uint64_t lastPrint, uint64_t toPrint) {
  if (toPrint != lastPrint) {
    print((uint64_t*) ", ");
    print_integer(toPrint);
    return toPrint;
  }
  return lastPrint;
}
void print_msiid(uint64_t start, uint64_t end, uint64_t st) {
  print((uint64_t*) "<");
  print_integer(start);
  print((uint64_t*) ",");
  print_integer(end);
  print((uint64_t*) ",");
  print_integer(st);
  print((uint64_t*) ">");
}

void print_concrete_bounds(uint64_t start, uint64_t end, uint64_t step) {
  uint64_t correct_end;
  uint64_t max_value;
  uint64_t last_value;

  //is a valid abstract value
  if (is_erroneous(start, end, step)) {
      print((uint64_t*) "Abstract value incorrect! Correct one: ");
      correct_end = compute_upper_bound(start, step, end);
  } else
      correct_end = end;

  print((uint64_t*) "{");
  //start
  print_integer(start);
  last_value = start;

  //if crossing 0 (wrapped)
  if (start > end) {
    //start + step
    if (start + step > start)
      last_value = print_on_diff(start, start + step);

    max_value = compute_upper_bound(start, step, UINT64_MAX);

    last_value = print_on_diff(last_value, max_value);
    if (max_value + step < correct_end)
      last_value = print_on_diff(last_value, max_value + step); //min_value

      //end -s
    if (signed_less_than(correct_end - step, 0))
      last_value = print_on_diff(last_value, correct_end - step);
  } else {
    //start + step
    if (start + step < correct_end)
      if (correct_end != (uint64_t) -1)
        last_value = print_on_diff(start, start + step);

    //end -s
  if (correct_end - step > last_value)
    if (correct_end != 0)
      last_value = print_on_diff(last_value, correct_end - step);
  }

  //end
  last_value = print_on_diff(last_value, correct_end);
  print((uint64_t*) "}");
}

uint64_t is_erroneous(uint64_t start, uint64_t end, uint64_t step) {
  uint64_t imax;
  imax = (end - start) / step;
  return end != start + imax * step;
}

uint64_t compute_upper_bound(uint64_t start, uint64_t step, uint64_t max) {
  return start + ((max - start) / step) * step;
}

void print_unreachable(uint64_t* label, uint64_t unreachable_pc) {
  print((uint64_t*) "[LINE:");
  print_code_line_number_for_instruction(unreachable_pc - entry_point);
  print((uint64_t*) "] branch ");
  print_string(label);
  print((uint64_t*) " unreachable");
  println();
}

void print_trace() {
  uint64_t idx;
  idx = tc;

  printf1((uint64_t*) "Trace of length %d:\n", (uint64_t*) idx);
  while (idx != 0) {
    print_symbolic_memory(idx);
    idx = idx - 1;
  }
}

void print_src_list(uint64_t idx) {
  uint64_t jdx;
  jdx = idx;

  printf1((uint64_t*) "Source list of %d:\n", (uint64_t*) jdx);
  while(jdx != 0) {
    print_symbolic_memory(jdx);
    jdx = get_trace_src(jdx);
  }
}

uint64_t get_src_input(uint64_t idx) {
  uint64_t jdx;
  jdx = idx;
  while(jdx != 0){
    if (get_trace_src(jdx) == 0)
      return jdx;
    else
      jdx = get_trace_src(jdx);
  }
  return jdx;
}

uint64_t add_sub_condition(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2) {
  uint64_t c1;
  uint64_t c2;

  c1 = up1 - lo1;
  c2 = UINT64_MAX - (up2 - lo2);

  if (c1 <= c2)
    return 1;
  else
    return 0;
}

uint64_t mul_condition(uint64_t lo, uint64_t up, uint64_t k) {
  uint64_t c1;
  uint64_t c2;
  if (k == 0)
    return 0;

  c1 = up - lo;
  c2 = UINT64_MAX / k;

  if (c1 <= c2)
    return 0;

  return 1;
}

uint64_t gcd(uint64_t n1, uint64_t n2) {
  if (n1 == 0)
    return n2;

  return gcd(n2%n1, n1);
}

uint64_t remu_condition(uint64_t lo, uint64_t up, uint64_t k) {
  if (up - lo >= k - 1)
    return 2;
  else if (up/k - lo/k == 0)
    return 0;
  else
    return 1;
}

uint64_t stride_remu_condition(uint64_t lo, uint64_t up, uint64_t step, uint64_t k) {
  uint64_t lcm;
  lcm = (step * k) / gcd(step, k);

  if (up/k == lo/k)
    return 0;
  else if (up - lo >= lcm - step)
    return 2;
  else if (up/k == lo/k + 1)
    return 1;
  else
    return 10;
}

uint64_t is_power_of_two(uint64_t n) {
  uint64_t c;

  c = 0;
  while (c < CPUBITWIDTH) {
    if (n == two_to_the_power_of(c))
      return 1;
    c = c + 1;
  }
  return 0;

  // if (n == 0)
  //   return 0;
  // while (n != 1) {
  //   if (n%2 != 0)
  //     return 0;
  //   n = n/2;
  // }
  // return 1;
}

uint64_t is_symbolic_value(uint64_t type) {
  //assume singleton intervals translated into concrete values
  return type != CONCRETE_T;
}

uint64_t is_safe_address(uint64_t vaddr, uint64_t reg) {

  if (*(reg_typ + reg) == ARRAY_T) {
    if (vaddr < *(registers + reg))
      // memory access below start address of mallocated block
      return 0;
    else if (vaddr - *(registers + reg) >= *(reg_alpha2 + reg))
      // memory access above end address of mallocated block
      return 0;
    else
      return 1;
  } else if (*(registers + reg) == *(reg_alpha2 + reg))
    return 1;
  else {
    printf2((uint64_t*) "%s: detected unsupported symbolic access of memory interval at %x", selfie_name, (uint64_t*) pc);
    print_code_line_number_for_instruction(pc - entry_point);
    println();

    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

uint64_t load_symbolic_memory(uint64_t* pt, uint64_t vaddr) {
  uint64_t mrvc;

  // assert: vaddr is valid and mapped
  mrvc = load_virtual_memory(pt, vaddr);

  if (mrvc <= tc)
    return mrvc;
  else {
    printf4((uint64_t*) "%s: detected most recent value counter %d at vaddr %x greater than current trace counter %d\n", selfie_name, (uint64_t*) mrvc, (uint64_t*) vaddr, (uint64_t*) tc);

    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

uint64_t is_trace_space_available() {
  return tc + 1 < MAX_TRACE_LENGTH;
}

void ealloc() {
  tc = tc + 1;
}

void efree() {
  // assert: tc > 0
  tc = tc - 1;
}

void store_symbolic_memory(uint64_t* pt, uint64_t stc, uint64_t vaddr,  uint64_t type, uint64_t lo, uint64_t up, uint64_t step, uint64_t corr_id, uint64_t trb) {
  uint64_t mrvc;

  if (vaddr == 0)
    // tracking program break and size for malloc
    mrvc = 0;
  else if (vaddr < NUMBEROFREGISTERS)
    // tracking a register value for sltu
    mrvc = mrcc;
  else {
    // assert: vaddr is valid and mapped
    mrvc = load_symbolic_memory(pt, vaddr);

    if (stc == get_trace_src(mrvc))
      if (vaddr == get_trace_vaddr(mrvc))
        if (type == get_trace_type(mrvc))
          if (lo == get_trace_a1(mrvc))
            if (up == get_trace_a2(mrvc))
              if (step == get_trace_a3(mrvc))
                // prevent tracking identical updates
                return;
  }

  if (trb < mrvc) {
    // current value at vaddr does not need to be tracked,
    // just overwrite it in the trace
    set_trace_type(mrvc, type);
    set_trace_src(mrvc, stc);

    set_trace_a1(mrvc, lo);
    set_trace_a2(mrvc, up);
    set_trace_a3(mrvc, step);

    set_trace_corr(mrvc, corr_id);

    if (do_taint_flag) store_taint_memory(mrvc);

    // assert: vaddr == getTraceVaddr(mrvc)

    if (debug_symbolic) {
      printf1((uint64_t*) "%s: overwriting ", selfie_name);
      print_symbolic_memory(mrvc);
    }
  } else if (is_trace_space_available()) {
    // current value at vaddr is from before most recent branch,
    // track that value by creating a new trace event
    ealloc();

    set_trace_pc(tc, pc);
    set_trace_tc(tc, mrvc);

    set_trace_type(tc, type);

    set_trace_src(tc, stc);
    set_trace_vaddr(tc, vaddr);

    set_trace_a1(tc, lo);
    set_trace_a2(tc, up);
    set_trace_a3(tc, step);

    set_trace_corr(tc, corr_id);

    if (do_taint_flag) store_taint_memory(tc);

    if (vaddr < NUMBEROFREGISTERS) {
      if (vaddr > 0)
        // register tracking marks most recent constraint
        mrcc = tc;
    } else
      // assert: vaddr is valid and mapped
      store_virtual_memory(pt, vaddr, tc);

    if (debug_symbolic) {
      printf1((uint64_t*) "%s: storing ", selfie_name);
      print_symbolic_memory(tc);
    }
  } else
    throw_exception(EXCEPTION_MAXTRACE, 0);
}

void store_constrained_memory(uint64_t type, uint64_t stc, uint64_t vaddr, uint64_t lo, uint64_t up, uint64_t step, uint64_t trb) {
  uint64_t mrvc;

  if (vaddr >= get_program_break(current_context))
    if (vaddr < *(registers + REG_SP))
      // do not constrain free memory
      return;

  mrvc = load_virtual_memory(pt, vaddr);

  if (mrvc < trb) {
    // we do not support potentially aliased constrained memory
    printf1((uint64_t*) "%s: detected potentially aliased constrained memory\n", selfie_name);

    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }
  // always track constrained memory by using tc as most recent branch
  //assert to_store_taint set
  store_symbolic_memory(pt, stc, vaddr, type, lo, up, step, get_trace_corr(mrvc), tc);
}

void store_register_memory(uint64_t reg, uint64_t value) {
  // always track register memory by using tc as most recent branch
  if (do_taint_flag) set_taint_memory(*(reg_is_tainted + reg), *(reg_is_minuend + reg), *(reg_has_step + reg));
  store_symbolic_memory(pt, 0, reg, 0, value, value, 1, -1, tc);
}

uint64_t reverse_up_division(uint64_t up, uint64_t factor) {
  uint64_t tmp;
  tmp = up * factor;

  if (tmp + (factor - 1) < tmp)
    return -1;
  tmp = tmp + (factor - 1);

  if (tmp < up)
    return -1;
  return tmp;
}

void store_propagate_constraint(uint64_t typ, uint64_t stc, uint64_t vaddr, uint64_t lo, uint64_t up, uint64_t step, uint64_t trb) {
  uint64_t pcc;
  if (sdebug_propagate) {
    printf6((uint64_t*) "%s: store constrained memory at %x with <%d,%d,%d>::@%d\n", selfie_name, (uint64_t*) vaddr, (uint64_t*) lo, (uint64_t*) up, (uint64_t*) step, (uint64_t*) stc);
  }

  if (stc)  { //side effect constraining
    pcc = get_trace_corr(load_symbolic_memory(pt,vaddr));

    if (sdebug_propagate) {
      printf3((uint64_t*) "%s: but propagate before to @%d with correction @%d\n", selfie_name, (uint64_t*) stc, (uint64_t*) pcc);
    }

    //update first the sources (for stc fields)
    if (pcc != (uint64_t) -1) {//relational constraint with the source address
      fill_constraint_buffer(get_trace_src(stc), get_trace_vaddr(stc), get_trace_type(stc),
      *(hasmns + pcc), *(exprs + pcc), *(colos + pcc), *(coups + pcc), *(factors + pcc));

      constrain_memory(stc, get_trace_vaddr(stc), lo, up, trb);
    } else //otherwise equals
      store_propagate_constraint(typ, get_trace_src(stc), get_trace_vaddr(stc), lo, up, step, trb);

    //store current constraint with updated stc
    store_constrained_memory(typ, load_virtual_memory(pt, get_trace_vaddr(stc)), vaddr, lo, up, step, trb);
  } else
    store_constrained_memory(typ, stc, vaddr, lo, up, step, trb);
}

void fill_constraint_buffer(uint64_t stc, uint64_t vaddr, uint64_t t, uint64_t h, uint64_t exp, uint64_t col, uint64_t cou, uint64_t f) {
  buffer_stc  = stc;
  buffer_vaddr  = vaddr;
  buffer_typ    = t;
  buffer_hasmn  = h;
  buffer_expr   = exp;
  buffer_colo  = col;
  buffer_coup  = cou;
  buffer_factor = f;
}


//assert(constraint buffer filled)
void constrain_memory(uint64_t mrvc, uint64_t from,  uint64_t lo, uint64_t up, uint64_t trb) {
  uint64_t tmp;
  uint64_t highest;
  uint64_t lowest;

  // load trace counter of previous constraint
  if (buffer_vaddr >= get_program_break(current_context))
    if (buffer_vaddr < *(registers + REG_SP))
      // do not constrain free memory
      return;

  //corrections computation
  //additions / substractions
  if (buffer_hasmn) {       //one minuend
    //backward semantics:rs2 = rs1 - rd
    //undo substraction (a-d,b-c)
    tmp = lo;
    lo = buffer_colo - up;
    up = buffer_coup - tmp;
  } else {                        //no minuend
    lo = lo - buffer_colo;
    up = up - buffer_coup;
  }

  //one multiplication or division or modulo
  if (buffer_expr == MUL_T) {         //one multiplication

    lo = signed_division(lo, buffer_factor);
    up = signed_division(up, buffer_factor);

  } else if (buffer_expr == DIV_T) {  //one division
    lo = lo * buffer_factor;
    up = reverse_up_division(up, buffer_factor); //overflow

    //special case
    if (lo == 0) {
      if (up == (uint64_t) -1) {
        lo = get_trace_a1(mrvc);
        up = get_trace_a2(mrvc);
        return;
      }
    }

    if (get_trace_a1(mrvc) <= get_trace_a2(mrvc)) {
      // original interval not wrapped around
      if (lo <= get_trace_a1(mrvc))  // intersect with the lower original interval
        lo = get_trace_a1(mrvc);
      else
        lo = compute_upper_bound(get_trace_a1(mrvc), get_trace_a3(mrvc), lo); // fitting the steps
      if (get_trace_a2(mrvc) < up) // intersect with the upper original interval
        up = compute_upper_bound(lo, get_trace_a3(mrvc), get_trace_a2(mrvc)); // fitting the steps
      else
        up = compute_upper_bound(lo, get_trace_a3(mrvc), up);
  } else {
    //original interval wrapped around
    //bound values
    highest = compute_upper_bound(get_trace_a1(mrvc), get_trace_a3(mrvc), -1);
    lowest = highest + get_trace_a3(mrvc);

    if (lo <= get_trace_a2(mrvc)) {
      //intersect with the lower original interval
      lo = compute_upper_bound(lowest, get_trace_a3(mrvc), lo + get_trace_a3(mrvc) - 1); // fitting the steps

      if (up < get_trace_a1(mrvc)) {

        if (up >= get_trace_a2(mrvc))
          up = get_trace_a2(mrvc);
        else
          up = compute_upper_bound(lo, get_trace_a3(mrvc), up);

      } else {
        //not allowed constrained result is not an interval
        //should be -----| sltu |-----
        printf2((uint64_t*) "%s: detected a divu of bad wrapped interval at %x", selfie_name, (uint64_t*) pc);
        print_code_line_number_for_instruction(pc - entry_point);
        println();

        throw_exception(EXCEPTION_INCOMPLETENESS, 0); //never in selfie
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }
    } else {
      // intersect with the upper original interval
      up = compute_upper_bound(get_trace_a1(mrvc), get_trace_a3(mrvc), up);

      if (lo <= get_trace_a1(mrvc))
        lo = get_trace_a1(mrvc);
      else
        lo = compute_upper_bound(get_trace_a1(mrvc), get_trace_a3(mrvc), lo + get_trace_a3(mrvc) - 1); // fitting the steps
      }
    }
  } else if (buffer_expr == REM_T) {  //one remainder

    printf2((uint64_t*) "%s: detected a remu in a condition at %x", selfie_name, (uint64_t*) pc);
    print_code_line_number_for_instruction(pc - entry_point);
    println();

    throw_exception(EXCEPTION_INCOMPLETENESS, 0); //never in selfie
    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    return;
  }

  if(do_taint_flag)
    if (from < NUMBEROFREGISTERS)
      set_taint_memory(*(reg_is_tainted + from), *(reg_is_minuend + from), *(reg_has_step + from));

  //cast singleton intervals into concrete values
  if (lo == up)
    store_propagate_constraint(CONCRETE_T, buffer_stc, buffer_vaddr, lo, up, 1, trb);
  else
    store_propagate_constraint(buffer_typ, buffer_stc, buffer_vaddr, lo, up, get_trace_a3(mrvc), trb);

  if (sdebug_trace) {
    printf2((uint64_t*) "%s: constrain-memory at %d", selfie_name, (uint64_t*) pc);
    print_code_line_number_for_instruction(pc - entry_point);
    if (from < NUMBEROFREGISTERS)
      printf1((uint64_t*) " for register ", get_register_name(from));
    else
      printf1((uint64_t*) " for memory address %x ", (uint64_t*) from);
    print_symbolic_memory(tc);
  }
}

void set_constraint(uint64_t reg, uint64_t stc, uint64_t vaddr, uint64_t start, uint64_t end, uint64_t step) {
  *(reg_stc + reg) = stc;
  *(reg_vaddr + reg) = vaddr;
  *(registers + reg) = start;
  *(reg_alpha2 + reg) = end;
  *(reg_alpha3 + reg) = step;
}

void set_correction(uint64_t reg, uint64_t hasmn, uint64_t expr, uint64_t colos, uint64_t coups, uint64_t operand) {
  *(reg_hasmn + reg)  = hasmn;
  *(reg_expr + reg)   = expr;
  *(reg_colos + reg)  = colos;
  *(reg_coups + reg)  = coups;
  *(reg_factor + reg) = operand;
}

void take_branch(uint64_t b, uint64_t how_many_more) {
  if (how_many_more > 0) {
    // record that we need to set rd to true
    store_register_memory(rd, b);

    // record frame and stack pointer
    store_register_memory(REG_FP, *(registers + REG_FP));
    store_register_memory(REG_SP, *(registers + REG_SP));
  } else {
    *(registers + rd) = b;

    *(reg_typ + rd) =  0;
    set_correction(rd, 0, 0, 0, 0, 0);
    set_constraint(rd, 0, 0, b, b, 1);
  }
}

void apply_correction(uint64_t reg, uint64_t mrvc, uint64_t lo, uint64_t up, uint64_t trb) {
  if (*(reg_typ + reg) == MSIID_T) {
    fill_constraint_buffer(*(reg_stc + reg), *(reg_vaddr + reg), *(reg_typ + reg), *(reg_hasmn + reg), *(reg_expr + reg),*(reg_colos + reg), *(reg_coups + reg), *(reg_factor + reg));
    constrain_memory(mrvc, reg, lo, up, trb);
  }
  //concrete case
  if (no_concrete)
    print_branch = 0;
}

// assert(isErroneous(lo1, up1, s1) == 0);
// assert(isErroneous(lo2, up2, s2) == 0);
void create_constraints(uint64_t lo1, uint64_t up1, uint64_t s1, uint64_t lo2, uint64_t up2, uint64_t s2, uint64_t trb, uint64_t how_many_more) {
  uint64_t lo1_2;
  uint64_t up1_2;

  if (lo1 <= up1) {
    // rs1 interval is not wrapped around
    if (lo2 <= up2) {
      // both rs1 and rs2 intervals are not wrapped around
      if (up1 < lo2) {
        // rs1 interval is strictly less than rs2 interval

        apply_correction(rs1, mrvc_rs1, lo1, up1, trb);
        apply_correction(rs2, mrvc_rs2, lo2, up2, trb);
        has_true_branch = 1;

        take_branch(1, how_many_more);
      } else if (up2 <= lo1) {
        // rs2 interval is less than or equal to rs1 interval

        apply_correction(rs1, mrvc_rs1, lo1, up1, trb);
        apply_correction(rs2, mrvc_rs2, lo2, up2, trb);
        has_false_branch = 1;

        take_branch(0, how_many_more);
      } else if (lo2 == up2) {
        // rs2 interval is a singleton

        // rounded values of resulting rs1 values
        up1_2 = compute_upper_bound(lo1, s1, lo2 - 1);
        lo1_2 = up1_2 + s1;

        // [false]  rs1:[ |lo2| , up1, s1 ] >= rs2:[ lo2, up2, s2 ]
        // [true]   rs1:[ lo1, |lo2 - 1|, s1 ] < rs2:[ lo2, up2, s2 ]

        // construct constraint for false case
        apply_correction(rs1, mrvc_rs1, lo1_2, up1, trb);
        apply_correction(rs2, mrvc_rs2, lo2, up2, trb);
        has_false_branch = 1;

        // record that we need to set rd to false
        store_register_memory(rd, 0);

        // record frame and stack pointer
        store_register_memory(REG_FP, *(registers + REG_FP));
        store_register_memory(REG_SP, *(registers + REG_SP));

        // construct constraint for true case
        apply_correction(rs1, mrvc_rs1, lo1, up1_2, trb);
        apply_correction(rs2, mrvc_rs2, lo2, up2, trb);
        has_true_branch = 1;

        take_branch(1, how_many_more);
      } else if (lo1 == up1) {
        // rs1 interval is a singleton

        // rounded values of resulting rs1 values
        up1_2 = compute_upper_bound(lo2, s2, lo1);
        lo1_2 = up1_2 + s2;

        // [false]  rs1:[ lo1, up1, s1 ] >= rs2:[ lo2, |lo1|, s2 ]
        // [true]   rs1:[ lo1, up1, s1 ] < rs2:[ |lo1 + 1|, up2, s2 ]

        // construct constraint for false case
        apply_correction(rs1, mrvc_rs1, lo1, up1, trb);
        apply_correction(rs2, mrvc_rs2, lo2, up1_2, trb);
        has_false_branch = 1;

        // record that we need to set rd to false
        store_register_memory(rd, 0);

        // record frame and stack pointer
        store_register_memory(REG_FP, *(registers + REG_FP));
        store_register_memory(REG_SP, *(registers + REG_SP));

        // construct constraint for true case
        apply_correction(rs1, mrvc_rs1, lo1, up1, trb);
        apply_correction(rs2, mrvc_rs2, lo1_2, up2, trb);
        has_true_branch = 1;

        take_branch(1, how_many_more);
      } else {
        // we cannot handle non-singleton interval intersections in comparison
        printf1((uint64_t*) "%s: detected non-singleton interval intersection\n", selfie_name);

        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }
    } else {
      // rs1 interval is not wrapped around but rs2 is

      up1_2 = compute_upper_bound(lo2, s2, UINT64_MAX);
      lo1_2 = up1_2 + s2;

      // unwrap rs2 interval and use higher portion first
      create_constraints(lo1, up1, s1, lo2, up1_2, s2, trb, 1);

      // then use lower portion of rs2 interval
      create_constraints(lo1, up1, s1, lo1_2, up2, s2, trb, 0);
    }
  } else if (lo2 <= up2) {
    // rs2 interval is not wrapped around but rs1 is

    up1_2 = compute_upper_bound(lo1, s1, UINT64_MAX);
    lo1_2 = up1_2 + s1;

    // unwrap rs1 interval and use higher portion first
    create_constraints(lo1, up1_2, s1, lo2, up2, s2, trb, 1);

    // then use lower portion of rs1 interval
    create_constraints(lo1_2, up1, s1, lo2, up2, s2, trb, 0);
  } else {
    // both rs1 and rs2 intervals are wrapped around
    print(selfie_name);
    print((uint64_t*) ": detected two wrap interval in sltu");
    println();

    throw_exception(EXCEPTION_INCOMPLETENESS, 0); //never in selfie

    // unwrap rs1 and rs2 intervals and use higher portions
    create_constraints(lo1, UINT64_MAX, s1, lo2, UINT64_MAX, s2, trb, 3);

    // use higher portion of rs1 interval and lower portion of rs2 interval
    create_constraints(lo1, UINT64_MAX, s1, 0, up2, s2, trb, 2);

    // use lower portions of rs1 and rs2 intervals
    create_constraints(0, up1, s1, 0, up2, s2, trb, 1);

    // use lower portion of rs1 interval and higher portion of rs2 interval
    create_constraints(0, up1, s1, lo2, UINT64_MAX, s2, trb, 0);
  }
}

uint64_t fuzz_lo(uint64_t value) {
  if (fuzz >= CPUBITWIDTH)
    return 0;
  else if (value > (two_to_the_power_of(fuzz) - 1) / 2)
    return value - (two_to_the_power_of(fuzz) - 1) / 2;
  else
    return 0;
}

uint64_t fuzz_up(uint64_t value) {
  if (fuzz >= CPUBITWIDTH)
    return UINT64_MAX;
  else if (UINT64_MAX - value < two_to_the_power_of(fuzz) / 2)
    return UINT64_MAX;
  else if (value > (two_to_the_power_of(fuzz) - 1) / 2)
    return value + two_to_the_power_of(fuzz) / 2;
  else
    return two_to_the_power_of(fuzz) - 1;
}

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void print_register_hexadecimal(uint64_t reg) {
  printf2((uint64_t*) "%s=%x", get_register_name(reg), (uint64_t*) *(registers + reg));
}

void print_register_octal(uint64_t reg) {
  printf2((uint64_t*) "%s=%o", get_register_name(reg), (uint64_t*) *(registers + reg));
}

uint64_t is_system_register(uint64_t reg) {
  if (reg == REG_GP)
    return 1;
  else if (reg == REG_FP)
    return 1;
  else if (reg == REG_RA)
    return 1;
  else if (reg == REG_SP)
    return 1;
  else
    return 0;
}

void print_register_value(uint64_t reg) {
  if (symbolic)
   if (*(reg_typ + reg) != CONCRETE_T) {
    print_symbolic_register(reg);
    return;
  }
  if (is_system_register(reg))
    print_register_hexadecimal(reg);
  else
    printf3((uint64_t*) "%s=%d(%x)", get_register_name(reg), (uint64_t*) *(registers + reg), (uint64_t*) *(registers + reg));
}

void print_exception(uint64_t exception, uint64_t faulting_page) {
  print((uint64_t*) *(EXCEPTIONS + exception));

  if (exception == EXCEPTION_PAGEFAULT)
    printf1((uint64_t*) " at %p", (uint64_t*) faulting_page);
}

void throw_exception(uint64_t exception, uint64_t faulting_page) {
  if (get_exception(current_context) != EXCEPTION_NOEXCEPTION)
    if (get_exception(current_context) != exception) {
      printf2((uint64_t*) "%s: context %p throws ", selfie_name, current_context);
      print_exception(exception, faulting_page);
      print((uint64_t*) " exception in presence of ");
      print_exception(get_exception(current_context), get_faulting_page(current_context));
      print((uint64_t*) " exception\n");

      exit(EXITCODE_MULTIPLEEXCEPTIONERROR);
    }

  set_exception(current_context, exception);
  set_faulting_page(current_context, faulting_page);

  if (exception != EXCEPTION_SYSCALL)
    last_jal_from = pc; //for test line numbers

  trap = 1;

  if (debug_exception) {
    printf2((uint64_t*) "%s: context %p throws ", selfie_name, current_context);
    print_exception(exception, faulting_page);
    print((uint64_t*) " exception\n");
  }
}

void fetch() {
  // assert: is_valid_virtual_address(pc) == 1
  // assert: is_virtual_address_mapped(pt, pc) == 1

  if (pc % REGISTERSIZE == 0)
    ir = get_low_word(load_virtual_memory(pt, pc));
  else
    ir = get_high_word(load_virtual_memory(pt, pc - INSTRUCTIONSIZE));
}

void decode_execute() {
  opcode = get_opcode(ir);

  if (opcode == OP_IMM) {
    decode_i_format();

    if (funct3 == F3_ADDI) {
      if (debug) {
        if (disassemble) {
          print_addi();
          if (execute) {
            print_addi_before();
            do_addi();
            print_addi_add_sub_mul_divu_remu_sltu_after();
          }
          println();
        } else if (symbolic) {
          if (debug_symbolic) {
            print_addi();
            print_addi_before();
            constrain_addi();
            print_addi_add_sub_mul_divu_remu_sltu_after();
            println();
          } else
            constrain_addi();
        }
      } else
        do_addi();

      return;
    }
  } else if (opcode == OP_LD) {
    decode_i_format();

    if (funct3 == F3_LD) {
      if (debug) {
        if (disassemble) {
          print_ld();
          if (execute) {
            print_ld_before();
            print_ld_after(do_ld());
          }
          println();
        } else if (symbolic) {
          if (debug_symbolic) {
            print_ld();
            print_ld_before();
            print_ld_after(constrain_ld());
            println();
          } else
            constrain_ld();
        }
      } else
        do_ld();

      return;
    }
  } else if (opcode == OP_SD) {
    decode_s_format();

    if (funct3 == F3_SD) {
      if (debug) {
        if (disassemble) {
          print_sd();
          if (execute) {
            print_sd_before();
            print_sd_after(do_sd());
          }
          println();
        } else if (symbolic) {
          if (debug_symbolic) {
            print_sd();
            print_sd_before();
            println();
            print_sd_after(constrain_sd());
            println();
          } else
            constrain_sd();
          } else if (backtrack)
            backtrack_sd();
      } else
        do_sd();

      return;
    }
  } else if (opcode == OP_OP) { // could be ADD, SUB, MUL, DIVU, REMU, SLTU
    decode_r_format();

    if (funct3 == F3_ADD) { // = F3_SUB = F3_MUL
      if (funct7 == F7_ADD) {
        if (debug) {
          if (disassemble) {
            print_add_sub_mul_divu_remu_sltu((uint64_t*) "add");
            if (execute) {
              print_add_sub_mul_divu_remu_sltu_before();
              do_add();
              print_addi_add_sub_mul_divu_remu_sltu_after();
            }
            println();
          } else if (symbolic) {
            if (debug_symbolic) {
              print_add_sub_mul_divu_remu_sltu((uint64_t*) "add");
              print_add_sub_mul_divu_remu_sltu_before();
              constrain_add();
              print_addi_add_sub_mul_divu_remu_sltu_after();
              println();
            } else
              constrain_add();
          }
        } else
          do_add();

        return;
      } else if (funct7 == F7_SUB) {
        if (debug) {
          if (disassemble) {
            print_add_sub_mul_divu_remu_sltu((uint64_t*) "sub");
            if (execute) {
              print_add_sub_mul_divu_remu_sltu_before();
              do_sub();
              print_addi_add_sub_mul_divu_remu_sltu_after();
            }
            println();
          } else if (symbolic) {
            if (debug_symbolic) {
              print_add_sub_mul_divu_remu_sltu((uint64_t*) "sub");
              print_add_sub_mul_divu_remu_sltu_before();
              constrain_sub();
              print_addi_add_sub_mul_divu_remu_sltu_after();
              println();
            } else
              constrain_sub();
          }
        } else
          do_sub();

        return;
      } else if (funct7 == F7_MUL) {
        if (debug) {
          if (disassemble) {
            print_add_sub_mul_divu_remu_sltu((uint64_t*) "mul");
            if (execute) {
              print_add_sub_mul_divu_remu_sltu_before();
              do_mul();
              print_addi_add_sub_mul_divu_remu_sltu_after();
            }
            println();
          } else if (symbolic) {
            if (debug_symbolic) {
              print_add_sub_mul_divu_remu_sltu((uint64_t*) "mul");
              print_add_sub_mul_divu_remu_sltu_before();
              constrain_mul();
              print_addi_add_sub_mul_divu_remu_sltu_after();
              println();
            } else
              constrain_mul();
          }
        } else
          do_mul();

        return;
      }
    } else if (funct3 == F3_DIVU) {
      if (funct7 == F7_DIVU) {
        if (debug) {
          if (disassemble) {
            print_add_sub_mul_divu_remu_sltu((uint64_t*) "divu");
            if (execute) {
              print_add_sub_mul_divu_remu_sltu_before();
              do_divu();
              print_addi_add_sub_mul_divu_remu_sltu_after();
            }
            println();
          } else if (symbolic) {
            if (debug_symbolic) {
              print_add_sub_mul_divu_remu_sltu((uint64_t*) "divu");
              print_add_sub_mul_divu_remu_sltu_before();
              constrain_divu();
              print_addi_add_sub_mul_divu_remu_sltu_after();
              println();
            } else
              constrain_divu();
          }
        } else
          do_divu();

        return;
      }
    } else if (funct3 == F3_REMU) {
      if (funct7 == F7_REMU) {
        if (debug) {
          if (disassemble) {
            print_add_sub_mul_divu_remu_sltu((uint64_t*) "remu");
            if (execute) {
              print_add_sub_mul_divu_remu_sltu_before();
              do_remu();
              print_addi_add_sub_mul_divu_remu_sltu_after();
            }
            println();
          } else if (symbolic) {
            if (debug_symbolic) {
              print_add_sub_mul_divu_remu_sltu((uint64_t*) "remu");
              print_add_sub_mul_divu_remu_sltu_before();
              constrain_remu();
              print_addi_add_sub_mul_divu_remu_sltu_after();
              println();
            } else
              constrain_remu();
          }
        } else
          do_remu();

        return;
      }
    } else if (funct3 == F3_SLTU) {
      if (funct7 == F7_SLTU) {
        if (debug) {
          if (disassemble) {
            print_add_sub_mul_divu_remu_sltu((uint64_t*) "sltu");
            if (execute) {
              print_add_sub_mul_divu_remu_sltu_before();
              do_sltu();
              print_addi_add_sub_mul_divu_remu_sltu_after();
            }
            println();
          } else if (symbolic) {
            if (debug_symbolic) {
              print_add_sub_mul_divu_remu_sltu((uint64_t*) "sltu");
              print_add_sub_mul_divu_remu_sltu_before();
              constrain_sltu();
              print_addi_add_sub_mul_divu_remu_sltu_after();
              println();
            } else
              constrain_sltu();
            } else if (backtrack)
              backtrack_sltu();
        } else
          do_sltu();

        return;
      }
    }
  } else if (opcode == OP_BRANCH) {
    decode_b_format();

    if (funct3 == F3_BEQ) {
      if (debug) {
        if (disassemble) {
          print_beq();
          if (execute) {
            print_beq_before();
            do_beq();
            print_beq_after();
          }
          println();
        } else if (symbolic) {
          if (debug_symbolic) {
            print_beq();
            print_beq_before();
            do_beq();
            print_beq_after();
            println();
          } else
            do_beq();
        }
      } else
        do_beq();

      return;
    }
  } else if (opcode == OP_JAL) {
    decode_j_format();

    if (debug) {
      if (disassemble) {
        print_jal();
        if (execute) {
          print_jal_before();
          do_jal();
          print_jal_jalr_after();
        }
        println();
      } else if (symbolic) {
        if (debug_symbolic) {
          print_jal();
          print_jal_before();
          do_jal();
          constrain_jal_jalr();
          print_jal_jalr_after();
          println();
        } else {
          do_jal();
          constrain_jal_jalr();
       }
      }
    } else
      do_jal();

    return;
  } else if (opcode == OP_JALR) {
    decode_i_format();

    if (funct3 == F3_JALR) {
      if (debug) {
        if (disassemble) {
          print_jalr();
          if (execute) {
            print_jalr_before();
            do_jalr();
            print_jal_jalr_after();
          }
          println();
        } else if (symbolic) {
          if (debug_symbolic) {
            print_jalr();
            print_jalr_before();
            do_jalr();
            constrain_jal_jalr();
            print_jal_jalr_after();
            println();
          } else {
            do_jalr();
            constrain_jal_jalr();
         }
        }
      } else
        do_jalr();

      return;
    }
  } else if (opcode == OP_LUI) {
    decode_u_format();

    if (debug) {
      if (disassemble) {
        print_lui();
        if (execute) {
          print_lui_before();
          do_lui();
          print_lui_after();
        }
        println();
      } else if (symbolic) {
        if (debug_symbolic) {
          print_lui();
          print_lui_before();
          constrain_lui();
          print_lui_after();
          println();
        } else
          constrain_lui();
      }
    } else
      do_lui();

    return;
  } else if (opcode == OP_SYSTEM) {
    decode_i_format();

    if (funct3 == F3_ECALL) {
      if (debug) {
        if (disassemble) {
          print_ecall();
          if (execute)
            do_ecall();
          else
            println();
        } else if (symbolic) {
          if (debug_symbolic) {
            print_ecall();
            print_ecall_before();
            do_ecall();
            print_ecall_after();
            println();
          } else
            do_ecall();
        } else if (backtrack)
          backtrack_ecall();
      } else
        do_ecall();

      return;
    }
  }

  if (execute)
    throw_exception(EXCEPTION_UNKNOWNINSTRUCTION, 0);
  else {
    //report the error on the console
    output_fd = 1;

    printf2((uint64_t*) "%s: unknown instruction with %x opcode detected\n", selfie_name, (uint64_t*) opcode);

    exit(EXITCODE_UNKNOWNINSTRUCTION);
  }
}

void interrupt() {
  if (timer != TIMEROFF) {
    timer = timer - 1;

    if (timer == 0) {
      if (get_exception(current_context) == EXCEPTION_NOEXCEPTION)
        // only throw exception if no other is pending
        // TODO: handle multiple pending exceptions
        throw_exception(EXCEPTION_TIMER, 0);
      else
        // trigger timer in the next interrupt cycle
        timer = 1;
    }
  }
}

uint64_t* run_until_exception() {
  trap = 0;

  while (trap == 0) {
    fetch();
    decode_execute();
    interrupt();
  }

  trap = 0;

  return current_context;
}

uint64_t instruction_with_max_counter(uint64_t* counters, uint64_t max) {
  uint64_t a;
  uint64_t n;
  uint64_t i;
  uint64_t c;

  a = UINT64_MAX;

  n = 0;
  i = 0;

  while (i < code_length / INSTRUCTIONSIZE) {
    c = *(counters + i);

    if (n < c) {
      if (c < max) {
        n = c;
        a = i;
      } else
        return i * INSTRUCTIONSIZE;
    }

    i = i + 1;
  }

  if (a != UINT64_MAX)
    return a * INSTRUCTIONSIZE;
  else
    return UINT64_MAX;
}

uint64_t print_per_instruction_counter(uint64_t total, uint64_t* counters, uint64_t max) {
  uint64_t a;
  uint64_t c;

  a = instruction_with_max_counter(counters, max);

  if (a != UINT64_MAX) {
    c = *(counters + a / INSTRUCTIONSIZE);

    // CAUTION: we reset counter to avoid reporting it again
    *(counters + a / INSTRUCTIONSIZE) = 0;

    printf3((uint64_t*) ",%d(%.2d%%)@%x", (uint64_t*) c, (uint64_t*) fixed_point_percentage(fixed_point_ratio(total, c, 4), 4), (uint64_t*) a);
    print_code_line_number_for_instruction(a);

    return c;
  } else {
    print((uint64_t*) ",0(0.00%)");

    return 0;
  }
}

void print_per_instruction_profile(uint64_t* message, uint64_t total, uint64_t* counters) {
  printf3((uint64_t*) "%s%s%d", selfie_name, message, (uint64_t*) total);
  print_per_instruction_counter(total, counters, print_per_instruction_counter(total, counters, print_per_instruction_counter(total, counters, UINT64_MAX)));
  println();
}

void print_profile() {
  printf4((uint64_t*)
    "%s: summary: %d executed instructions and %.2dMB(%.2d%%) mapped memory\n",
    selfie_name,
    (uint64_t*) get_total_number_of_instructions(),
    (uint64_t*) fixed_point_ratio(pused(), MEGABYTE, 2),
    (uint64_t*) fixed_point_percentage(fixed_point_ratio(page_frame_memory, pused(), 4), 4));

  if (get_total_number_of_instructions() > 0) {
    print_instruction_counters();

    if (code_line_number != (uint64_t*) 0)
      printf1((uint64_t*) "%s: profile: total,max(ratio%%)@addr(line#),2max,3max\n", selfie_name);
    else
      printf1((uint64_t*) "%s: profile: total,max(ratio%%)@addr,2max,3max\n", selfie_name);

    print_per_instruction_profile((uint64_t*) ": calls:   ", calls, calls_per_procedure);
    print_per_instruction_profile((uint64_t*) ": loops:   ", iterations, iterations_per_loop);
    print_per_instruction_profile((uint64_t*) ": loads:   ", ic_ld, loads_per_instruction);
    print_per_instruction_profile((uint64_t*) ": stores:  ", ic_sd, stores_per_instruction);
  }
}

void selfie_disassemble(uint64_t verbose) {
  uint64_t data;

  assembly_name = get_argument();

  if (code_length == 0) {
    printf2((uint64_t*) "%s: nothing to disassemble to output file %s\n", selfie_name, assembly_name);

    return;
  }

  // assert: assembly_name is mapped and not longer than MAX_FILENAME_LENGTH

  assembly_fd = open_write_only(assembly_name);

  if (signed_less_than(assembly_fd, 0)) {
    printf2((uint64_t*) "%s: could not create assembly output file %s\n", selfie_name, assembly_name);

    exit(EXITCODE_IOERROR);
  }

  output_name = assembly_name;
  output_fd   = assembly_fd;

  execute = 0;

  reset_library();
  reset_interpreter();

  debug               = 1;
  disassemble         = 1;
  disassemble_verbose = verbose;

  while (pc < code_length) {
    ir = load_instruction(pc);

    decode_execute();

    pc = pc + INSTRUCTIONSIZE;
  }

  while (pc < binary_length) {
    data = load_data(pc);

    print_data(data);
    println();

    pc = pc + REGISTERSIZE;
  }

  disassemble_verbose = 0;
  disassemble         = 0;
  debug               = 0;

  output_name = (uint64_t*) 0;
  output_fd   = 1;

  printf5((uint64_t*) "%s: %d characters of assembly with %d instructions and %d bytes of data written into %s\n", selfie_name,
    (uint64_t*) number_of_written_characters,
    (uint64_t*) (code_length / INSTRUCTIONSIZE),
    (uint64_t*) (binary_length - code_length),
    assembly_name);
}

// -----------------------------------------------------------------
// --------------------------TAINT ANALYSIS ------------------------
// -----------------------------------------------------------------

void taint_unop() {
  //steps
  *(reg_has_step + rd) = *(reg_has_step + rs1);

  //minuend
  if (*(reg_is_minuend + rs1))
    push_new_entry(pc - INSTRUCTIONSIZE - entry_point);

  *(reg_is_minuend + rd) = 0; //do not propagate minuend

  //taint
  if (*(reg_is_tainted + rs1)) {
    *(reg_is_tainted + rd) = 1;
    nb_addis = nb_addis + 1;
  }
  else  *(reg_is_tainted + rd) = 0;
}

void taint_binop(uint64_t op) {
  //steps
  if (ADD == op)       check_step();
  else if (SUB == op)  check_step();

  //minuend
  if (SLTU != op) {
    if (*(reg_is_minuend + rs1))      push_new_entry(pc - INSTRUCTIONSIZE - entry_point);
    else if (*(reg_is_minuend + rs2)) push_new_entry(pc - INSTRUCTIONSIZE - entry_point);
  }
  *(reg_is_minuend + rd) = 0; //reset minuend

  //taint
  if (*(reg_is_tainted + rs1)) {
    if (SLTU != op)
      *(reg_is_tainted + rd) = 1;

    if (*(reg_is_tainted + rs2)) {
      *(reg_is_tainted + rd) = 1;
      incr_opss(op);                              // operation with two symbolics
      step_opss(op);
      push_new_symbollic_entry(pc - INSTRUCTIONSIZE - entry_point);
      if (op == SUB) *(reg_is_minuend + rd) = 1;    //(source of correction problems)
    }
    else {
      incr_oprs1(op);         // only rs1 symbolic
      step_oprs1(op);
    }
  }
  else if (*(reg_is_tainted + rs2))  {                   // only rs2 symbolic
    *(reg_is_tainted + rd) = 1;
    incr_oprs2(op);
    step_oprs2(op);
    if (op == SUB) *(reg_is_minuend + rd) = 1;    //(source of correction problems)
  }
  else *(reg_is_tainted + rd) = 0;                        // concrete operation

  // check MUL with negative number
  check_signed_mul();
}

void check_signed_mul() {
  if (*(reg_is_tainted + rd))
  {
    if (*(reg_is_tainted + rs1)) {
      if (signed_less_than(get_trace_a1(rs2), 0))
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }
    else if (*(reg_is_tainted + rs2)) {
      if (signed_less_than(get_trace_a1(rs1), 0))
        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  }
}

void step_opss(uint64_t op) {
  if      (op == ADD)  *(reg_has_step + rd) = gcd(*(reg_has_step + rs1), *(reg_has_step + rs2));
  else if (op == SUB)  *(reg_has_step + rd) = gcd(*(reg_has_step + rs1), *(reg_has_step + rs2));
  else exit(EXITCODE_SYMBOLICEXECUTIONERROR);
}

void incr_opss(uint64_t op) {
  if      (op == ADD)  nb_addss = nb_addss + 1;
  else if (op == SUB)  nb_subss = nb_subss + 1;
  else if (op == MUL)  nb_mulss = nb_mulss + 1;
  else if (op == DIVU) nb_divuss = nb_divuss + 1;
  else if (op == REMU) nb_remuss = nb_remuss + 1;
  else                nb_sltuss = nb_sltuss + 1;
}

void step_oprs1(uint64_t op) {
  if      (op == ADD)  *(reg_has_step + rd) = *(reg_has_step + rs1);
  else if (op == SUB)  *(reg_has_step + rd) = *(reg_has_step + rs1);
  else if (op == MUL)  *(reg_has_step + rd) = *(reg_has_step + rs1) * *(registers + rs2);
  else if (op == DIVU) *(reg_has_step + rd) = *(reg_has_step + rs1) / *(registers + rs2);
  else if (op == REMU) *(reg_has_step + rd) = *(reg_has_step + rs1); //MOD?
}

void incr_oprs1(uint64_t op) {
  if      (op == ADD)  nb_addrs1 = nb_addrs1 + 1;
  else if (op == SUB)  nb_subrs1 = nb_subrs1 + 1;
  else if (op == MUL)  nb_mulrs1 = nb_mulrs1 + 1;
  else if (op == DIVU) nb_divurs1 = nb_divurs1 + 1;
  else if (op == REMU) nb_remurs1 = nb_remurs1 + 1;
  else                nb_slturs1 = nb_slturs1 + 1;
}

void step_oprs2(uint64_t op) {
  if      (op == ADD)  *(reg_has_step + rd) = *(reg_has_step + rs2);
  else if (op == SUB)  *(reg_has_step + rd) = *(reg_has_step + rs2);
  else if (op == MUL)  *(reg_has_step + rd) = *(reg_has_step + rs2) * *(registers + rs1);
  else if (op == DIVU) *(reg_has_step + rd) = *(reg_has_step + rs2) / *(registers + rs1);
  else if (op == REMU) *(reg_has_step + rd) = *(reg_has_step + rs2); //MOD?
}

void incr_oprs2(uint64_t op) {
  if      (op == ADD)  nb_addrs2 = nb_addrs2 + 1;
  else if (op == SUB)  nb_subrs2 = nb_subrs2 + 1;
  else if (op == MUL)  nb_mulrs2 = nb_mulrs2 + 1;
  else if (op == DIVU) nb_divurs2 = nb_divurs2 + 1;
  else if (op == REMU) nb_remurs2 = nb_remurs2 + 1;
  else                nb_slturs2 = nb_slturs2 + 1;
}

void check_step() {
  uint64_t vgcd;
  uint64_t imax;

  if (*(reg_has_step + rs1)) {
    if (*(reg_has_step + rs2)) {

      if (*(reg_has_step + rs1) != *(reg_has_step + rs2)) {
        vgcd = gcd(*(reg_has_step + rs1), *(reg_has_step + rs2));

          if (vgcd != *(reg_has_step + rs1)) {
            if (vgcd != *(reg_has_step + rs2))
              push_new_entry_step(pc - INSTRUCTIONSIZE - entry_point);
            else if (*(reg_alpha2 + rs2) < *(reg_alpha2 + rs1)) { // gcp == s2
              imax = (*(reg_alpha2 + rs2) - *(registers + rs2)) / *(reg_has_step + rs2);
              if (imax < *(reg_has_step + rs1)/vgcd - 1)
                push_new_entry_step(pc - INSTRUCTIONSIZE - entry_point);
            }
          }
          else if (*(reg_alpha2 + rs1) < *(reg_alpha2 + rs2)) {   // gcp == s1
            imax = (*(reg_alpha2 + rs1) - *(registers + rs1)) / *(reg_has_step + rs1);
            if (imax < *(reg_has_step + rs2)/vgcd - 1)
              push_new_entry_step(pc - INSTRUCTIONSIZE - entry_point);
         }
      }
    }
  }
}

void set_taint_memory(uint64_t is_taint, uint64_t is_minuend, uint64_t has_steps) {
  to_store_taint    = is_taint;
  to_store_minuend  = is_minuend;
  to_store_step  = has_steps;
}

void store_taint_memory(uint64_t offset) {
  *(taints + offset)    = to_store_taint;
  *(minuends + offset)  = to_store_minuend;
  *(has_steps + offset)  = to_store_step;
}

void push_new_entry(uint64_t hot_pc) {
  uint64_t i;
  i = 0;

  while(i < minuends_size) {
    if (hot_pc == *(minuends_pcs + i))
      return;
    i = i + 1;
  }
  *(minuends_pcs + minuends_size) = hot_pc;
  minuends_size = minuends_size + 1;
}

void push_new_entry_step(uint64_t hot_pc) {
  uint64_t i;
  i = 0;

  while(i < addsub_size) {
    if (hot_pc == *(addsub_incompleteness_pcs + i))
      return;
    i = i + 1;
  }
  *(addsub_incompleteness_pcs + addsub_size) = hot_pc;
  addsub_size = addsub_size + 1;
}

void push_new_symbollic_entry(uint64_t hot_pc) {
  uint64_t i;
  i = 0;

  if (both_symbolics_size == MAXPROBLEMATICINSTR)
    exit(EXITCODE_OUTOFTRACEMEMORY);

  while(i < both_symbolics_size) {
    if (hot_pc == *(both_symbolics_pcs + i))
      return;
    i = i + 1;
  }
  *(both_symbolics_pcs + both_symbolics_size) = hot_pc;
  both_symbolics_size = both_symbolics_size + 1;
}

void print_symbolic_counters() {
  println();
  print((uint64_t*)"Symbolic analysis sum-up: ");
  println();

  printf3((uint64_t*)"Total immediate additions: %d with %d (%.2d%%)\n",
  (uint64_t*) ic_addi,
  (uint64_t*) nb_addis,
  (uint64_t*) fixed_point_percentage(fixed_point_ratio(ic_addi, nb_addis, 4), 4));

  printf3((uint64_t*)"Total additions: %d with %d (%.2d%%)",
  (uint64_t*) ic_add,
  (uint64_t*) (nb_addrs1 + nb_addrs2 + nb_addss),
  (uint64_t*) fixed_point_percentage(fixed_point_ratio(ic_add, nb_addrs1 + nb_addrs2 + nb_addss, 4), 4));
  printf3((uint64_t*)" symbolic implications (rs1:%d, rs2:%d, both:%d)\n",
  (uint64_t*) nb_addrs1,
  (uint64_t*) nb_addrs2,
  (uint64_t*) nb_addss);

  printf3((uint64_t*)"Total subtractions: %d with %d (%.2d%%)",
  (uint64_t*) ic_sub,
  (uint64_t*) (nb_subrs1 + nb_subrs2 + nb_subss),
  (uint64_t*) fixed_point_percentage(fixed_point_ratio(ic_sub, nb_subrs1 + nb_subrs2 + nb_subss, 4), 4));
  printf3((uint64_t*)" symbolic implications (rs1:%d, rs2:%d, both:%d)\n",
  (uint64_t*) nb_subrs1,
  (uint64_t*) nb_subrs2,
  (uint64_t*) nb_subss);

  printf3((uint64_t*)"Total multiplications: %d with %d (%.2d%%)",
  (uint64_t*) ic_mul,
  (uint64_t*) (nb_mulrs1 + nb_mulrs2 + nb_mulss),
  (uint64_t*) fixed_point_percentage(fixed_point_ratio(ic_mul, nb_mulrs1 + nb_mulrs2 + nb_mulss, 4), 4));
  printf3((uint64_t*)" symbolic implications (rs1:%d, rs2:%d, both:%d)\n",
  (uint64_t*) nb_mulrs1,
  (uint64_t*) nb_mulrs2,
  (uint64_t*) nb_mulss);

  printf3((uint64_t*)"Total divisions: %d with %d (%.2d%%)",
  (uint64_t*) ic_divu,
  (uint64_t*) (nb_divurs1 + nb_divurs2 + nb_divuss),
  (uint64_t*) fixed_point_percentage(fixed_point_ratio(ic_divu, nb_divurs1 + nb_divurs2 + nb_divuss, 4), 4));
  printf3((uint64_t*)" symbolic implications (rs1:%d, rs2:%d, both:%d)\n",
  (uint64_t*) nb_divurs1,
  (uint64_t*) nb_divurs2,
  (uint64_t*) nb_divuss);

  printf3((uint64_t*)"Total remainders: %d with %d (%.2d%%)",
  (uint64_t*) ic_remu,
  (uint64_t*) (nb_remurs1 + nb_remurs2 + nb_remuss),
  (uint64_t*) fixed_point_percentage(fixed_point_ratio(ic_remu, nb_remurs1 + nb_remurs2 + nb_remuss, 4), 4));
  printf3((uint64_t*)" symbolic implications (rs1:%d, rs2:%d, both:%d)\n",
  (uint64_t*) nb_remurs1,
  (uint64_t*) nb_remurs2,
  (uint64_t*) nb_remuss);

  printf3((uint64_t*)"Total Set on Less Than Unsigneds: %d with %d (%.2d%%)",
  (uint64_t*) ic_sltu,
  (uint64_t*) (nb_slturs1 + nb_slturs2 + nb_sltuss),
  (uint64_t*) fixed_point_percentage(fixed_point_ratio(ic_sltu, nb_slturs1 + nb_slturs2 + nb_sltuss, 4), 4));
  printf3((uint64_t*)" symbolic implications (rs1:%d, rs2:%d, both:%d)\n",
  (uint64_t*) nb_slturs1,
  (uint64_t*) nb_slturs2,
  (uint64_t*) nb_sltuss);
}

void print_minuend_fails() {
  uint64_t i;
  i = 0;

  print((uint64_t*) "Instructions raising minuend problems: ");
  while(i < minuends_size) {
    print_hexadecimal(*(minuends_pcs + i), 0);
    print_code_line_number_for_instruction((uint64_t) *(minuends_pcs + i));
    print((uint64_t*) " ");

    i = i + 1;
  }
  print((uint64_t*) "(");
  print_integer(i);
  print((uint64_t*) " instruction(s))");
  println();
}

void print_incomplete_operations() {
  uint64_t i;
  i = 0;

  print((uint64_t*) "Instructions raising step (add and sub) problems: ");
  while(i < addsub_size) {
    print_hexadecimal(*(addsub_incompleteness_pcs + i), 0);
    print_code_line_number_for_instruction((uint64_t) *(addsub_incompleteness_pcs + i));
    print((uint64_t*) " ");

    i = i + 1;
  }
  print((uint64_t*) "(");
  print_integer(i);
  print((uint64_t*) " instruction(s))");
  println();
}

void print_both_symbolic() {
  uint64_t i;
  i = 0;

  print((uint64_t*) "Instructions (add and sub) with two symbolics: ");
  while(i < both_symbolics_size) {
    print_hexadecimal(*(both_symbolics_pcs + i), 0);
    print_code_line_number_for_instruction((uint64_t) *(both_symbolics_pcs + i));
    print((uint64_t*) " ");

    i = i + 1;
  }
  print((uint64_t*) "(");
  print_integer(i);
  print((uint64_t*) " instruction(s))");
  println();
}

// -----------------------------------------------------------------
// ---------------------------- CONTEXTS ---------------------------
// -----------------------------------------------------------------

uint64_t* allocate_context(uint64_t* parent, uint64_t* vctxt, uint64_t* in) {
  uint64_t* context;

  if (free_contexts == (uint64_t*) 0)
    if (symbolic)
      context = smalloc(7 * SIZEOFUINT64STAR + 11 * SIZEOFUINT64);
    else
      context = smalloc(7 * SIZEOFUINT64STAR + 9 * SIZEOFUINT64);
  else {
    context = free_contexts;

    free_contexts = get_next_context(free_contexts);
  }

  set_next_context(context, in);
  set_prev_context(context, (uint64_t*) 0);

  if (in != (uint64_t*) 0)
    set_prev_context(in, context);

  set_pc(context, 0);

  // allocate zeroed memory for general purpose registers
  // TODO: reuse memory
  set_regs(context, zalloc(NUMBEROFREGISTERS * REGISTERSIZE));

  // allocate zeroed memory for page table
  // TODO: save and reuse memory for page table
  set_pt(context, zalloc(VIRTUALMEMORYSIZE / PAGESIZE * REGISTERSIZE));

  // determine range of recently mapped pages
  set_lo_page(context, 0);
  set_me_page(context, 0);
  set_hi_page(context, get_page_of_virtual_address(VIRTUALMEMORYSIZE - REGISTERSIZE));

  set_exception(context, EXCEPTION_NOEXCEPTION);
  set_faulting_page(context, 0);

  set_exit_code(context, EXITCODE_NOERROR);

  set_parent(context, parent);
  set_virtual_context(context, vctxt);

  set_name(context, (uint64_t*) 0);

  return context;
}

uint64_t* find_context(uint64_t* parent, uint64_t* vctxt, uint64_t* in) {
  uint64_t* context;

  context = in;

  while (context != (uint64_t*) 0) {
    if (get_parent(context) == parent)
      if (get_virtual_context(context) == vctxt)
        return context;

    context = get_next_context(context);
  }

  return (uint64_t*) 0;
}

void free_context(uint64_t* context) {
  set_next_context(context, free_contexts);

  free_contexts = context;
}

uint64_t* delete_context(uint64_t* context, uint64_t* from) {
  if (get_next_context(context) != (uint64_t*) 0)
    set_prev_context(get_next_context(context), get_prev_context(context));

  if (get_prev_context(context) != (uint64_t*) 0) {
    set_next_context(get_prev_context(context), get_next_context(context));
    set_prev_context(context, (uint64_t*) 0);
  } else
    from = get_next_context(context);

  free_context(context);

  return from;
}

// -----------------------------------------------------------------
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

uint64_t* create_context(uint64_t* parent, uint64_t* vctxt) {
  // TODO: check if context already exists
  used_contexts = allocate_context(parent, vctxt, used_contexts);

  if (current_context == (uint64_t*) 0)
    current_context = used_contexts;

  if (debug_create)
    printf3((uint64_t*) "%s: parent context %p created child context %p\n", selfie_name, parent, used_contexts);

  return used_contexts;
}

uint64_t* cache_context(uint64_t* vctxt) {
  uint64_t* context;

  // find cached context on my boot level
  context = find_context(current_context, vctxt, used_contexts);

  if (context == (uint64_t*) 0)
    // create cached context on my boot level
    context = create_context(current_context, vctxt);

  return context;
}

void save_context(uint64_t* context) {
  uint64_t* parent_table;
  uint64_t* vctxt;
  uint64_t r;
  uint64_t* registers;
  uint64_t* vregisters;

  // save machine state
  set_pc(context, pc);

  if (get_parent(context) != MY_CONTEXT) {
    parent_table = get_pt(get_parent(context));

    vctxt = get_virtual_context(context);

    store_virtual_memory(parent_table, program_counter(vctxt), get_pc(context));

    r = 0;

    registers = get_regs(context);

    vregisters = (uint64_t*) load_virtual_memory(parent_table, regs(vctxt));

    while (r < NUMBEROFREGISTERS) {
      store_virtual_memory(parent_table, (uint64_t) (vregisters + r), *(registers + r));

      r = r + 1;
    }

    store_virtual_memory(parent_table, program_break(vctxt), get_program_break(context));

    store_virtual_memory(parent_table, exception(vctxt), get_exception(context));
    store_virtual_memory(parent_table, faulting_page(vctxt), get_faulting_page(context));
    store_virtual_memory(parent_table, exit_code(vctxt), get_exit_code(context));
  }
}

void map_page(uint64_t* context, uint64_t page, uint64_t frame) {
  uint64_t* table;

  table = get_pt(context);

  // assert: 0 <= page < VIRTUALMEMORYSIZE / PAGESIZE

  *(table + page) = frame;

  if (page <= get_page_of_virtual_address(get_program_break(context) - REGISTERSIZE)) {
    // exploit spatial locality in page table caching
    if (page < get_lo_page(context))
      set_lo_page(context, page);
    else if (page > get_me_page(context))
      set_me_page(context, page);
  }

  if (debug_map) {
    printf1((uint64_t*) "%s: page ", selfie_name);
    print_hexadecimal(page, 4);
    printf2((uint64_t*) " mapped to frame %p in context %p\n", (uint64_t*) frame, context);
  }
}

void restore_context(uint64_t* context) {
  uint64_t* parent_table;
  uint64_t* vctxt;
  uint64_t r;
  uint64_t* registers;
  uint64_t* vregisters;
  uint64_t* table;
  uint64_t page;
  uint64_t me;
  uint64_t frame;

  if (get_parent(context) != MY_CONTEXT) {
    parent_table = get_pt(get_parent(context));

    vctxt = get_virtual_context(context);

    set_pc(context, load_virtual_memory(parent_table, program_counter(vctxt)));

    r = 0;

    registers = get_regs(context);

    vregisters = (uint64_t*) load_virtual_memory(parent_table, regs(vctxt));

    while (r < NUMBEROFREGISTERS) {
      *(registers + r) = load_virtual_memory(parent_table, (uint64_t) (vregisters + r));

      r = r + 1;
    }

    set_program_break(context, load_virtual_memory(parent_table, program_break(vctxt)));

    set_exception(context, load_virtual_memory(parent_table, exception(vctxt)));
    set_faulting_page(context, load_virtual_memory(parent_table, faulting_page(vctxt)));
    set_exit_code(context, load_virtual_memory(parent_table, exit_code(vctxt)));

    table = (uint64_t*) load_virtual_memory(parent_table, page_table(vctxt));

    // assert: context page table is only mapped from beginning up and end down

    page = load_virtual_memory(parent_table, lo_page(vctxt));
    me   = load_virtual_memory(parent_table, me_page(vctxt));

    while (page <= me) {
      if (is_virtual_address_mapped(parent_table, frame_for_page(table, page))) {
        frame = load_virtual_memory(parent_table, frame_for_page(table, page));

        map_page(context, page, get_frame_for_page(parent_table, get_page_of_virtual_address(frame)));
      }

      page = page + 1;
    }

    store_virtual_memory(parent_table, lo_page(vctxt), page);

    page = load_virtual_memory(parent_table, hi_page(vctxt));

    if (is_virtual_address_mapped(parent_table, frame_for_page(table, page)))
      frame = load_virtual_memory(parent_table, frame_for_page(table, page));
    else
      frame = 0;

    while (frame != 0) {
      map_page(context, page, get_frame_for_page(parent_table, get_page_of_virtual_address(frame)));

      page  = page - 1;

      if (is_virtual_address_mapped(parent_table, frame_for_page(table, page)))
        frame = load_virtual_memory(parent_table, frame_for_page(table, page));
      else
        frame = 0;
    }

    store_virtual_memory(parent_table, hi_page(vctxt), page);
  }
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

uint64_t pavailable() {
  if (free_page_frame_memory > 0)
    return 1;
  else if (allocated_page_frame_memory + MEGABYTE <= page_frame_memory)
    return 1;
  else
    return 0;
}

uint64_t pexcess() {
  if (pavailable())
    return 1;
  else if (allocated_page_frame_memory + MEGABYTE <= 2 * page_frame_memory)
    // tolerate twice as much memory mapped on demand than physically available
    return 1;
  else
    return 0;
}

uint64_t pused() {
  return allocated_page_frame_memory - free_page_frame_memory;
}

uint64_t* palloc() {
  uint64_t block;
  uint64_t frame;

  // assert: page_frame_memory is equal to or a multiple of MEGABYTE
  // assert: PAGESIZE is a factor of MEGABYTE strictly less than MEGABYTE

  if (free_page_frame_memory == 0) {
    if (pexcess()) {
      free_page_frame_memory = MEGABYTE;

      // on boot level zero allocate zeroed memory
      block = (uint64_t) zalloc(free_page_frame_memory);

      allocated_page_frame_memory = allocated_page_frame_memory + free_page_frame_memory;

      // page frames must be page-aligned to work as page table index
      next_page_frame = round_up(block, PAGESIZE);

      if (next_page_frame > block)
        // losing one page frame to fragmentation
        free_page_frame_memory = free_page_frame_memory - PAGESIZE;
    } else {
      print(selfie_name);
      print((uint64_t*) ": palloc out of physical memory\n");

      exit(EXITCODE_OUTOFPHYSICALMEMORY);
    }
  }

  frame = next_page_frame;

  next_page_frame = next_page_frame + PAGESIZE;

  free_page_frame_memory = free_page_frame_memory - PAGESIZE;

  // strictly, touching is only necessary on boot levels higher than zero
  return touch((uint64_t*) frame, PAGESIZE);
}

void pfree(uint64_t* frame) {
  // TODO: implement free list of page frames
  frame = frame + 1;
}

void map_and_store(uint64_t* context, uint64_t vaddr, uint64_t data) {
  // assert: is_valid_virtual_address(vaddr) == 1

  if (is_virtual_address_mapped(get_pt(context), vaddr) == 0)
    map_page(context, get_page_of_virtual_address(vaddr), (uint64_t) palloc());

  if (symbolic) {
    if (is_trace_space_available()) {
      set_taint_memory(0, 0, 1);
      // always track initialized memory by using tc as most recent branch
      store_symbolic_memory(get_pt(context), 0, vaddr, CONCRETE_T, data, data, 1, -1, tc);
    }
    else {
      printf1((uint64_t*) "%s: ealloc out of memory\n", selfie_name);

      exit(EXITCODE_OUTOFTRACEMEMORY);
    }
  } else
    store_virtual_memory(get_pt(context), vaddr, data);
}

void up_load_binary(uint64_t* context) {
  uint64_t baddr;

  // assert: entry_point is multiple of PAGESIZE and REGISTERSIZE

  set_pc(context, entry_point);
  set_lo_page(context, get_page_of_virtual_address(entry_point));
  set_me_page(context, get_page_of_virtual_address(entry_point));
  set_original_break(context, entry_point + binary_length);
  set_program_break(context, get_original_break(context));

  baddr = 0;

  if (symbolic) {
    // code is never constrained...
    symbolic = 0;

    while (baddr < code_length) {
      map_and_store(context, entry_point + baddr, load_data(baddr));

      baddr = baddr + REGISTERSIZE;
    }

    // ... but data is
    symbolic = 1;
  }

  while (baddr < binary_length) {
    map_and_store(context, entry_point + baddr, load_data(baddr));

    baddr = baddr + REGISTERSIZE;
  }

  set_name(context, binary_name);
}

uint64_t up_load_string(uint64_t* context, uint64_t* s, uint64_t SP) {
  uint64_t bytes;
  uint64_t i;

  bytes = round_up(string_length(s) + 1, REGISTERSIZE);

  // allocate memory for storing string
  SP = SP - bytes;

  i = 0;

  while (i < bytes) {
    map_and_store(context, SP + i, *s);

    s = s + 1;

    i = i + REGISTERSIZE;
  }

  return SP;
}

void up_load_arguments(uint64_t* context, uint64_t argc, uint64_t* argv) {
  /* upload arguments like a UNIX system

      SP
      |
      V
   | argc | argv[0] | ... | argv[n] | 0 | env[0] | ... | env[m] | 0 |

     with argc > 0, n == argc - 1, and m == 0 (that is, env is empty) */
  uint64_t SP;
  uint64_t* vargv;
  uint64_t i;

  // the call stack grows top down
  SP = VIRTUALMEMORYSIZE;

  vargv = smalloc(argc * SIZEOFUINT64STAR);

  i = 0;

  // push program parameters onto the stack
  while (i < argc) {
    SP = up_load_string(context, (uint64_t*) *(argv + i), SP);

    // store pointer in virtual *argv
    *(vargv + i) = SP;

    i = i + 1;
  }

  // allocate memory for termination of env table
  SP = SP - REGISTERSIZE;

  // push null value to terminate env table
  map_and_store(context, SP, 0);

  // allocate memory for termination of argv table
  SP = SP - REGISTERSIZE;

  // push null value to terminate argv table
  map_and_store(context, SP, 0);

  // assert: i == argc

  // push argv table onto the stack
  while (i > 0) {
    // allocate memory for argv table entry
    SP = SP - REGISTERSIZE;

    i = i - 1;

    // push argv table entry
    map_and_store(context, SP, *(vargv + i));
  }

  // allocate memory for argc
  SP = SP - REGISTERSIZE;

  // push argc
  map_and_store(context, SP, argc);

  // store stack pointer value in stack pointer register
  *(get_regs(context) + REG_SP) = SP;

  // set bounds to register value for symbolic execution
  if (symbolic) {
    *(reg_typ + REG_SP) = CONCRETE_T;
    *(reg_alpha2 + REG_SP) = SP;
  }
}

uint64_t handle_system_call(uint64_t* context) {
  uint64_t a7;

  set_exception(context, EXCEPTION_NOEXCEPTION);

  a7 = *(get_regs(context) + REG_A7);

  if (a7 == SYSCALL_BRK)
    implement_brk(context);
  else if (a7 == SYSCALL_READ)
    implement_read(context);
  else if (a7 == SYSCALL_WRITE)
    implement_write(context);
  else if (a7 == SYSCALL_OPEN)
    implement_open(context);
  else if (a7 == SYSCALL_INPUT)
    implement_input(context);
  else if (a7 == SYSCALL_EXIT) {
    implement_exit(context);

    // TODO: exit only if all contexts have exited
    return EXIT;
  } else {
    printf2((uint64_t*) "%s: unknown system call %d\n", selfie_name, (uint64_t*) a7);

    set_exit_code(context, EXITCODE_UNKNOWNSYSCALL);

    return EXIT;
  }

  //after implement_syscall
  if (get_exception(context) == EXCEPTION_MAXTRACE) {
    // exiting during symbolic execution, no exit code necessary
    set_exception(context, EXCEPTION_NOEXCEPTION);

    return EXIT;
  } else
  return DONOTEXIT;
}

uint64_t handle_page_fault(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  // TODO: use this table to unmap and reuse frames
  map_page(context, get_faulting_page(context), (uint64_t) palloc());

  return DONOTEXIT;
}

uint64_t handle_division_by_zero(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  printf1((uint64_t*) "%s: division by zero\n", selfie_name);

  set_exit_code(context, EXITCODE_DIVISIONBYZERO);
  if (symbolic) {
    set_exit_code_a2(context, EXITCODE_DIVISIONBYZERO);
    set_exit_code_a3(context, 1);
  }

  return EXIT;
}

uint64_t handle_max_trace(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  printf1((uint64_t*) "%s: Max trace length reached\n", selfie_name);
  set_exit_code(context, EXITCODE_OUTOFTRACEMEMORY);
  if (symbolic) {
    set_exit_code_a2(context, EXITCODE_OUTOFTRACEMEMORY);
    set_exit_code_a3(context, 1);
  }

  return EXIT;
}

uint64_t handle_incompleteness(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  printf1((uint64_t*) "%s: incomplete case\n", selfie_name);
  set_exit_code(context, EXITCODE_INCOMPLETENESS);
  if (symbolic) {
    set_exit_code_a2(context, EXITCODE_INCOMPLETENESS);
    set_exit_code_a3(context, 1);
  }

  return EXIT;
}

uint64_t handle_timer(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  return DONOTEXIT;
}

uint64_t handle_exception(uint64_t* context) {
  uint64_t exception;

  exception = get_exception(context);

  if (exception == EXCEPTION_SYSCALL)
    return handle_system_call(context);
  else if (exception == EXCEPTION_PAGEFAULT)
    return handle_page_fault(context);
  else if (exception == EXCEPTION_DIVISIONBYZERO)
    return handle_division_by_zero(context);
  else if (exception == EXCEPTION_MAXTRACE)
    return handle_max_trace(context);
  else if (exception == EXCEPTION_INCOMPLETENESS)
    return handle_incompleteness(context);
  else if (exception == EXCEPTION_TIMER)
    return handle_timer(context);
  else {
    printf2((uint64_t*) "%s: context %s throws uncaught ", selfie_name, get_name(context));
    print_exception(exception, get_faulting_page(context));
    println();

    set_exit_code(context, EXITCODE_UNCAUGHTEXCEPTION);
    if (symbolic) {
      set_exit_code_a2(context, EXITCODE_UNCAUGHTEXCEPTION);
      set_exit_code_a3(context, 1);
    }

    return EXIT;
  }
}

uint64_t mipster(uint64_t* to_context) {
  uint64_t timeout;
  uint64_t* from_context;

  print((uint64_t*) "mipster\n");

  timeout = TIMESLICE;

  while (1) {
    from_context = mipster_switch(to_context, timeout);

    if (get_parent(from_context) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      to_context = get_parent(from_context);

      timeout = TIMEROFF;
    } else if (handle_exception(from_context) == EXIT)
      return get_exit_code(from_context);
    else {
      // TODO: scheduler should go here
      to_context = from_context;

      timeout = TIMESLICE;
    }
  }
}

uint64_t hypster(uint64_t* to_context) {
  uint64_t* from_context;

  print((uint64_t*) "hypster\n");

  while (1) {
    from_context = hypster_switch(to_context, TIMESLICE);

    if (handle_exception(from_context) == EXIT)
      return get_exit_code(from_context);
    else
      // TODO: scheduler should go here
      to_context = from_context;
  }
}

uint64_t mixter(uint64_t* to_context, uint64_t mix) {
  // works with mipsters and hypsters
  uint64_t mslice;
  uint64_t timeout;
  uint64_t* from_context;

  printf2((uint64_t*) "mixter (%d%% mipster/%d%% hypster)\n", (uint64_t*) mix, (uint64_t*) (100 - mix));

  mslice = TIMESLICE;

  if (mslice <= UINT64_MAX / 100)
    mslice = mslice * mix / 100;
  else if (mslice <= UINT64_MAX / 10)
    mslice = mslice / 10 * (mix / 10);
  else
    mslice = mslice / 100 * mix;

  if (mslice > 0) {
    mix = 1;

    timeout = mslice;
  } else {
    mix = 0;

    timeout = TIMESLICE;
  }

  while (1) {
    if (mix)
      from_context = mipster_switch(to_context, timeout);
    else
      from_context = hypster_switch(to_context, timeout);

    if (get_parent(from_context) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      to_context = get_parent(from_context);

      timeout = TIMEROFF;
    } else if (handle_exception(from_context) == EXIT)
      return get_exit_code(from_context);
    else {
      // TODO: scheduler should go here
      to_context = from_context;

      if (mix) {
        if (mslice != TIMESLICE) {
          mix = 0;

          timeout = TIMESLICE - mslice;
        }
      } else if (mslice > 0) {
        mix = 1;

        timeout = mslice;
      }
    }
  }
}

uint64_t minmob(uint64_t* to_context) {
  uint64_t timeout;
  uint64_t* from_context;

  timeout = TIMESLICE;

  while (1) {
    from_context = mipster_switch(to_context, timeout);

    if (get_parent(from_context) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      to_context = get_parent(from_context);

      timeout = TIMEROFF;
    } else {
      // minster and mobster do not handle page faults
      if (get_exception(from_context) == EXCEPTION_PAGEFAULT) {
        printf2((uint64_t*) "%s: context %s throws uncaught ", selfie_name, get_name(from_context));
        print_exception(get_exception(from_context), get_faulting_page(from_context));
        println();

        return EXITCODE_UNCAUGHTEXCEPTION;
      } else if (handle_exception(from_context) == EXIT)
        return get_exit_code(from_context);

      // TODO: scheduler should go here
      to_context = from_context;

      timeout = TIMESLICE;
    }
  }
}

void map_unmapped_pages(uint64_t* context) {
  uint64_t page;

  // assert: page table is only mapped from beginning up and end down

  page = get_lo_page(context);

  while (is_page_mapped(get_pt(context), page))
    page = page + 1;

  while (pavailable()) {
    map_page(context, page, (uint64_t) palloc());

    page = page + 1;
  }
}

uint64_t minster(uint64_t* to_context) {
  print((uint64_t*) "minster\n");

  // virtual is like physical memory in initial context up to memory size
  // by mapping unmapped pages (for the heap) to all available page frames
  // CAUTION: consumes memory even when not accessed
  map_unmapped_pages(to_context);

  // does not handle page faults, works only until running out of mapped pages
  return minmob(to_context);
}

uint64_t mobster(uint64_t* to_context) {
  print((uint64_t*) "mobster\n");

  // does not handle page faults, relies on fancy hypsters to do that
  return minmob(to_context);
}

void backtrack_trace(uint64_t* context) {
  uint64_t savepc;

  if (debug_symbolic)
    printf3((uint64_t*) "%s: backtracking %s from exit code %d\n", selfie_name, get_name(context), (uint64_t*) sign_extend(get_exit_code(context), SYSCALL_BITWIDTH));

  symbolic = 0;

  backtrack = 1;

  while (backtrack) {
    pc = get_trace_pc(tc);

    if (pc == 0)
      // we have backtracked all code back to the data segment
      backtrack = 0;
    else {
      savepc = pc;

      fetch();
      decode_execute();

      if (pc != savepc)
        // backtracking stopped by sltu
        backtrack = 0;
    }
  }

  symbolic = 1;

  set_pc(context, pc);
}

uint64_t monster(uint64_t* to_context) {
  uint64_t b;
  uint64_t timeout;
  uint64_t* from_context;

  print((uint64_t*) "monster\n");


  b = 0;

  timeout = TIMESLICE;

  while (1) {
    from_context = mipster_switch(to_context, timeout);

    if (get_parent(from_context) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      to_context = get_parent(from_context);

      timeout = TIMEROFF;
    } else {
      if (handle_exception(from_context) == EXIT) {

        if (debug_end_point)
            print_end_point_status(from_context, get_exit_code(from_context), get_exit_code_a2(from_context), get_exit_code_a3(from_context));

        backtrack_trace(from_context);

        if (b == 0)
          printf1((uint64_t*) "%s: backtracking ", selfie_name);
        else
          unprint_integer(b);

        b = b + 1;

        print_integer(b);

        if (pc == 0) {
          println();

          return EXITCODE_NOERROR;
        }
      }

      // TODO: scheduler should go here
      to_context = from_context;

      timeout = TIMESLICE;
    }
  }
}

uint64_t is_boot_level_zero() {
  // in C99 malloc(0) returns either a null pointer or a unique pointer.
  // (see http://pubs.opengroup.org/onlinepubs/9699919799/)
  // selfie's malloc implementation, on the other hand,
  // returns the same not null address, if malloc(0) is called consecutively.
  uint64_t first_malloc;
  uint64_t second_malloc;

  first_malloc = (uint64_t) malloc(0);
  second_malloc = (uint64_t) malloc(0);

  if (first_malloc == 0)
    return 1;
  if (first_malloc != second_malloc)
    return 1;

  // it is selfie's malloc, so it can not be boot level zero.
  return 0;
}

uint64_t selfie_run(uint64_t machine) {
  uint64_t exit_code;

  if (binary_length == 0) {
    printf1((uint64_t*) "%s: nothing to run, debug, or host\n", selfie_name);

    return EXITCODE_BADARGUMENTS;
  }

  if (machine == DIPSTER) {
    debug       = 1;
    disassemble = 1;
  } else if (machine == MONSTER) {
    debug    = 1;
    symbolic = 1;

    init_symbolic_engine();
    if (do_taint_flag) init_taint_engine();
  }

  if (machine == MONSTER) {
    init_memory(round_up(MAX_TRACE_LENGTH * SIZEOFUINT64, MEGABYTE) / MEGABYTE + 1);

    fuzz = atoi(peek_argument());
  } else
    init_memory(atoi(peek_argument()));

  execute = 1;

  reset_interpreter();
  reset_microkernel();

  create_context(MY_CONTEXT, 0);

  up_load_binary(current_context);

  // pass binary name as first argument by replacing memory size
  set_argument(binary_name);

  up_load_arguments(current_context, number_of_remaining_arguments(), remaining_arguments());

  printf3((uint64_t*) "%s: selfie executing %s with %dMB physical memory on ", selfie_name, binary_name, (uint64_t*) (page_frame_memory / MEGABYTE));

  if (machine == MIPSTER)
    exit_code = mipster(current_context);
  else if (machine == DIPSTER)
    exit_code = mipster(current_context);
  else if (machine == RIPSTER)
    exit_code = mipster(current_context);
  else if (machine == MONSTER)
    exit_code = monster(current_context);
  else if (machine == MINSTER)
    exit_code = minster(current_context);
  else if (machine == MOBSTER)
    exit_code = mobster(current_context);
  else if (machine == HYPSTER)
    if (is_boot_level_zero())
      // no hypster on boot level zero
      exit_code = mipster(current_context);
    else
      exit_code = hypster(current_context);
  else
    // change 0 to anywhere between 0% to 100% mipster
    exit_code = mixter(current_context, 0);

  execute = 0;

  printf3((uint64_t*) "%s: selfie terminating %s with exit code %d\n", selfie_name, get_name(current_context), (uint64_t*) sign_extend(exit_code, SYSCALL_BITWIDTH));

  print_profile();
  if (do_taint_flag) {
    print_symbolic_counters();
    println();
    print_minuend_fails();
    println();
    print_incomplete_operations();
    println();
    print_both_symbolic();
  }

  symbolic    = 0;
  disassemble = 0;
  debug       = 0;

  fuzz = 0;

  return exit_code;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------   T H E O R E M  P R O V E R    ----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// -------------------------- SAT Solver ---------------------------
// -----------------------------------------------------------------

uint64_t clause_may_be_true(uint64_t* clause_address, uint64_t depth) {
  uint64_t variable;

  variable = 0;

  while (variable <= depth) {
    if (*(sat_assignment + variable) == TRUE) {
      if (*(clause_address + 2 * variable))
        return TRUE;
    } else if (*(clause_address + 2 * variable + 1))
      // variable must be FALSE because variable <= depth
      return TRUE;

    variable = variable + 1;
  }

  while (variable < number_of_sat_variables) {
    // variable must be unassigned because variable > depth
    if (*(clause_address + 2 * variable))
      return TRUE;
    else if (*(clause_address + 2 * variable + 1))
      return TRUE;

    variable = variable + 1;
  }

  return FALSE;
}

uint64_t instance_may_be_true(uint64_t depth) {
  uint64_t clause;

  clause = 0;

  while (clause < number_of_sat_clauses) {
    if (clause_may_be_true(sat_instance + clause * 2 * number_of_sat_variables, depth))
      clause = clause + 1;
    else
      // clause is FALSE under current assignment
      return FALSE;
  }

  return TRUE;
}

uint64_t babysat(uint64_t depth) {
  if (depth == number_of_sat_variables)
    return SAT;

  *(sat_assignment + depth) = TRUE;

  if (instance_may_be_true(depth)) if (babysat(depth + 1) == SAT)
    return SAT;

  *(sat_assignment + depth) = FALSE;

  if (instance_may_be_true(depth)) if (babysat(depth + 1) == SAT)
    return SAT;

  return UNSAT;
}

// -----------------------------------------------------------------
// ----------------------- DIMACS CNF PARSER -----------------------
// -----------------------------------------------------------------

void selfie_print_dimacs() {
  uint64_t clause;
  uint64_t variable;

  printf2((uint64_t*) "p cnf %d %d\n", (uint64_t*) number_of_sat_variables, (uint64_t*) number_of_sat_clauses);

  clause = 0;

  while (clause < number_of_sat_clauses) {
    variable = 0;

    while (variable < number_of_sat_variables) {
      if (*(sat_instance + clause * 2 * number_of_sat_variables + 2 * variable) == TRUE) {
        print_integer(variable + 1);
        print((uint64_t*) " ");
      } else if (*(sat_instance + clause * 2 * number_of_sat_variables + 2 * variable + 1) == TRUE) {
        print_integer(-(variable + 1));
        print((uint64_t*) " ");
      }

      variable = variable + 1;
    }

    print((uint64_t*) "0\n");

    clause = clause + 1;
  }
}

void dimacs_find_next_character(uint64_t new_line) {
  uint64_t in_comment;

  // assuming we are not in a comment
  in_comment = 0;

  // read and discard all whitespace and comments until a character is found
  // that is not whitespace and does not occur in a comment, or the file ends
  while (1) {
    if (in_comment) {
      get_character();

      if (is_character_new_line())
        // comments end with new line
        in_comment = 0;
      else if (character == CHAR_EOF)
        return;
      else
        // count the characters in comments as ignored characters
        // line feed and carriage return are counted below
        number_of_ignored_characters = number_of_ignored_characters + 1;
    } else if (new_line) {
      new_line = 0;

      if (character == 'c') {
        // 'c' at beginning of a line begins a comment
        in_comment = 1;

        // count the number of comments
        number_of_comments = number_of_comments + 1;
      }
    } else if (is_character_whitespace()) {
      if (is_character_new_line())
        new_line = 1;
      else
        new_line = 0;

      // count whitespace as ignored characters
      number_of_ignored_characters = number_of_ignored_characters + 1;

      get_character();
    } else
      // character found that is not whitespace and not occurring in a comment
      return;
  }
}

void dimacs_get_symbol() {
  dimacs_find_next_character(0);

  get_symbol();
}

void dimacs_word(uint64_t* word) {
  if (symbol == SYM_IDENTIFIER) {
    if (string_compare(identifier, word)) {
      dimacs_get_symbol();

      return;
    } else
      syntax_error_identifier(word);
  } else
    syntax_error_symbol(SYM_IDENTIFIER);

  exit(EXITCODE_PARSERERROR);
}

uint64_t dimacs_number() {
  uint64_t number;

  if (symbol == SYM_INTEGER) {
    number = literal;

    dimacs_get_symbol();

    return number;
  } else
    syntax_error_symbol(SYM_INTEGER);

  exit(EXITCODE_PARSERERROR);
}

void dimacs_get_clause(uint64_t clause) {
  uint64_t not;

  while (1) {
    not = 0;

    if (symbol == SYM_MINUS) {
      not = 1;

      dimacs_get_symbol();
    }

    if (symbol == SYM_INTEGER) {
      if (literal == 0) {
        dimacs_get_symbol();

        return;
      } else if (literal > number_of_sat_variables) {
        syntax_error_message((uint64_t*) "clause exceeds declared number of variables");

        exit(EXITCODE_PARSERERROR);
      }

      // literal encoding starts at 0
      literal = literal - 1;

      if (not)
        *(sat_instance + clause * 2 * number_of_sat_variables + 2 * literal + 1) = TRUE;
      else
        *(sat_instance + clause * 2 * number_of_sat_variables + 2 * literal) = TRUE;
    } else if (symbol == SYM_EOF)
      return;
    else
      syntax_error_symbol(SYM_INTEGER);

    dimacs_get_symbol();
  }
}

void dimacs_get_instance() {
  uint64_t clauses;

  clauses = 0;

  while (clauses < number_of_sat_clauses)
    if (symbol != SYM_EOF) {
      dimacs_get_clause(clauses);

      clauses = clauses + 1;
    } else {
      syntax_error_message((uint64_t*) "instance has fewer clauses than declared");

      exit(EXITCODE_PARSERERROR);
    }

  if (symbol != SYM_EOF) {
    syntax_error_message((uint64_t*) "instance has more clauses than declared");

    exit(EXITCODE_PARSERERROR);
  }
}

void selfie_load_dimacs() {
  source_name = get_argument();

  printf2((uint64_t*) "%s: selfie loading SAT instance %s\n", selfie_name, source_name);

  // assert: source_name is mapped and not longer than MAX_FILENAME_LENGTH

  source_fd = sign_extend(open(source_name, O_RDONLY, 0), SYSCALL_BITWIDTH);

  if (signed_less_than(source_fd, 0)) {
    printf2((uint64_t*) "%s: could not open input file %s\n", selfie_name, source_name);

    exit(EXITCODE_IOERROR);
  }

  reset_scanner();

  // ignore all comments before problem
  dimacs_find_next_character(1);

  dimacs_get_symbol();

  dimacs_word((uint64_t*) "p");
  dimacs_word((uint64_t*) "cnf");

  number_of_sat_variables = dimacs_number();

  sat_assignment = (uint64_t*) smalloc(number_of_sat_variables * SIZEOFUINT64);

  number_of_sat_clauses = dimacs_number();

  sat_instance = (uint64_t*) smalloc(number_of_sat_clauses * 2 * number_of_sat_variables * SIZEOFUINT64);

  dimacs_get_instance();

  printf4((uint64_t*) "%s: %d clauses with %d declared variables loaded from %s\n", selfie_name, (uint64_t*) number_of_sat_clauses, (uint64_t*) number_of_sat_variables, source_name);

  dimacs_name = source_name;
}

void selfie_sat() {
  uint64_t variable;

  selfie_load_dimacs();

  if (dimacs_name == (uint64_t*) 0) {
    printf1((uint64_t*) "%s: nothing to SAT solve\n", selfie_name);

    return;
  }

  selfie_print_dimacs();

  if (babysat(0) == SAT) {
    printf2((uint64_t*) "%s: %s is satisfiable with ", selfie_name, dimacs_name);

    variable = 0;

    while (variable < number_of_sat_variables) {
      if (*(sat_assignment + variable) == FALSE)
        printf1((uint64_t*) "-%d ", (uint64_t*) (variable + 1));
      else
        printf1((uint64_t*) "%d ", (uint64_t*) (variable + 1));

      variable = variable + 1;
    }
  } else
    printf2((uint64_t*) "%s: %s is unsatisfiable", selfie_name, dimacs_name);

  println();
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

uint64_t number_of_remaining_arguments() {
  return selfie_argc;
}

uint64_t* remaining_arguments() {
  return selfie_argv;
}

uint64_t* peek_argument() {
  if (number_of_remaining_arguments() > 0)
    return (uint64_t*) *selfie_argv;
  else
    return (uint64_t*) 0;
}

uint64_t* get_argument() {
  uint64_t* argument;

  argument = peek_argument();

  if (number_of_remaining_arguments() > 0) {
    selfie_argc = selfie_argc - 1;
    selfie_argv = selfie_argv + 1;
  }

  return argument;
}

void set_argument(uint64_t* argv) {
  *selfie_argv = (uint64_t) argv;
}

void print_usage() {
  printf3((uint64_t*) "%s: usage: selfie { %s } [ %s ]\n",
    selfie_name,
      (uint64_t*) "-c { source } | -o binary | [ -s | -S ] assembly | -l binary | -sat dimacs",
      (uint64_t*) "( -m | -d | -r | -n | -y | -min | -mob ) 0-64 ...");
}

uint64_t selfie() {
  uint64_t* option;

  if (number_of_remaining_arguments() == 0)
    print_usage();
  else {
    init_scanner();
    init_register();
    init_interpreter();

    while (number_of_remaining_arguments() > 0) {
      option = get_argument();

      if (string_compare(option, (uint64_t*) "-c"))
        selfie_compile();

      else if (number_of_remaining_arguments() == 0) {
        // remaining options have at least one argument
        print_usage();

        return EXITCODE_BADARGUMENTS;
      } else if (string_compare(option, (uint64_t*) "-o"))
        selfie_output();
      else if (string_compare(option, (uint64_t*) "-s"))
        selfie_disassemble(0);
      else if (string_compare(option, (uint64_t*) "-S"))
        selfie_disassemble(1);
      else if (string_compare(option, (uint64_t*) "-l"))
        selfie_load();
      else if (string_compare(option, (uint64_t*) "-sat"))
        selfie_sat();
      else if (string_compare(option, (uint64_t*) "-m"))
        return selfie_run(MIPSTER);
      else if (string_compare(option, (uint64_t*) "-d"))
        return selfie_run(DIPSTER);
      else if (string_compare(option, (uint64_t*) "-r"))
        return selfie_run(RIPSTER);
      else if (string_compare(option, (uint64_t*) "-n"))
        return selfie_run(MONSTER);
      else if (string_compare(option, (uint64_t*) "-y"))
        return selfie_run(HYPSTER);
      else if (string_compare(option, (uint64_t*) "-min"))
        return selfie_run(MINSTER);
      else if (string_compare(option, (uint64_t*) "-mob"))
        return selfie_run(MOBSTER);
      else if (string_compare(option, (uint64_t*) "-t"))
        do_taint_flag = 1;
      else if (string_compare(option, (uint64_t*) "-test"))
        debug_end_point = 1;
      else if (string_compare(option, (uint64_t*) "-no_concrete"))
        no_concrete = 1;
      else {
        print_usage();

        return EXITCODE_BADARGUMENTS;
      }
    }
  }

  return EXITCODE_NOERROR;
}

// selfie bootstraps int and char** to uint64_t and uint64_t*, respectively!
int main(int argc, char** argv) {
  init_selfie((uint64_t) argc, (uint64_t*) argv);

  init_library();

  return selfie();
}
