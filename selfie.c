/*
Copyright (c) 2015-2019, the Selfie Project authors. All rights reserved.
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

Selfie is a self-contained 64-bit, 12-KLOC C implementation of:

1. a self-compiling compiler called starc that compiles
   a tiny but still fast subset of C called C Star (C*) to
   a tiny and easy-to-teach subset of RISC-V called RISC-U,
2. a self-executing emulator called mipster that executes
   RISC-U code including itself when compiled with starc,
3. a self-hosting hypervisor called hypster that provides
   RISC-U virtual machines that can host all of selfie,
   that is, starc, mipster, and hypster itself,
4. a self-translating modeling engine called monster that
   translates RISC-U code including itself to SMT-LIB and
   BTOR2 formulae that are satisfiable if and only if
   there is input to the code such that the code exits
   with non-zero exit codes, performs division by zero,
   or accesses memory outside of allocated memory blocks,
5. a simple SAT solver that reads CNF DIMACS files, and
6. a tiny C* library called libcstar utilized by selfie.

Selfie is implemented in a single (!) file and kept minimal for simplicity.
There is also a simple in-memory linker, a RISC-U disassembler, a profiler,
and a debugger with replay as well as minimal operating system support in
the form of RISC-V system calls built into the emulator and hypervisor.

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

The modeling engine implements a simple yet sound and complete
translation of RISC-U code to SMT-LIB and BTOR2 formulae. The SAT
solver implements a naive brute-force enumeration of all possible
variable assignments. Both engine and solver facilitate teaching
the absolute basics of SAT and SMT solving applied to real code.

Selfie is the result of many years of teaching systems engineering.
The design of the compiler is inspired by the Oberon compiler of
Professor Niklaus Wirth from ETH Zurich. RISC-U is inspired by the
RISC-V community around Professor David Patterson from UC Berkeley.
The design of the hypervisor is inspired by microkernels of Professor
Jochen Liedtke from University of Karlsruhe. The modeling engine and
the SAT solver are inspired by Professor Armin Biere from JKU Linz.
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

// selfie bootstraps char to uint64_t!
uint64_t open(char* filename, uint64_t flags, uint64_t mode);

// selfie bootstraps void* and unsigned long to uint64_t* and uint64_t, respectively!
void* malloc(unsigned long);

// -----------------------------------------------------------------
// ----------------------- LIBRARY PROCEDURES ----------------------
// -----------------------------------------------------------------

void init_library();
void reset_library();

uint64_t two_to_the_power_of(uint64_t p);
uint64_t ten_to_the_power_of(uint64_t p);

uint64_t log_ten(uint64_t n);

uint64_t left_shift(uint64_t n, uint64_t b);
uint64_t right_shift(uint64_t n, uint64_t b);

uint64_t get_bits(uint64_t n, uint64_t i, uint64_t b);
uint64_t get_low_word(uint64_t n);
uint64_t get_high_word(uint64_t n);

uint64_t absolute(uint64_t n);
uint64_t max(uint64_t a, uint64_t b);

uint64_t signed_less_than(uint64_t a, uint64_t b);
uint64_t signed_division(uint64_t a, uint64_t b);

uint64_t is_signed_integer(uint64_t n, uint64_t b);
uint64_t sign_extend(uint64_t n, uint64_t b);
uint64_t sign_shrink(uint64_t n, uint64_t b);

uint64_t load_character(char* s, uint64_t i);
char*    store_character(char* s, uint64_t i, uint64_t c);

char*    string_alloc(uint64_t l);
uint64_t string_length(char* s);
char*    string_copy(char* s);
void     string_reverse(char* s);
uint64_t string_compare(char* s, char* t);

uint64_t atoi(char* s);
char*    itoa(uint64_t n, char* s, uint64_t b, uint64_t a);

uint64_t fixed_point_ratio(uint64_t a, uint64_t b, uint64_t f);
uint64_t fixed_point_percentage(uint64_t r, uint64_t f);

void put_character(uint64_t c);

void print(char* s);
void println();

void print_character(uint64_t c);
void print_string(char* s);
void print_integer(uint64_t n);
void unprint_integer(uint64_t n);
void print_hexadecimal(uint64_t n, uint64_t a);
void print_octal(uint64_t n, uint64_t a);
void print_binary(uint64_t n, uint64_t a);

uint64_t print_format0(char* s, uint64_t i);
uint64_t print_format1(char* s, uint64_t i, char* a);

void printf1(char* s, char* a1);
void printf2(char* s, char* a1, char* a2);
void printf3(char* s, char* a1, char* a2, char* a3);
void printf4(char* s, char* a1, char* a2, char* a3, char* a4);
void printf5(char* s, char* a1, char* a2, char* a3, char* a4, char* a5);
void printf6(char* s, char* a1, char* a2, char* a3, char* a4, char* a5, char* a6);

void sprintf1(char* b, char* s, char* a1);
void sprintf2(char* b, char* s, char* a1, char* a2);
void sprintf3(char* b, char* s, char* a1, char* a2, char* a3);
void sprintf4(char* b, char* s, char* a1, char* a2, char* a3, char* a4);

uint64_t round_up(uint64_t n, uint64_t m);

uint64_t* smalloc(uint64_t size);
uint64_t* zalloc(uint64_t size);

// ------------------------ GLOBAL CONSTANTS -----------------------

char* SELFIE_URL = (char*) 0;

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

uint64_t* character_buffer; // buffer for reading and writing characters

char* integer_buffer; // buffer for formatting integers

uint64_t MAX_FILENAME_LENGTH = 128;

char* filename_buffer; // buffer for opening files

uint64_t* binary_buffer; // buffer for binary I/O

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

char*    output_name = (char*) 0;
uint64_t output_fd   = 1; // 1 is file descriptor of standard output

char*    output_buffer = (char*) 0;
uint64_t output_cursor = 0; // cursor for output buffer

// ------------------------- INITIALIZATION ------------------------

void init_library() {
  uint64_t i;

  SELFIE_URL = "http://selfie.cs.uni-salzburg.at";

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
  integer_buffer = string_alloc(CPUBITWIDTH);

  // does not need to be mapped
  filename_buffer = string_alloc(MAX_FILENAME_LENGTH);

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
void print_line_number(char* message, uint64_t line);

void syntax_error_message(char* message);
void syntax_error_character(uint64_t character);
void syntax_error_identifier(char* expected);

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

char* identifier = (char*) 0; // stores scanned identifier as string
char* integer    = (char*) 0; // stores scanned integer as string
char* string     = (char*) 0; // stores scanned string

uint64_t literal = 0; // stores numerical value of scanned integer or character

uint64_t integer_is_signed = 0; // enforce INT64_MIN limit if '-' was scanned before

uint64_t character; // most recently read character

uint64_t number_of_read_characters = 0;

uint64_t symbol; // most recently recognized symbol

uint64_t number_of_ignored_characters = 0;
uint64_t number_of_comments           = 0;
uint64_t number_of_scanned_symbols    = 0;

char*    source_name = (char*) 0; // name of source file
uint64_t source_fd   = 0; // file descriptor of open source file

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

void create_symbol_table_entry(uint64_t which, char* string, uint64_t line, uint64_t class, uint64_t type, uint64_t value, uint64_t address);

uint64_t* search_symbol_table(uint64_t* entry, char* string, uint64_t class);
uint64_t* search_global_symbol_table(char* string, uint64_t class);
uint64_t* get_scoped_symbol_table_entry(char* string, uint64_t class);

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

uint64_t* allocate_symbol_table_entry() {
  return smalloc(2 * SIZEOFUINT64STAR + 6 * SIZEOFUINT64);
}

uint64_t* get_next_entry(uint64_t* entry)  { return (uint64_t*) *entry; }
char*     get_string(uint64_t* entry)      { return (char*)     *(entry + 1); }
uint64_t  get_line_number(uint64_t* entry) { return             *(entry + 2); }
uint64_t  get_class(uint64_t* entry)       { return             *(entry + 3); }
uint64_t  get_type(uint64_t* entry)        { return             *(entry + 4); }
uint64_t  get_value(uint64_t* entry)       { return             *(entry + 5); }
uint64_t  get_address(uint64_t* entry)     { return             *(entry + 6); }
uint64_t  get_scope(uint64_t* entry)       { return             *(entry + 7); }

void set_next_entry(uint64_t* entry, uint64_t* next)   { *entry       = (uint64_t) next; }
void set_string(uint64_t* entry, char* identifier)     { *(entry + 1) = (uint64_t) identifier; }
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

void     talloc();
uint64_t current_temporary();
uint64_t previous_temporary();
uint64_t next_temporary();
void     tfree(uint64_t number_of_temporaries);

void save_temporaries();
void restore_temporaries(uint64_t number_of_temporaries);

void syntax_error_symbol(uint64_t expected);
void syntax_error_unexpected();
void print_type(uint64_t type);
void type_warning(uint64_t expected, uint64_t found);

uint64_t* get_variable_or_big_int(char* variable, uint64_t class);
void      load_upper_base_address(uint64_t* entry);
uint64_t  load_variable_or_big_int(char* variable, uint64_t class);
void      load_integer(uint64_t value);
void      load_string(char* string);

uint64_t help_call_codegen(uint64_t* entry, char* procedure);
void     help_procedure_prologue(uint64_t number_of_local_variable_bytes);
void     help_procedure_epilogue(uint64_t number_of_parameter_bytes);

uint64_t compile_call(char* procedure);
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
void     compile_procedure(char* procedure, uint64_t type);
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

char* get_register_name(uint64_t reg);
void  print_register_name(uint64_t reg);

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

  *(REGISTERS + REG_ZR)  = (uint64_t) "zero";
  *(REGISTERS + REG_RA)  = (uint64_t) "ra";
  *(REGISTERS + REG_SP)  = (uint64_t) "sp";
  *(REGISTERS + REG_GP)  = (uint64_t) "gp";
  *(REGISTERS + REG_TP)  = (uint64_t) "tp";
  *(REGISTERS + REG_T0)  = (uint64_t) "t0";
  *(REGISTERS + REG_T1)  = (uint64_t) "t1";
  *(REGISTERS + REG_T2)  = (uint64_t) "t2";
  *(REGISTERS + REG_FP)  = (uint64_t) "s0"; // used to be fp
  *(REGISTERS + REG_S1)  = (uint64_t) "s1";
  *(REGISTERS + REG_A0)  = (uint64_t) "a0";
  *(REGISTERS + REG_A1)  = (uint64_t) "a1";
  *(REGISTERS + REG_A2)  = (uint64_t) "a2";
  *(REGISTERS + REG_A3)  = (uint64_t) "a3";
  *(REGISTERS + REG_A4)  = (uint64_t) "a4";
  *(REGISTERS + REG_A5)  = (uint64_t) "a5";
  *(REGISTERS + REG_A6)  = (uint64_t) "a6";
  *(REGISTERS + REG_A7)  = (uint64_t) "a7";
  *(REGISTERS + REG_S2)  = (uint64_t) "s2";
  *(REGISTERS + REG_S3)  = (uint64_t) "s3";
  *(REGISTERS + REG_S4)  = (uint64_t) "s4";
  *(REGISTERS + REG_S5)  = (uint64_t) "s5";
  *(REGISTERS + REG_S6)  = (uint64_t) "s6";
  *(REGISTERS + REG_S7)  = (uint64_t) "s7";
  *(REGISTERS + REG_S8)  = (uint64_t) "s8";
  *(REGISTERS + REG_S9)  = (uint64_t) "s9";
  *(REGISTERS + REG_S10) = (uint64_t) "s10";
  *(REGISTERS + REG_S11) = (uint64_t) "s11";
  *(REGISTERS + REG_T3)  = (uint64_t) "t3";
  *(REGISTERS + REG_T4)  = (uint64_t) "t4";
  *(REGISTERS + REG_T5)  = (uint64_t) "t5";
  *(REGISTERS + REG_T6)  = (uint64_t) "t6";
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

void print_instruction_counter(uint64_t total, uint64_t counter, char* mnemonics);
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

uint64_t* allocate_elf_header();
uint64_t* create_elf_header(uint64_t binary_length, uint64_t code_length);
uint64_t  validate_elf_header(uint64_t* header);

uint64_t open_write_only(char* name);

void selfie_output();

uint64_t* touch(uint64_t* memory, uint64_t length);

void selfie_load();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t MAX_BINARY_LENGTH = 262144; // 256KB = MAX_CODE_LENGTH + MAX_DATA_LENGTH

uint64_t MAX_CODE_LENGTH = 229376; // 224KB
uint64_t MAX_DATA_LENGTH = 32768; // 32KB

// page-aligned ELF header for storing file header (64 bytes),
// program header (56 bytes), and code length (8 bytes)
uint64_t ELF_HEADER_LEN = 4096;

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
uint64_t  binary_length = 0;             // length of binary in bytes including data segment
char*     binary_name   = (char*) 0;     // file name of binary

uint64_t code_length = 0; // length of code segment in binary in bytes
uint64_t entry_point = 0; // beginning of code segment in virtual address space

uint64_t* code_line_number = (uint64_t*) 0; // code line number per emitted instruction
uint64_t* data_line_number = (uint64_t*) 0; // data line number per emitted data

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
uint64_t down_load_string(uint64_t* table, uint64_t vstring, char* s);
void     implement_openat(uint64_t* context);

void emit_malloc();
void implement_brk(uint64_t* context);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t debug_read  = 0;
uint64_t debug_write = 0;
uint64_t debug_open  = 0;
uint64_t debug_brk   = 0;

uint64_t SYSCALL_EXIT   = 93;
uint64_t SYSCALL_READ   = 63;
uint64_t SYSCALL_WRITE  = 64;
uint64_t SYSCALL_OPENAT = 56;
uint64_t SYSCALL_BRK    = 214;

/* DIRFD_AT_FDCWD corresponds to AT_FDCWD in fcntl.h and
   is passed as first argument of the openat system call
   emulating the (in Linux) deprecated open system call. */

uint64_t DIRFD_AT_FDCWD = -100;

// -----------------------------------------------------------------
// ----------------------- HYPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void      emit_switch();
uint64_t* do_switch(uint64_t* from_context, uint64_t* to_context, uint64_t timeout);
void      implement_switch();
uint64_t* mipster_switch(uint64_t* to_context, uint64_t timeout);

// ------------------------ GLOBAL CONSTANTS -----------------------

// TODO: fix this syscall for spike
uint64_t SYSCALL_SWITCH = 401;

uint64_t debug_switch = 0;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------    A R C H I T E C T U R E    -----------------
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

void print_code_line_number_for_instruction(uint64_t address, uint64_t offset);
void print_code_context_for_instruction(uint64_t address);

void print_lui();
void print_lui_before();
void print_lui_after();
void record_lui_addi_add_sub_mul_sltu_jal_jalr();
void do_lui();
void undo_lui_addi_add_sub_mul_divu_remu_sltu_ld_jal_jalr();
void constrain_lui();

void print_addi();
void print_addi_before();
void print_addi_add_sub_mul_divu_remu_sltu_after();
void do_addi();
void constrain_addi();

void print_add_sub_mul_divu_remu_sltu(char *mnemonics);
void print_add_sub_mul_divu_remu_sltu_before();

void do_add();
void constrain_add_sub_mul_divu_remu_sltu(char* operator);

void do_sub();

void do_mul();

void record_divu_remu();
void do_divu();

void do_remu();

void do_sltu();
void zero_extend_sltu();

void     print_ld();
void     print_ld_before();
void     print_ld_after(uint64_t vaddr);
void     record_ld();
uint64_t do_ld();
void     constrain_ld();

void     print_sd();
void     print_sd_before();
void     print_sd_after(uint64_t vaddr);
void     record_sd();
uint64_t do_sd();
void     undo_sd();
void     constrain_sd();

void print_beq();
void print_beq_before();
void print_beq_after();
void record_beq();
void do_beq();
void constrain_beq();

void print_jal();
void print_jal_before();
void print_jal_jalr_after();
void do_jal();

void print_jalr();
void print_jalr_before();
void do_jalr();
void constrain_jalr();

void print_ecall();
void record_ecall();
void do_ecall();
void undo_ecall();

void print_data_line_number();
void print_data_context(uint64_t data);
void print_data(uint64_t data);

// -----------------------------------------------------------------
// -------------------------- REPLAY ENGINE ------------------------
// -----------------------------------------------------------------

void init_replay_engine();

void record_state(uint64_t value);

void replay_trace();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t MAX_REPLAY_LENGTH = 100;

// trace

uint64_t tc = 0; // trace counter

uint64_t* pcs    = (uint64_t*) 0; // trace of program counter values
uint64_t* values = (uint64_t*) 0; // trace of values

// ------------------------- INITIALIZATION ------------------------

void init_replay_engine() {
  pcs    = zalloc(MAX_REPLAY_LENGTH * SIZEOFUINT64);
  values = zalloc(MAX_REPLAY_LENGTH * SIZEOFUINT64);
}

// -----------------------------------------------------------------
// ------------------------ SYMBOLIC MEMORY ------------------------
// -----------------------------------------------------------------

uint64_t* load_symbolic_memory(uint64_t vaddr);
void      store_symbolic_memory(uint64_t vaddr, uint64_t val, char* sym, char* var, uint64_t bits);
uint64_t* find_word_in_unshared_symbolic_memory(uint64_t vaddr);
void      update_begin_of_shared_symbolic_memory(uint64_t* context);

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
  return smalloc(2 * SIZEOFUINT64STAR + 3 * SIZEOFUINT64);
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

uint64_t  find_merge_location(uint64_t beq_imm);

void      add_mergeable_context(uint64_t* context);
uint64_t* get_mergeable_context();

void      add_waiting_context(uint64_t* context);
uint64_t* get_waiting_context();

void      add_prologue_start_and_corresponding_merge_location(uint64_t prologue_start, uint64_t merge_location, uint64_t* context);
uint64_t  get_merge_location_from_corresponding_prologue_start(uint64_t prologue_start, uint64_t* context);
uint64_t  currently_in_this_procedure(uint64_t prologue_start, uint64_t* context);

void      merge(uint64_t* active_context, uint64_t* mergeable_context, uint64_t location);
void      merge_symbolic_memory_and_registers(uint64_t* active_context, uint64_t* mergeable_context);
void      merge_symbolic_memory_of_active_context(uint64_t* active_context, uint64_t* mergeable_context);
void      merge_symbolic_memory_of_mergeable_context(uint64_t* active_context, uint64_t* mergeable_context);
void      merge_registers(uint64_t* active_context, uint64_t* mergeable_context);
uint64_t* merge_if_possible_and_get_next_context(uint64_t* context);

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t max_execution_depth = 1; // in number of instructions, unbounded with 0

uint64_t variable_version = 0; // generates unique SMT-LIB variable names

uint64_t* symbolic_contexts = (uint64_t*) 0;

char* path_condition = (char*) 0;

uint64_t* symbolic_memory = (uint64_t*) 0;

uint64_t* reg_sym = (uint64_t*) 0; // symbolic values in registers as strings in SMT-LIB format

char*    smt_name = (char*) 0; // name of SMT-LIB file
uint64_t smt_fd   = 0;         // file descriptor of open SMT-LIB file

uint64_t merge_enabled = 0; // enable or disable the merging of paths

uint64_t* mergeable_contexts                          = (uint64_t*) 0; // contexts that have reached their merge location
uint64_t* waiting_contexts                            = (uint64_t*) 0; // contexts that were created at a symbolic beq instruction and are waiting to be executed

uint64_t* current_mergeable_context                   = (uint64_t*) 0; // current context with which the active context can possibly be merged

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t DELETED                         = -1; // indicates that a symbolic memory word has been deleted
uint64_t MERGED                          = -2; // indicates that a symbolic memory word has been merged
uint64_t BEGIN_OF_SHARED_SYMBOLIC_MEMORY = -3; // indicates the begin of the shared symbolic memory space

uint64_t BEQ_LIMIT                 = 35;  // limit of symbolic beq instructions on each part of the path between two merge locations

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void init_interpreter();
void reset_interpreter();
void reset_profiler();

void     print_register_hexadecimal(uint64_t reg);
void     print_register_octal(uint64_t reg);
uint64_t is_system_register(uint64_t reg);
void     print_register_value(uint64_t reg);

void print_exception(uint64_t exception, uint64_t faulting_page);
void throw_exception(uint64_t exception, uint64_t faulting_page);

void fetch();
void decode();
void execute();

void execute_record();
void execute_undo();
void execute_debug();
void execute_symbolically();

void interrupt();

void run_until_exception();

uint64_t instruction_with_max_counter(uint64_t* counters, uint64_t max);
uint64_t print_per_instruction_counter(uint64_t total, uint64_t* counters, uint64_t max);
void     print_per_instruction_profile(char* message, uint64_t total, uint64_t* counters);

void print_profile();

// ------------------------ GLOBAL CONSTANTS -----------------------

// RISC-U instructions

uint64_t LUI   = 1; // 0 is reserved for unknown instructions
uint64_t ADDI  = 2;
uint64_t ADD   = 3;
uint64_t SUB   = 4;
uint64_t MUL   = 5;
uint64_t DIVU  = 6;
uint64_t REMU  = 7;
uint64_t SLTU  = 8;
uint64_t LD    = 9;
uint64_t SD    = 10;
uint64_t BEQ   = 11;
uint64_t JAL   = 12;
uint64_t JALR  = 13;
uint64_t ECALL = 14;

// exceptions

uint64_t EXCEPTION_NOEXCEPTION        = 0;
uint64_t EXCEPTION_PAGEFAULT          = 1;
uint64_t EXCEPTION_SYSCALL            = 2;
uint64_t EXCEPTION_TIMER              = 3;
uint64_t EXCEPTION_INVALIDADDRESS     = 4;
uint64_t EXCEPTION_DIVISIONBYZERO     = 5;
uint64_t EXCEPTION_UNKNOWNINSTRUCTION = 6;
uint64_t EXCEPTION_MERGE              = 7;

uint64_t* EXCEPTIONS; // strings representing exceptions

uint64_t debug_exception = 0;

uint64_t run = 0; // flag for running code

// enables recording, symbolically executing, and debugging code
uint64_t debug = 0;

uint64_t debug_syscalls = 0; // flag for debugging syscalls

uint64_t record   = 0; // flag for recording code execution
uint64_t symbolic = 0; // flag for symbolically executing code

uint64_t redo = 0; // flag for redoing code execution

uint64_t disassemble_verbose = 0; // flag for disassembling code in more detail
uint64_t model_check         = 0; // flag for model checking code
uint64_t check_block_access  = 0; // flag for checking memory access validity on malloced block level

// number of instructions from context switch to timer interrupt
// CAUTION: avoid interrupting any kernel activities, keep TIMESLICE large
// TODO: implement proper interrupt controller to turn interrupts on and off
uint64_t TIMESLICE = 10000000;

uint64_t TIMEROFF = 0; // must be 0 to turn off timer interrupt

// ------------------------ GLOBAL VARIABLES -----------------------

// hardware thread state

uint64_t pc = 0; // program counter

uint64_t ir = 0; // instruction register
uint64_t is = 0; // instruction id

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
  EXCEPTIONS = smalloc((EXCEPTION_MERGE + 1) * SIZEOFUINT64STAR);

  *(EXCEPTIONS + EXCEPTION_NOEXCEPTION)        = (uint64_t) "no exception";
  *(EXCEPTIONS + EXCEPTION_PAGEFAULT)          = (uint64_t) "page fault";
  *(EXCEPTIONS + EXCEPTION_SYSCALL)            = (uint64_t) "syscall";
  *(EXCEPTIONS + EXCEPTION_TIMER)              = (uint64_t) "timer interrupt";
  *(EXCEPTIONS + EXCEPTION_INVALIDADDRESS)     = (uint64_t) "invalid address";
  *(EXCEPTIONS + EXCEPTION_DIVISIONBYZERO)     = (uint64_t) "division by zero";
  *(EXCEPTIONS + EXCEPTION_UNKNOWNINSTRUCTION) = (uint64_t) "unknown instruction";
  *(EXCEPTIONS + EXCEPTION_MERGE)              = (uint64_t) "merge interrupt";
}

void reset_interpreter() {
  pc = 0;
  ir = 0;
  is = 0;

  registers = (uint64_t*) 0;

  pt = (uint64_t*) 0;

  trap = 0;

  timer = TIMEROFF;
}

void reset_profiler() {
  reset_instruction_counters();

  calls               = 0;
  calls_per_procedure = zalloc(code_length / INSTRUCTIONSIZE * SIZEOFUINT64);

  iterations          = 0;
  iterations_per_loop = zalloc(code_length / INSTRUCTIONSIZE * SIZEOFUINT64);

  loads_per_instruction  = zalloc(code_length / INSTRUCTIONSIZE * SIZEOFUINT64);
  stores_per_instruction = zalloc(code_length / INSTRUCTIONSIZE * SIZEOFUINT64);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- CONTEXTS ---------------------------
// -----------------------------------------------------------------

uint64_t* new_context();

void      init_context(uint64_t* context, uint64_t* parent, uint64_t* vctxt);
uint64_t* copy_context(uint64_t* original, uint64_t location, char* condition);

uint64_t* find_context(uint64_t* parent, uint64_t* vctxt);

void      free_context(uint64_t* context);
uint64_t* delete_context(uint64_t* context, uint64_t* from);

// context struct:
// +----+-----------------+
// |  0 | next context    | pointer to next context
// |  1 | prev context    | pointer to previous context
// |  2 | program counter | program counter
// |  3 | registers       | pointer to general purpose registers
// |  4 | page table      | pointer to page table
// |  5 | lowest lo page  | lowest low unmapped page (code, data, heap)
// |  6 | highest lo page | highest low unmapped page (code, data, heap)
// |  7 | lowest hi page  | lowest high unmapped page (stack)
// |  8 | highest hi page | highest high unmapped page (stack)
// |  9 | original break  | original end of data segment
// | 10 | program break   | end of data segment
// | 11 | exception       | exception ID
// | 12 | faulting page   | faulting page
// | 13 | exit code       | exit code
// | 14 | parent          | context that created this context
// | 15 | virtual context | virtual context address
// | 16 | name            | binary name loaded into context
// +----+-----------------+
// symbolic extension:
// +----+-----------------+
// | 17 | execution depth | number of executed instructions
// | 18 | path condition  | pointer to path condition
// | 19 | symbolic memory | pointer to symbolic memory
// | 20 | symbolic regs   | pointer to symbolic registers
// | 21 | beq counter     | number of executed symbolic beq instructions
// | 22 | merge location  | program location at which the context can possibly be merged (later)
// | 23 | prologues       | pointer to a stack that stores the prologues of procedures within which the context is currently located
// | 24 | in recursion    | if the value is 1, then the context is currently in a recursion
// | 25 | outside rec loc | program location at which the context has finished the recursion
// | 26 | merge partner   | pointer to the context from which this context was created
// +----+-----------------+

uint64_t* allocate_context() {
  return smalloc(7 * SIZEOFUINT64STAR + 10 * SIZEOFUINT64);
}

uint64_t* allocate_symbolic_context() {
  return smalloc(7 * SIZEOFUINT64STAR + 10 * SIZEOFUINT64 + 5 * SIZEOFUINT64STAR + 5 * SIZEOFUINT64);
}

uint64_t next_context(uint64_t* context)    { return (uint64_t) context; }
uint64_t prev_context(uint64_t* context)    { return (uint64_t) (context + 1); }
uint64_t program_counter(uint64_t* context) { return (uint64_t) (context + 2); }
uint64_t regs(uint64_t* context)            { return (uint64_t) (context + 3); }
uint64_t page_table(uint64_t* context)      { return (uint64_t) (context + 4); }
uint64_t lowest_lo_page(uint64_t* context)  { return (uint64_t) (context + 5); }
uint64_t highest_lo_page(uint64_t* context) { return (uint64_t) (context + 6); }
uint64_t lowest_hi_page(uint64_t* context)  { return (uint64_t) (context + 7); }
uint64_t highest_hi_page(uint64_t* context) { return (uint64_t) (context + 8); }
uint64_t original_break(uint64_t* context)  { return (uint64_t) (context + 9); }
uint64_t program_break(uint64_t* context)   { return (uint64_t) (context + 10); }
uint64_t exception(uint64_t* context)       { return (uint64_t) (context + 11); }
uint64_t faulting_page(uint64_t* context)   { return (uint64_t) (context + 12); }
uint64_t exit_code(uint64_t* context)       { return (uint64_t) (context + 13); }
uint64_t parent(uint64_t* context)          { return (uint64_t) (context + 14); }
uint64_t virtual_context(uint64_t* context) { return (uint64_t) (context + 15); }
uint64_t name(uint64_t* context)            { return (uint64_t) (context + 16); }

uint64_t* get_next_context(uint64_t* context)    { return (uint64_t*) *context; }
uint64_t* get_prev_context(uint64_t* context)    { return (uint64_t*) *(context + 1); }
uint64_t  get_pc(uint64_t* context)              { return             *(context + 2); }
uint64_t* get_regs(uint64_t* context)            { return (uint64_t*) *(context + 3); }
uint64_t* get_pt(uint64_t* context)              { return (uint64_t*) *(context + 4); }
uint64_t  get_lowest_lo_page(uint64_t* context)  { return             *(context + 5); }
uint64_t  get_highest_lo_page(uint64_t* context) { return             *(context + 6); }
uint64_t  get_lowest_hi_page(uint64_t* context)  { return             *(context + 7); }
uint64_t  get_highest_hi_page(uint64_t* context) { return             *(context + 8); }
uint64_t  get_original_break(uint64_t* context)  { return             *(context + 9); }
uint64_t  get_program_break(uint64_t* context)   { return             *(context + 10); }
uint64_t  get_exception(uint64_t* context)       { return             *(context + 11); }
uint64_t  get_faulting_page(uint64_t* context)   { return             *(context + 12); }
uint64_t  get_exit_code(uint64_t* context)       { return             *(context + 13); }
uint64_t* get_parent(uint64_t* context)          { return (uint64_t*) *(context + 14); }
uint64_t* get_virtual_context(uint64_t* context) { return (uint64_t*) *(context + 15); }
char*     get_name(uint64_t* context)            { return (char*)     *(context + 16); }

uint64_t  get_execution_depth(uint64_t* context) { return             *(context + 17); }
char*     get_path_condition(uint64_t* context)  { return (char*)     *(context + 18); }
uint64_t* get_symbolic_memory(uint64_t* context) { return (uint64_t*) *(context + 19); }
uint64_t* get_symbolic_regs(uint64_t* context)   { return (uint64_t*) *(context + 20); }
uint64_t  get_beq_counter(uint64_t* context)     { return             *(context + 21); }
uint64_t  get_merge_location(uint64_t* context)  { return             *(context + 22); }
uint64_t* get_prologues(uint64_t* context)       { return (uint64_t*) *(context + 23); }
uint64_t  get_in_recursion(uint64_t* context)    { return             *(context + 24); }
uint64_t  get_outside_rec_loc(uint64_t* context) { return             *(context + 25); }
uint64_t* get_merge_partner(uint64_t* context)   { return (uint64_t*) *(context + 26); }

void set_next_context(uint64_t* context, uint64_t* next)      { *context        = (uint64_t) next; }
void set_prev_context(uint64_t* context, uint64_t* prev)      { *(context + 1)  = (uint64_t) prev; }
void set_pc(uint64_t* context, uint64_t pc)                   { *(context + 2)  = pc; }
void set_regs(uint64_t* context, uint64_t* regs)              { *(context + 3)  = (uint64_t) regs; }
void set_pt(uint64_t* context, uint64_t* pt)                  { *(context + 4)  = (uint64_t) pt; }
void set_lowest_lo_page(uint64_t* context, uint64_t page)     { *(context + 5)  = page; }
void set_highest_lo_page(uint64_t* context, uint64_t page)    { *(context + 6)  = page; }
void set_lowest_hi_page(uint64_t* context, uint64_t page)     { *(context + 7)  = page; }
void set_highest_hi_page(uint64_t* context, uint64_t page)    { *(context + 8)  = page; }
void set_original_break(uint64_t* context, uint64_t brk)      { *(context + 9)  = brk; }
void set_program_break(uint64_t* context, uint64_t brk)       { *(context + 10) = brk; }
void set_exception(uint64_t* context, uint64_t exception)     { *(context + 11) = exception; }
void set_faulting_page(uint64_t* context, uint64_t page)      { *(context + 12) = page; }
void set_exit_code(uint64_t* context, uint64_t code)          { *(context + 13) = code; }
void set_parent(uint64_t* context, uint64_t* parent)          { *(context + 14) = (uint64_t) parent; }
void set_virtual_context(uint64_t* context, uint64_t* vctxt)  { *(context + 15) = (uint64_t) vctxt; }
void set_name(uint64_t* context, char* name)                  { *(context + 16) = (uint64_t) name; }

void set_execution_depth(uint64_t* context, uint64_t depth)    { *(context + 17) =            depth; }
void set_path_condition(uint64_t* context, char* path)         { *(context + 18) = (uint64_t) path; }
void set_symbolic_memory(uint64_t* context, uint64_t* memory)  { *(context + 19) = (uint64_t) memory; }
void set_symbolic_regs(uint64_t* context, uint64_t* regs)      { *(context + 20) = (uint64_t) regs; }
void set_beq_counter(uint64_t* context, uint64_t counter)      { *(context + 21) =            counter; }
void set_merge_location(uint64_t* context, uint64_t location)  { *(context + 22) =            location; }
void set_prologues(uint64_t* context, uint64_t* prologues)     { *(context + 23) = (uint64_t) prologues; }
void set_in_recursion(uint64_t* context, uint64_t in_rec)      { *(context + 24) =            in_rec; }
void set_outside_rec_loc(uint64_t* context, uint64_t location) { *(context + 25) =            location; }
void set_merge_partner(uint64_t* context, uint64_t* partner)   { *(context + 26) = (uint64_t) partner; }

// -----------------------------------------------------------------
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

void reset_microkernel();

uint64_t* create_context(uint64_t* parent, uint64_t* vctxt);
uint64_t* cache_context(uint64_t* vctxt);

void save_context(uint64_t* context);
void map_page(uint64_t* context, uint64_t page, uint64_t frame);
void restore_region(uint64_t* context, uint64_t* table, uint64_t* parent_table, uint64_t lo, uint64_t hi);
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

uint64_t up_load_string(uint64_t* context, char* s, uint64_t SP);
void     up_load_arguments(uint64_t* context, uint64_t argc, uint64_t* argv);

uint64_t handle_system_call(uint64_t* context);
uint64_t handle_page_fault(uint64_t* context);
uint64_t handle_division_by_zero(uint64_t* context);
uint64_t handle_timer(uint64_t* context);
uint64_t handle_merge(uint64_t* context);

uint64_t handle_exception(uint64_t* context);

uint64_t mipster(uint64_t* to_context);
uint64_t hypster(uint64_t* to_context);

uint64_t mixter(uint64_t* to_context, uint64_t mix);

uint64_t minmob(uint64_t* to_context);
void     map_unmapped_pages(uint64_t* context);
uint64_t minster(uint64_t* to_context);
uint64_t mobster(uint64_t* to_context);

char*    replace_extension(char* filename, char* extension);
uint64_t monster(uint64_t* to_context);

uint64_t is_boot_level_zero();
void     boot_loader();

uint64_t selfie_run(uint64_t machine);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t* MY_CONTEXT = (uint64_t*) 0;

uint64_t DONOTEXIT = 0;
uint64_t EXIT      = 1;
uint64_t MERGE     = 2;

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
uint64_t EXITCODE_MODELCHECKINGERROR     = 13;
uint64_t EXITCODE_UNCAUGHTEXCEPTION      = 14;

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
// -------------------   C O R R E C T N E S S    ------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// -------------------------- DISASSEMBLER -------------------------
// -----------------------------------------------------------------

void translate_to_assembler();

void selfie_disassemble(uint64_t verbose);

// ------------------------ GLOBAL VARIABLES -----------------------

char*    assembly_name = (char*) 0; // name of assembly file
uint64_t assembly_fd   = 0;         // file descriptor of open assembly file

// -----------------------------------------------------------------
// ------------------------ MODEL GENERATOR ------------------------
// -----------------------------------------------------------------

uint64_t pc_nid(uint64_t nid, uint64_t pc);
uint64_t is_procedure_call(uint64_t instruction, uint64_t link);
uint64_t validate_procedure_body(uint64_t from_instruction, uint64_t from_link, uint64_t to_address);

void go_to_instruction(uint64_t from_instruction, uint64_t from_link, uint64_t from_address, uint64_t to_address, uint64_t condition_nid);

void reset_bounds();

void model_lui();

void transfer_bounds();

void model_addi();
void model_add();
void model_sub();
void model_mul();
void model_divu();
void model_remu();
void model_sltu();

uint64_t record_start_bounds(uint64_t offset, uint64_t activation_nid, uint64_t reg);
uint64_t record_end_bounds(uint64_t offset, uint64_t activation_nid, uint64_t reg);
uint64_t compute_address();

void model_ld();
void model_sd();

void model_beq();
void model_jal();
void model_jalr();
void model_ecall();

void translate_to_model();

void model_syscalls();

uint64_t control_flow(uint64_t activate_nid, uint64_t control_flow_nid);

void check_division_by_zero(uint64_t division, uint64_t flow_nid);

void check_address_validity(uint64_t start, uint64_t flow_nid, uint64_t lo_flow_nid, uint64_t up_flow_nid);

uint64_t selfie_model_generate();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t LO_FLOW = 32; // offset of nids of lower bounds on addresses in registers
uint64_t UP_FLOW = 64; // offset of nids of upper bounds on addresses in registers

// ------------------------ GLOBAL VARIABLES -----------------------

char*    model_name = (char*) 0; // name of model file
uint64_t model_fd   = 0;         // file descriptor of open model file

uint64_t bad_exit_code = 0; // model check for this exit code

uint64_t current_nid = 0; // nid of current line

uint64_t  reg_nids      = 0;             // nids of registers
uint64_t* reg_flow_nids = (uint64_t*) 0; // nids of most recent update of registers

uint64_t reg_a7 = 0; // most recent update of $a7 register in sequential translation flow

uint64_t pcs_nid = 0; // nid of first program counter flag

// per-instruction list of control-flow in-edges
uint64_t* control_in = (uint64_t*) 0;

// per-procedure (target of procedure call jal) address of matching jalr instruction
uint64_t* call_return = (uint64_t*) 0;

uint64_t current_callee = 0; // address of first instruction of current callee

// address of currently farthest forward branch or jump to find matching jalr instruction
uint64_t estimated_return = 0;

uint64_t memory_nid      = 0; // nid of memory
uint64_t memory_flow_nid = 0; // nid of most recent update of memory

uint64_t lo_memory_nid      = 0; // nid of lower bounds on addresses in memory
uint64_t lo_memory_flow_nid = 0; // nid of most recent update of lower bounds on addresses in memory

uint64_t up_memory_nid      = 0; // nid of upper bounds on addresses in memory
uint64_t up_memory_flow_nid = 0; // nid of most recent update of upper bounds on addresses in memory

// for checking division and remainder by zero
// 21 is nid of 1 which is ok as divisor
uint64_t division_flow_nid  = 21;
uint64_t remainder_flow_nid = 21;

// for checking address validity during state transitions with no memory access:
// 30 is nid of end of code segment which must be a valid address (thus also checked)
uint64_t access_flow_start_nid = 30;

// 50 is nid of 4GB of memory addresses
uint64_t lo_flow_start_nid = 30; // nid of most recent update of current lower bound
uint64_t up_flow_start_nid = 50; // nid of most recent update of current upper bound

// for checking address validity for a whole range of addresses
uint64_t access_flow_end_nid = 30;

uint64_t lo_flow_end_nid = 30; // nid of most recent update of current lower bound
uint64_t up_flow_end_nid = 50; // nid of most recent update of current upper bound

// keep track of pc flags of ecalls, 10 is nid of 1-bit 0
uint64_t ecall_flow_nid = 10;

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

char* dimacs_name = (char*) 0;

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
void     dimacs_word(char* word);
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

char* peek_argument(uint64_t lookahead);

char* get_argument();
void  set_argument(char* argv);

void print_usage();

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t  selfie_argc = 0;
uint64_t* selfie_argv = (uint64_t*) 0;

char* selfie_name = (char*) 0;

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

uint64_t log_ten(uint64_t n) {
  // use recursion for simplicity and educational value
  // for n < 1000000 performance is not relevant
  if (n < 10)
    return 0;
  else
    return log_ten(n / 10) + 1;
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

uint64_t max(uint64_t a, uint64_t b) {
  if (a > b)
    return a;
  else
    return b;
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

uint64_t load_character(char* s, uint64_t i) {
  // assert: i >= 0
  uint64_t a;

  // a is the index of the double word where
  // the to-be-loaded i-th character in s is
  a = i / SIZEOFUINT64;

  // CAUTION: at boot levels higher than zero, s is only accessible
  // in C* at machine word granularity, not individual characters

  // return i-th 8-bit character in s
  return get_bits(*((uint64_t*) s + a), (i % SIZEOFUINT64) * 8, 8);
}

char* store_character(char* s, uint64_t i, uint64_t c) {
  // assert: i >= 0, 0 <= c < 2^8 (all characters are 8-bit)
  uint64_t a;

  // a is the index of the double word where
  // the with c to-be-overwritten i-th character in s is
  a = i / SIZEOFUINT64;

  // CAUTION: at boot levels higher than zero, s is only accessible
  // in C* at machine word granularity, not individual characters

  // subtract the to-be-overwritten character to reset its bits in s
  // then add c to set its bits at the i-th position in s
  *((uint64_t*) s + a) = (*((uint64_t*) s + a) - left_shift(load_character(s, i), (i % SIZEOFUINT64) * 8)) + left_shift(c, (i % SIZEOFUINT64) * 8);

  return s;
}

char* string_alloc(uint64_t l) {
  // allocates zeroed memory for a string of l characters
  // plus a null terminator aligned to machine word size
  return (char*) zalloc(l + 1);
}

uint64_t string_length(char* s) {
  uint64_t i;

  i = 0;

  while (load_character(s, i) != 0)
    i = i + 1;

  return i;
}

char* string_copy(char* s) {
  uint64_t l;
  char* t;
  uint64_t i;

  l = string_length(s);

  t = string_alloc(l);

  i = 0;

  while (i <= l) {
    store_character(t, i, load_character(s, i));

    i = i + 1;
  }

  store_character(t, i, 0); // null-terminated string

  return t;
}

void string_reverse(char* s) {
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

uint64_t string_compare(char* s, char* t) {
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

uint64_t atoi(char* s) {
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
      printf2("%s: cannot convert non-decimal number %s\n", selfie_name, s);

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
        printf2("%s: cannot convert out-of-bound number %s\n", selfie_name, s);

        exit(EXITCODE_BADARGUMENTS);
      }
    else {
      // s contains a decimal number larger than UINT64_MAX
      printf2("%s: cannot convert out-of-bound number %s\n", selfie_name, s);

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

char* itoa(uint64_t n, char* s, uint64_t b, uint64_t a) {
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
  if (output_buffer) {
    // buffering character instead of outputting
    store_character(output_buffer, output_cursor, c);

    output_cursor = output_cursor + 1;
  } else {
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

        printf2("%s: could not write character to output file %s\n", selfie_name, output_name);
      }

      exit(EXITCODE_IOERROR);
    }
  }
}

void print(char* s) {
  uint64_t i;

  if (s == (char*) 0)
    print("NULL");
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
    print("end of file");
  else if (c == CHAR_TAB)
    print("tabulator");
  else if (c == CHAR_LF)
    print("line feed");
  else if (c == CHAR_CR)
    print("carriage return");
  else
    put_character(c);

  put_character(CHAR_SINGLEQUOTE);
}

void print_string(char* s) {
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

uint64_t print_format0(char* s, uint64_t i) {
  // print string s from index i on
  // ignore % formatting codes except for %%
  if (s == (char*) 0)
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

uint64_t print_format1(char* s, uint64_t i, char* a) {
  // print string s from index i on until next % formatting code except for %%
  // then print argument a according to the encountered % formatting code

  uint64_t p;

  if (s == (char*) 0)
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

void printf1(char* s, char* a1) {
  print_format0(s, print_format1(s, 0, a1));
}

void printf2(char* s, char* a1, char* a2) {
  print_format0(s, print_format1(s, print_format1(s, 0, a1), a2));
}

void printf3(char* s, char* a1, char* a2, char* a3) {
  print_format0(s, print_format1(s, print_format1(s, print_format1(s, 0, a1), a2), a3));
}

void printf4(char* s, char* a1, char* a2, char* a3, char* a4) {
  print_format0(s, print_format1(s, print_format1(s, print_format1(s, print_format1(s, 0, a1), a2), a3), a4));
}

void printf5(char* s, char* a1, char* a2, char* a3, char* a4, char* a5) {
  print_format0(s, print_format1(s, print_format1(s, print_format1(s, print_format1(s, print_format1(s, 0, a1), a2), a3), a4), a5));
}

void printf6(char* s, char* a1, char* a2, char* a3, char* a4, char* a5, char* a6) {
  print_format0(s, print_format1(s, print_format1(s, print_format1(s, print_format1(s, print_format1(s, print_format1(s, 0, a1), a2), a3), a4), a5), a6));
}

void sprintf1(char* b, char* s, char* a1) {
  output_buffer = b;
  output_cursor = 0;

  printf1(s, a1);put_character(0);

  output_buffer = (char*) 0;
  output_cursor = 0;
}

void sprintf2(char* b, char* s, char* a1, char* a2) {
  output_buffer = b;
  output_cursor = 0;

  printf2(s, a1, a2);put_character(0);

  output_buffer = (char*) 0;
  output_cursor = 0;
}

void sprintf3(char* b, char* s, char* a1, char* a2, char* a3) {
  output_buffer = b;
  output_cursor = 0;

  printf3(s, a1, a2, a3);put_character(0);

  output_buffer = (char*) 0;
  output_cursor = 0;
}

void sprintf4(char* b, char* s, char* a1, char* a2, char* a3, char* a4) {
  output_buffer = b;
  output_cursor = 0;

  printf4(s, a1, a2, a3, a4);put_character(0);

  output_buffer = (char*) 0;
  output_cursor = 0;
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
  else if (memory == (uint64_t*) 0) {
    printf1("%s: malloc out of memory\n", selfie_name);

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
    print("end of file");
  else
    print((char*) *(SYMBOLS + symbol));

  put_character(CHAR_DOUBLEQUOTE);
}

void print_line_number(char* message, uint64_t line) {
  printf4("%s: %s in %s in line %d: ", selfie_name, message, source_name, (char*) line);
}

void syntax_error_message(char* message) {
  print_line_number("syntax error", line_number);
  printf1("%s\n", message);
}

void syntax_error_character(uint64_t expected) {
  print_line_number("syntax error", line_number);
  print_character(expected);
  print(" expected but ");
  print_character(character);
  print(" found\n");
}

void syntax_error_identifier(char* expected) {
  print_line_number("syntax error", line_number);
  print_string(expected);
  print(" expected but ");
  print_string(identifier);
  print(" found\n");
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
    printf2("%s: could not read character from input file %s\n", selfie_name, source_name);

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
          // only line feeds count, not carriage returns
          line_number = line_number + 1;
        else if (character == CHAR_EOF) {
          // multi-line comment is not terminated
          syntax_error_message("runaway multi-line comment");

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
  return string_compare(identifier, (char*) *(SYMBOLS + keyword));
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
        identifier = string_alloc(MAX_IDENTIFIER_LENGTH);

        i = 0;

        while (is_character_letter_or_digit_or_underscore()) {
          if (i >= MAX_IDENTIFIER_LENGTH) {
            syntax_error_message("identifier too long");

            exit(EXITCODE_SCANNERERROR);
          }

          store_character(identifier, i, character);

          i = i + 1;

          get_character();
        }

        store_character(identifier, i, 0); // null-terminated string

        symbol = identifier_or_keyword();

      } else if (is_character_digit()) {
        // accommodate integer and null for termination
        integer = string_alloc(MAX_INTEGER_LENGTH);

        i = 0;

        while (is_character_digit()) {
          if (i >= MAX_INTEGER_LENGTH) {
            if (integer_is_signed)
              syntax_error_message("signed integer out of bound");
            else
              syntax_error_message("integer out of bound");

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
              syntax_error_message("signed integer out of bound");

              exit(EXITCODE_SCANNERERROR);
            }

        symbol = SYM_INTEGER;

      } else if (character == CHAR_SINGLEQUOTE) {
        get_character();

        literal = 0;

        if (character == CHAR_EOF) {
          syntax_error_message("reached end of file looking for a character literal");

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
        string = string_alloc(MAX_STRING_LENGTH);

        i = 0;

        while (is_character_not_double_quote_or_new_line_or_eof()) {
          if (i >= MAX_STRING_LENGTH) {
            syntax_error_message("string too long");

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
        print_line_number("syntax error", line_number);
        print("found unknown character ");
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
    syntax_error_message("unknown escape sequence found");

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

void create_symbol_table_entry(uint64_t which_table, char* string, uint64_t line, uint64_t class, uint64_t type, uint64_t value, uint64_t address) {
  uint64_t* new_entry;
  uint64_t* hashed_entry_address;

  new_entry = allocate_symbol_table_entry();

  set_string(new_entry, string);
  set_line_number(new_entry, line);
  set_class(new_entry, class);
  set_type(new_entry, type);
  set_value(new_entry, value);
  set_address(new_entry, address);

  // create entry at head of list of symbols
  if (which_table == GLOBAL_TABLE) {
    set_scope(new_entry, REG_GP);

    hashed_entry_address = global_symbol_table + hash((uint64_t*) string);

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

uint64_t* search_symbol_table(uint64_t* entry, char* string, uint64_t class) {
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

uint64_t* search_global_symbol_table(char* string, uint64_t class) {
  return search_symbol_table((uint64_t*) *(global_symbol_table + hash((uint64_t*) string)), string, class);
}

uint64_t* get_scoped_symbol_table_entry(char* string, uint64_t class) {
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

        print_line_number("syntax error", get_line_number(entry));
        printf1("procedure %s undefined\n", get_string(entry));
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
    syntax_error_message("out of registers");

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
    syntax_error_message("illegal register access");

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
    syntax_error_message("illegal register access");

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
    syntax_error_message("out of registers");

    exit(EXITCODE_COMPILERERROR);
  }
}

void tfree(uint64_t number_of_temporaries) {
  if (allocated_temporaries >= number_of_temporaries)
    allocated_temporaries = allocated_temporaries - number_of_temporaries;
  else {
    syntax_error_message("illegal register deallocation");

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
  print_line_number("syntax error", line_number);
  print_symbol(expected);
  print(" expected but ");
  print_symbol(symbol);
  print(" found\n");
}

void syntax_error_unexpected() {
  print_line_number("syntax error", line_number);
  print("unexpected symbol ");
  print_symbol(symbol);
  print(" found\n");
}

void print_type(uint64_t type) {
  if (type == UINT64_T)
    print("uint64_t");
  else if (type == UINT64STAR_T)
    print("uint64_t*");
  else if (type == VOID_T)
    print("void");
  else
    print("unknown");
}

void type_warning(uint64_t expected, uint64_t found) {
  print_line_number("warning", line_number);
  print("type mismatch, ");
  print_type(expected);
  print(" expected but ");
  print_type(found);
  print(" found\n");
}

uint64_t* get_variable_or_big_int(char* variable_or_big_int, uint64_t class) {
  uint64_t* entry;

  if (class == BIGINT)
    return search_global_symbol_table(variable_or_big_int, class);
  else {
    entry = get_scoped_symbol_table_entry(variable_or_big_int, class);

    if (entry == (uint64_t*) 0) {
      print_line_number("syntax error", line_number);
      printf1("%s undeclared\n", variable_or_big_int);

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

uint64_t load_variable_or_big_int(char* variable_or_big_int, uint64_t class) {
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

void load_string(char* string) {
  uint64_t length;

  // assert: n = allocated_temporaries

  length = string_length(string) + 1;

  allocated_memory = allocated_memory + round_up(length, REGISTERSIZE);

  create_symbol_table_entry(GLOBAL_TABLE, string, line_number, STRING, UINT64STAR_T, 0, -allocated_memory);

  load_integer(-allocated_memory);

  emit_add(current_temporary(), REG_GP, current_temporary());

  // assert: allocated_temporaries == n + 1
}

uint64_t help_call_codegen(uint64_t* entry, char* procedure) {
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

uint64_t compile_call(char* procedure) {
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
  char* variable_or_procedure_name;

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
          syntax_error_message("(uint64_t*) + (uint64_t*) is undefined");
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
        syntax_error_message("(uint64_t) - (uint64_t*) is undefined");
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

    // for lack of boolean type
    ltype = UINT64_T;

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
  char* variable_or_procedure_name;
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

    create_symbol_table_entry(LOCAL_TABLE, "missing variable name", line_number, VARIABLE, type, 0, offset);
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

void compile_procedure(char* procedure, uint64_t type) {
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

        if (string_compare(procedure, "main")) {
          // first source containing main procedure provides binary name
          binary_name = source_name;

          // account for initial call to main procedure
          number_of_calls = number_of_calls + 1;
        }
      } else {
        // procedure already defined
        print_line_number("warning", line_number);
        printf1("redefinition of procedure %s ignored\n", procedure);
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
  char* variable_or_procedure_name;
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
            print_line_number("warning", current_line_number);
            printf1("redefinition of global variable %s ignored\n", variable_or_procedure_name);
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
      syntax_error_message("maximum program break exceeded");

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
    entry = search_global_symbol_table(string_copy("_bump"), VARIABLE);

    // store aligned program break in _bump
    emit_sd(get_scope(entry), get_address(entry), REG_A0);

    // reset return register to initial return value
    emit_addi(REG_A0, REG_ZR, 0);

    // assert: stack is set up with argv pointer still missing
    //
    //    sp
    //     |
    //     V
    // | argc | argv[0] | argv[1] | ... | argv[n]

    talloc();

    // first obtain pointer to argv
    //
    //    sp + REGISTERSIZE
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
    entry = get_scoped_symbol_table_entry(string_copy("main"), PROCEDURE);

    help_call_codegen(entry, "main");
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

  source_name = "library";

  binary_name = source_name;

  // allocate memory for storing binary
  binary       = zalloc(MAX_BINARY_LENGTH);
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

  // implicitly declare main procedure in global symbol table
  // copy "main" string into zeroed double word to obtain unique hash
  create_symbol_table_entry(GLOBAL_TABLE, string_copy("main"), 0, PROCEDURE, UINT64_T, 0, 0);

  while (link) {
    if (number_of_remaining_arguments() == 0)
      link = 0;
    else if (load_character(peek_argument(0), 0) == '-')
      link = 0;
    else {
      source_name = get_argument();

      number_of_source_files = number_of_source_files + 1;

      printf2("%s: selfie compiling %s with starc\n", selfie_name, source_name);

      // assert: source_name is mapped and not longer than MAX_FILENAME_LENGTH

      source_fd = sign_extend(open(source_name, O_RDONLY, 0), SYSCALL_BITWIDTH);

      if (signed_less_than(source_fd, 0)) {
        printf2("%s: could not open input file %s\n", selfie_name, source_name);

        exit(EXITCODE_IOERROR);
      }

      reset_scanner();
      reset_parser();

      compile_cstar();

      printf4("%s: %d characters read in %d lines and %d comments\n", selfie_name,
        (char*) number_of_read_characters,
        (char*) line_number,
        (char*) number_of_comments);

      printf4("%s: with %d(%.2d%%) characters in %d actual symbols\n", selfie_name,
        (char*) (number_of_read_characters - number_of_ignored_characters),
        (char*) fixed_point_percentage(fixed_point_ratio(number_of_read_characters, number_of_read_characters - number_of_ignored_characters, 4), 4),
        (char*) number_of_scanned_symbols);

      printf4("%s: %d global variables, %d procedures, %d string literals\n", selfie_name,
        (char*) number_of_global_variables,
        (char*) number_of_procedures,
        (char*) number_of_strings);

      printf6("%s: %d calls, %d assignments, %d while, %d if, %d return\n", selfie_name,
        (char*) number_of_calls,
        (char*) number_of_assignments,
        (char*) number_of_while,
        (char*) number_of_if,
        (char*) number_of_return);
    }
  }

  if (number_of_source_files == 0)
    printf1("%s: nothing to compile, only library generated\n", selfie_name);

  emit_bootstrapping();

  emit_data_segment();

  ELF_header = create_elf_header(binary_length, code_length);

  entry_point = ELF_ENTRY_POINT;

  printf3("%s: symbol table search time was %d iterations on average and %d in total\n", selfie_name,
    (char*) (total_search_time / number_of_searches),
    (char*) total_search_time);

  printf4("%s: %d bytes generated with %d instructions and %d bytes of data\n", selfie_name,
    (char*) binary_length,
    (char*) (code_length / INSTRUCTIONSIZE),
    (char*) (binary_length - code_length));

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

char* get_register_name(uint64_t reg) {
  return (char*) *(REGISTERS + reg);
}

void print_register_name(uint64_t reg) {
  print(get_register_name(reg));
}

// -----------------------------------------------------------------
// ------------------------ ENCODER/DECODER ------------------------
// -----------------------------------------------------------------

void check_immediate_range(uint64_t immediate, uint64_t bits) {
  if (is_signed_integer(immediate, bits) == 0) {
    print_line_number("encoding error", line_number);
    printf3("%d expected between %d and %d\n",
      (char*) immediate,
      (char*) -two_to_the_power_of(bits - 1),
      (char*) two_to_the_power_of(bits - 1) - 1);

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

void print_instruction_counter(uint64_t total, uint64_t counter, char* mnemonics) {
  printf3("%s: %d(%.2d%%)",
    mnemonics,
    (char*) counter,
    (char*) fixed_point_percentage(fixed_point_ratio(total, counter, 4), 4));
}

void print_instruction_counters() {
  uint64_t ic;

  ic = get_total_number_of_instructions();

  printf1("%s: init:    ", selfie_name);
  print_instruction_counter(ic, ic_lui, "lui");
  print(", ");
  print_instruction_counter(ic, ic_addi, "addi");
  println();

  printf1("%s: memory:  ", selfie_name);
  print_instruction_counter(ic, ic_ld, "ld");
  print(", ");
  print_instruction_counter(ic, ic_sd, "sd");
  println();

  printf1("%s: compute: ", selfie_name);
  print_instruction_counter(ic, ic_add, "add");
  print(", ");
  print_instruction_counter(ic, ic_sub, "sub");
  print(", ");
  print_instruction_counter(ic, ic_mul, "mul");
  print(", ");
  print_instruction_counter(ic, ic_divu, "divu");
  print(", ");
  print_instruction_counter(ic, ic_remu, "remu");
  println();

  printf1("%s: compare: ", selfie_name);
  print_instruction_counter(ic, ic_sltu, "sltu");
  println();

  printf1("%s: control: ", selfie_name);
  print_instruction_counter(ic, ic_beq, "beq");
  print(", ");
  print_instruction_counter(ic, ic_jal, "jal");
  print(", ");
  print_instruction_counter(ic, ic_jalr, "jalr");
  println();

  printf1("%s: system:  ", selfie_name);
  print_instruction_counter(ic, ic_ecall, "ecall");
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
    syntax_error_message("maximum code length exceeded");

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
  if (baddr - code_length >= MAX_DATA_LENGTH) {
    syntax_error_message("maximum data length exceeded");

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
  char* s;
  uint64_t i;
  uint64_t l;

  s = get_string(entry);

  i = 0;

  l = round_up(string_length(s) + 1, REGISTERSIZE);

  while (i < l) {
    // CAUTION: at boot levels higher than zero, s is only accessible
    // in C* at machine word granularity, not individual characters
    emit_data_word(*((uint64_t*) s), get_address(entry) + i, get_line_number(entry));

    s = (char*) ((uint64_t*) s + 1);

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

uint64_t* allocate_elf_header() {
  // allocate and map (on all boot levels) zeroed memory for ELF header preparing
  // read calls (memory must be mapped) and write calls (memory must be mapped and zeroed)
  return touch(zalloc(ELF_HEADER_LEN), ELF_HEADER_LEN);
}

uint64_t* create_elf_header(uint64_t binary_length, uint64_t code_length) {
  uint64_t* header;

  header = allocate_elf_header();

  // store all data necessary for creating a minimal and valid ELF64 file and program header

  // RISC-U ELF64 file header:
  *(header + 0) = 127                               // magic number part 0 is 0x7F
                + left_shift((uint64_t) 'E', 8)     // magic number part 1
                + left_shift((uint64_t) 'L', 16)    // magic number part 2
                + left_shift((uint64_t) 'F', 24)    // magic number part 3
                + left_shift(2, 32)                 // file class is ELFCLASS64
                + left_shift(1, 40)                 // object file data structures endianness is ELFDATA2LSB
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
  *(header + 9)  = ELF_HEADER_LEN;                // segment offset in file (must be page-aligned)
  *(header + 10) = ELF_ENTRY_POINT;               // virtual address in memory
  *(header + 11) = 0;                             // physical address (reserved)
  *(header + 12) = binary_length;                 // size of segment in file
  *(header + 13) = binary_length;                 // size of segment in memory
  *(header + 14) = PAGESIZE;                      // alignment of segment

  // This field is not part of the standard ELF header but
  // used by selfie to load its own generated ELF files
  *(header + 15) = code_length;

  return header;
}

uint64_t validate_elf_header(uint64_t* header) {
  uint64_t  new_entry_point;
  uint64_t  new_binary_length;
  uint64_t  new_code_length;
  uint64_t  position;
  uint64_t* valid_header;

  new_entry_point   = *(header + 10);
  new_binary_length = *(header + 12);
  new_code_length   = *(header + 15);

  if (new_binary_length != *(header + 13))
    // segment size in file is not the same as segment size in memory
    return 0;

  if (new_entry_point > VIRTUALMEMORYSIZE - PAGESIZE - new_binary_length)
    // binary does not fit into virtual address space
    return 0;

  valid_header = create_elf_header(new_binary_length, new_code_length);

  position = 0;

  while (position < ELF_HEADER_LEN / SIZEOFUINT64) {
    if (*(header + position) != *(valid_header + position))
      return 0;

    position = position + 1;
  }

  entry_point   = new_entry_point;
  binary_length = new_binary_length;
  code_length   = new_code_length;

  return 1;
}

uint64_t open_write_only(char* name) {
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
    printf2("%s: nothing to emit to output file %s\n", selfie_name, binary_name);

    return;
  }

  // assert: binary_name is mapped and not longer than MAX_FILENAME_LENGTH

  fd = open_write_only(binary_name);

  if (signed_less_than(fd, 0)) {
    printf2("%s: could not create binary output file %s\n", selfie_name, binary_name);

    exit(EXITCODE_IOERROR);
  }

  // assert: ELF_header is mapped

  // first write ELF header
  if (write(fd, ELF_header, ELF_HEADER_LEN) != ELF_HEADER_LEN) {
    printf2("%s: could not write ELF header of binary output file %s\n", selfie_name, binary_name);

    exit(EXITCODE_IOERROR);
  }

  // assert: binary is mapped

  // then write binary
  if (write(fd, binary, binary_length) != binary_length) {
    printf2("%s: could not write binary into binary output file %s\n", selfie_name, binary_name);

    exit(EXITCODE_IOERROR);
  }

  printf5("%s: %d bytes with %d instructions and %d bytes of data written into %s\n", selfie_name,
    (char*) (ELF_HEADER_LEN + binary_length),
    (char*) (code_length / INSTRUCTIONSIZE),
    (char*) (binary_length - code_length),
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
    printf2("%s: could not open input file %s\n", selfie_name, binary_name);

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

  // this call makes sure ELF_header is mapped for reading into it
  ELF_header = allocate_elf_header();

  // read ELF_header first
  number_of_read_bytes = read(fd, ELF_header, ELF_HEADER_LEN);

  if (number_of_read_bytes == ELF_HEADER_LEN) {
    if (validate_elf_header(ELF_header)) {
      if (binary_length <= MAX_BINARY_LENGTH) {
        // now read binary including global variables and strings
        number_of_read_bytes = sign_extend(read(fd, binary, binary_length), SYSCALL_BITWIDTH);

        if (signed_less_than(0, number_of_read_bytes)) {
          // check if we are really at EOF
          if (read(fd, binary_buffer, SIZEOFUINT64) == 0) {
            printf5("%s: %d bytes with %d instructions and %d bytes of data loaded from %s\n",
              selfie_name,
              (char*) ELF_HEADER_LEN,
              (char*) (code_length / INSTRUCTIONSIZE),
              (char*) (binary_length - code_length),
              binary_name);

            return;
          }
        }
      }
    }
  }

  printf2("%s: failed to load code from input file %s\n", selfie_name, binary_name);

  exit(EXITCODE_IOERROR);
}

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emit_exit() {
  create_symbol_table_entry(LIBRARY_TABLE, "exit", 0, PROCEDURE, VOID_T, 0, binary_length);

  // load signed 32-bit integer exit code
  emit_ld(REG_A0, REG_SP, 0);

  // remove the exit code from the stack
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  // load the correct syscall number and invoke syscall
  emit_addi(REG_A7, REG_ZR, SYSCALL_EXIT);

  emit_ecall();

  // never returns here
}

void implement_exit(uint64_t* context) {
  // parameter;
  uint64_t signed_int_exit_code;

  if (debug_syscalls) {
    print("(exit): ");
    print_register_hexadecimal(REG_A0);
    print(" |- ->\n");
  }

  signed_int_exit_code = *(get_regs(context) + REG_A0);

  set_exit_code(context, sign_shrink(signed_int_exit_code, SYSCALL_BITWIDTH));

  if (symbolic) {
    print("\n(push 1)\n");

    printf2("(assert (and %s (not (= %s (_ bv0 64))))); exit in ",
      path_condition,
      smt_value(*(registers + REG_A0), (char*) *(reg_sym + REG_A0)));
    print_code_context_for_instruction(pc);

    print("\n(check-sat)\n(get-model)\n(pop 1)\n");

    return;
  }

  printf4("%s: %s exiting with exit code %d and %.2dMB mallocated memory\n", selfie_name,
    get_name(context),
    (char*) sign_extend(get_exit_code(context), SYSCALL_BITWIDTH),
    (char*) fixed_point_ratio(get_program_break(context) - get_original_break(context), MEGABYTE, 2));
}

void emit_read() {
  create_symbol_table_entry(LIBRARY_TABLE, "read", 0, PROCEDURE, UINT64_T, 0, binary_length);

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

  if (debug_syscalls) {
    print("(read): ");
    print_register_value(REG_A0);
    print(",");
    print_register_hexadecimal(REG_A1);
    print(",");
    print_register_value(REG_A2);
    print(" |- ");
    print_register_value(REG_A0);
  }

  fd      = *(get_regs(context) + REG_A0);
  vbuffer = *(get_regs(context) + REG_A1);
  size    = *(get_regs(context) + REG_A2);

  if (debug_read)
    printf4("%s: trying to read %d bytes from file with descriptor %d into buffer at virtual address %p\n", selfie_name,
      (char*) size,
      (char*) fd,
      (char*) vbuffer);

  read_total = 0;

  bytes_to_read = SIZEOFUINT64;

  failed = 0;

  while (size > 0) {
    if (is_valid_virtual_address(vbuffer)) {
      if (size < bytes_to_read)
        bytes_to_read = size;

      if (symbolic) {
        store_symbolic_memory(vbuffer,
          0,
          0,
          smt_variable("r", bytes_to_read * 8),
          bytes_to_read * 8);

        // save symbolic memory here since context switching has already happened
        set_symbolic_memory(context, symbolic_memory);

        actually_read = bytes_to_read;
      } else if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
        buffer = tlb(get_pt(context), vbuffer);

        actually_read = sign_extend(read(fd, buffer, bytes_to_read), SYSCALL_BITWIDTH);
      } else {
        failed = 1;

        size = 0;

        if (debug_read)
          printf2("%s: reading into virtual address %p failed because the address is unmapped\n", selfie_name,
            (char*) vbuffer);
      }

      if (failed == 0) {
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
      }
    } else {
      failed = 1;

      size = 0;

      if (debug_read)
        printf2("%s: reading into virtual address %p failed because the address is invalid\n", selfie_name,
          (char*) vbuffer);
    }
  }

  if (failed)
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);
  else
    *(get_regs(context) + REG_A0) = read_total;

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);

  if (debug_read)
    printf3("%s: actually read %d bytes from file with descriptor %d\n", selfie_name,
      (char*) read_total,
      (char*) fd);

  if (debug_syscalls) {
    print(" -> ");
    print_register_value(REG_A0);
    println();
  }
}

void emit_write() {
  create_symbol_table_entry(LIBRARY_TABLE, "write", 0, PROCEDURE, UINT64_T, 0, binary_length);

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

  if (debug_syscalls) {
    print("(write): ");
    print_register_value(REG_A0);
    print(",");
    print_register_hexadecimal(REG_A1);
    print(",");
    print_register_value(REG_A2);
    print(" |- ");
    print_register_value(REG_A0);
  }

  fd      = *(get_regs(context) + REG_A0);
  vbuffer = *(get_regs(context) + REG_A1);
  size    = *(get_regs(context) + REG_A2);

  if (debug_write)
    printf4("%s: trying to write %d bytes from buffer at virtual address %p into file with descriptor %d\n", selfie_name,
      (char*) size,
      (char*) vbuffer,
      (char*) fd);

  written_total = 0;

  bytes_to_write = SIZEOFUINT64;

  failed = 0;

  while (size > 0) {
    if (is_valid_virtual_address(vbuffer)) {
      if (symbolic) {
        // TODO: What should symbolically executed code actually output?
        written_total = size;

        size = 0;
      } else if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
        buffer = tlb(get_pt(context), vbuffer);

        if (size < bytes_to_write)
          bytes_to_write = size;

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
          printf2("%s: writing into virtual address %p failed because the address is unmapped\n", selfie_name,
            (char*) vbuffer);
      }
    } else {
      failed = 1;

      size = 0;

      if (debug_write)
        printf2("%s: writing into virtual address %p failed because the address is invalid\n", selfie_name,
          (char*) vbuffer);
    }
  }

  if (failed)
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);
  else
    *(get_regs(context) + REG_A0) = written_total;

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);

  if (debug_write)
    printf3("%s: actually wrote %d bytes into file with descriptor %d\n", selfie_name,
      (char*) written_total,
      (char*) fd);

  if (debug_syscalls) {
    print(" -> ");
    print_register_value(REG_A0);
    println();
  }
}

void emit_open() {
  create_symbol_table_entry(LIBRARY_TABLE, "open", 0, PROCEDURE, UINT64_T, 0, binary_length);

  emit_ld(REG_A3, REG_SP, 0); // mode
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A2, REG_SP, 0); // flags
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A1, REG_SP, 0); // filename
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  // DIRFD_AT_FDCWD makes sure that openat behaves like open
  emit_addi(REG_A0, REG_ZR, DIRFD_AT_FDCWD);

  emit_addi(REG_A7, REG_ZR, SYSCALL_OPENAT);

  emit_ecall();

  emit_jalr(REG_ZR, REG_RA, 0);
}

uint64_t down_load_string(uint64_t* table, uint64_t vaddr, char* s) {
  uint64_t i;
  uint64_t* sword;
  uint64_t j;

  i = 0;

  while (i < MAX_FILENAME_LENGTH / SIZEOFUINT64) {
    if (is_valid_virtual_address(vaddr)) {
      if (symbolic) {
        sword = load_symbolic_memory(vaddr);

        if (sword) {
          if (is_symbolic_value(sword)) {
            printf1("%s: detected symbolic value ", selfie_name);
            print_symbolic_memory(sword);
            print(" in filename of open call\n");

            exit(EXITCODE_SYMBOLICEXECUTIONERROR);
          } else
            // CAUTION: at boot levels higher than zero, s is only accessible
            // in C* at machine word granularity, not individual characters
            *((uint64_t*) s + i) = get_word_value(sword);
        } else
          // assert: vaddr is mapped
          *((uint64_t*) s + i) = load_virtual_memory(table, vaddr);
      } else if (is_virtual_address_mapped(table, vaddr))
        *((uint64_t*) s + i) = load_virtual_memory(table, vaddr);
      else {
        if (debug_open)
          printf2("%s: opening file with name at virtual address %p failed because the address is unmapped\n", selfie_name,
            (char*) vaddr);

        return 0;
      }

      j = 0;

      // check if string ends in the current machine word
      while (j < SIZEOFUINT64) {
        if (load_character((char*) ((uint64_t*) s + i), j) == 0)
          return 1;

        j = j + 1;
      }

      // advance to the next machine word in virtual memory
      vaddr = vaddr + SIZEOFUINT64;

      // advance to the next machine word in our memory
      i = i + 1;
    } else {
      if (debug_open)
        printf2("%s: opening file with name at virtual address %p failed because the address is invalid\n", selfie_name,
          (char*) vaddr);

      return 0;
    }
  }

  return 0;
}

void implement_openat(uint64_t* context) {
  // parameters
  uint64_t vfilename;
  uint64_t flags;
  uint64_t mode;

  // return value
  uint64_t fd;

  if (debug_syscalls) {
    print("(openat): ");
    print_register_hexadecimal(REG_A0);
    print(",");
    print_register_hexadecimal(REG_A1);
    print(",");
    print_register_hexadecimal(REG_A2);
    print(",");
    print_register_octal(REG_A3);
    print(" |- ");
    print_register_value(REG_A1);
  }

  /* We actually emulate the part of the openat system call here that is
     implemented by the open system call which is deprecated in Linux.
     In particular, the first parameter (REG_A0) is ignored here while
     set to DIRFD_AT_FDCWD in the wrapper for the open library call to
     make sure openat behaves like open when bootstrapping selfie. */

  vfilename = *(get_regs(context) + REG_A1);
  flags     = *(get_regs(context) + REG_A2);
  mode      = *(get_regs(context) + REG_A3);

  if (down_load_string(get_pt(context), vfilename, filename_buffer)) {
    if (symbolic)
      // TODO: check if opening vfilename has been attempted before
      fd = 0;
    else
      fd = sign_extend(open(filename_buffer, flags, mode), SYSCALL_BITWIDTH);

    *(get_regs(context) + REG_A0) = fd;

    if (debug_open)
      printf5("%s: opened file %s with flags %x and mode %o returning file descriptor %d\n", selfie_name,
        filename_buffer,
        (char*) flags,
        (char*) mode,
        (char*) fd);
  } else {
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);

    if (debug_open)
      printf2("%s: opening file with name at virtual address %p failed because the name is too long\n", selfie_name,
        (char*) vfilename);
  }

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);

  if (debug_syscalls) {
    print(" -> ");
    print_register_value(REG_A0);
    println();
  }
}

void emit_malloc() {
  uint64_t* entry;

  create_symbol_table_entry(LIBRARY_TABLE, "malloc", 0, PROCEDURE, UINT64STAR_T, 0, binary_length);

  // on boot levels higher than zero, zalloc falls back to malloc
  // assuming that page frames are zeroed on boot level zero
  create_symbol_table_entry(LIBRARY_TABLE, "zalloc", 0, PROCEDURE, UINT64STAR_T, 0, binary_length);

  // allocate memory in data segment for recording state of
  // malloc (bump pointer) in compiler-declared global variable
  allocated_memory = allocated_memory + REGISTERSIZE;

  // define global variable _bump for storing malloc's bump pointer
  // copy "_bump" string into zeroed double word to obtain unique hash
  create_symbol_table_entry(GLOBAL_TABLE, string_copy("_bump"), 1, VARIABLE, UINT64_T, 0, -allocated_memory);

  // do not account for _bump as global variable
  number_of_global_variables = number_of_global_variables - 1;

  entry = search_global_symbol_table(string_copy("_bump"), VARIABLE);

  // allocate register for size parameter
  talloc();

  emit_ld(current_temporary(), REG_SP, 0); // size
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  // round up size to double-word alignment
  emit_round_up(current_temporary(), SIZEOFUINT64);

  // allocate register to compute new bump pointer
  talloc();

  // assert: current temporary is $t1 register to enable propagation of
  // lower and upper bounds on addresses in model generation of brk syscall

  // get current _bump which will be returned upon success
  emit_ld(current_temporary(), get_scope(entry), get_address(entry));

  // call brk syscall to set new program break to _bump + size
  emit_add(REG_A0, current_temporary(), previous_temporary());
  emit_addi(REG_A7, REG_ZR, SYSCALL_BRK);
  emit_ecall();

  // return 0 if memory allocation failed, that is,
  // if new program break is still _bump and size != 0
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

  emit_jalr(REG_ZR, REG_RA, 0);
}

void implement_brk(uint64_t* context) {
  // parameter
  uint64_t program_break;

  // local variables
  uint64_t previous_program_break;
  uint64_t valid;

  if (debug_syscalls) {
    print("(brk): ");
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
    if (debug_syscalls)
      print(" |- ->\n");

    if (debug_brk)
      printf2("%s: setting program break to %p\n", selfie_name, (char*) program_break);

    set_program_break(context, program_break);
  } else {
    // error returns current program break
    program_break = previous_program_break;

    if (debug_brk)
      printf2("%s: retrieving current program break %p\n", selfie_name, (char*) program_break);

    if (debug_syscalls) {
      print(" |- ");
      print_register_hexadecimal(REG_A0);
    }

    *(get_regs(context) + REG_A0) = program_break;

    if (debug_syscalls) {
      print(" -> ");
      print_register_hexadecimal(REG_A0);
      println();
    }
  }

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

// -----------------------------------------------------------------
// ----------------------- HYPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emit_switch() {
  create_symbol_table_entry(LIBRARY_TABLE, "hypster_switch", 0, PROCEDURE, UINT64STAR_T, 0, binary_length);

  emit_ld(REG_A1, REG_SP, 0); // number of instructions to execute
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_ld(REG_A0, REG_SP, 0); // context to which we switch
  emit_addi(REG_SP, REG_SP, REGISTERSIZE);

  emit_addi(REG_A7, REG_ZR, SYSCALL_SWITCH);

  emit_ecall();

  // save context from which we are switching here in return register
  emit_addi(REG_A0, REG_A6, 0);

  emit_jalr(REG_ZR, REG_RA, 0);
}

uint64_t* do_switch(uint64_t* from_context, uint64_t* to_context, uint64_t timeout) {
  restore_context(to_context);

  // restore machine state
  pc        = get_pc(to_context);
  registers = get_regs(to_context);
  pt        = get_pt(to_context);

  if (symbolic) {
    path_condition  = get_path_condition(to_context);
    symbolic_memory = get_symbolic_memory(to_context);
    reg_sym         = get_symbolic_regs(to_context);
  }

  // use REG_A6 instead of REG_A0 for returning from_context
  // to avoid overwriting REG_A0 in to_context
  if (get_parent(from_context) != MY_CONTEXT)
    *(registers + REG_A6) = (uint64_t) get_virtual_context(from_context);
  else
    *(registers + REG_A6) = (uint64_t) from_context;

  timer = timeout;

  if (debug_switch) {
    printf3("%s: switched from context %p to context %p", selfie_name,
      (char*) from_context,
      (char*) to_context);
    if (timer != TIMEROFF)
      printf1(" to execute %d instructions", (char*) timer);
    println();
  }

  return to_context;
}

void implement_switch() {
  // parameters
  uint64_t* to_context;
  uint64_t timeout;

  if (debug_syscalls) {
    print("(switch): ");
    print_register_hexadecimal(REG_A0);
    print(",");
    print_register_value(REG_A1);
    print(" |- ");
    print_register_value(REG_A6);
  }

  to_context = (uint64_t*) *(registers + REG_A0);
  timeout    =             *(registers + REG_A1);

  save_context(current_context);

  // cache context on my boot level before switching
  to_context = cache_context(to_context);

  current_context = do_switch(current_context, to_context, timeout);

  if (debug_syscalls) {
    print(" -> ");
    print_register_hexadecimal(REG_A6);
    println();
  }
}

uint64_t* mipster_switch(uint64_t* to_context, uint64_t timeout) {
  current_context = do_switch(current_context, to_context, timeout);

  run_until_exception();

  save_context(current_context);

  return current_context;
}

uint64_t* hypster_switch(uint64_t* to_context, uint64_t timeout) {
  // this procedure is only executed at boot level zero
  return mipster_switch(to_context, timeout);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------    A R C H I T E C T U R E    -----------------
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
    printf5("%s: tlb access:\n vaddr: %p\n page:  %p\n frame: %p\n paddr: %p\n", selfie_name,
      (char*) vaddr,
      (char*) (page * PAGESIZE),
      (char*) frame,
      (char*) paddr);

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

void print_code_line_number_for_instruction(uint64_t address, uint64_t offset) {
  if (code_line_number != (uint64_t*) 0)
    printf1("(~%d)", (char*) *(code_line_number + (address - offset) / INSTRUCTIONSIZE));
}

void print_code_context_for_instruction(uint64_t address) {
  if (run) {
    printf2("%s: pc=%x", binary_name, (char*) address);
    print_code_line_number_for_instruction(address, entry_point);
    if (symbolic)
      // skip further output
      return;
    else
      print(": ");
  } else {
    if (model_check) {
      printf1("%x", (char*) address);
      print_code_line_number_for_instruction(address, entry_point);
      print(": ");
    } else if (disassemble_verbose) {
      printf1("%x", (char*) address);
      print_code_line_number_for_instruction(address, 0);
      printf1(": %p: ", (char*) ir);
    }
  }
}

void print_lui() {
  print_code_context_for_instruction(pc);
  printf2("lui %s,%x", get_register_name(rd), (char*) sign_shrink(imm, 20));
}

void print_lui_before() {
  print(": |- ");
  print_register_hexadecimal(rd);
}

void print_lui_after() {
  print(" -> ");
  print_register_hexadecimal(rd);
}

void record_lui_addi_add_sub_mul_sltu_jal_jalr() {
  record_state(*(registers + rd));
}

void do_lui() {
  // load upper immediate

  if (rd != REG_ZR)
    // semantics of lui
    *(registers + rd) = left_shift(imm, 12);

  pc = pc + INSTRUCTIONSIZE;

  ic_lui = ic_lui + 1;
}

void undo_lui_addi_add_sub_mul_divu_remu_sltu_ld_jal_jalr() {
  *(registers + rd) = *(values + (tc % MAX_REPLAY_LENGTH));
}

void constrain_lui() {
  if (rd != REG_ZR)
    *(reg_sym + rd) = 0;
}

void print_addi() {
  print_code_context_for_instruction(pc);

  if (rd == REG_ZR)
    if (rs1 == REG_ZR)
      if (imm == 0) {
        print("nop");

        return;
      }

  printf3("addi %s,%s,%d", get_register_name(rd), get_register_name(rs1), (char*) imm);
}

void print_addi_before() {
  print(": ");
  print_register_value(rs1);
  print(" |- ");
  print_register_value(rd);
}

void print_addi_add_sub_mul_divu_remu_sltu_after() {
  print(" -> ");
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

void constrain_addi() {
  if (rd != REG_ZR) {
    if (*(reg_sym + rs1))
      *(reg_sym + rd) = (uint64_t) smt_binary("bvadd", (char*) *(reg_sym + rs1), bv_constant(imm));
    else
      *(reg_sym + rd) = 0;
  }
}

void print_add_sub_mul_divu_remu_sltu(char *mnemonics) {
  print_code_context_for_instruction(pc);
  printf4("%s %s,%s,%s", mnemonics, get_register_name(rd), get_register_name(rs1), get_register_name(rs2));
}

void print_add_sub_mul_divu_remu_sltu_before() {
  print(": ");
  print_register_value(rs1);
  print(",");
  print_register_value(rs2);
  print(" |- ");
  print_register_value(rd);
}

void do_add() {
  if (rd != REG_ZR)
    // semantics of add
    *(registers + rd) = *(registers + rs1) + *(registers + rs2);

  pc = pc + INSTRUCTIONSIZE;

  ic_add = ic_add + 1;
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
    if (string_compare(operator, "bvudiv")) {
      print("(push 1)\n");
      printf2("(assert (and %s %s)); check if a division by zero is possible", path_condition, smt_binary("=", op2, bv_constant(0)));
      print("\n(check-sat)\n(get-model)\n(pop 1)\n");
    }
  }
}

void do_sub() {
  if (rd != REG_ZR)
    // semantics of sub
    *(registers + rd) = *(registers + rs1) - *(registers + rs2);

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

void record_divu_remu() {
  // record even for division by zero
  record_state(*(registers + rd));
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

void zero_extend_sltu() {
  if (rd != REG_ZR)
    if (*(reg_sym + rd))
      *(reg_sym + rd) = (uint64_t) smt_unary(bv_zero_extension(1), (char*) *(reg_sym + rd));
}

void print_ld() {
  print_code_context_for_instruction(pc);
  printf3("ld %s,%d(%s)", get_register_name(rd), (char*) imm, get_register_name(rs1));
}

void print_ld_before() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  print(": ");
  print_register_hexadecimal(rs1);

  if (is_valid_virtual_address(vaddr))
    if (is_virtual_address_mapped(pt, vaddr)) {
      if (is_system_register(rd))
        printf2(",mem[%x]=%x |- ", (char*) vaddr, (char*) load_virtual_memory(pt, vaddr));
      else
        printf2(",mem[%x]=%d |- ", (char*) vaddr, (char*) load_virtual_memory(pt, vaddr));
      print_register_value(rd);

      return;
    }

  print(" |-");
}

void print_ld_after(uint64_t vaddr) {
  if (is_valid_virtual_address(vaddr))
    if (is_virtual_address_mapped(pt, vaddr)) {
      print(" -> ");
      print_register_value(rd);
      printf1("=mem[%x]", (char*) vaddr);
    }
}

void record_ld() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  if (is_valid_virtual_address(vaddr))
    if (is_virtual_address_mapped(pt, vaddr))
      record_state(*(registers + rd));
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

void constrain_ld() {
  uint64_t vaddr;
  uint64_t* sword;
  uint64_t a;

  // load double word

  if (*(reg_sym + rs1)) {
    // symbolic memory addresses not yet supported
    printf2("%s: symbolic memory address in ld instruction at %x", selfie_name, (char*) pc);
    print_code_line_number_for_instruction(pc, entry_point);
    println();

    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  vaddr = *(registers + rs1) + imm;

  if (is_valid_virtual_address(vaddr)) {
    // semantics of ld
    if (rd != REG_ZR) {
      sword = load_symbolic_memory(vaddr);

      if (sword) {
        *(registers + rd) = get_word_value(sword);

        if (get_number_of_bits(sword) < CPUBITWIDTH)
          *(reg_sym + rd) = (uint64_t) smt_unary(bv_zero_extension(get_number_of_bits(sword)), get_word_symbolic(sword));
        else
          *(reg_sym + rd) = (uint64_t) get_word_symbolic(sword);
      } else {
        // assert: vaddr is mapped
        *(registers + rd) = load_virtual_memory(pt, vaddr);
        *(reg_sym + rd)   = 0;
      }
    }

    // keep track of instruction address for profiling loads
    a = (pc - entry_point) / INSTRUCTIONSIZE;

    pc = pc + INSTRUCTIONSIZE;

    // keep track of number of loads in total
    ic_ld = ic_ld + 1;

    // and individually
    *(loads_per_instruction + a) = *(loads_per_instruction + a) + 1;
  } else
    // invalid concrete memory address
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
}

void print_sd() {
  print_code_context_for_instruction(pc);
  printf3("sd %s,%d(%s)", get_register_name(rs2), (char*) imm, get_register_name(rs1));
}

void print_sd_before() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  print(": ");
  print_register_hexadecimal(rs1);

  if (is_valid_virtual_address(vaddr))
    if (is_virtual_address_mapped(pt, vaddr)) {
      print(",");
      print_register_value(rs2);
      if (is_system_register(rd))
        printf2(" |- mem[%x]=%x", (char*) vaddr, (char*) load_virtual_memory(pt, vaddr));
      else
        printf2(" |- mem[%x]=%d", (char*) vaddr, (char*) load_virtual_memory(pt, vaddr));

      return;
    }

  print(" |-");
}

void print_sd_after(uint64_t vaddr) {
  if (is_valid_virtual_address(vaddr))
    if (is_virtual_address_mapped(pt, vaddr)) {
      printf1(" -> mem[%x]=", (char*) vaddr);
      print_register_value(rs2);
    }
}

void record_sd() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  if (is_valid_virtual_address(vaddr))
    if (is_virtual_address_mapped(pt, vaddr))
      record_state(load_virtual_memory(pt, vaddr));
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

void undo_sd() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  store_virtual_memory(pt, vaddr, *(values + (tc % MAX_REPLAY_LENGTH)));
}

void constrain_sd() {
  uint64_t vaddr;
  uint64_t a;

  // store double word

  if (*(reg_sym + rs1)) {
    // symbolic memory addresses not yet supported
    printf2("%s: symbolic memory address in sd instruction at %x", selfie_name, (char*) pc);
    print_code_line_number_for_instruction(pc, entry_point);
    println();

    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  vaddr = *(registers + rs1) + imm;

  if (is_valid_virtual_address(vaddr)) {
    // semantics of sd
    store_symbolic_memory(vaddr,
      *(registers + rs2),
      (char*) *(reg_sym + rs2),
      0,
      CPUBITWIDTH);

    // keep track of instruction address for profiling stores
    a = (pc - entry_point) / INSTRUCTIONSIZE;

    pc = pc + INSTRUCTIONSIZE;

    // keep track of number of stores in total
    ic_sd = ic_sd + 1;

    // and individually
    *(stores_per_instruction + a) = *(stores_per_instruction + a) + 1;
  } else
    // invalid concrete memory address
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);
}

void print_beq() {
  print_code_context_for_instruction(pc);
  printf3("beq %s,%s,%d", get_register_name(rs1), get_register_name(rs2), (char*) signed_division(imm, INSTRUCTIONSIZE));
  if (disassemble_verbose)
    printf1("[%x]", (char*) (pc + imm));
}

void print_beq_before() {
  print(": ");
  print_register_value(rs1);
  print(",");
  print_register_value(rs2);
  printf1(" |- pc=%x", (char*) pc);
}

void print_beq_after() {
  printf1(" -> pc=%x", (char*) pc);
}

void record_beq() {
  record_state(0);
}

void do_beq() {
  // branch on equal

  // semantics of beq
  if (*(registers + rs1) == *(registers + rs2))
    pc = pc + imm;
  else
    pc = pc + INSTRUCTIONSIZE;

  ic_beq = ic_beq + 1;
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

  printf2("(assert (= %s %s)); beq in ", bvar, smt_binary("bvcomp", op1, op2));
  print_code_context_for_instruction(pc);
  println();

  pvar = smt_variable("p", 1);

  printf2("(assert (= %s %s)); path condition in ", pvar, path_condition);
  print_code_context_for_instruction(pc);
  println();

  // increase the number of executed symbolic beq instructions
  set_beq_counter(current_context, get_beq_counter(current_context) + 1);

  if (get_beq_counter(current_context) < BEQ_LIMIT) {
    // save symbolic memory so that it is copied correctly afterwards
    set_symbolic_memory(current_context, symbolic_memory);

    // the copied context is executed later and takes the other path
    add_waiting_context(copy_context(current_context, pc + imm, smt_binary("and", pvar, bvar)));

    path_condition = smt_binary("and", pvar, smt_unary("not", bvar));

    // set the merge location only when merging is enabled
    if (merge_enabled)
      set_merge_location(current_context, find_merge_location(imm));

    // check if a context is waiting to be merged
    if (current_mergeable_context != (uint64_t*) 0) {
      // we cannot merge with this one (yet), so we push it back onto the stack of mergeable contexts
      add_mergeable_context(current_mergeable_context);
      current_mergeable_context = (uint64_t*) 0;
    }

    pc = pc + INSTRUCTIONSIZE;
  } else {
    // if the limit of symbolic beq instructions is reached, the part of the path still continues until it can be merged or has reached its
    // maximal execution depth, respectively, but only by following the true case of the next encountered symbolic beq instructions
    path_condition = smt_binary("and", pvar, bvar);

    pc = pc + imm;
  }
}

void print_jal() {
  print_code_context_for_instruction(pc);
  printf2("jal %s,%d", get_register_name(rd), (char*) signed_division(imm, INSTRUCTIONSIZE));
  if (disassemble_verbose)
    printf1("[%x]", (char*) (pc + imm));
}

void print_jal_before() {
  print(": |- ");
  if (rd != REG_ZR) {
    print_register_hexadecimal(rd);
    print(",");
  }
  printf1("pc=%x", (char*) pc);
}

void print_jal_jalr_after() {
  print_beq_after();
  if (rd != REG_ZR) {
    print(",");
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

    // and individually
    *(iterations_per_loop + a) = *(iterations_per_loop + a) + 1;
  } else
    // just jump forward
    pc = pc + imm;

  ic_jal = ic_jal + 1;
}

void print_jalr() {
  print_code_context_for_instruction(pc);
  printf3("jalr %s,%d(%s)", get_register_name(rd), (char*) signed_division(imm, INSTRUCTIONSIZE), get_register_name(rs1));
}

void print_jalr_before() {
  print(": ");
  print_register_hexadecimal(rs1);
  print(" |- ");
  if (rd != REG_ZR) {
    print_register_hexadecimal(rd);
    print(",");
  }
  printf1("pc=%x", (char*) pc);
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

void constrain_jalr() {
  if (*(reg_sym + rs1)) {
    // symbolic memory addresses not yet supported
    printf2("%s: symbolic memory address in jalr instruction at %x", selfie_name, (char*) pc);
    print_code_line_number_for_instruction(pc, entry_point);
    println();

    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

void print_ecall() {
  print_code_context_for_instruction(pc);
  print("ecall");
}

void record_ecall() {
  // TODO: record all side effects
  record_state(*(registers + REG_A0));
}

void do_ecall() {
  ic_ecall = ic_ecall + 1;

  if (redo) {
    // TODO: redo all side effects
    *(registers + REG_A0) = *(values + (tc % MAX_REPLAY_LENGTH));

    pc = pc + INSTRUCTIONSIZE;
  } else if (*(registers + REG_A7) == SYSCALL_SWITCH)
    if (record) {
      printf1("%s: context switching during recording is unsupported\n", selfie_name);

      exit(EXITCODE_BADARGUMENTS);
    } else if (symbolic) {
      printf1("%s: context switching during symbolic execution is unsupported\n", selfie_name);

      exit(EXITCODE_BADARGUMENTS);
    } else {
      pc = pc + INSTRUCTIONSIZE;

      implement_switch();
    }
  else
    // all system calls other than switch are handled by exception
    throw_exception(EXCEPTION_SYSCALL, 0);
}

void undo_ecall() {
  uint64_t a0;

  a0 = *(registers + REG_A0);

  // TODO: undo all side effects
  *(registers + REG_A0) = *(values + (tc % MAX_REPLAY_LENGTH));

  // save register a0 for redoing system call
  *(values + (tc % MAX_REPLAY_LENGTH)) = a0;
}

void print_data_line_number() {
  if (data_line_number != (uint64_t*) 0)
    printf1("(~%d)", (char*) *(data_line_number + (pc - code_length) / REGISTERSIZE));
}

void print_data_context(uint64_t data) {
  printf1("%x", (char*) pc);

  if (disassemble_verbose) {
    print_data_line_number();
    print(": ");
    print_hexadecimal(data, SIZEOFUINT64 * 2);
    print(" ");
  } else
    print(": ");
}

void print_data(uint64_t data) {
  if (disassemble_verbose)
    print_data_context(data);
  printf1(".quad %x", (char*) data);
}

// -----------------------------------------------------------------
// -------------------------- REPLAY ENGINE ------------------------
// -----------------------------------------------------------------

void record_state(uint64_t value) {
  *(pcs + (tc % MAX_REPLAY_LENGTH))    = pc;
  *(values + (tc % MAX_REPLAY_LENGTH)) = value;

  tc = tc + 1;
}

void replay_trace() {
  uint64_t trace_length;
  uint64_t tl;

  if (tc < MAX_REPLAY_LENGTH)
    trace_length = tc;
  else
    trace_length = MAX_REPLAY_LENGTH;

  record = 0;

  tl = trace_length;

  // undo trace_length number of instructions
  while (tl > 0) {
    tc = tc - 1;

    pc = *(pcs + (tc % MAX_REPLAY_LENGTH));

    fetch();
    decode();
    execute_undo();

    tl = tl - 1;
  }

  redo = 1;

  debug_syscalls = 1;

  tl = trace_length;

  // redo trace_length number of instructions
  while (tl > 0) {
    // assert: pc == *(pcs + (tc % MAX_REPLAY_LENGTH))

    fetch();
    decode();
    execute_debug();

    tc = tc + 1;
    tl = tl - 1;
  }

  debug_syscalls = 0;

  redo   = 0;
  record = 1;
}

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
    set_word_symbolic(sword, smt_variable("m", SIZEOFUINT64 * 8));

    printf2("(assert (= %s %s)); sd in ", get_word_symbolic(sword), sym);
    print_code_context_for_instruction(pc);
    println();
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

void update_begin_of_shared_symbolic_memory(uint64_t* context) {
  uint64_t* sword;

  if (context == (uint64_t*) 0)
    return;

  sword = get_symbolic_memory(context);

  while (sword) {
    if (get_word_address(sword) == BEGIN_OF_SHARED_SYMBOLIC_MEMORY) {
      set_word_address(sword, DELETED);
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
    print(get_word_symbolic(sword));

  printf2("[%x]@%x\n", (char*) get_word_value(sword), (char*) get_word_address(sword));
}

// -----------------------------------------------------------------
// ------------------- SYMBOLIC EXECUTION ENGINE -------------------
// -----------------------------------------------------------------

char* bv_constant(uint64_t value) {
  char* string;

  string = string_alloc(5 + 20 + 4); // 64-bit numbers require up to 20 decimal digits

  sprintf1(string, "(_ bv%d 64)", (char*) value);

  return string;
}

char* bv_variable(uint64_t bits) {
  char* string;

  string = string_alloc(10 + 2); // up to 64-bit variables require up to 2 decimal digits

  sprintf1(string, "(_ BitVec %d)", (char*) bits);

  return string;
}

char* bv_zero_extension(uint64_t bits) {
  char* string;

  string = string_alloc(15 + 2); // up to 64-bit variables require up to 2 decimal digits

  sprintf1(string, "(_ zero_extend %d)", (char*) (CPUBITWIDTH - bits));

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

  sprintf2(svar, "%s%d", prefix, (char*) variable_version);

  printf2("(declare-fun %s () (_ BitVec %d)); variable for ", svar, (char*) bits);
  print_code_context_for_instruction(pc);
  println();

  variable_version = variable_version + 1;

  return svar;
}

char* smt_unary(char* opt, char* op) {
  char* string;

  string = string_alloc(1 + string_length(opt) + 1 + string_length(op) + 1);

  sprintf2(string, "(%s %s)", opt, op);

  return string;
}

char* smt_binary(char* opt, char* op1, char* op2) {
  char* string;

  string = string_alloc(1 + string_length(opt) + 1 + string_length(op1) + 1 + string_length(op2) + 1);

  sprintf3(string, "(%s %s %s)", opt, op1, op2);

  return string;
}

char* smt_ternary(char* opt, char* op1, char* op2, char* op3) {
  char* string;

  string = string_alloc(1 + string_length(opt) + 1 + string_length(op1) + 1 + string_length(op2) + 1 + string_length(op3) + 1);

  sprintf4(string, "(%s %s %s %s)", opt, op1, op2, op3);

  return string;
}

uint64_t find_merge_location(uint64_t beq_imm) {
  uint64_t original_pc;
  uint64_t merge_location;

  // assert: the current instruction is a symbolic beq instruction
  original_pc = pc;

  // examine last instruction before target location of the beq instruction
  pc = pc + (beq_imm - INSTRUCTIONSIZE);

  // we need to know which instruction it is
  fetch();
  decode();

  if (is != JAL)
    /* no jal instruction -> end of if without else branch
       merge is directly at target location of the beq instruction possible

    note: this is a dependency on the selfie compiler */
    merge_location = original_pc + beq_imm;
  else {
    if (signed_less_than(imm, 0) == 0) {
      /* jal with positive imm -> end of if with else branch
         we have to skip the else branch in order to merge afterwards

         note: this is a dependency on the selfie compiler
         the selfie compiler emits a jal instruction with a positive immediate value if it sees an else branch */
      merge_location = pc + imm;

      pc = original_pc + INSTRUCTIONSIZE;
    } else
      /* jal with negative imm -> end of loop body
         merge is only outside of the loop body possible

         note: this is a dependency on the selfie compiler
         the selfie compiler emits a jal instruction with a negative immediate value at
         the end of the loop body in order to jump back to the loop condition */
      merge_location = pc + INSTRUCTIONSIZE;
  }

  // we need to check if we are inside of a recursion before we reach the merge location
  while (pc != merge_location) {
    fetch();
    decode();

    if (is == JAL)
      // if we are inside of a (arbitrarily deep nested) recursion,
      // we merge only after the entire recursion has been finished (i.e. the program
      // has reached a program location which is not part of any recursion)
      if (currently_in_this_procedure(pc + imm, current_context)) {
        if (get_in_recursion(current_context) == 0)
          set_outside_rec_loc(current_context, get_merge_location_from_corresponding_prologue_start(pc + imm, current_context));

        merge_location = get_outside_rec_loc(current_context);
        set_in_recursion(current_context, 1);
      }

    pc = pc + INSTRUCTIONSIZE;
  }

  // restore the original program state
  pc = original_pc;
  fetch();
  decode();

  return merge_location;
}

void add_mergeable_context(uint64_t* context) {
  uint64_t* entry;

  entry = smalloc(2 * SIZEOFUINT64STAR);

  *(entry + 0) = (uint64_t) mergeable_contexts;
  *(entry + 1) = (uint64_t) context;

  mergeable_contexts = entry;
}

uint64_t* get_mergeable_context() {
  uint64_t* head;

  if (mergeable_contexts == (uint64_t*) 0)
    return (uint64_t*) 0;

  head = mergeable_contexts;
  mergeable_contexts = (uint64_t*) *(head + 0);

  return (uint64_t*) *(head + 1);
}

void add_waiting_context(uint64_t* context) {
  uint64_t* entry;

  entry = smalloc(2 * SIZEOFUINT64STAR);

  *(entry + 0) = (uint64_t) waiting_contexts;
  *(entry + 1) = (uint64_t) context;

  waiting_contexts = entry;
}

uint64_t* get_waiting_context() {
  uint64_t* head;

  if (waiting_contexts == (uint64_t*) 0)
    return (uint64_t*) 0;

  head = waiting_contexts;
  waiting_contexts = (uint64_t*) *(head + 0);

  return (uint64_t*) *(head + 1);
}

void add_prologue_start_and_corresponding_merge_location(uint64_t prologue_start, uint64_t merge_location, uint64_t* context) {
  uint64_t* entry;

  entry = get_prologues(context);

  // do not add duplicates
  while (entry) {
    if (*(entry + 1) == prologue_start)
      return;

    entry = (uint64_t*) *(entry + 0);
  }

  entry = smalloc(3 * SIZEOFUINT64STAR);

  *(entry + 0) = (uint64_t) get_prologues(context);
  *(entry + 1) = (uint64_t) prologue_start;
  *(entry + 2) = (uint64_t) merge_location;

  set_prologues(context, entry);
}

uint64_t get_merge_location_from_corresponding_prologue_start(uint64_t prologue_start, uint64_t* context) {
  uint64_t* entry;

  entry = get_prologues(context);

  while (entry) {
    if (*(entry + 1) == prologue_start)
      return (uint64_t) *(entry + 2);

    entry = (uint64_t*) *(entry + 0);
  }

  return -1;
}

uint64_t currently_in_this_procedure(uint64_t prologue_start, uint64_t* context) {
  return (get_merge_location_from_corresponding_prologue_start(prologue_start, context) != (uint64_t) -1);
}

void merge(uint64_t* active_context, uint64_t* mergeable_context, uint64_t location) {
  // do not merge if merging is disabled
  if (merge_enabled == 0) {
    if (current_mergeable_context != (uint64_t*) 0) {
      add_mergeable_context(current_mergeable_context);
      current_mergeable_context = (uint64_t*) 0;
    }

    return;
  }

  print("; merging two contexts at ");
  print_code_context_for_instruction(location);
  println();

  if (get_prologues(active_context) != (uint64_t*) 0)
    if (get_pc(active_context) == *(get_prologues(active_context) + 2))
      // we have finished the recursion (i.e. the program has reached a program location which is not part of any recursion)
      set_in_recursion(active_context, 0);

  // merging the symbolic store
  merge_symbolic_memory_and_registers(active_context, mergeable_context);

  // merging the path condition
  path_condition = smt_binary("or", get_path_condition(active_context), get_path_condition(mergeable_context));
  set_path_condition(active_context, path_condition);

  if (get_execution_depth(mergeable_context) > get_execution_depth(active_context))
    set_execution_depth(active_context, get_execution_depth(mergeable_context));

  current_mergeable_context = get_mergeable_context();

  // it may be possible that more contexts can be merged
  if (current_mergeable_context != (uint64_t*) 0)
    if (pc == get_pc(current_mergeable_context))
      merge(active_context, current_mergeable_context, pc);

}

void merge_symbolic_memory_and_registers(uint64_t* active_context, uint64_t* mergeable_context) {
  // merging the symbolic memory
  merge_symbolic_memory_of_active_context(active_context, mergeable_context);
  merge_symbolic_memory_of_mergeable_context(active_context, mergeable_context);

  // merging the registers
  merge_registers(active_context, mergeable_context);

  // the shared symbolic memory space needs needs to be updated since the other context was merged into the active context
  update_begin_of_shared_symbolic_memory(active_context);
}

void merge_symbolic_memory_of_active_context(uint64_t* active_context, uint64_t* mergeable_context) {
  uint64_t* sword_from_active_context;
  uint64_t* sword_from_mergeable_context;
  uint64_t  in_unshared_symbolic_memory;

  sword_from_active_context = symbolic_memory;

  while (sword_from_active_context) {
    // we need to stop at the end of the unshared symbolic memory space of the active context
    if (get_word_address(sword_from_active_context) == BEGIN_OF_SHARED_SYMBOLIC_MEMORY)
      return;

    // check if the word has not already been deleted
    if (get_word_address(sword_from_active_context) != (uint64_t) DELETED) {
      // check if the word has not already been merged
      if (get_word_address(sword_from_active_context) != (uint64_t) MERGED) {
        sword_from_mergeable_context = get_symbolic_memory(mergeable_context);
        in_unshared_symbolic_memory = 1;

        while (sword_from_mergeable_context) {
          // we need to know if we are in the unshared symbolic memory space of the mergeable context
          if (get_word_address(sword_from_mergeable_context) == BEGIN_OF_SHARED_SYMBOLIC_MEMORY)
            in_unshared_symbolic_memory = 0;

          if (get_word_address(sword_from_active_context) == get_word_address(sword_from_mergeable_context)) {
            if (get_word_symbolic(sword_from_active_context) != (char*) 0) {
              if (get_word_symbolic(sword_from_mergeable_context) != (char*) 0) {
                if (get_word_symbolic(sword_from_active_context) != get_word_symbolic(sword_from_mergeable_context)) {
                  // merge symbolic values if they are different
                  set_word_symbolic(sword_from_active_context,
                    smt_ternary("ite",
                      get_path_condition(active_context),
                      get_word_symbolic(sword_from_active_context),
                      get_word_symbolic(sword_from_mergeable_context)
                    )
                  );

                  // we mark the word as merged so that we do not merge it again when merging from the side of the mergeable context
                  if (in_unshared_symbolic_memory)
                    set_word_address(sword_from_mergeable_context, MERGED);

                  // we need to break out of the loop
                  sword_from_mergeable_context = (uint64_t*) - 1;
                }
              } else {
                // merge symbolic value and concrete value
                set_word_symbolic(sword_from_active_context,
                  smt_ternary("ite",
                    get_path_condition(active_context),
                    get_word_symbolic(sword_from_active_context),
                    bv_constant(get_word_value(sword_from_mergeable_context))
                  )
                );

                // we mark the word as merged so that we do not merge it again when merging from the side of the mergeable context
                if (in_unshared_symbolic_memory)
                  set_word_address(sword_from_mergeable_context, MERGED);

                // we need to break out of the loop
                sword_from_mergeable_context = (uint64_t*) - 1;
              }
            } else {
              if (get_word_symbolic(sword_from_mergeable_context) != (char*) 0) {
                // merge concrete value and symbolic value
                set_word_symbolic(sword_from_active_context,
                  smt_ternary("ite",
                    get_path_condition(active_context),
                    bv_constant(get_word_value(sword_from_active_context)),
                    get_word_symbolic(sword_from_mergeable_context)
                  )
                );

                // we mark the word as merged so that we do not merge it again when merging from the side of the mergeable context
                if (in_unshared_symbolic_memory)
                  set_word_address(sword_from_mergeable_context, MERGED);

                // we need to break out of the loop
                sword_from_mergeable_context = (uint64_t*) - 1;
              } else {
                if (get_word_value(sword_from_active_context) != get_word_value(sword_from_mergeable_context)) {
                  // merge concrete values if they are different
                  set_word_symbolic(sword_from_active_context,
                    smt_ternary("ite",
                      get_path_condition(active_context),
                      bv_constant(get_word_value(sword_from_active_context)),
                      bv_constant(get_word_value(sword_from_mergeable_context))
                    )
                  );

                  // we mark the word as merged so that we do not merge it again when merging from the side of the mergeable context
                  if (in_unshared_symbolic_memory)
                    set_word_address(sword_from_mergeable_context, MERGED);

                  // we need to break out of the loop
                  sword_from_mergeable_context = (uint64_t*) - 1;
                }
              }
            }
          }
          if (sword_from_mergeable_context == (uint64_t*) - 1)
            sword_from_mergeable_context = (uint64_t*) 0;
          else
            sword_from_mergeable_context = get_next_word(sword_from_mergeable_context);
        }
      }
    }

    sword_from_active_context = get_next_word(sword_from_active_context);
  }
}

void merge_symbolic_memory_of_mergeable_context(uint64_t* active_context, uint64_t* mergeable_context) {
  uint64_t* sword_from_active_context;
  uint64_t* sword_from_mergeable_context;
  uint64_t* sword;
  uint64_t* additional_memory;
  uint64_t  shared_symbolic_memory_depth;

  additional_memory = symbolic_memory;
  sword_from_mergeable_context = get_symbolic_memory(mergeable_context);

  while (sword_from_mergeable_context) {
    // we need to stop at the end of the unshared symbolic memory space of the mergeable context
    if (get_word_address(sword_from_mergeable_context) == BEGIN_OF_SHARED_SYMBOLIC_MEMORY) {
      symbolic_memory = additional_memory;

      // the active context contains now the merged symbolic memory
      set_symbolic_memory(active_context, symbolic_memory);
      return;
    }

    // check if the word has not already been deleted
    if (get_word_address(sword_from_mergeable_context) != (uint64_t) DELETED) {
      // check if the word has not already been merged
      if (get_word_address(sword_from_mergeable_context) != (uint64_t) MERGED) {
        sword_from_active_context = symbolic_memory;
        shared_symbolic_memory_depth = 0;

        while (sword_from_active_context) {
          // we need to know how far we are into the shared symbolic memory space
          if (get_word_address(sword_from_active_context) == (uint64_t) BEGIN_OF_SHARED_SYMBOLIC_MEMORY)
            shared_symbolic_memory_depth = shared_symbolic_memory_depth + 1;

          if (get_word_address(sword_from_active_context) == get_word_address(sword_from_mergeable_context)) {
            if (get_word_symbolic(sword_from_active_context) != (char*) 0) {
              if (get_word_symbolic(sword_from_mergeable_context) != (char*) 0) {
                if (get_word_symbolic(sword_from_active_context) != get_word_symbolic(sword_from_mergeable_context)) {
                  // merge symbolic values if they are different
                  if (shared_symbolic_memory_depth < 2)
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
                  }

                  // we need to break out of the loop
                  sword_from_active_context = (uint64_t*) - 1;
                }
              } else {
                // merge symbolic value and concrete value
                if (shared_symbolic_memory_depth < 2)
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
                }

                // we need to break out of the loop
                sword_from_active_context = (uint64_t*) - 1;
              }
            } else {
              if (get_word_symbolic(sword_from_mergeable_context) != (char*) 0) {
                // merge concrete value and symbolic value
                if (shared_symbolic_memory_depth < 2)
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
                }

                // we need to break out of the loop
                sword_from_active_context = (uint64_t*) - 1;
              } else {
                if (get_word_value(sword_from_active_context) != get_word_value(sword_from_mergeable_context)) {
                  // merge concrete values if they are different
                  if (shared_symbolic_memory_depth < 2)
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
                  }

                  // we need to break out of the loop
                  sword_from_active_context = (uint64_t*) - 1;
                }
              }
            }
          }
          if (sword_from_active_context == (uint64_t*) - 1)
            sword_from_active_context = (uint64_t*) 0;
          else
            sword_from_active_context = get_next_word(sword_from_active_context);
        }
      }
    }
    sword_from_mergeable_context = get_next_word(sword_from_mergeable_context);
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

uint64_t* merge_if_possible_and_get_next_context(uint64_t* context) {
  uint64_t merge_not_finished;
  uint64_t mergeable;
  uint64_t pauseable;

  if (merge_enabled)
    merge_not_finished = 1;
  else
    merge_not_finished = 0;

  while (merge_not_finished) {
    mergeable = 1;
    pauseable = 1;

    if (context == (uint64_t*) 0) {
      // break out of the loop
      mergeable = 0;
      pauseable = 0;
    } else
      symbolic_memory = get_symbolic_memory(context);

    // check if the context can be merged with one or more mergeable contexts
    while (mergeable) {
      if (current_mergeable_context == (uint64_t*) 0)
        current_mergeable_context = get_mergeable_context();

      if (current_mergeable_context != (uint64_t*) 0) {
        if (get_pc(context) == get_pc(current_mergeable_context)) {
          if (merge_enabled)
            merge(context, current_mergeable_context, get_pc(context));
          else
            mergeable = 0;
        } else
          mergeable = 0;
      } else
        mergeable = 0;
    }

    // check if the context has reached a merge location and needs to be paused
    while (pauseable) {
      if (get_pc(context) == get_merge_location(context)) {
        current_mergeable_context = context;
        context = get_waiting_context();

        if (context) {
          if (get_pc(context) == get_pc(current_mergeable_context)) {
            pauseable = 0;
            mergeable = 1;
          }
          else {
            add_mergeable_context(current_mergeable_context);
            current_mergeable_context = (uint64_t*) 0;
          }
        }

        // break out of the loop
        if (context == (uint64_t*) 0) {
          mergeable = 0;
          pauseable = 0;
        }

      } else {
        if (current_mergeable_context == (uint64_t*) 0)
          current_mergeable_context = get_mergeable_context();

        if (current_mergeable_context != (uint64_t*) 0)
          if (get_pc(context) == get_pc(current_mergeable_context))
            mergeable = 1;

        pauseable = 0;
      }
    }

    if (mergeable == 0)
      if (pauseable == 0)
        merge_not_finished = 0;
  }

  // check if there are contexts which have been paused and were not merged yet
  if (context == (uint64_t*) 0)
    context = get_mergeable_context();

  if (merge_enabled == 0)
    merge_not_finished = 0;

  return context;
}


// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void print_register_hexadecimal(uint64_t reg) {
  printf2("%s=%x", get_register_name(reg), (char*) *(registers + reg));
}

void print_register_octal(uint64_t reg) {
  printf2("%s=%o", get_register_name(reg), (char*) *(registers + reg));
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
  if (is_system_register(reg))
    print_register_hexadecimal(reg);
  else
    printf3("%s=%d(%x)", get_register_name(reg), (char*) *(registers + reg), (char*) *(registers + reg));
}

void print_exception(uint64_t exception, uint64_t faulting_page) {
  print((char*) *(EXCEPTIONS + exception));

  if (exception == EXCEPTION_PAGEFAULT)
    printf1(" at %p", (char*) faulting_page);
}

void throw_exception(uint64_t exception, uint64_t faulting_page) {
  if (get_exception(current_context) != EXCEPTION_NOEXCEPTION)
    if (get_exception(current_context) != exception) {
      printf2("%s: context %p throws ", selfie_name, (char*) current_context);
      print_exception(exception, faulting_page);
      print(" exception in presence of ");
      print_exception(get_exception(current_context), get_faulting_page(current_context));
      print(" exception\n");

      exit(EXITCODE_MULTIPLEEXCEPTIONERROR);
    }

  set_exception(current_context, exception);
  set_faulting_page(current_context, faulting_page);

  trap = 1;

  if (debug_exception) {
    printf2("%s: context %p throws ", selfie_name, (char*) current_context);
    print_exception(exception, faulting_page);
    print(" exception\n");
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

void decode() {
  opcode = get_opcode(ir);

  is = 0;

  if (opcode == OP_IMM) {
    decode_i_format();

    if (funct3 == F3_ADDI)
      is = ADDI;
  } else if (opcode == OP_LD) {
    decode_i_format();

    if (funct3 == F3_LD)
      is = LD;
  } else if (opcode == OP_SD) {
    decode_s_format();

    if (funct3 == F3_SD)
      is = SD;
  } else if (opcode == OP_OP) { // could be ADD, SUB, MUL, DIVU, REMU, SLTU
    decode_r_format();

    if (funct3 == F3_ADD) { // = F3_SUB = F3_MUL
      if (funct7 == F7_ADD)
        is = ADD;
      else if (funct7 == F7_SUB)
        is = SUB;
      else if (funct7 == F7_MUL)
        is = MUL;
    } else if (funct3 == F3_DIVU) {
      if (funct7 == F7_DIVU)
        is = DIVU;
    } else if (funct3 == F3_REMU) {
      if (funct7 == F7_REMU)
        is = REMU;
    } else if (funct3 == F3_SLTU) {
      if (funct7 == F7_SLTU)
        is = SLTU;
    }
  } else if (opcode == OP_BRANCH) {
    decode_b_format();

    if (funct3 == F3_BEQ)
      is = BEQ;
  } else if (opcode == OP_JAL) {
    decode_j_format();

    is = JAL;
  } else if (opcode == OP_JALR) {
    decode_i_format();

    if (funct3 == F3_JALR)
      is = JALR;
  } else if (opcode == OP_LUI) {
    decode_u_format();

    is = LUI;
  } else if (opcode == OP_SYSTEM) {
    decode_i_format();

    if (funct3 == F3_ECALL)
      is = ECALL;
  }

  if (is == 0) {
    if (run)
      throw_exception(EXCEPTION_UNKNOWNINSTRUCTION, 0);
    else {
      //report the error on the console
      output_fd = 1;

      printf2("%s: unknown instruction with %x opcode detected\n", selfie_name, (char*) opcode);

      exit(EXITCODE_UNKNOWNINSTRUCTION);
    }
  }
}

void execute() {
  if (debug) {
    if (record)
      execute_record();
    else if (symbolic)
      execute_symbolically();
    else
      execute_debug();

    return;
  }

  // assert: 1 <= is <= number of RISC-U instructions
  if (is == ADDI)
    do_addi();
  else if (is == LD)
    do_ld();
  else if (is == SD)
    do_sd();
  else if (is == ADD)
    do_add();
  else if (is == SUB)
    do_sub();
  else if (is == MUL)
    do_mul();
  else if (is == DIVU)
    do_divu();
  else if (is == REMU)
    do_remu();
  else if (is == SLTU)
    do_sltu();
  else if (is == BEQ)
    do_beq();
  else if (is == JAL)
    do_jal();
  else if (is == JALR)
    do_jalr();
  else if (is == LUI)
    do_lui();
  else if (is == ECALL)
    do_ecall();
}

void execute_record() {
  // assert: 1 <= is <= number of RISC-U instructions
  if (is == ADDI) {
    record_lui_addi_add_sub_mul_sltu_jal_jalr();
    do_addi();
  } else if (is == LD) {
    record_ld();
    do_ld();
  } else if (is == SD) {
    record_sd();
    do_sd();
  } else if (is == ADD) {
    record_lui_addi_add_sub_mul_sltu_jal_jalr();
    do_add();
  } else if (is == SUB) {
    record_lui_addi_add_sub_mul_sltu_jal_jalr();
    do_sub();
  } else if (is == MUL) {
    record_lui_addi_add_sub_mul_sltu_jal_jalr();
    do_mul();
  } else if (is == DIVU) {
    record_divu_remu();
    do_divu();
  } else if (is == REMU) {
    record_divu_remu();
    do_remu();
  } else if (is == SLTU) {
    record_lui_addi_add_sub_mul_sltu_jal_jalr();
    do_sltu();
  } else if (is == BEQ) {
    record_beq();
    do_beq();
  } else if (is == JAL) {
    record_lui_addi_add_sub_mul_sltu_jal_jalr();
    do_jal();
  } else if (is == JALR) {
    record_lui_addi_add_sub_mul_sltu_jal_jalr();
    do_jalr();
  } else if (is == LUI) {
    record_lui_addi_add_sub_mul_sltu_jal_jalr();
    do_lui();
  } else if (is == ECALL) {
    record_ecall();
    do_ecall();
  }
}

void execute_undo() {
  // assert: 1 <= is <= number of RISC-U instructions
  if (is == SD)
    undo_sd();
  else if (is == BEQ)
    // beq does not require any undo
    return;
  else if (is == ECALL)
    undo_ecall();
  else
    undo_lui_addi_add_sub_mul_divu_remu_sltu_ld_jal_jalr();
}

void execute_debug() {
  translate_to_assembler();

  // assert: 1 <= is <= number of RISC-U instructions
  if (is == ADDI){
    print_addi_before();
    do_addi();
    print_addi_add_sub_mul_divu_remu_sltu_after();
  } else if (is == LD) {
    print_ld_before();
    print_ld_after(do_ld());
  } else if (is == SD) {
    print_sd_before();
    print_sd_after(do_sd());
  } else if (is == ADD) {
    print_add_sub_mul_divu_remu_sltu_before();
    do_add();
    print_addi_add_sub_mul_divu_remu_sltu_after();
  } else if (is == SUB) {
    print_add_sub_mul_divu_remu_sltu_before();
    do_sub();
    print_addi_add_sub_mul_divu_remu_sltu_after();
  } else if (is == MUL) {
    print_add_sub_mul_divu_remu_sltu_before();
    do_mul();
    print_addi_add_sub_mul_divu_remu_sltu_after();
  } else if (is == DIVU) {
    print_add_sub_mul_divu_remu_sltu_before();
    do_divu();
    print_addi_add_sub_mul_divu_remu_sltu_after();
  } else if (is == REMU) {
    print_add_sub_mul_divu_remu_sltu_before();
    do_remu();
    print_addi_add_sub_mul_divu_remu_sltu_after();
  } else if (is == SLTU) {
    print_add_sub_mul_divu_remu_sltu_before();
    do_sltu();
    print_addi_add_sub_mul_divu_remu_sltu_after();
  } else if (is == BEQ) {
    print_beq_before();
    do_beq();
    print_beq_after();
  } else if (is == JAL) {
    print_jal_before();
    do_jal();
    print_jal_jalr_after();
  } else if (is == JALR) {
    print_jalr_before();
    do_jalr();
    print_jal_jalr_after();
  } else if (is == LUI) {
    print_lui_before();
    do_lui();
    print_lui_after();
  } else if (is == ECALL) {
    do_ecall();

    return;
  }

  println();
}

void execute_symbolically() {
  uint64_t prologue_start;
  uint64_t corresponding_merge_location;
  uint64_t pc_before_jal;
  uint64_t jal_rd;

  // assert: 1 <= is <= number of RISC-U instructions
  if (is == ADDI) {
    constrain_addi();
    do_addi();
  } else if (is == LD)
    constrain_ld();
  else if (is == SD)
    constrain_sd();
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
    pc_before_jal = pc;
    jal_rd = rd;

    do_jal();
    // note: this is a dependency on the selfie compiler
    // the selfie compiler uses jal with the RA register to call a procedure
    if (jal_rd == REG_RA)
      // if we are already in a recursion, we do not add a new merge location since we only merge when the
      // recursion is finished (i.e. the program has reached a program location which is not part of any recursion)
      if (get_in_recursion(current_context) == 0) {
        corresponding_merge_location = pc_before_jal + INSTRUCTIONSIZE;
        prologue_start = pc;
        add_prologue_start_and_corresponding_merge_location(prologue_start, corresponding_merge_location, current_context);
      }

  } else if (is == JALR) {
    constrain_jalr();
    do_jalr();
  } else if (is == LUI) {
    constrain_lui();
    do_lui();
  } else if (is == ECALL)
    do_ecall();
}

void interrupt() {
  if (timer != TIMEROFF) {
    timer = timer - 1;

    if (symbolic)
      set_execution_depth(current_context, get_execution_depth(current_context) + 1);

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

  if (symbolic) {
    if (get_in_recursion(current_context) == 0)
      if (get_prologues(current_context) != (uint64_t*) 0)
        if (pc == *(get_prologues(current_context) + 2))
          // pop prologue off the stack if we have finished the procedure
          set_prologues(current_context, (uint64_t*) *(get_prologues(current_context) + 0));

    if (current_mergeable_context != (uint64_t*) 0)
      // if both contexts are at the same program location, they can be merged
      if (pc == get_pc(current_mergeable_context))
        merge(current_context, current_mergeable_context, pc);

    // check if the current context has reached a merge location
    if (pc == get_merge_location(current_context))
      if (get_exception(current_context) == EXCEPTION_NOEXCEPTION)
        // only throw exception if no other is pending
        // TODO: handle multiple pending exceptions
        throw_exception(EXCEPTION_MERGE, 0);
  }
}

void run_until_exception() {
  trap = 0;

  while (trap == 0) {
    fetch();
    decode();
    execute();

    interrupt();
  }

  trap = 0;
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

    printf3(",%d(%.2d%%)@%x", (char*) c, (char*) fixed_point_percentage(fixed_point_ratio(total, c, 4), 4), (char*) a);
    print_code_line_number_for_instruction(a, 0);

    return c;
  } else {
    print(",0(0.00%)");

    return 0;
  }
}

void print_per_instruction_profile(char* message, uint64_t total, uint64_t* counters) {
  printf3("%s%s%d", selfie_name, message, (char*) total);
  print_per_instruction_counter(total, counters, print_per_instruction_counter(total, counters, print_per_instruction_counter(total, counters, UINT64_MAX)));
  println();
}

void print_profile() {
  printf4("%s: summary: %d executed instructions and %.2dMB(%.2d%%) mapped memory\n", selfie_name,
    (char*) get_total_number_of_instructions(),
    (char*) fixed_point_ratio(pused(), MEGABYTE, 2),
    (char*) fixed_point_percentage(fixed_point_ratio(page_frame_memory, pused(), 4), 4));

  if (get_total_number_of_instructions() > 0) {
    print_instruction_counters();

    if (code_line_number != (uint64_t*) 0)
      printf1("%s: profile: total,max(ratio%%)@addr(line#),2max,3max\n", selfie_name);
    else
      printf1("%s: profile: total,max(ratio%%)@addr,2max,3max\n", selfie_name);

    print_per_instruction_profile(": calls:   ", calls, calls_per_procedure);
    print_per_instruction_profile(": loops:   ", iterations, iterations_per_loop);
    print_per_instruction_profile(": loads:   ", ic_ld, loads_per_instruction);
    print_per_instruction_profile(": stores:  ", ic_sd, stores_per_instruction);
  }
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- CONTEXTS ---------------------------
// -----------------------------------------------------------------

uint64_t* new_context() {
  uint64_t* context;

  if (free_contexts == (uint64_t*) 0)
    if (symbolic)
      context = allocate_symbolic_context();
    else
      context = allocate_context();
  else {
    context = free_contexts;

    free_contexts = get_next_context(free_contexts);
  }

  set_next_context(context, used_contexts);
  set_prev_context(context, (uint64_t*) 0);

  if (used_contexts != (uint64_t*) 0)
    set_prev_context(used_contexts, context);

  used_contexts = context;

  return context;
}

void init_context(uint64_t* context, uint64_t* parent, uint64_t* vctxt) {
  set_pc(context, 0);

  // allocate zeroed memory for general purpose registers
  // TODO: reuse memory
  set_regs(context, zalloc(NUMBEROFREGISTERS * REGISTERSIZE));

  // allocate zeroed memory for page table
  // TODO: save and reuse memory for page table
  set_pt(context, zalloc(VIRTUALMEMORYSIZE / PAGESIZE * REGISTERSIZE));

  // determine range of recently mapped pages
  set_lowest_lo_page(context, 0);
  set_highest_lo_page(context, get_lowest_lo_page(context));
  set_lowest_hi_page(context, get_page_of_virtual_address(VIRTUALMEMORYSIZE - REGISTERSIZE));
  set_highest_hi_page(context, get_lowest_hi_page(context));

  set_exception(context, EXCEPTION_NOEXCEPTION);
  set_faulting_page(context, 0);

  set_exit_code(context, EXITCODE_NOERROR);

  set_parent(context, parent);
  set_virtual_context(context, vctxt);

  set_name(context, 0);

  if (symbolic) {
    set_execution_depth(context, 0);
    set_path_condition(context, "true");
    set_symbolic_memory(context, (uint64_t*) 0);
    set_symbolic_regs(context, zalloc(NUMBEROFREGISTERS * REGISTERSIZE));
    set_beq_counter(context, 0);
    set_merge_location(context, -1);
    set_prologues(context, (uint64_t*) 0);
    set_in_recursion(context, 0);
    set_outside_rec_loc(context, 0);
    set_merge_partner(context, (uint64_t*) 0);
  }
}

uint64_t* copy_context(uint64_t* original, uint64_t location, char* condition) {
  uint64_t* context;
  uint64_t* begin_of_shared_symbolic_memory;
  uint64_t r;

  context = new_context();

  set_pc(context, location);

  set_regs(context, smalloc(NUMBEROFREGISTERS * REGISTERSIZE));

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
  set_exception(context, get_exception(original));
  set_faulting_page(context, get_faulting_page(original));
  set_exit_code(context, get_exit_code(original));
  set_parent(context, get_parent(original));
  set_virtual_context(context, get_virtual_context(original));
  set_name(context, get_name(original));

  set_execution_depth(context, get_execution_depth(original));
  set_path_condition(context, condition);
  set_beq_counter(context, get_beq_counter(original));
  set_merge_location(context, get_merge_location(original));

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

  set_prologues(context, get_prologues(original));
  set_in_recursion(context, get_in_recursion(original));
  set_outside_rec_loc(context, get_outside_rec_loc(original));

  set_symbolic_regs(context, smalloc(NUMBEROFREGISTERS * REGISTERSIZE));

  set_merge_partner(context, original);

  r = 0;

  while (r < NUMBEROFREGISTERS) {
    *(get_symbolic_regs(context) + r) = *(get_symbolic_regs(original) + r);

    r = r + 1;
  }

  symbolic_contexts = context;

  return context;
}

uint64_t* find_context(uint64_t* parent, uint64_t* vctxt) {
  uint64_t* context;

  context = used_contexts;

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
  uint64_t* context;

  context = new_context();

  init_context(context, parent, vctxt);

  if (debug_create)
    printf3("%s: parent context %p created child context %p\n", selfie_name,
      (char*) parent,
      (char*) used_contexts);

  return context;
}

uint64_t* cache_context(uint64_t* vctxt) {
  uint64_t* context;

  // find cached context on my boot level
  context = find_context(current_context, vctxt);

  if (context == (uint64_t*) 0)
    // create cached context on my boot level
    context = create_context(current_context, vctxt);

  return context;
}

void save_context(uint64_t* context) {
  uint64_t* parent_table;
  uint64_t* vctxt;
  uint64_t r;
  uint64_t* pregs;
  uint64_t* vregs;

  // save machine state
  set_pc(context, pc);

  if (symbolic) {
    set_path_condition(context, path_condition);
    set_symbolic_memory(context, symbolic_memory);
  }

  if (get_parent(context) != MY_CONTEXT) {
    parent_table = get_pt(get_parent(context));

    vctxt = get_virtual_context(context);

    store_virtual_memory(parent_table, program_counter(vctxt), get_pc(context));

    r = 0;

    pregs = get_regs(context);
    vregs = (uint64_t*) load_virtual_memory(parent_table, regs(vctxt));

    while (r < NUMBEROFREGISTERS) {
      store_virtual_memory(parent_table, (uint64_t) (vregs + r), *(pregs + r));

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

  // exploit spatial locality in page table caching
  if (page <= get_page_of_virtual_address(get_program_break(context) - REGISTERSIZE)) {
    if (page < get_lowest_lo_page(context))
      set_lowest_lo_page(context, page);
    else if (page > get_highest_lo_page(context))
      set_highest_lo_page(context, page);
  } else {
    if (page < get_lowest_hi_page(context))
      set_lowest_hi_page(context, page);
    else if (page > get_highest_hi_page(context))
      set_highest_hi_page(context, page);
  }

  if (debug_map) {
    printf1("%s: page ", selfie_name);
    print_hexadecimal(page, 4);
    printf2(" mapped to frame %p in context %p\n", (char*) frame, (char*) context);
  }
}

void restore_region(uint64_t* context, uint64_t* table, uint64_t* parent_table, uint64_t lo, uint64_t hi) {
  uint64_t frame;

  while (lo <= hi) {
    if (is_virtual_address_mapped(parent_table, frame_for_page(table, lo))) {
      frame = load_virtual_memory(parent_table, frame_for_page(table, lo));

      map_page(context, lo, get_frame_for_page(parent_table, get_page_of_virtual_address(frame)));
    }

    lo = lo + 1;
  }
}

void restore_context(uint64_t* context) {
  uint64_t* parent_table;
  uint64_t* vctxt;
  uint64_t r;
  uint64_t* pregs;
  uint64_t* vregs;
  uint64_t* table;
  uint64_t lo;
  uint64_t hi;

  if (get_parent(context) != MY_CONTEXT) {
    parent_table = get_pt(get_parent(context));

    vctxt = get_virtual_context(context);

    set_pc(context, load_virtual_memory(parent_table, program_counter(vctxt)));

    r = 0;

    pregs = get_regs(context);
    vregs = (uint64_t*) load_virtual_memory(parent_table, regs(vctxt));

    while (r < NUMBEROFREGISTERS) {
      *(pregs + r) = load_virtual_memory(parent_table, (uint64_t) (vregs + r));

      r = r + 1;
    }

    set_program_break(context, load_virtual_memory(parent_table, program_break(vctxt)));

    set_exception(context, load_virtual_memory(parent_table, exception(vctxt)));
    set_faulting_page(context, load_virtual_memory(parent_table, faulting_page(vctxt)));
    set_exit_code(context, load_virtual_memory(parent_table, exit_code(vctxt)));

    table = (uint64_t*) load_virtual_memory(parent_table, page_table(vctxt));

    // assert: context page table is only mapped from beginning up and end down

    lo = load_virtual_memory(parent_table, lowest_lo_page(vctxt));
    hi = load_virtual_memory(parent_table, highest_lo_page(vctxt));

    restore_region(context, table, parent_table, lo, hi);

    store_virtual_memory(parent_table, lowest_lo_page(vctxt), hi);

    lo = load_virtual_memory(parent_table, lowest_hi_page(vctxt));
    hi = load_virtual_memory(parent_table, highest_hi_page(vctxt));

    restore_region(context, table, parent_table, lo, hi);

    store_virtual_memory(parent_table, highest_hi_page(vctxt), lo);
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
      print(": palloc out of physical memory\n");

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

  store_virtual_memory(get_pt(context), vaddr, data);
}

void up_load_binary(uint64_t* context) {
  uint64_t baddr;

  // assert: entry_point is multiple of PAGESIZE and REGISTERSIZE

  set_pc(context, entry_point);
  set_lowest_lo_page(context, get_page_of_virtual_address(entry_point));
  set_highest_lo_page(context, get_lowest_lo_page(context));
  set_original_break(context, entry_point + binary_length);
  set_program_break(context, get_original_break(context));

  baddr = 0;

  while (baddr < binary_length) {
    map_and_store(context, entry_point + baddr, load_data(baddr));

    baddr = baddr + REGISTERSIZE;
  }

  set_name(context, binary_name);
}

uint64_t up_load_string(uint64_t* context, char* s, uint64_t SP) {
  uint64_t bytes;
  uint64_t i;

  bytes = round_up(string_length(s) + 1, REGISTERSIZE);

  // allocate memory for storing string
  SP = SP - bytes;

  i = 0;

  while (i < bytes) {
    // CAUTION: at boot levels higher than zero, s is only accessible
    // in C* at machine word granularity, not individual characters
    map_and_store(context, SP + i, *((uint64_t*) s));

    s = (char*) ((uint64_t*) s + 1);

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
    SP = up_load_string(context, (char*) *(argv + i), SP);

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
  else if (a7 == SYSCALL_OPENAT)
    implement_openat(context);
  else if (a7 == SYSCALL_EXIT) {
    implement_exit(context);

    // TODO: exit only if all contexts have exited
    return EXIT;
  } else {
    printf2("%s: unknown system call %d\n", selfie_name, (char*) a7);

    set_exit_code(context, EXITCODE_UNKNOWNSYSCALL);

    return EXIT;
  }

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

  if (record) {
    printf1("%s: division by zero, replaying...\n", selfie_name);

    replay_trace();

    set_exit_code(context, EXITCODE_NOERROR);
  } else if (symbolic) {
    // check if this division by zero is reachable
    print("(push 1)\n");
    printf1("(assert %s); division by zero detected; check if this division by zero is reachable", path_condition);
    print("\n(check-sat)\n(get-model)\n(pop 1)\n");

    // we terminate the execution of the context, because if the location is not reachable,
    // the rest of the path is not reachable either, and otherwise
    // the execution would be terminated by this error anyway
    set_exit_code(context, EXITCODE_DIVISIONBYZERO);
  } else {
    printf1("%s: division by zero\n", selfie_name);

    set_exit_code(context, EXITCODE_DIVISIONBYZERO);
  }

  return EXIT;
}

uint64_t handle_timer(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  if (symbolic) {
    printf1("; timeout in ", path_condition);
    print_code_context_for_instruction(pc);
    println();

    return EXIT;
  } else
    return DONOTEXIT;
}

uint64_t handle_merge(uint64_t* context) {
  add_mergeable_context(current_context);

  set_exception(context, EXCEPTION_NOEXCEPTION);

  return MERGE;
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
  else if (exception == EXCEPTION_TIMER)
    return handle_timer(context);
  else if (exception == EXCEPTION_MERGE)
    return handle_merge(context);
  else {
    if (symbolic)
      if (exception == EXCEPTION_INVALIDADDRESS) {
        // check if this invalid memory access is reachable
        print("(push 1)\n");
        printf1("(assert %s); invalid memory access detected; check if this invalid memory access is reachable", path_condition);
        print("\n(check-sat)\n(get-model)\n(pop 1)\n");

        set_exit_code(context, EXITCODE_SYMBOLICEXECUTIONERROR);

        // we terminate the execution of the context, because if the location is not reachable,
        // the rest of the path is not reachable either, and otherwise
        // the execution would be terminated by this error anyway
        return EXIT;
      }

    printf2("%s: context %s throws uncaught ", selfie_name, get_name(context));
    print_exception(exception, get_faulting_page(context));
    println();

    set_exit_code(context, EXITCODE_UNCAUGHTEXCEPTION);

    return EXIT;
  }
}

uint64_t mipster(uint64_t* to_context) {
  uint64_t timeout;
  uint64_t* from_context;

  print("mipster\n");

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

  print("hypster\n");

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

  printf2("mixter (%d%% mipster/%d%% hypster)\n", (char*) mix, (char*) (100 - mix));

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
        printf2("%s: context %s throws uncaught ", selfie_name, get_name(from_context));
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

  page = get_lowest_lo_page(context);

  while (is_page_mapped(get_pt(context), page))
    page = page + 1;

  while (pavailable()) {
    map_page(context, page, (uint64_t) palloc());

    page = page + 1;
  }
}

uint64_t minster(uint64_t* to_context) {
  print("minster\n");

  // virtual is like physical memory in initial context up to memory size
  // by mapping unmapped pages (for the heap) to all available page frames
  // CAUTION: consumes memory even when not accessed
  map_unmapped_pages(to_context);

  // does not handle page faults, works only until running out of mapped pages
  return minmob(to_context);
}

uint64_t mobster(uint64_t* to_context) {
  print("mobster\n");

  // does not handle page faults, relies on fancy hypsters to do that
  return minmob(to_context);
}

char* replace_extension(char* filename, char* extension) {
  char* s;
  uint64_t i;
  uint64_t c;

  // assert: string_length(filename) + 1 + string_length(extension) < MAX_FILENAME_LENGTH

  s = string_alloc(string_length(filename) + 1 + string_length(extension));

  i = 0;

  c = load_character(filename, i);

  while (c != 0) {
    store_character(s, i, c);

    if (c == '.') {
      store_character(s, i, 0);

      c = 0;
    } else {
      i = i + 1;

      c = load_character(filename, i);
    }
  }

  // writing s plus extension into s
  sprintf2(s, "%s.%s", s, extension);

  return s;
}

uint64_t monster(uint64_t* to_context) {
  uint64_t  timeout;
  uint64_t* from_context;
  uint64_t  exception;

  print("monster\n");

  // use extension ".smt" in name of SMT-LIB file
  smt_name = replace_extension(binary_name, "smt");

  // assert: smt_name is mapped and not longer than MAX_FILENAME_LENGTH

  smt_fd = open_write_only(smt_name);

  if (signed_less_than(smt_fd, 0)) {
    printf2("%s: could not create SMT-LIB output file %s\n", selfie_name, smt_name);

    exit(EXITCODE_IOERROR);
  }

  output_name = smt_name;
  output_fd   = smt_fd;

  if (number_of_remaining_arguments() > 1)
    if (string_compare(peek_argument(1), "--merge-enabled")) {
      merge_enabled = 1;

      get_argument();
    }

  printf1("; %s\n\n", SELFIE_URL);

  printf1("; SMT-LIB formulae generated by %s for\n", selfie_name);
  printf1("; RISC-V code obtained from %s with ", binary_name);
  if (max_execution_depth)
    printf1("%d execution depth\n\n", (char*) max_execution_depth);
  else
    print("unbounded execution depth\n\n");

  print("(set-option :produce-models true)\n");
  print("(set-option :incremental true)\n");
  print("(set-logic QF_BV)\n\n");

  timeout = max_execution_depth - get_execution_depth(to_context);

  while (1) {
    from_context = mipster_switch(to_context, timeout);

    if (get_parent(from_context) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      to_context = get_parent(from_context);

      timeout = TIMEROFF;
    } else {
      exception = handle_exception(from_context);

      if (exception == EXIT) {
        // we need to update the end of the shared symbolic memory of the corresponding context
        update_begin_of_shared_symbolic_memory(get_merge_partner(from_context));

        // if a context is currently waiting to be merged, we need to switch to this one
        if (current_mergeable_context != (uint64_t*) 0) {
          // update the merge location, so the 'new' context can be merged later
          set_merge_location(current_mergeable_context, get_merge_location(current_context));

          to_context = current_mergeable_context;

        // if no context is currently waiting to be merged, we switch to the next waiting context
        } else
          to_context = get_waiting_context();

        // it may be possible that there are no waiting contexts, but mergeable contexts
        if (to_context == (uint64_t*) 0) {
          to_context = get_mergeable_context();

          if (to_context)
            // update the merge location, so the 'new' context can be merged later
            set_merge_location(to_context, get_merge_location(current_context));
        }

        to_context = merge_if_possible_and_get_next_context(to_context);

        if (to_context)
          timeout = max_execution_depth - get_execution_depth(to_context);
        else {
          print("\n(exit)");

          output_name = (char*) 0;
          output_fd   = 1;

          printf3("%s: %d characters of SMT-LIB formulae written into %s\n", selfie_name,
            (char*) number_of_written_characters,
            smt_name);

          return EXITCODE_NOERROR;
        }
      } else if (exception == MERGE) {
        to_context = merge_if_possible_and_get_next_context(get_waiting_context());

        timeout = max_execution_depth - get_execution_depth(to_context);
      } else {
        timeout = timer;

        to_context = from_context;
      }
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

void boot_loader() {
  current_context = create_context(MY_CONTEXT, 0);

  up_load_binary(current_context);

  // pass binary name as first argument by replacing current argument
  set_argument(binary_name);

  up_load_arguments(current_context, number_of_remaining_arguments(), remaining_arguments());
}

uint64_t selfie_run(uint64_t machine) {
  uint64_t exit_code;

  if (binary_length == 0) {
    printf1("%s: nothing to run, debug, or host\n", selfie_name);

    return EXITCODE_BADARGUMENTS;
  }

  reset_interpreter();
  reset_profiler();
  reset_microkernel();

  if (machine == DIPSTER) {
    debug          = 1;
    debug_syscalls = 1;
  } else if (machine == RIPSTER) {
    debug  = 1;
    record = 1;

    init_replay_engine();
  } else if (machine == MONSTER) {
    debug    = 1;
    symbolic = 1;
  }

  if (machine != MONSTER)
    init_memory(atoi(peek_argument(0)));
  else {
    init_memory(1);

    max_execution_depth = atoi(peek_argument(0));
  }

  boot_loader();

  printf3("%s: selfie executing %s with %dMB physical memory on ", selfie_name,
    binary_name,
    (char*) (page_frame_memory / MEGABYTE));

  run = 1;

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

  run = 0;

  printf3("%s: selfie terminating %s with exit code %d\n", selfie_name,
    get_name(current_context),
    (char*) sign_extend(exit_code, SYSCALL_BITWIDTH));

  print_profile();

  symbolic = 0;
  record   = 0;

  debug_syscalls = 0;
  debug          = 0;

  return exit_code;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------   C O R R E C T N E S S    ------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// -------------------------- DISASSEMBLER -------------------------
// -----------------------------------------------------------------

void translate_to_assembler() {
  // assert: 1 <= is <= number of RISC-U instructions
  if (is == ADDI)
    print_addi();
  else if (is == LD)
    print_ld();
  else if (is == SD)
    print_sd();
  else if (is == ADD)
    print_add_sub_mul_divu_remu_sltu("add");
  else if (is == SUB)
    print_add_sub_mul_divu_remu_sltu("sub");
  else if (is == MUL)
    print_add_sub_mul_divu_remu_sltu("mul");
  else if (is == DIVU)
    print_add_sub_mul_divu_remu_sltu("divu");
  else if (is == REMU)
    print_add_sub_mul_divu_remu_sltu("remu");
  else if (is == SLTU)
    print_add_sub_mul_divu_remu_sltu("sltu");
  else if (is == BEQ)
    print_beq();
  else if (is == JAL)
    print_jal();
  else if (is == JALR)
    print_jalr();
  else if (is == LUI)
    print_lui();
  else if (is == ECALL)
    print_ecall();
}

void selfie_disassemble(uint64_t verbose) {
  uint64_t data;

  assembly_name = get_argument();

  if (code_length == 0) {
    printf2("%s: nothing to disassemble to output file %s\n", selfie_name, assembly_name);

    return;
  }

  // assert: assembly_name is mapped and not longer than MAX_FILENAME_LENGTH

  assembly_fd = open_write_only(assembly_name);

  if (signed_less_than(assembly_fd, 0)) {
    printf2("%s: could not create assembly output file %s\n", selfie_name, assembly_name);

    exit(EXITCODE_IOERROR);
  }

  output_name = assembly_name;
  output_fd   = assembly_fd;

  reset_library();
  reset_interpreter();

  run = 0;

  disassemble_verbose = verbose;

  while (pc < code_length) {
    ir = load_instruction(pc);

    decode();
    translate_to_assembler();
    println();

    pc = pc + INSTRUCTIONSIZE;
  }

  while (pc < binary_length) {
    data = load_data(pc);

    print_data(data);
    println();

    pc = pc + REGISTERSIZE;
  }

  disassemble_verbose = 0;

  output_name = (char*) 0;
  output_fd   = 1;

  printf5("%s: %d characters of assembly with %d instructions and %d bytes of data written into %s\n", selfie_name,
    (char*) number_of_written_characters,
    (char*) (code_length / INSTRUCTIONSIZE),
    (char*) (binary_length - code_length),
    assembly_name);
}

// -----------------------------------------------------------------
// ------------------------ MODEL GENERATOR ------------------------
// -----------------------------------------------------------------

uint64_t pc_nid(uint64_t nid, uint64_t pc) {
  return nid + pc * 100;
}

uint64_t is_procedure_call(uint64_t instruction, uint64_t link) {
  if (instruction == JAL)
    if (link != REG_ZR)
      return 1;

  return 0;
}

uint64_t validate_procedure_body(uint64_t from_instruction, uint64_t from_link, uint64_t to_address) {
  if (is_procedure_call(from_instruction, from_link) == 0) {
    // no forward branches and jumps that are not "procedure calls" outside of "procedure body"
    if (to_address > estimated_return)
      // estimating address of jalr at the end of "procedure body"
      estimated_return = to_address;

    if (to_address < current_callee)
      // no backward branches and jumps that are not "procedure calls" outside of "procedure body"
      return 0;
  }

  return 1;
}

void go_to_instruction(uint64_t from_instruction, uint64_t from_link, uint64_t from_address, uint64_t to_address, uint64_t condition_nid) {
  uint64_t* in_edge;

  if (to_address < entry_point + code_length) {
    if (validate_procedure_body(from_instruction, from_link, to_address)) {
      in_edge = smalloc(SIZEOFUINT64STAR + 3 * SIZEOFUINT64);

      *in_edge       = *(control_in + (to_address - entry_point) / INSTRUCTIONSIZE);
      *(in_edge + 1) = from_instruction; // from which instruction
      *(in_edge + 2) = from_address;     // at which address
      *(in_edge + 3) = condition_nid;    // under which condition are we coming

      *(control_in + (to_address - entry_point) / INSTRUCTIONSIZE) = (uint64_t) in_edge;

      return;
    }
  } else if (from_address == entry_point + code_length - INSTRUCTIONSIZE)
    // from_instruction is last instruction in binary
    if (*(control_in + (from_address - entry_point) / INSTRUCTIONSIZE) == 0)
      // and unreachable
      return;

  // the instruction at from_address proceeds to an instruction at an invalid to_address

  //report the error on the console
  output_fd = 1;

  printf2("%s: invalid instruction address %x detected\n", selfie_name, (char*) to_address);

  exit(EXITCODE_MODELCHECKINGERROR);
}

void reset_bounds() {
  if (check_block_access) {
    // if this instruction is active reset lower bound on $rd register to end of code segment
    printf3("%d ite 2 %d 30 %d\n",
      (char*) current_nid,                      // nid of this line
      (char*) pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
      (char*) *(reg_flow_nids + LO_FLOW + rd)); // nid of most recent update of lower bound on $rd register

    *(reg_flow_nids + LO_FLOW + rd) = current_nid;

    current_nid = current_nid + 1;

    // if this instruction is active reset upper bound on $rd register to 4GB of memory addresses
    printf3("%d ite 2 %d 50 %d\n",
      (char*) current_nid,                      // nid of this line
      (char*) pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
      (char*) *(reg_flow_nids + UP_FLOW + rd)); // nid of most recent update of upper bound on $rd register

    *(reg_flow_nids + UP_FLOW + rd) = current_nid;

    current_nid = current_nid + 1;
  }
}

void model_lui() {
  if (rd != REG_ZR) {
    reset_bounds();

    printf3("%d constd 2 %d ; %x << 12\n", (char*) current_nid, (char*) left_shift(imm, 12), (char*) imm);

    // if this instruction is active set $rd = imm << 12
    printf4("%d ite 2 %d %d %d ; ",
      (char*) (current_nid + 1),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) current_nid,            // nid of immediate argument left-shifted by 12 bits
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_lui();println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void transfer_bounds() {
  if (check_block_access) {
    // if this instruction is active set lower bound on $rd = lower bound on $rs1 register
    printf4("%d ite 2 %d %d %d\n",
      (char*) current_nid,                      // nid of this line
      (char*) pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
      (char*) (reg_nids + LO_FLOW + rs1),       // nid of lower bound on $rs1 register
      (char*) *(reg_flow_nids + LO_FLOW + rd)); // nid of most recent update of lower bound on $rd register

    *(reg_flow_nids + LO_FLOW + rd) = current_nid;

    current_nid = current_nid + 1;

    // if this instruction is active set upper bound on $rd = upper bound on $rs1 register
    printf4("%d ite 2 %d %d %d\n",
      (char*) current_nid,                      // nid of this line
      (char*) pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
      (char*) (reg_nids + UP_FLOW + rs1),       // nid of upper bound on $rs1 register
      (char*) *(reg_flow_nids + UP_FLOW + rd)); // nid of most recent update of upper bound on $rd register

    *(reg_flow_nids + UP_FLOW + rd) = current_nid;

    current_nid = current_nid + 1;
  }
}

void model_addi() {
  uint64_t result_nid;

  if (rd != REG_ZR) {
    transfer_bounds();

    if (imm == 0)
      result_nid = reg_nids + rs1;
    else {
      printf3("%d constd 2 %d ; %x\n", (char*) current_nid, (char*) imm, (char*) imm);

      if (rs1 == REG_ZR) {
        result_nid = current_nid;

        current_nid = current_nid + 1;

        if (rd == REG_A7)
          // assert: next instruction is ecall
          reg_a7 = imm;
      } else {
        // compute $rs1 + imm
        printf3("%d add 2 %d %d\n",
          (char*) (current_nid + 1), // nid of this line
          (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
          (char*) current_nid);      // nid of immediate value

        result_nid = current_nid + 1;

        current_nid = current_nid + 2;
      }
    }

    // if this instruction is active set $rd = $rs1 + imm
    printf4("%d ite 2 %d %d %d ; ",
      (char*) current_nid,            // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) result_nid,             // nid of $rs1 + ismm
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid;

    print_addi();println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_add() {
  if (rd != REG_ZR) {
    if (check_block_access) {
      // lower bound on $rs1 register > lower bound on $rs2 register
      printf3("%d ugt 1 %d %d\n",
        (char*) current_nid,                 // nid of this line
        (char*) (reg_nids + LO_FLOW + rs1),  // nid of lower bound on $rs1 register
        (char*) (reg_nids + LO_FLOW + rs2)); // nid of lower bound on $rs2 register

      // greater lower bound of $rs1 and $rs2 registers
      printf4("%d ite 2 %d %d %d\n",
        (char*) (current_nid + 1),           // nid of this line
        (char*) current_nid,                 // nid of lower bound on $rs1 > lower bound on $rs2
        (char*) (reg_nids + LO_FLOW + rs1),  // nid of lower bound on $rs1 register
        (char*) (reg_nids + LO_FLOW + rs2)); // nid of lower bound on $rs2 register

      // if this instruction is active set lower bound on $rd = greater lower bound of $rs1 and $rs2 registers
      printf4("%d ite 2 %d %d %d\n",
        (char*) (current_nid + 2),                // nid of this line
        (char*) pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
        (char*) (current_nid + 1),                // nid of greater lower bound of $rs1 and $rs2 registers
        (char*) *(reg_flow_nids + LO_FLOW + rd)); // nid of most recent update of lower bound on $rd register

      *(reg_flow_nids + LO_FLOW + rd) = current_nid + 2;

      current_nid = current_nid + 3;

      // upper bound on $rs1 register < upper bound on $rs2 register
      printf3("%d ult 1 %d %d\n",
        (char*) current_nid,                 // nid of this line
        (char*) (reg_nids + UP_FLOW + rs1),  // nid of upper bound on $rs1 register
        (char*) (reg_nids + UP_FLOW + rs2)); // nid of upper bound on $rs2 register

      // lesser upper bound of $rs1 and $rs2 registers
      printf4("%d ite 2 %d %d %d\n",
        (char*) (current_nid + 1),           // nid of this line
        (char*) current_nid,                 // nid of upper bound on $rs1 < upper bound on $rs2
        (char*) (reg_nids + UP_FLOW + rs1),  // nid of upper bound on $rs1 register
        (char*) (reg_nids + UP_FLOW + rs2)); // nid of upper bound on $rs2 register

      // if this instruction is active set upper bound on $rd = lesser upper bound of $rs1 and $rs2 registers
      printf4("%d ite 2 %d %d %d\n",
        (char*) (current_nid + 2),                // nid of this line
        (char*) pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
        (char*) (current_nid + 1),                // nid of lesser upper bound of $rs1 and $rs2 registers
        (char*) *(reg_flow_nids + UP_FLOW + rd)); // nid of most recent update of upper bound on $rd register

      *(reg_flow_nids + UP_FLOW + rd) = current_nid + 2;

      current_nid = current_nid + 3;
    }

    // compute $rs1 + $rs2
    printf3("%d add 2 %d %d\n",
      (char*) current_nid,       // nid of this line
      (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
      (char*) (reg_nids + rs2)); // nid of current value of $rs2 register

    // if this instruction is active set $rd = $rs1 + $rs2
    printf4("%d ite 2 %d %d %d ; ",
      (char*) (current_nid + 1),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) current_nid,            // nid of $rs1 + $rs2
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_add_sub_mul_divu_remu_sltu("add");println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_sub() {
  if (rd != REG_ZR) {
    // TODO: check if bounds on $rs2 are really initial bounds
    transfer_bounds();

    // compute $rs1 - $rs2
    printf3("%d sub 2 %d %d\n",
      (char*) current_nid,       // nid of this line
      (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
      (char*) (reg_nids + rs2)); // nid of current value of $rs2 register

    // if this instruction is active set $rd = $rs1 - $rs2
    printf4("%d ite 2 %d %d %d ; ",
      (char*) (current_nid + 1),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) current_nid,            // nid of $rs1 - $rs2
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_add_sub_mul_divu_remu_sltu("sub");println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_mul() {
  if (rd != REG_ZR) {
    // TODO: check if bounds on $rs1 and $rs2 are really initial bounds
    reset_bounds();

    // compute $rs1 * $rs2
    printf3("%d mul 2 %d %d\n",
      (char*) current_nid,       // nid of this line
      (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
      (char*) (reg_nids + rs2)); // nid of current value of $rs2 register

    // if this instruction is active set $rd = $rs1 * $rs2
    printf4("%d ite 2 %d %d %d ; ",
      (char*) (current_nid + 1),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) current_nid,            // nid of $rs1 * $rs2
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_add_sub_mul_divu_remu_sltu("mul");println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_divu() {
  if (rd != REG_ZR) {
    // TODO: check if bounds on $rs1 and $rs2 are really initial bounds
    reset_bounds();

    // if this instruction is active record $rs2 for checking if $rs2 == 0
    printf5("%d ite 2 %d %d %d ; record %s for checking division by zero\n",
      (char*) current_nid,         // nid of this line
      (char*) pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
      (char*) (reg_nids + rs2),    // nid of current value of $rs2 register
      (char*) division_flow_nid,   // nid of divisor of most recent division
      get_register_name(rs2));     // register name

    division_flow_nid = current_nid;

    current_nid = current_nid + 1;

    // compute $rs1 / $rs2
    printf3("%d udiv 2 %d %d\n",
      (char*) current_nid,       // nid of this line
      (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
      (char*) (reg_nids + rs2)); // nid of current value of $rs2 register

    // if this instruction is active set $rd = $rs1 / $rs2
    printf4("%d ite 2 %d %d %d ; ",
      (char*) (current_nid + 1),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) current_nid,            // nid of $rs1 / $rs2
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_add_sub_mul_divu_remu_sltu("divu");println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_remu() {
  if (rd != REG_ZR) {
    // TODO: check if bounds on $rs1 and $rs2 are really initial bounds
    reset_bounds();

    // if this instruction is active record $rs2 for checking if $rs2 == 0
    printf5("%d ite 2 %d %d %d ; record %s for checking remainder by zero\n",
      (char*) current_nid,         // nid of this line
      (char*) pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
      (char*) (reg_nids + rs2),    // nid of current value of $rs2 register
      (char*) remainder_flow_nid,  // nid of divisor of most recent remainder
      get_register_name(rs2));     // register name

    remainder_flow_nid = current_nid;

    current_nid = current_nid + 1;

    // compute $rs1 % $rs2
    printf3("%d urem 2 %d %d\n",
      (char*) current_nid,       // nid of this line
      (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
      (char*) (reg_nids + rs2)); // nid of current value of $rs2 register

    // if this instruction is active set $rd = $rs1 % $rs2
    printf4("%d ite 2 %d %d %d ; ",
      (char*) (current_nid + 1),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) current_nid,            // nid of $rs1 % $rs2
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_add_sub_mul_divu_remu_sltu("remu");println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_sltu() {
  if (rd != REG_ZR) {
    reset_bounds();

    // compute $rs1 < $rs2
    printf3("%d ult 1 %d %d\n",
      (char*) current_nid,       // nid of this line
      (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
      (char*) (reg_nids + rs2)); // nid of current value of $rs2 register

    // unsigned-extend $rs1 < $rs2 by 63 bits to 64 bits
    printf2("%d uext 2 %d 63\n",
      (char*) (current_nid + 1), // nid of this line
      (char*) current_nid);      // nid of $rs1 < $rs2

    // if this instruction is active set $rd = $rs1 < $rs2
    printf4("%d ite 2 %d %d %d ; ",
      (char*) (current_nid + 2),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) (current_nid + 1),      // nid of unsigned-64-bit-extended $rs1 < $rs2
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 2;

    print_add_sub_mul_divu_remu_sltu("sltu");println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

uint64_t record_start_bounds(uint64_t offset, uint64_t activation_nid, uint64_t reg) {
  if (check_block_access) {
    // if current instruction is active record lower bound on $reg register for checking address validity
    printf4("%d ite 2 %d %d %d\n",
      (char*) (current_nid + offset),     // nid of this line
      (char*) activation_nid,             // nid of activation condition of current instruction
      (char*) (reg_nids + LO_FLOW + reg), // nid of current lower bound on $reg register
      (char*) lo_flow_start_nid);         // nid of most recent update of lower bound on memory access

    lo_flow_start_nid = current_nid + offset;

    offset = offset + 1;

    // if current instruction is active record upper bound on $reg register for checking address validity
    printf4("%d ite 2 %d %d %d\n",
      (char*) (current_nid + offset),     // nid of this line
      (char*) activation_nid,             // nid of activation condition of current instruction
      (char*) (reg_nids + UP_FLOW + reg), // nid of current upper bound on $reg register
      (char*) up_flow_start_nid);         // nid of most recent update of upper bound on memory access

    up_flow_start_nid = current_nid + offset;

    return offset + 1;
  } else
    return offset;
}

uint64_t record_end_bounds(uint64_t offset, uint64_t activation_nid, uint64_t reg) {
  if (check_block_access) {
    // if current instruction is active record lower bound on $reg register for checking address validity
    printf4("%d ite 2 %d %d %d\n",
      (char*) (current_nid + offset),     // nid of this line
      (char*) activation_nid,             // nid of activation condition of current instruction
      (char*) (reg_nids + LO_FLOW + reg), // nid of current lower bound on $reg register
      (char*) lo_flow_end_nid);           // nid of most recent update of lower bound on memory access

    lo_flow_end_nid = current_nid + offset;

    offset = offset + 1;

    // if current instruction is active record upper bound on $reg register for checking address validity
    printf4("%d ite 2 %d %d %d\n",
      (char*) (current_nid + offset),     // nid of this line
      (char*) activation_nid,             // nid of activation condition of current instruction
      (char*) (reg_nids + UP_FLOW + reg), // nid of current upper bound on $reg register
      (char*) up_flow_end_nid);           // nid of most recent update of upper bound on memory access

    up_flow_end_nid = current_nid + offset;

    return offset + 1;
  } else
    return offset;
}

uint64_t compute_address() {
  if (imm == 0)
    return reg_nids + rs1; // nid of current value of $rs1 register
  else {
    printf3("%d constd 2 %d ; %x\n", (char*) current_nid, (char*) imm, (char*) imm);

    // compute $rs1 + imm
    printf3("%d add 2 %d %d\n",
      (char*) (current_nid + 1), // nid of this line
      (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
      (char*) current_nid);      // nid of immediate value

    current_nid = current_nid + 2;

    return current_nid - 1; // nid of $rs1 + imm
  }
}

void model_ld() {
  uint64_t address_nid;

  if (rd != REG_ZR) {
    current_nid = current_nid + record_start_bounds(0, pc_nid(pcs_nid, pc), rs1);

    address_nid = compute_address();

    // if this instruction is active record $rs1 + imm for checking address validity
    printf4("%d ite 2 %d %d %d\n",
      (char*) current_nid,            // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) address_nid,            // nid of $rs1 + imm
      (char*) access_flow_start_nid); // nid of address of most recent memory access

    access_flow_start_nid = current_nid;

    current_nid = current_nid + 1;

    if (check_block_access) {
      // read from lower-bounds memory[$rs1 + imm] into lower bound on $rd register
      printf3("%d read 2 %d %d\n",
        (char*) current_nid,   // nid of this line
        (char*) lo_memory_nid, // nid of lower bounds on addresses in memory
        (char*) address_nid);  // nid of $rs1 + imm

      // if this instruction is active set lower bound on $rd = lower-bounds memory[$rs1 + imm]
      printf4("%d ite 2 %d %d %d\n",
        (char*) (current_nid + 1),                // nid of this line
        (char*) pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
        (char*) current_nid,                      // nid of lower-bounds memory[$rs1 + imm]
        (char*) *(reg_flow_nids + LO_FLOW + rd)); // nid of most recent update of lower bound on $rd register

      *(reg_flow_nids + LO_FLOW + rd) = current_nid + 1;

      current_nid = current_nid + 2;

      // read from upper-bounds memory[$rs1 + imm] into upper bound on $rd register
      printf3("%d read 2 %d %d\n",
        (char*) current_nid,   // nid of this line
        (char*) up_memory_nid, // nid of upper bounds on addresses in memory
        (char*) address_nid);  // nid of $rs1 + imm

      // if this instruction is active set upper bound on $rd = upper-bounds memory[$rs1 + imm]
      printf4("%d ite 2 %d %d %d\n",
        (char*) (current_nid + 1),                // nid of this line
        (char*) pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
        (char*) current_nid,                      // nid of upper-bounds memory[$rs1 + imm]
        (char*) *(reg_flow_nids + UP_FLOW + rd)); // nid of most recent update of upper bound on $rd register

      *(reg_flow_nids + UP_FLOW + rd) = current_nid + 1;

      current_nid = current_nid + 2;
    }

    // read from memory[$rs1 + imm] into $rd register
    printf3("%d read 2 %d %d\n",
      (char*) current_nid,  // nid of this line
      (char*) memory_nid,   // nid of memory
      (char*) address_nid); // nid of $rs1 + imm

    // if this instruction is active set $rd = memory[$rs1 + imm]
    printf4("%d ite 2 %d %d %d ; ",
      (char*) (current_nid + 1),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) current_nid,            // nid of memory[$rs1 + imm]
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_ld();println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_sd() {
  uint64_t address_nid;

  current_nid = current_nid + record_start_bounds(0, pc_nid(pcs_nid, pc), rs1);

  address_nid = compute_address();

  // if this instruction is active record $rs1 + imm for checking address validity
  printf4("%d ite 2 %d %d %d\n",
    (char*) current_nid,            // nid of this line
    (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
    (char*) address_nid,            // nid of $rs1 + imm
    (char*) access_flow_start_nid); // nid of address of most recent memory access

  access_flow_start_nid = current_nid;

  current_nid = current_nid + 1;

  if (check_block_access) {
    // write lower bound on $rs2 register to lower-bounds memory[$rs1 + imm]
    printf4("%d write 3 %d %d %d\n",
      (char*) current_nid,                 // nid of this line
      (char*) lo_memory_nid,               // nid of lower bounds on addresses in memory
      (char*) address_nid,                 // nid of $rs1 + imm
      (char*) (reg_nids + LO_FLOW + rs2)); // nid of lower bound on $rs2 register

    // if this instruction is active set lower-bounds memory[$rs1 + imm] = lower bound on $rs2
    printf4("%d ite 3 %d %d %d\n",
      (char*) (current_nid + 1),   // nid of this line
      (char*) pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
      (char*) current_nid,         // nid of lower-bounds memory[$rs1 + imm]
      (char*) lo_memory_flow_nid); // nid of most recent update of lower-bounds memory

    lo_memory_flow_nid = current_nid + 1;

    current_nid = current_nid + 2;

    // write upper bound on $rs2 register to upper-bounds memory[$rs1 + imm]
    printf4("%d write 3 %d %d %d\n",
      (char*) current_nid,                 // nid of this line
      (char*) up_memory_nid,               // nid of upper bounds on addresses in memory
      (char*) address_nid,                 // nid of $rs1 + imm
      (char*) (reg_nids + UP_FLOW + rs2)); // nid of upper bound on $rs2 register

    // if this instruction is active set upper-bounds memory[$rs1 + imm] = upper bound on $rs2
    printf4("%d ite 3 %d %d %d\n",
      (char*) (current_nid + 1),   // nid of this line
      (char*) pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
      (char*) current_nid,         // nid of upper-bounds memory[$rs1 + imm]
      (char*) up_memory_flow_nid); // nid of most recent update of upper-bounds memory

    up_memory_flow_nid = current_nid + 1;

    current_nid = current_nid + 2;
  }

  // write $rs2 register to memory[$rs1 + imm]
  printf4("%d write 3 %d %d %d\n",
    (char*) current_nid,       // nid of this line
    (char*) memory_nid,        // nid of memory
    (char*) address_nid,       // nid of $rs1 + imm
    (char*) (reg_nids + rs2)); // nid of current value of $rs2 register

  // if this instruction is active set memory[$rs1 + imm] = $rs2
  printf4("%d ite 3 %d %d %d ; ",
    (char*) (current_nid + 1),   // nid of this line
    (char*) pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
    (char*) current_nid,         // nid of memory[$rs1 + imm] = $rs2
    (char*) memory_flow_nid);    // nid of most recent update of memory

  memory_flow_nid = current_nid + 1;

  print_sd();println();

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_beq() {
  // compute if beq condition is true
  printf3("%d eq 1 %d %d ; ",
    (char*) current_nid,       // nid of this line
    (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
    (char*) (reg_nids + rs2)); // nid of current value of $rs2 register

  print_beq();println();

  // true branch
  go_to_instruction(is, REG_ZR, pc, pc + imm, current_nid);

  // compute if beq condition is false
  printf2("%d not 1 %d\n",
    (char*) current_nid + 1, // nid of this line
    (char*) current_nid);    // nid of preceding line

  // false branch
  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, current_nid + 1);
}

void model_jal() {
  if (rd != REG_ZR) {
    // address of next instruction used here and in returning jalr instruction
    printf3("%d constd 2 %d ; %x\n",
      (char*) current_nid,             // nid of this line
      (char*) (pc + INSTRUCTIONSIZE),  // address of next instruction
      (char*) (pc + INSTRUCTIONSIZE)); // address of next instruction

    // if this instruction is active link $rd register to address of next instruction
    printf4("%d ite 2 %d %d %d ; ",
      (char*) (current_nid + 1),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this jal instruction
      (char*) current_nid,            // nid of address of next instruction
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_jal();println();

    // link next instruction to returning jalr instruction via instruction at address pc + imm
    go_to_instruction(JALR, REG_ZR, pc + imm, pc + INSTRUCTIONSIZE, current_nid);
  }

  // jump from this instruction to instruction at address pc + imm
  go_to_instruction(is, rd, pc, pc + imm, 0);
}

void model_jalr() {
  if (rd == REG_ZR)
    if (imm == 0)
      if (rs1 == REG_RA)
        if (pc >= estimated_return)
          // no forward branches and jumps outside of "procedure body"
          if (current_callee > entry_point) {
            // assert: current_callee points to an instruction to which a jal jumps
            *(call_return + (current_callee - entry_point) / INSTRUCTIONSIZE) = pc;

            // assert: next "procedure body" begins right after jalr
            current_callee = pc + INSTRUCTIONSIZE;

            estimated_return = current_callee;

            return;
          }

  //report the error on the console
  output_fd = 1;

  printf3("%s: unsupported jalr at address %x with estimated address %x detected\n", selfie_name, (char*) pc, (char*) estimated_return);

  exit(EXITCODE_MODELCHECKINGERROR);
}

void model_ecall() {
  if (reg_a7 == SYSCALL_EXIT) {
    // assert: exit ecall is immediately followed by first procedure in code
    current_callee = pc + INSTRUCTIONSIZE;

    estimated_return = current_callee;
  }

  reg_a7 = 0;

  // keep track of whether any ecall is active
  printf3("%d ite 1 %d 11 %d ; ",
    (char*) current_nid,         // nid of this line
    (char*) pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
    (char*) ecall_flow_nid);     // nid of most recent update of ecall activation

  ecall_flow_nid = current_nid;

  print_ecall();println();

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void translate_to_model() {
  // assert: 1 <= is <= number of RISC-U instructions
  if (is == ADDI)
    model_addi();
  else if (is == LD)
    model_ld();
  else if (is == SD)
    model_sd();
  else if (is == ADD)
    model_add();
  else if (is == SUB)
    model_sub();
  else if (is == MUL)
    model_mul();
  else if (is == DIVU)
    model_divu();
  else if (is == REMU)
    model_remu();
  else if (is == SLTU)
    model_sltu();
  else if (is == BEQ)
    model_beq();
  else if (is == JAL)
    model_jal();
  else if (is == JALR)
    model_jalr();
  else if (is == LUI)
    model_lui();
  else if (is == ECALL)
    model_ecall();
}

void model_syscalls() {
  uint64_t kernel_mode_flow_nid;

  printf2("%d constd 2 %d ; SYSCALL_EXIT\n", (char*) current_nid, (char*) SYSCALL_EXIT);
  printf2("%d constd 2 %d ; SYSCALL_READ\n", (char*) (current_nid + 1), (char*) SYSCALL_READ);
  printf2("%d constd 2 %d ; SYSCALL_WRITE\n", (char*) (current_nid + 2), (char*) SYSCALL_WRITE);
  printf2("%d constd 2 %d ; SYSCALL_OPENAT\n", (char*) (current_nid + 3), (char*) SYSCALL_OPENAT);
  printf2("%d constd 2 %d ; SYSCALL_BRK\n\n", (char*) (current_nid + 4), (char*) SYSCALL_BRK);

  printf3("%d eq 1 %d %d ; $a7 == SYSCALL_EXIT\n",
    (char*) (current_nid + 10),  // nid of this line
    (char*) (reg_nids + REG_A7), // nid of current value of $a7 register
    (char*) current_nid);        // nid of SYSCALL_EXIT
  printf3("%d eq 1 %d %d ; $a7 == SYSCALL_READ\n",
    (char*) (current_nid + 11),  // nid of this line
    (char*) (reg_nids + REG_A7), // nid of current value of $a7 register
    (char*) (current_nid + 1));  // nid of SYSCALL_READ
  printf3("%d eq 1 %d %d ; $a7 == SYSCALL_WRITE\n",
    (char*) (current_nid + 12),  // nid of this line
    (char*) (reg_nids + REG_A7), // nid of current value of $a7 register
    (char*) (current_nid + 2));  // nid of SYSCALL_WRITE
  printf3("%d eq 1 %d %d ; $a7 == SYSCALL_OPENAT\n",
    (char*) (current_nid + 13),  // nid of this line
    (char*) (reg_nids + REG_A7), // nid of current value of $a7 register
    (char*) (current_nid + 3));  // nid of SYSCALL_OPENAT
  printf3("%d eq 1 %d %d ; $a7 == SYSCALL_BRK\n\n",
    (char*) (current_nid + 14),  // nid of this line
    (char*) (reg_nids + REG_A7), // nid of current value of $a7 register
    (char*) (current_nid + 4));  // nid of SYSCALL_BRK

  printf2("%d not 1 %d ; $a7 != SYSCALL_EXIT\n",
    (char*) (current_nid + 20),  // nid of this line
    (char*) (current_nid + 10)); // nid of $a7 == SYSCALL_EXIT
  printf3("%d ite 1 %d 10 %d ; ... and $a7 != SYSCALL_READ\n",
    (char*) (current_nid + 21),  // nid of this line
    (char*) (current_nid + 11),  // nid of $a7 == SYSCALL_READ
    (char*) (current_nid + 20)); // nid of preceding line
  printf3("%d ite 1 %d 10 %d ; ... and $a7 != SYSCALL_WRITE\n",
    (char*) (current_nid + 22),  // nid of this line
    (char*) (current_nid + 12),  // nid of $a7 == SYSCALL_WRITE
    (char*) (current_nid + 21)); // nid of preceding line
  printf3("%d ite 1 %d 10 %d ; ... and $a7 != SYSCALL_OPENAT\n",
    (char*) (current_nid + 23),  // nid of this line
    (char*) (current_nid + 13),  // nid of $a7 == SYSCALL_OPENAT
    (char*) (current_nid + 22)); // nid of preceding line
  printf3("%d ite 1 %d 10 %d ; ... and $a7 != SYSCALL_BRK (invalid syscall id in $a7 detected)\n\n",
    (char*) (current_nid + 24),  // nid of this line
    (char*) (current_nid + 14),  // nid of $a7 == SYSCALL_BRK
    (char*) (current_nid + 23)); // nid of preceding line

  // if any ecall is active check if $a7 register contains invalid syscall id
  printf3("%d and 1 %d %d ; ecall is active for invalid syscall id\n",
    (char*) (current_nid + 30),  // nid of this line
    (char*) ecall_flow_nid,      // nid of most recent update of ecall activation
    (char*) (current_nid + 24)); // nid of invalid syscall id check
  printf2("%d bad %d ; ecall invalid syscall id\n\n",
    (char*) (current_nid + 31),  // nid of this line
    (char*) (current_nid + 30)); // nid of preceding line


  // if exit ecall is active check if exit code in $a0 register is not 0
  printf3("%d and 1 %d %d ; exit ecall is active\n",
    (char*) (current_nid + 1000), // nid of this line
    (char*) ecall_flow_nid,       // nid of most recent update of ecall activation
    (char*) (current_nid + 10));  // nid of $a7 == SYSCALL_EXIT
  if (bad_exit_code == 0)
    printf2("%d neq 1 %d 20 ; $a0 != zero exit code\n",
      (char*) (current_nid + 1002), // nid of this line
      (char*) (reg_nids + REG_A0)); // nid of current value of $a0 register
  else {
    printf2("%d constd 2 %d ; bad exit code\n",
      (char*) (current_nid + 1001), // nid of this line
      (char*) bad_exit_code);       // value of bad exit code
    printf3("%d eq 1 %d %d ; $a0 == bad non-zero exit code\n",
      (char*) (current_nid + 1002),  // nid of this line
      (char*) (reg_nids + REG_A0),   // nid of current value of $a0 register
      (char*) (current_nid + 1001)); // nid of value of bad non-zero exit code
  }
  printf3("%d and 1 %d %d ; exit ecall is active with non-zero exit code\n",
    (char*) (current_nid + 1003),  // nid of this line
    (char*) (current_nid + 1000),  // nid of exit ecall is active
    (char*) (current_nid + 1002)); // nid of non-zero exit code
  printf2("%d bad %d ; non-zero exit code\n",
    (char*) (current_nid + 1004),  // nid of this line
    (char*) (current_nid + 1003)); // nid of preceding line

  // if exit ecall is active stay in kernel mode indefinitely
  printf3("%d ite 1 60 %d %d ; stay in kernel mode indefinitely if exit ecall is active\n\n",
    (char*) (current_nid + 1050),  // nid of this line
    (char*) (current_nid + 10),    // nid of $a7 == SYSCALL_EXIT
    (char*) (current_nid + 1000)); // nid of exit ecall is active

  kernel_mode_flow_nid = current_nid + 1050;


  // read ecall
  printf3("%d and 1 %d %d ; read ecall is active\n",
    (char*) (current_nid + 1100), // nid of this line
    (char*) ecall_flow_nid,       // nid of most recent update of ecall activation
    (char*) (current_nid + 11));  // nid of $a7 == SYSCALL_READ

  // if read ecall is active record $a1 register for checking address validity
  printf4("%d ite 2 %d %d %d ; $a1 is start address of write buffer for checking address validity\n",
    (char*) (current_nid + 1101),   // nid of this line
    (char*) (current_nid + 1100),   // nid of read ecall is active
    (char*) (reg_nids + REG_A1),    // nid of current value of $a1 register
    (char*) access_flow_start_nid); // nid of address of most recent memory access

  access_flow_start_nid = current_nid + 1101;

  // if read ecall is active record $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and
  // $a1 otherwise, as address for checking address validity
  printf2("%d dec 2 %d ; $a2 - 1\n",
    (char*) (current_nid + 1102), // nid of this line
    (char*) (reg_nids + REG_A2)); // nid of current value of $a2 register
  printf1("%d not 2 27 ; not 7\n",
    (char*) (current_nid + 1103)); // nid of this line
  printf3("%d and 2 %d %d ; reset 3 LSBs of $a2 - 1\n",
    (char*) (current_nid + 1104),  // nid of this line
    (char*) (current_nid + 1102),  // nid of $a2 - 1
    (char*) (current_nid + 1103)); // nid of not 7
  printf3("%d add 2 %d %d ; $a1 + (($a2 - 1) / 8) * 8\n",
    (char*) (current_nid + 1105),  // nid of this line
    (char*) (reg_nids + REG_A1),   // nid of current value of $a1 register
    (char*) (current_nid + 1104)); // nid of (($a2 - 1) / 8) * 8
  printf2("%d ugt 1 %d 20 ; $a2 > 0\n",
    (char*) (current_nid + 1106), // nid of this line
    (char*) (reg_nids + REG_A2)); // nid of current value of $a2 register
  printf4("%d ite 2 %d %d %d ; $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and $a1 otherwise\n",
    (char*) (current_nid + 1107), // nid of this line
    (char*) (current_nid + 1106), // nid of $a2 > 0
    (char*) (current_nid + 1105), // nid of $a1 + (($a2 - 1) / 8) * 8
    (char*) (reg_nids + REG_A1)); // nid of current value of $a1 register
  printf4("%d ite 2 %d %d %d ; $a1 + (($a2 - 1) / 8) * 8 is end address of write buffer for checking address validity\n",
    (char*) (current_nid + 1108), // nid of this line
    (char*) (current_nid + 1100), // nid of read ecall is active
    (char*) (current_nid + 1107), // nid of $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and $a1 otherwise
    (char*) access_flow_end_nid); // nid of address of most recent memory access

  access_flow_end_nid = current_nid + 1108;

  // if read ecall is active record $a1 bounds for checking address validity
  record_end_bounds(record_start_bounds(1109, current_nid + 1100, REG_A1), current_nid + 1100, REG_A1);

  // TODO: check file descriptor validity, return error codes

  // if read ecall is active go into kernel mode
  printf3("%d ite 1 %d 11 %d ; go into kernel mode if read ecall is active\n",
    (char*) (current_nid + 1150),  // nid of this line
    (char*) (current_nid + 1100),  // nid of read ecall is active
    (char*) kernel_mode_flow_nid); // nid of most recent update of kernel-mode flag

  kernel_mode_flow_nid = current_nid + 1150;

  // if read ecall is active set $a0 (number of read bytes) = 0 bytes
  printf3("%d ite 2 %d 20 %d ; set $a0 = 0 bytes if read ecall is active\n",
    (char*) (current_nid + 1151),       // nid of this line
    (char*) (current_nid + 1100),       // nid of read ecall is active
    (char*) *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_nid + 1151;

  // determine number of bytes to read in next step
  printf3("%d sub 2 %d %d ; $a2 - $a0\n",
    (char*) (current_nid + 1160), // nid of this line
    (char*) (reg_nids + REG_A2),  // nid of current value of $a2 register
    (char*) (reg_nids + REG_A0)); // nid of current value of $a0 register
  printf2("%d ugte 1 %d 28 ; $a2 - $a0 >= 8 bytes\n",
    (char*) (current_nid + 1161),  // nid of this line
    (char*) (current_nid + 1160)); // nid of $a2 - $a0
  printf3("%d ite 2 %d 28 %d ; read 8 bytes if $a2 - $a0 >= 8 bytes, or else $a2 - $a0 bytes\n",
    (char*) (current_nid + 1162),  // nid of this line
    (char*) (current_nid + 1161),  // nid of $a2 - $a0 >= 8 bytes
    (char*) (current_nid + 1160)); // nid of $a2 - $a0

  // compute unsigned-extended input
  printf2("%d eq 1 %d 22 ; increment == 2\n",
    (char*) (current_nid + 1170),  // nid of this line
    (char*) (current_nid + 1162)); // nid of increment
  printf2("%d ite 2 %d 92 91 ; unsigned-extended 2-byte input if increment == 2, or else unsigned-extended 1-byte input\n",
    (char*) (current_nid + 1171),  // nid of this line
    (char*) (current_nid + 1170)); // nid of increment == 2
  printf2("%d eq 1 %d 23 ; increment == 3\n",
    (char*) (current_nid + 1172),  // nid of this line
    (char*) (current_nid + 1162)); // nid of increment
  printf3("%d ite 2 %d 93 %d ; unsigned-extended 3-byte input if increment == 3\n",
    (char*) (current_nid + 1173),  // nid of this line
    (char*) (current_nid + 1172),  // nid of increment == 3
    (char*) (current_nid + 1171)); // nid of unsigned-extended 2-byte input
  printf2("%d eq 1 %d 24 ; increment == 4\n",
    (char*) (current_nid + 1174),  // nid of this line
    (char*) (current_nid + 1162)); // nid of increment
  printf3("%d ite 2 %d 94 %d ; unsigned-extended 4-byte input if increment == 4\n",
    (char*) (current_nid + 1175),  // nid of this line
    (char*) (current_nid + 1174),  // nid of increment == 4
    (char*) (current_nid + 1173)); // nid of unsigned-extended 3-byte input
  printf2("%d eq 1 %d 25 ; increment == 5\n",
    (char*) (current_nid + 1176),  // nid of this line
    (char*) (current_nid + 1162)); // nid of increment
  printf3("%d ite 2 %d 95 %d ; unsigned-extended 5-byte input if increment == 5\n",
    (char*) (current_nid + 1177),  // nid of this line
    (char*) (current_nid + 1176),  // nid of increment == 5
    (char*) (current_nid + 1175)); // nid of unsigned-extended 4-byte input
  printf2("%d eq 1 %d 26 ; increment == 6\n",
    (char*) (current_nid + 1178),  // nid of this line
    (char*) (current_nid + 1162)); // nid of increment
  printf3("%d ite 2 %d 96 %d ; unsigned-extended 6-byte input if increment == 6\n",
    (char*) (current_nid + 1179),  // nid of this line
    (char*) (current_nid + 1178),  // nid of increment == 6
    (char*) (current_nid + 1177)); // nid of unsigned-extended 5-byte input
  printf2("%d eq 1 %d 27 ; increment == 7\n",
    (char*) (current_nid + 1180),  // nid of this line
    (char*) (current_nid + 1162)); // nid of increment
  printf3("%d ite 2 %d 97 %d ; unsigned-extended 7-byte input if increment == 7\n",
    (char*) (current_nid + 1181),  // nid of this line
    (char*) (current_nid + 1180),  // nid of increment == 7
    (char*) (current_nid + 1179)); // nid of unsigned-extended 6-byte input
  printf2("%d eq 1 %d 28 ; increment == 8\n",
    (char*) (current_nid + 1182),  // nid of this line
    (char*) (current_nid + 1162)); // nid of increment
  printf3("%d ite 2 %d 98 %d ; 8-byte input if increment == 8\n",
    (char*) (current_nid + 1183),  // nid of this line
    (char*) (current_nid + 1182),  // nid of increment == 8
    (char*) (current_nid + 1181)); // nid of unsigned-extended 7-byte input

  // write input to memory at address $a1 + $a0
  printf3("%d add 2 %d %d ; $a1 + $a0\n",
    (char*) (current_nid + 1184), // nid of this line
    (char*) (reg_nids + REG_A1),  // nid of current value of $a1 register
    (char*) (reg_nids + REG_A0)); // nid of current value of $a0 register
  printf4("%d write 3 %d %d %d ; memory[$a1 + $a0] = input\n",
    (char*) (current_nid + 1185),  // nid of this line
    (char*) memory_nid,            // nid of memory
    (char*) (current_nid + 1184),  // nid of $a1 + $a0
    (char*) (current_nid + 1183)); // nid of input

  // read ecall is in kernel mode and not done yet
  printf3("%d ult 1 %d %d ; $a0 < $a2\n",
    (char*) (current_nid + 1190), // nid of this line
    (char*) (reg_nids + REG_A0),  // nid of current value of $a0 register
    (char*) (reg_nids + REG_A2)); // nid of current value of $a2 register
  printf3("%d and 1 %d %d ; $a7 == SYSCALL_READ and $a0 < $a2\n",
    (char*) (current_nid + 1191),  // nid of this line
    (char*) (current_nid + 11),    // nid of $a7 == SYSCALL_READ
    (char*) (current_nid + 1190)); // nid of $a0 < $a2
  printf2("%d and 1 60 %d ; read ecall is in kernel mode and not done yet\n",
    (char*) (current_nid + 1192),  // nid of this line
    (char*) (current_nid + 1191)); // nid of $a7 == SYSCALL_READ and $a0 < $a2

  // if read ecall is in kernel mode and not done yet write input to memory at address $a1 + $a0
  printf2("%d ugt 1 %d 20 ; increment > 0\n",
    (char*) (current_nid + 1193),  // nid of this line
    (char*) (current_nid + 1162)); // nid of increment
  printf3("%d and 1 %d %d ; read ecall is in kernel mode and not done yet and increment > 0\n",
    (char*) (current_nid + 1194),  // nid of this line
    (char*) (current_nid + 1192),  // nid of read ecall is in kernel mode and not done yet
    (char*) (current_nid + 1193)); // nid of increment > 0
  printf4("%d ite 3 %d %d %d ; set memory[$a1 + $a0] = input if read ecall is in kernel mode and not done yet and increment > 0\n",
    (char*) (current_nid + 1195), // nid of this line
    (char*) (current_nid + 1194), // nid of read ecall is in kernel mode and not done yet and increment > 0
    (char*) (current_nid + 1185), // nid of memory[$a1 + $a0] = input
    (char*) memory_flow_nid);     // nid of most recent update of memory

  memory_flow_nid = current_nid + 1195;

  // if read ecall is in kernel mode and not done yet increment number of bytes read
  printf3("%d add 2 %d %d ; $a0 + increment\n",
    (char*) (current_nid + 1196),  // nid of this line
    (char*) (reg_nids + REG_A0),   // nid of current value of $a0 register
    (char*) (current_nid + 1162)); // nid of increment
  printf4("%d ite 2 %d %d %d ; set $a0 = $a0 + increment if read ecall is in kernel mode and not done yet\n",
    (char*) (current_nid + 1197),       // nid of this line
    (char*) (current_nid + 1192),       // nid of read ecall is in kernel mode and not done yet
    (char*) (current_nid + 1196),       // nid of $a0 + increment
    (char*) *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_nid + 1197;

  // if read ecall is in kernel mode and not done yet stay in kernel mode
  printf3("%d ite 1 %d 11 %d ; stay in kernel mode if read ecall is in kernel mode and not done yet\n\n",
    (char*) (current_nid + 1198),  // nid of this line
    (char*) (current_nid + 1192),  // nid of read ecall is in kernel mode and not done yet
    (char*) kernel_mode_flow_nid); // nid of most recent update of kernel-mode flag

  kernel_mode_flow_nid = current_nid + 1198;


  // write ecall
  printf3("%d and 1 %d %d ; write ecall is active\n",
    (char*) (current_nid + 1200), // nid of this line
    (char*) ecall_flow_nid,       // nid of most recent update of ecall activation
    (char*) (current_nid + 12));  // nid of $a7 == SYSCALL_WRITE

  // if write ecall is active record $a1 register for checking address validity
  printf4("%d ite 2 %d %d %d ; $a1 is start address of read buffer for checking address validity\n",
    (char*) (current_nid + 1201),   // nid of this line
    (char*) (current_nid + 1200),   // nid of write ecall is active
    (char*) (reg_nids + REG_A1),    // nid of current value of $a1 register
    (char*) access_flow_start_nid); // nid of address of most recent memory access

  access_flow_start_nid = current_nid + 1201;

  // if write ecall is active record $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and
  // $a1 otherwise, as address for checking address validity
  printf2("%d dec 2 %d ; $a2 - 1\n",
    (char*) (current_nid + 1202), // nid of this line
    (char*) (reg_nids + REG_A2)); // nid of current value of $a2 register
  printf1("%d not 2 27 ; not 7\n",
    (char*) (current_nid + 1203)); // nid of this line
  printf3("%d and 2 %d %d ; reset 3 LSBs of $a2 - 1\n",
    (char*) (current_nid + 1204),  // nid of this line
    (char*) (current_nid + 1202),  // nid of $a2 - 1
    (char*) (current_nid + 1203)); // nid of not 7
  printf3("%d add 2 %d %d ; $a1 + (($a2 - 1) / 8) * 8\n",
    (char*) (current_nid + 1205),  // nid of this line
    (char*) (reg_nids + REG_A1),   // nid of current value of $a1 register
    (char*) (current_nid + 1204)); // nid of (($a2 - 1) / 8) * 8
  printf2("%d ugt 1 %d 20 ; $a2 > 0\n",
    (char*) (current_nid + 1206), // nid of this line
    (char*) (reg_nids + REG_A2)); // nid of current value of $a2 register
  printf4("%d ite 2 %d %d %d ; $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and $a1 otherwise\n",
    (char*) (current_nid + 1207), // nid of this line
    (char*) (current_nid + 1206), // nid of $a2 > 0
    (char*) (current_nid + 1205), // nid of $a1 + (($a2 - 1) / 8) * 8
    (char*) (reg_nids + REG_A1)); // nid of current value of $a1 register
  printf4("%d ite 2 %d %d %d ; $a1 + (($a2 - 1) / 8) * 8 is end address of read buffer for checking address validity\n",
    (char*) (current_nid + 1208), // nid of this line
    (char*) (current_nid + 1200), // nid of write ecall is active
    (char*) (current_nid + 1207), // nid of $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and $a1 otherwise
    (char*) access_flow_end_nid); // nid of address of most recent memory access

  access_flow_end_nid = current_nid + 1208;

  // if write ecall is active record $a1 bounds for checking address validity
  record_end_bounds(record_start_bounds(1209, current_nid + 1200, REG_A1), current_nid + 1200, REG_A1);

  // TODO: check file descriptor validity, return error codes

  // if write ecall is active set $a0 (written number of bytes) = $a2 (size)
  printf4("%d ite 2 %d %d %d ; set $a0 = $a2 if write ecall is active\n\n",
    (char*) (current_nid + 1250),       // nid of this line
    (char*) (current_nid + 1200),       // nid of write ecall is active
    (char*) (reg_nids + REG_A2),        // nid of current value of $a2 register
    (char*) *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_nid + 1250;


  // openat ecall
  printf3("%d and 1 %d %d ; openat ecall is active\n",
    (char*) (current_nid + 1300), // nid of this line
    (char*) ecall_flow_nid,       // nid of most recent update of ecall activation
    (char*) (current_nid + 13));  // nid of $a7 == SYSCALL_OPENAT

  // if openat ecall is active record $a1 register for checking address validity
  printf4("%d ite 2 %d %d %d ; $a1 is start address of filename for checking address validity\n",
    (char*) (current_nid + 1301),   // nid of this line
    (char*) (current_nid + 1300),   // nid of openat ecall is active
    (char*) (reg_nids + REG_A1),    // nid of current value of $a1 register
    (char*) access_flow_start_nid); // nid of address of most recent memory access

  access_flow_start_nid = current_nid + 1301;

  // if openat ecall is active record $a1 bounds for checking address validity
  record_start_bounds(1302, current_nid + 1300, REG_A1);

  // TODO: check address validity of whole filename, flags and mode arguments

  printf1("%d state 2 fd-bump\n", (char*) (current_nid + 1350));
  printf2("%d init 2 %d 21 ; initial fd-bump is 1 (file descriptor bump pointer)\n",
    (char*) (current_nid + 1351),  // nid of this line
    (char*) (current_nid + 1350)); // nid of fd-bump

  // if openat ecall is active set $a0 (file descriptor) = fd-bump + 1 (next file descriptor)
  printf2("%d inc 2 %d\n",
    (char*) (current_nid + 1352),  // nid of this line
    (char*) (current_nid + 1350)); // nid of fd-bump
  printf4("%d ite 2 %d %d %d ; fd-bump + 1 if openat ecall is active\n",
    (char*) (current_nid + 1353),  // nid of this line
    (char*) (current_nid + 1300),  // nid of openat ecall is active
    (char*) (current_nid + 1352),  // nid of fd-bump + 1
    (char*) (current_nid + 1350)); // nid of fd-bump
  printf3("%d next 2 %d %d ; increment fd-bump if openat ecall is active\n",
    (char*) (current_nid + 1354),  // nid of this line
    (char*) (current_nid + 1350),  // nid of fd-bump
    (char*) (current_nid + 1353)); // nid of fd-bump + 1
  printf4("%d ite 2 %d %d %d ; set $a0 = fd-bump + 1 if openat ecall is active\n\n",
    (char*) (current_nid + 1355),       // nid of this line
    (char*) (current_nid + 1300),       // nid of openat ecall is active
    (char*) (current_nid + 1352),       // nid of fd-bump + 1
    (char*) *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_nid + 1355;


  // is brk ecall is active?
  printf3("%d and 1 %d %d ; brk ecall is active\n",
    (char*) (current_nid + 1400), // nid of this line
    (char*) ecall_flow_nid,       // nid of most recent update of ecall activation
    (char*) (current_nid + 14));  // nid of $a7 == SYSCALL_BRK

  printf1("%d state 2 brk\n", (char*) (current_nid + 1450));
  printf2("%d init 2 %d 31 ; original program break is end of binary\n",
    (char*) (current_nid + 1451),  // nid of this line
    (char*) (current_nid + 1450)); // nid of brk

  // if brk ecall is active and $a0 is valid set brk = $a0
  // $a0 is valid if brk <= $a0 < $sp and $a0 is word-aligned
  printf3("%d ulte 1 %d %d ; brk <= $a0\n",
    (char*) (current_nid + 1452), // nid of this line
    (char*) (current_nid + 1450), // nid of brk
    (char*) (reg_nids + REG_A0)); // nid of current value of $a0 register
  printf3("%d ult 1 %d %d ; $a0 < $sp\n",
    (char*) (current_nid + 1453), // nid of this line
    (char*) (reg_nids + REG_A0),  // nid of current value of $a0 register
    (char*) (reg_nids + REG_SP)); // nid of current value of $sp register
  printf3("%d and 1 %d %d ; brk <= $a0 < $sp\n",
    (char*) (current_nid + 1454),  // nid of this line
    (char*) (current_nid + 1452),  // nid of brk <= $a0
    (char*) (current_nid + 1453)); // nid of $a0 < $sp
  printf2("%d and 2 %d 27 ; reset all but 3 LSBs of $a0\n",
    (char*) (current_nid + 1455), // nid of this line
    (char*) (reg_nids + REG_A0)); // nid of current value of $a0 register
  printf2("%d eq 1 %d 20 ; 3 LSBs of $a0 == 0 ($a0 is word-aligned)\n",
    (char*) (current_nid + 1456),  // nid of this line
    (char*) (current_nid + 1455)); // nid of 3 LSBs of current value of $a0 register
  printf3("%d and 1 %d %d ; brk <= $a0 < $sp and $a0 is word-aligned ($a0 is valid)\n",
    (char*) (current_nid + 1457),  // nid of this line
    (char*) (current_nid + 1454),  // nid of brk <= $a0 < $sp
    (char*) (current_nid + 1456)); // nid of $a0 is word-aligned
  printf3("%d and 1 %d %d ; brk ecall is active and $a0 is valid\n",
    (char*) (current_nid + 1458),  // nid of this line
    (char*) (current_nid + 1400),  // nid of brk ecall is active
    (char*) (current_nid + 1457)); // nid of $a0 is valid
  printf4("%d ite 2 %d %d %d ; brk = $a0 if brk ecall is active and $a0 is valid\n",
    (char*) (current_nid + 1459),  // nid of this line
    (char*) (current_nid + 1458),  // nid of brk ecall is active and $a0 is valid
    (char*) (reg_nids + REG_A0),   // nid of current value of $a0 register
    (char*) (current_nid + 1450)); // nid of brk
  printf3("%d next 2 %d %d ; set brk = $a0 if brk ecall is active and $a0 is valid\n",
    (char*) (current_nid + 1460),  // nid of this line
    (char*) (current_nid + 1450),  // nid of brk
    (char*) (current_nid + 1459)); // nid of preceding line

  // if brk ecall is active and $a0 is invalid set $a0 = brk
  printf2("%d not 1 %d ; $a0 is invalid\n",
    (char*) (current_nid + 1461),  // nid of this line
    (char*) (current_nid + 1457)); // nid of $a0 is valid
  printf3("%d and 1 %d %d ; brk ecall is active and $a0 is invalid\n",
    (char*) (current_nid + 1462),  // nid of this line
    (char*) (current_nid + 1400),  // nid of brk ecall is active
    (char*) (current_nid + 1461)); // nid of $a0 is invalid
  printf4("%d ite 2 %d %d %d ; set $a0 = brk if brk ecall is active and $a0 is invalid\n",
    (char*) (current_nid + 1463),       // nid of this line
    (char*) (current_nid + 1462),       // nid of brk ecall is active and $a0 is invalid
    (char*) (current_nid + 1450),       // nid of brk
    (char*) *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_nid + 1463;

  if (check_block_access) {
    printf4("%d ite 2 %d %d %d ; lower bound on $t1 = brk if brk ecall is active and $a0 is valid\n",
      (char*) (current_nid + 1464),                 // nid of this line
      (char*) (current_nid + 1458),                 // nid of brk ecall is active and $a0 is valid
      (char*) (current_nid + 1450),                 // nid of brk
      (char*) *(reg_flow_nids + LO_FLOW + REG_T1)); // nid of most recent update of lower bound on $t1 register

    *(reg_flow_nids + LO_FLOW + REG_T1) = current_nid + 1464;

    printf4("%d ite 2 %d %d %d ; upper bound on $t1 = $a0 if brk ecall is active and $a0 is valid\n",
      (char*) (current_nid + 1465),                 // nid of this line
      (char*) (current_nid + 1458),                 // nid of brk ecall is active and $a0 is valid
      (char*) (reg_nids + REG_A0),                  // nid of current value of $a0 register
      (char*) *(reg_flow_nids + UP_FLOW + REG_T1)); // nid of most recent update of upper bound on $t1 register

    *(reg_flow_nids + UP_FLOW + REG_T1) = current_nid + 1465;

    printf3("%d ite 2 %d 30 %d ; lower bound on $t1 = end of code segment if brk ecall is active and $a0 is invalid\n",
      (char*) (current_nid + 1466),                 // nid of this line
      (char*) (current_nid + 1462),                 // nid of brk ecall is active and $a0 is invalid
      (char*) *(reg_flow_nids + LO_FLOW + REG_T1)); // nid of most recent update of lower bound on $t1 register

    *(reg_flow_nids + LO_FLOW + REG_T1) = current_nid + 1466;

    printf3("%d ite 2 %d 50 %d ; upper bound on $t1 = 4GB of memory addresses if brk ecall is active and $a0 is invalid\n",
      (char*) (current_nid + 1467),                 // nid of this line
      (char*) (current_nid + 1462),                 // nid of brk ecall is active and $a0 is invalid
      (char*) *(reg_flow_nids + UP_FLOW + REG_T1)); // nid of most recent update of upper bound on $t1 register

    *(reg_flow_nids + UP_FLOW + REG_T1) = current_nid + 1467;
  }

  printf2("\n%d next 1 60 %d ; update kernel-mode flag\n",
    (char*) (current_nid + 1500),  // nid of this line
    (char*) kernel_mode_flow_nid); // nid of most recent update of kernel-mode flag
}

uint64_t control_flow(uint64_t activate_nid, uint64_t control_flow_nid) {
  if (control_flow_nid == 10)
    // instruction proceeding here is first instruction to do so
    return activate_nid;
  else {
    // activate current instruction if instruction proceeding here is active
    printf3("%d ite 1 %d 11 %d\n",
      (char*) current_nid,       // nid of this line
      (char*) activate_nid,      // nid of pc flag of instruction proceeding here
      (char*) control_flow_nid); // nid of previously processed in-edge

    current_nid = current_nid + 1;

    return current_nid - 1;
  }
}

void check_division_by_zero(uint64_t division, uint64_t flow_nid) {
  // check if divisor == 0
  printf2("%d eq 1 %d 20\n",
    (char*) current_nid, // nid of this line
    (char*) flow_nid);   // nid of divisor of most recent division or remainder
  printf2("%d bad %d ; ",
    (char*) (current_nid + 1), // nid of this line
    (char*) current_nid);      // nid of divisor == 0
  if (division)
    print("division by zero\n\n");
  else
    print("remainder by zero\n\n");

  current_nid = current_nid + 2;
}

void check_address_validity(uint64_t start, uint64_t flow_nid, uint64_t lo_flow_nid, uint64_t up_flow_nid) {
  if (start)
    print("; at start of memory block\n\n");
  else
    print("; at end of memory block\n\n");

  // check if address of most recent memory access < current lower bound
  printf3("%d ult 1 %d %d\n",
    (char*) current_nid,  // nid of this line
    (char*) flow_nid,     // nid of address of most recent memory access
    (char*) lo_flow_nid); // nid of current lower bound on memory addresses
  printf2("%d bad %d ; memory access below lower bound\n",
    (char*) (current_nid + 1), // nid of this line
    (char*) current_nid);      // nid of previous check

  current_nid = current_nid + 2;

  // check if address of most recent memory access >= current upper bound
  printf3("%d ugte 1 %d %d\n",
    (char*) current_nid,  // nid of this line
    (char*) flow_nid,     // nid of address of most recent memory access
    (char*) up_flow_nid); // nid of current upper bound on memory addresses
  printf2("%d bad %d ; memory access at or above upper bound\n",
    (char*) (current_nid + 1), // nid of this line
    (char*) current_nid);      // nid of previous check

  current_nid = current_nid + 2;

  // check if address of most recent memory access is word-aligned
  printf2("%d and 2 %d 27\n",
    (char*) current_nid, // nid of this line
    (char*) flow_nid);   // nid of address of most recent memory access
  printf2("%d neq 1 %d 20\n",
    (char*) (current_nid + 1), // nid of this line
    (char*) current_nid);      // nid of 3 LSBs of address of most recent memory access
  printf2("%d bad %d ; word-unaligned memory access\n\n",
    (char*) (current_nid + 2),  // nid of this line
    (char*) (current_nid + 1)); // nid of previous check

  current_nid = current_nid + 3;
}

uint64_t selfie_model_generate() {
  uint64_t i;

  uint64_t machine_word;

  uint64_t loader_nid;
  uint64_t code_nid;
  uint64_t control_nid;
  uint64_t condition_nid;

  uint64_t data_flow_nid;
  uint64_t control_flow_nid;

  uint64_t* in_edge;

  uint64_t from_instruction;
  uint64_t from_address;
  uint64_t jalr_address;

  // use extension ".btor2" in name of SMT-LIB file
  model_name = replace_extension(binary_name, "btor2");

  if (code_length == 0) {
    printf2("%s: nothing to disassemble to output file %s\n", selfie_name, model_name);

    return EXITCODE_BADARGUMENTS;
  }

  // assert: model_name is mapped and not longer than MAX_FILENAME_LENGTH

  model_fd = open_write_only(model_name);

  if (signed_less_than(model_fd, 0)) {
    printf2("%s: could not create model output file %s\n", selfie_name, model_name);

    return EXITCODE_IOERROR;
  }

  output_name = model_name;
  output_fd   = model_fd;

  reset_library();
  reset_interpreter();
  reset_microkernel();

  init_memory(1);

  bad_exit_code = atoi(peek_argument(0));

  check_block_access = 0;

  if (number_of_remaining_arguments() > 1)
    if (string_compare(peek_argument(1), "--check-block-access")) {
      check_block_access = 1;

      get_argument();
    }

  boot_loader();

  run = 0;

  model_check = 1;

  printf1("; %s\n\n", SELFIE_URL);

  printf2("; BTOR2 %s generated by %s for\n", model_name, selfie_name);
  printf1("; RISC-V code obtained from %s and\n; invoked as", binary_name);

  i = 0;

  while (i < number_of_remaining_arguments()) {
    printf1(" %s", (char*) *(remaining_arguments() + i));

    i = i + 1;
  }

  print("\n\n1 sort bitvec 1 ; Boolean\n");
  print("2 sort bitvec 64 ; 64-bit machine word\n");
  print("3 sort array 2 2 ; 64-bit memory\n\n");

  print("10 zero 1\n11 one 1\n\n");

  print("20 zero 2\n21 one 2\n22 constd 2 2\n23 constd 2 3\n24 constd 2 4\n25 constd 2 5\n26 constd 2 6\n27 constd 2 7\n28 constd 2 8\n\n");

  print("; word-aligned end of code segment in memory\n\n");

  // end of code segment for checking address validity
  printf2("30 constd 2 %d ; %x\n\n", (char*) (entry_point + code_length), (char*) (entry_point + code_length));

  print("; word-aligned end of data segment in memory (original program break)\n\n");

  // original program break (end of binary = code + data segment) for checking program break validity
  printf2("31 constd 2 %d ; %x\n\n", (char*) get_original_break(current_context), (char*) get_original_break(current_context));

  print("; word-aligned initial $sp (stack pointer) value from boot loader\n\n");

  // $sp register value from boot loader
  printf2("40 constd 2 %d ; %x\n\n", (char*) *(get_regs(current_context) + REG_SP), (char*) *(get_regs(current_context) + REG_SP));

  print("; 4GB of memory\n\n");

  printf2("50 constd 2 %d ; %x\n\n", (char*) VIRTUALMEMORYSIZE, (char*) VIRTUALMEMORYSIZE);

  print("; kernel-mode flag\n\n");

  print("60 state 1 kernel-mode\n");
  print("61 init 1 60 10 kernel-mode ; initial value is false\n");
  print("62 not 1 60\n\n");

  print("; unsigned-extended inputs for byte-wise reading\n\n");

  print("71 sort bitvec 8 ; 1 byte\n");
  print("72 sort bitvec 16 ; 2 bytes\n");
  print("73 sort bitvec 24 ; 3 bytes\n");
  print("74 sort bitvec 32 ; 4 bytes\n");
  print("75 sort bitvec 40 ; 5 bytes\n");
  print("76 sort bitvec 48 ; 6 bytes\n");
  print("77 sort bitvec 56 ; 7 bytes\n\n");

  print("81 input 71 ; 1 byte\n");
  print("82 input 72 ; 2 bytes\n");
  print("83 input 73 ; 3 bytes\n");
  print("84 input 74 ; 4 bytes\n");
  print("85 input 75 ; 5 bytes\n");
  print("86 input 76 ; 6 bytes\n");
  print("87 input 77 ; 7 bytes\n\n");

  print("91 uext 2 81 56 ; 1 byte\n");
  print("92 uext 2 82 48 ; 2 bytes\n");
  print("93 uext 2 83 40 ; 3 bytes\n");
  print("94 uext 2 84 32 ; 4 bytes\n");
  print("95 uext 2 85 24 ; 5 bytes\n");
  print("96 uext 2 86 16 ; 6 bytes\n");
  print("97 uext 2 87 8 ; 7 bytes\n");
  print("98 input 2 ; 8 bytes\n\n");

  print("; 32 64-bit general-purpose registers\n");

  reg_nids = 100;

  reg_flow_nids = smalloc(3 * NUMBEROFREGISTERS * SIZEOFUINT64STAR);

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    *(reg_flow_nids + i) = reg_nids + i;

    if (i == 0)
      printf2("\n%d zero 2 %s ; register $0 is always 0\n",
        (char*) *(reg_flow_nids + i), // nid of this line
        get_register_name(i));        // register name
    else
      printf3("%d state 2 %s ; register $%d\n",
        (char*) *(reg_flow_nids + i), // nid of this line
        get_register_name(i),         // register name
        (char*) i);                   // register index as comment

    i = i + 1;
  }

  if (check_block_access)
    while (i < 3 * NUMBEROFREGISTERS) {
      *(reg_flow_nids + i) = reg_nids + i;

      if (i == LO_FLOW)
        printf3("\n%d constd 2 %d ; %x\n",
          (char*) *(reg_flow_nids + i),         // nid of this line
          (char*) (entry_point + code_length),  // end of code segment
          (char*) (entry_point + code_length)); // end of code segment
      else if (i == UP_FLOW)
        printf3("\n%d constd 2 %d ; %x\n",
          (char*) *(reg_flow_nids + i), // nid of this line
          (char*) VIRTUALMEMORYSIZE,    // 4GB of memory addresses
          (char*) VIRTUALMEMORYSIZE);   // 4GB of memory addresses
      else {
        printf1("%d state 2 ", (char*) *(reg_flow_nids + i));

        if (i < LO_FLOW + NUMBEROFREGISTERS)
          printf2("lo-%s ; lower bound on $%d\n",
            get_register_name(i % NUMBEROFREGISTERS), // register name
            (char*) (i % NUMBEROFREGISTERS));         // register index as comment
        else if (i < UP_FLOW + NUMBEROFREGISTERS)
          printf2("up-%s ; upper bound on $%d\n",
            get_register_name(i % NUMBEROFREGISTERS), // register name
            (char*) (i % NUMBEROFREGISTERS));         // register index as comment
      }

      i = i + 1;
    }

  print("\n; initializing registers\n");

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    if (i == 0)
      println();
    else if (i == REG_SP)
      printf3("%d init 2 %d 40 %s ; initial value from boot loader\n",
        (char*) (reg_nids * 2 + i), // nid of this line
        (char*) (reg_nids + i),     // nid of $sp register
        get_register_name(i));      // register name as comment
    else
      printf3("%d init 2 %d 20 %s ; initial value is 0\n",
        (char*) (reg_nids * 2 + i), // nid of this line
        (char*) (reg_nids + i),     // nid of to-be-initialized register
        get_register_name(i));      // register name as comment

    i = i + 1;
  }

  if (check_block_access)
    while (i < 3 * NUMBEROFREGISTERS) {
      if (i % NUMBEROFREGISTERS == 0)
        println();
      else if (i < LO_FLOW + NUMBEROFREGISTERS)
        printf3("%d init 2 %d 30 %s ; initial value is end of code segment\n",
          (char*) (reg_nids * 2 + i),                // nid of this line
          (char*) (reg_nids + i),                    // nid of to-be-initialized register
          get_register_name(i % NUMBEROFREGISTERS)); // register name as comment
      else if (i < UP_FLOW + NUMBEROFREGISTERS)
        printf3("%d init 2 %d 50 %s ; initial value is 4GB of memory addresses\n",
          (char*) (reg_nids * 2 + i),                // nid of this line
          (char*) (reg_nids + i),                    // nid of to-be-initialized register
          get_register_name(i % NUMBEROFREGISTERS)); // register name as comment

      i = i + 1;
    }

  print("\n; 64-bit program counter encoded in Boolean flags\n\n");

  // 3 more digits to accommodate binary starting at entry point and stack with
  // 100*4 lines per 32-bit instruction (pc increments by 4) and
  // 100*8 lines per 64-bit machine word in data segment
  pcs_nid = ten_to_the_power_of(
    log_ten(entry_point + binary_length +
      (VIRTUALMEMORYSIZE - *(get_regs(current_context) + REG_SP))) + 3);

  pc = get_pc(current_context);
  pt = get_pt(current_context);

  while (pc < entry_point + code_length) {
    current_nid = pc_nid(pcs_nid, pc);

    // pc flag of current instruction
    printf1("%d state 1\n", (char*) current_nid);

    if (pc == entry_point)
      // set pc here by initializing pc flag of instruction at address 0 to true
      printf2("%d init 1 %d 11 ; initial program counter\n",
        (char*) (current_nid + 1), // nid of this line
        (char*) current_nid);      // nid of pc flag of current instruction
    else
      // initialize all other pc flags to false
      printf2("%d init 1 %d 10\n",
        (char*) (current_nid + 1), // nid of this line
        (char*) current_nid);      // nid of pc flag of current instruction

    pc = pc + INSTRUCTIONSIZE;
  }

  current_nid = pc_nid(pcs_nid, pc);

  printf1("\n%d state 3 boot-loader\n", (char*) current_nid);

  loader_nid    = current_nid;
  data_flow_nid = current_nid;
  current_nid   = current_nid + 1;

  print("\n; data segment\n\n");

  // assert: pc == entry_point + code_length

  while (pc < VIRTUALMEMORYSIZE) {
    if (pc == get_original_break(current_context)) {
      // assert: stack pointer < VIRTUALMEMORYSIZE
      pc = *(get_regs(current_context) + REG_SP);

      print("\n; stack\n\n");
    }

    // address in data segment or stack
    printf3("%d constd 2 %d ; %x\n",
      (char*) current_nid,     // nid of this line
      (char*) pc, (char*) pc); // address of current machine word

    machine_word = load_virtual_memory(pt, pc);

    if (machine_word == 0) {
      // load machine word == 0
      printf3("%d write 3 %d %d 20\n",
        (char*) (current_nid + 1), // nid of this line
        (char*) data_flow_nid,     // nid of most recent update to data segment
        (char*) current_nid);      // nid of address of current machine word

      data_flow_nid = current_nid + 1;
    } else {
      // load non-zero machine word
      printf3("%d constd 2 %d ; %x\n",
        (char*) (current_nid + 1),                   // nid of this line
        (char*) machine_word, (char*) machine_word); // value of machine word at current address
      printf4("%d write 3 %d %d %d\n",
        (char*) (current_nid + 2),  // nid of this line
        (char*) data_flow_nid,      // nid of most recent update to data segment
        (char*) current_nid,        // nid of address of current machine word
        (char*) (current_nid + 1)); // nid of value of machine word at current address

      data_flow_nid = current_nid + 2;
    }

    pc = pc + REGISTERSIZE;

    if (current_nid == loader_nid + 1)
      current_nid = loader_nid + REGISTERSIZE;
    else
      current_nid = current_nid + REGISTERSIZE;
  }

  print("\n; 64-bit memory\n\n");

  memory_nid = pcs_nid * 2;

  current_nid = memory_nid;

  printf1("%d state 3 memory ; data segment, heap, stack\n", (char*) current_nid);
  printf3("%d init 3 %d %d ; loading data segment and stack into memory\n",
    (char*) (current_nid + 1), // nid of this line
    (char*) current_nid,       // nid of memory
    (char*) data_flow_nid);    // nid of most recent update to data segment

  memory_flow_nid = current_nid;

  if (check_block_access) {
    current_nid = current_nid + 2;

    lo_memory_nid = current_nid;

    printf1("\n%d state 3 lower-bounds ; for checking address validity\n", (char*) current_nid);
    printf2("%d init 3 %d 30 ; initializing lower bounds to end of code segment\n",
      (char*) (current_nid + 1), // nid of this line
      (char*) current_nid);      // nid of lower bounds on addresses in memory

    lo_memory_flow_nid = current_nid;

    current_nid = current_nid + 2;

    up_memory_nid = current_nid;

    printf1("\n%d state 3 upper-bounds ; for checking address validity\n", (char*) current_nid);
    printf2("%d init 3 %d 50 ; initializing upper bounds to 4GB of memory addresses\n",
      (char*) (current_nid + 1), // nid of this line
      (char*) current_nid);      // nid of upper bounds on addresses in memory

    up_memory_flow_nid = current_nid;
  }

  print("\n; data flow\n\n");

  code_nid = pcs_nid * 3;

  control_in  = zalloc(code_length / INSTRUCTIONSIZE * SIZEOFUINT64);
  call_return = zalloc(code_length / INSTRUCTIONSIZE * SIZEOFUINT64);

  current_callee   = entry_point;
  estimated_return = entry_point;

  pc = get_pc(current_context);

  while (pc < entry_point + code_length) {
    current_nid = pc_nid(code_nid, pc);

    fetch();
    decode();

    translate_to_model();

    pc = pc + INSTRUCTIONSIZE;
  }

  print("\n; syscalls\n\n");

  current_nid = pcs_nid * 4;

  model_syscalls();

  print("\n; control flow\n\n");

  control_nid = pcs_nid * 5;

  pc = get_pc(current_context);

  while (pc < entry_point + code_length) {
    current_nid = pc_nid(control_nid, pc);

    in_edge = (uint64_t*) *(control_in + (pc - entry_point) / INSTRUCTIONSIZE);

    // nid of 1-bit 0
    control_flow_nid = 10;

    while (in_edge != (uint64_t*) 0) {
      from_instruction = *(in_edge + 1);
      from_address     = *(in_edge + 2);
      condition_nid    = *(in_edge + 3);

      if (from_instruction == BEQ) {
        // is beq active and its condition true or false?
        printf5("%d and 1 %d %d ; beq %d[%x]",
          (char*) current_nid,                         // nid of this line
          (char*) pc_nid(pcs_nid, from_address),       // nid of pc flag of instruction proceeding here
          (char*) condition_nid,                       // nid of true or false beq condition
          (char*) from_address, (char*) from_address); // address of instruction proceeding here
        print_code_line_number_for_instruction(from_address, entry_point);println();

        current_nid = current_nid + 1;

        // activate this instruction if beq is active and its condition is true (false)
        control_flow_nid = control_flow(current_nid - 1, control_flow_nid);
      } else if (from_instruction == JALR) {
        jalr_address = *(call_return + (from_address - entry_point) / INSTRUCTIONSIZE);

        if (jalr_address != 0) {
          // is value of $ra register with LSB reset equal to address of this instruction?
          printf3("%d not 2 21 ; jalr %d[%x]",
            (char*) current_nid,                         // nid of this line
            (char*) jalr_address, (char*) jalr_address); // address of instruction proceeding here
          print_code_line_number_for_instruction(jalr_address, entry_point);println();
          printf3("%d and 2 %d %d\n",
            (char*) (current_nid + 1),   // nid of this line
            (char*) (reg_nids + REG_RA), // nid of current value of $ra register
            (char*) current_nid);        // nid of not 1
          printf3("%d eq 1 %d %d\n",
            (char*) (current_nid + 2), // nid of this line
            (char*) (current_nid + 1), // nid of current value of $ra register with LSB reset
            (char*) condition_nid);    // nid of address of this instruction (generated by jal)

          // is jalr active and the previous condition true or false?
          printf3("%d and 1 %d %d\n",
            (char*) (current_nid + 3),             // nid of this line
            (char*) pc_nid(pcs_nid, jalr_address), // nid of pc flag of instruction proceeding here
            (char*) (current_nid + 2));            // nid of return address condition

          current_nid = current_nid + 4;

          // activate this instruction if jalr is active and its condition is true (false)
          control_flow_nid = control_flow(current_nid - 1, control_flow_nid);
        } else {
          // no jalr returning from jal found

          printf2("; exit ecall wrapper call or runaway jal %d[%x]", (char*) from_address, (char*) from_address);
          print_code_line_number_for_instruction(from_address, entry_point);println();

          // this instruction may stay deactivated if there is no more in-edges
        }
      } else if (from_instruction == ECALL) {
        printf3("%d state 1 ; kernel-mode pc flag of ecall %d[%x]",
          (char*) current_nid,                         // nid of this line
          (char*) from_address, (char*) from_address); // address of instruction proceeding here
        print_code_line_number_for_instruction(from_address, entry_point);println();

        printf2("%d init 1 %d 10 ; ecall is initially inactive\n",
          (char*) (current_nid + 1), // nid of this line
          (char*) current_nid);      // nid of kernel-mode pc flag of ecall

        printf3("%d ite 1 %d 60 %d ; activate ecall and keep active while in kernel mode\n",
          (char*) (current_nid + 2),              // nid of this line
          (char*) current_nid,                    // nid of kernel-mode pc flag of ecall
          (char*) pc_nid(pcs_nid, from_address)); // nid of pc flag of instruction proceeding here

        printf3("%d next 1 %d %d ; keep ecall active while in kernel mode\n",
          (char*) (current_nid + 3),  // nid of this line
          (char*) current_nid,        // nid of kernel-mode pc flag of ecall
          (char*) (current_nid + 2)); // nid of previous line

        printf2("%d and 1 %d 62 ; ecall is active but not in kernel mode anymore\n",
          (char*) (current_nid + 4), // nid of this line
          (char*) current_nid);      // nid of kernel-mode pc flag of ecall

        current_nid = current_nid + 5;

        // activate this instruction if ecall is active but not in kernel mode anymore
        control_flow_nid = control_flow(current_nid - 1, control_flow_nid);
      } else {
        if (from_instruction == JAL) print("; jal "); else print("; ");
        printf2("%d[%x]", (char*) from_address, (char*) from_address);
        print_code_line_number_for_instruction(from_address, entry_point);println();

        // activate this instruction if instruction proceeding here is active
        control_flow_nid = control_flow(pc_nid(pcs_nid, from_address), control_flow_nid);
      }

      in_edge = (uint64_t*) *in_edge;
    }

    // update pc flag of current instruction
    printf5("%d next 1 %d %d ; ->%d[%x]",
      (char*) current_nid,         // nid of this line
      (char*) pc_nid(pcs_nid, pc), // nid of pc flag of current instruction
      (char*) control_flow_nid,    // nid of most recently processed in-edge
      (char*) pc, (char*) pc);     // address of current instruction
    print_code_line_number_for_instruction(pc, entry_point);
    if (control_flow_nid == 10)
      if (pc > entry_point)
        // TODO: warn here about unreachable code
        print(" (unreachable)");
    println();

    if (current_nid >= pc_nid(control_nid, pc) + 400) {
      // the instruction at pc is reachable by too many other instructions

      //report the error on the console
      output_fd = 1;

      printf2("%s: too many in-edges at instruction address %x detected\n", selfie_name, (char*) pc);

      return EXITCODE_MODELCHECKINGERROR;
    }

    pc = pc + INSTRUCTIONSIZE;
  }

  print("\n; updating registers\n");

  current_nid = pcs_nid * 6;

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    if (i == 0)
      println();
    else
      printf5("%d next 2 %d %d %s ; register $%d\n",
        (char*) (current_nid + i),    // nid of this line
        (char*) (reg_nids + i),       // nid of register
        (char*) *(reg_flow_nids + i), // nid of most recent update to register
        get_register_name(i),         // register name
        (char*) i);                   // register index as comment

    i = i + 1;
  }

  if (check_block_access)
    while (i < 3 * NUMBEROFREGISTERS) {
      if (i % NUMBEROFREGISTERS == 0)
        println();
      else {
        printf3("%d next 2 %d %d ",
          (char*) (current_nid + i),     // nid of this line
          (char*) (reg_nids + i),        // nid of register
          (char*) *(reg_flow_nids + i)); // nid of most recent update to register

        if (i < LO_FLOW + NUMBEROFREGISTERS)
          printf2("lo-%s ; lower bound on $%d\n",
            get_register_name(i % NUMBEROFREGISTERS), // register name
            (char*) (i % NUMBEROFREGISTERS));         // register index as comment
        else if (i < UP_FLOW + NUMBEROFREGISTERS)
          printf2("up-%s ; upper bound on $%d\n",
            get_register_name(i % NUMBEROFREGISTERS), // register name
            (char*) (i % NUMBEROFREGISTERS));         // register index as comment
      }

      i = i + 1;
    }

  print("\n; updating memory\n\n");

  current_nid = pcs_nid * 7;

  printf3("%d next 3 %d %d memory\n",
      (char*) current_nid,      // nid of this line
      (char*) memory_nid,       // nid of memory
      (char*) memory_flow_nid); // nid of most recent write to memory

  if (check_block_access) {
    printf3("%d next 3 %d %d lower-bounds\n",
        (char*) (current_nid + 1),   // nid of this line
        (char*) lo_memory_nid,       // nid of lower bounds on addresses in memory
        (char*) lo_memory_flow_nid); // nid of most recent write to lower bounds on addresses in memory
    printf3("%d next 3 %d %d upper-bounds\n",
        (char*) (current_nid + 2),   // nid of this line
        (char*) up_memory_nid,       // nid of upper bounds on addresses in memory
        (char*) up_memory_flow_nid); // nid of most recent write to upper bounds on addresses in memory
  }

  print("\n; checking division and remainder by zero\n\n");

  current_nid = pcs_nid * 8;

  check_division_by_zero(1, division_flow_nid);
  check_division_by_zero(0, remainder_flow_nid);

  print("; checking address validity\n\n");

  current_nid = pcs_nid * 9;

  check_address_validity(1, access_flow_start_nid, lo_flow_start_nid, up_flow_start_nid);
  check_address_validity(0, access_flow_end_nid, lo_flow_end_nid, up_flow_end_nid);

  // TODO: check validity of return addresses in jalr

  printf1("; end of BTOR2 %s\n", model_name);

  model_check = 0;

  output_name = (char*) 0;
  output_fd   = 1;

  printf3("%s: %d characters of model formulae written into %s\n", selfie_name,
    (char*) number_of_written_characters,
    model_name);

  return EXITCODE_NOERROR;
}

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

  printf2("p cnf %d %d\n", (char*) number_of_sat_variables, (char*) number_of_sat_clauses);

  clause = 0;

  while (clause < number_of_sat_clauses) {
    variable = 0;

    while (variable < number_of_sat_variables) {
      if (*(sat_instance + clause * 2 * number_of_sat_variables + 2 * variable) == TRUE) {
        print_integer(variable + 1);
        print(" ");
      } else if (*(sat_instance + clause * 2 * number_of_sat_variables + 2 * variable + 1) == TRUE) {
        print_integer(-(variable + 1));
        print(" ");
      }

      variable = variable + 1;
    }

    print("0\n");

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

void dimacs_word(char* word) {
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
        syntax_error_message("clause exceeds declared number of variables");

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
      syntax_error_message("instance has fewer clauses than declared");

      exit(EXITCODE_PARSERERROR);
    }

  if (symbol != SYM_EOF) {
    syntax_error_message("instance has more clauses than declared");

    exit(EXITCODE_PARSERERROR);
  }
}

void selfie_load_dimacs() {
  source_name = get_argument();

  printf2("%s: selfie loading SAT instance %s\n", selfie_name, source_name);

  // assert: source_name is mapped and not longer than MAX_FILENAME_LENGTH

  source_fd = sign_extend(open(source_name, O_RDONLY, 0), SYSCALL_BITWIDTH);

  if (signed_less_than(source_fd, 0)) {
    printf2("%s: could not open input file %s\n", selfie_name, source_name);

    exit(EXITCODE_IOERROR);
  }

  reset_scanner();

  // ignore all comments before problem
  dimacs_find_next_character(1);

  dimacs_get_symbol();

  dimacs_word("p");
  dimacs_word("cnf");

  number_of_sat_variables = dimacs_number();

  sat_assignment = (uint64_t*) zalloc(number_of_sat_variables * SIZEOFUINT64);

  number_of_sat_clauses = dimacs_number();

  sat_instance = (uint64_t*) zalloc(number_of_sat_clauses * 2 * number_of_sat_variables * SIZEOFUINT64);

  dimacs_get_instance();

  printf4("%s: %d clauses with %d declared variables loaded from %s\n", selfie_name,
    (char*) number_of_sat_clauses,
    (char*) number_of_sat_variables,
    source_name);

  dimacs_name = source_name;
}

void selfie_sat() {
  uint64_t variable;

  selfie_load_dimacs();

  if (dimacs_name == (char*) 0) {
    printf1("%s: nothing to SAT solve\n", selfie_name);

    return;
  }

  selfie_print_dimacs();

  if (babysat(0) == SAT) {
    printf2("%s: %s is satisfiable with ", selfie_name, dimacs_name);

    variable = 0;

    while (variable < number_of_sat_variables) {
      if (*(sat_assignment + variable) == FALSE)
        printf1("-%d ", (char*) (variable + 1));
      else
        printf1("%d ", (char*) (variable + 1));

      variable = variable + 1;
    }
  } else
    printf2("%s: %s is unsatisfiable", selfie_name, dimacs_name);

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

char* peek_argument(uint64_t lookahead) {
  if (number_of_remaining_arguments() > lookahead)
    return (char*) *(selfie_argv + lookahead);
  else
    return (char*) 0;
}

char* get_argument() {
  char* argument;

  argument = peek_argument(0);

  if (number_of_remaining_arguments() > 0) {
    selfie_argc = selfie_argc - 1;
    selfie_argv = selfie_argv + 1;
  }

  return argument;
}

void set_argument(char* argv) {
  *selfie_argv = (uint64_t) argv;
}

void print_usage() {
  printf3("%s: usage: selfie { %s } [ %s ]\n", selfie_name,
    "-c { source } | -o binary | [ -s | -S ] assembly | -l binary | -sat dimacs",
    "( -m | -d | -r | -y | -min | -mob | -se | -mc ) 0-4096 ... ");
}

uint64_t selfie() {
  char* option;

  if (number_of_remaining_arguments() == 0)
    print_usage();
  else {
    init_scanner();
    init_register();
    init_interpreter();

    while (number_of_remaining_arguments() > 0) {
      option = get_argument();

      if (string_compare(option, "-c"))
        selfie_compile();
      else if (number_of_remaining_arguments() == 0) {
        // remaining options have at least one argument
        print_usage();

        return EXITCODE_BADARGUMENTS;
      } else if (string_compare(option, "-o"))
        selfie_output();
      else if (string_compare(option, "-s"))
        selfie_disassemble(0);
      else if (string_compare(option, "-S"))
        selfie_disassemble(1);
      else if (string_compare(option, "-l"))
        selfie_load();
      else if (string_compare(option, "-sat"))
        selfie_sat();
      else if (string_compare(option, "-m"))
        return selfie_run(MIPSTER);
      else if (string_compare(option, "-d"))
        return selfie_run(DIPSTER);
      else if (string_compare(option, "-r"))
        return selfie_run(RIPSTER);
      else if (string_compare(option, "-y"))
        return selfie_run(HYPSTER);
      else if (string_compare(option, "-min"))
        return selfie_run(MINSTER);
      else if (string_compare(option, "-mob"))
        return selfie_run(MOBSTER);
      else if (string_compare(option, "-se"))
        return selfie_run(MONSTER);
      else if (string_compare(option, "-mc"))
        return selfie_model_generate();
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