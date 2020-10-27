/*
Copyright (c) 2015-2020, the Selfie Project authors. All rights reserved.
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
   that is, starc, mipster, and hypster itself, and
5. a tiny C* library called libcstar utilized by selfie.

Selfie is implemented in a single (!) file and kept minimal for simplicity.
There is also a simple in-memory linker, a RISC-U disassembler, a garbage
collector, a profiler, and a debugger with replay as well as minimal
operating system support in the form of RISC-V system calls built into
the emulator and hypervisor. The garbage collector is conservative and
may operate as library in the same address space as the mutator and
as part of the emulator in the address space of the kernel.

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
The design of the hypervisor is inspired by microkernels of Professor
Jochen Liedtke from University of Karlsruhe. The garbage collector
is inspired by the conservative garbage collector of Hans Boehm.
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

// selfie bootstraps void* to uint64_t* and unsigned to uint64_t!
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
char*    itoa(uint64_t n, char* s, uint64_t b, uint64_t d, uint64_t a);

uint64_t fixed_point_ratio(uint64_t a, uint64_t b, uint64_t f);
uint64_t fixed_point_percentage(uint64_t r, uint64_t f);

void put_character(uint64_t c);

void print(char* s);
void println();

void print_character(uint64_t c);
void print_string(char* s);
void print_unsigned_integer(uint64_t n);
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
void printf7(char* s, char* a1, char* a2, char* a3, char* a4, char* a5, char* a6, char* a7);

void sprintf1(char* b, char* s, char* a1);
void sprintf2(char* b, char* s, char* a1, char* a2);
void sprintf3(char* b, char* s, char* a1, char* a2, char* a3);
void sprintf4(char* b, char* s, char* a1, char* a2, char* a3, char* a4);

uint64_t round_up(uint64_t n, uint64_t m);

void zero_memory(uint64_t* memory, uint64_t size);

uint64_t* smalloc(uint64_t size); // use this to allocate memory, not malloc
uint64_t* zmalloc(uint64_t size); // use this to allocate zeroed memory

// ------------------------ GLOBAL CONSTANTS -----------------------

char* SELFIE_URL = (char*) 0;

uint64_t WORDSIZE       = 8;  // (double) word size in bytes
uint64_t WORDSIZEINBITS = 64; // 8 * WORDSIZE

uint64_t SINGLEWORDSIZEINBITS = 32;

uint64_t SIZEOFUINT64     = 8; // must be the same as WORDSIZE
uint64_t SIZEOFUINT64STAR = 8; // must be the same as WORDSIZE

uint64_t* power_of_two_table;

uint64_t UINT64_MAX; // maximum numerical value of an unsigned 64-bit integer

uint64_t INT64_MAX; // maximum numerical value of a signed 64-bit integer
uint64_t INT64_MIN; // minimum numerical value of a signed 64-bit integer

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

  // powers of two table with WORDSIZEINBITS entries for 2^0 to 2^(WORDSIZEINBITS - 1)
  power_of_two_table = smalloc(WORDSIZEINBITS * SIZEOFUINT64);

  *power_of_two_table = 1; // 2^0 == 1

  i = 1;

  while (i < WORDSIZEINBITS) {
    // compute powers of two incrementally using this recurrence relation
    *(power_of_two_table + i) = *(power_of_two_table + (i - 1)) * 2;

    i = i + 1;
  }

  // compute 64-bit unsigned integer range using signed integer arithmetic
  UINT64_MAX = -1;

  // compute 64-bit signed integer range using unsigned integer arithmetic
  INT64_MAX = two_to_the_power_of(WORDSIZEINBITS - 1) - 1;
  INT64_MIN = INT64_MAX + 1;

  // allocate and touch to make sure memory is mapped for read calls
  character_buffer  = smalloc(SIZEOFUINT64);
  *character_buffer = 0;

  // accommodate at least WORDSIZEINBITS numbers for itoa, no mapping needed
  integer_buffer = string_alloc(WORDSIZEINBITS);

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
uint64_t SYM_DIVISION     = 19; // /
uint64_t SYM_REMAINDER    = 20; // %
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

uint64_t literal = 0; // numerical value of most recently scanned integer or character

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
  *(SYMBOLS + SYM_DIVISION)     = (uint64_t) "/";
  *(SYMBOLS + SYM_REMAINDER)    = (uint64_t) "%";
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
// |  7 | scope   | REG_GP (global), REG_S0 (local)
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
  global_symbol_table  = (uint64_t*) zmalloc(HASH_TABLE_SIZE * SIZEOFUINT64STAR);
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
uint64_t is_int_or_char_literal();
uint64_t is_mult_or_div_or_rem();
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

void      load_small_and_medium_integer(uint64_t reg, uint64_t value);
uint64_t* get_variable_or_big_int(char* variable, uint64_t class);
void      load_upper_base_address(uint64_t* entry);
uint64_t  load_variable_or_big_int(char* variable, uint64_t class);
void      load_integer(uint64_t value);
void      load_string(char* string);

uint64_t procedure_call(uint64_t* entry, char* procedure);

void procedure_prologue(uint64_t number_of_local_variable_bytes);
void procedure_epilogue(uint64_t number_of_parameter_bytes);

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

// bootstrapping binary

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

uint64_t is_stack_register(uint64_t reg);
uint64_t is_system_register(uint64_t reg);
uint64_t is_argument_register(uint64_t reg);
uint64_t is_temporary_register(uint64_t reg);

uint64_t read_register(uint64_t reg);
void     write_register(uint64_t reg);

void update_register_counters();

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
uint64_t REG_S0  = 8;
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
  *(REGISTERS + REG_S0)  = (uint64_t) "s0"; // used to be fp
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
uint64_t get_total_percentage_of_nops();

void print_instruction_counter(uint64_t total, uint64_t counter, char* mnemonics);
void print_instruction_counter_with_nops(uint64_t total, uint64_t counter, uint64_t nops, char* mnemonics);

void print_instruction_counters();

uint64_t load_instruction(uint64_t baddr);
void     store_instruction(uint64_t baddr, uint64_t instruction);

uint64_t load_data(uint64_t baddr);
void     store_data(uint64_t baddr, uint64_t data);

void emit_instruction(uint64_t instruction);

uint64_t encode_nop();
void     emit_nop();

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

void selfie_output(char* filename);

uint64_t* touch(uint64_t* memory, uint64_t length);

void selfie_load();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t MAX_BINARY_LENGTH = 524288; // 512KB = MAX_CODE_LENGTH + MAX_DATA_LENGTH

uint64_t MAX_CODE_LENGTH = 491520; // 480KB
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
uint64_t down_load_string(uint64_t* context, uint64_t vstring, char* s);
void     implement_openat(uint64_t* context);

void     emit_malloc();
uint64_t try_brk(uint64_t* context, uint64_t new_program_break);
void     implement_brk(uint64_t* context);

uint64_t is_boot_level_zero();

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

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t sc_brk = 0; // syscall counter

// -----------------------------------------------------------------
// ------------------------ HYPSTER SYSCALL ------------------------
// -----------------------------------------------------------------

void      emit_switch();
uint64_t* do_switch(uint64_t* from_context, uint64_t* to_context, uint64_t timeout);
void      implement_switch();
uint64_t* mipster_switch(uint64_t* to_context, uint64_t timeout);
uint64_t* hypster_switch(uint64_t* to_context, uint64_t timeout);

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

void reset_memory_counters();

uint64_t load_physical_memory(uint64_t* paddr);
void     store_physical_memory(uint64_t* paddr, uint64_t data);

uint64_t get_root_PDE_offset(uint64_t page);
uint64_t get_leaf_PTE_offset(uint64_t page);

uint64_t* get_PTE_address_for_page(uint64_t* parent_table, uint64_t* table, uint64_t page);
uint64_t  get_frame_for_page(uint64_t* table, uint64_t page);

void set_PTE_for_page(uint64_t* table, uint64_t page, uint64_t frame);

uint64_t is_page_mapped(uint64_t* table, uint64_t page);

uint64_t is_valid_virtual_address(uint64_t vaddr);
uint64_t get_page_of_virtual_address(uint64_t vaddr);
uint64_t get_virtual_address_of_page_start(uint64_t page);
uint64_t is_virtual_address_mapped(uint64_t* table, uint64_t vaddr);

uint64_t* tlb(uint64_t* table, uint64_t vaddr);

uint64_t load_virtual_memory(uint64_t* table, uint64_t vaddr);
void     store_virtual_memory(uint64_t* table, uint64_t vaddr, uint64_t data);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t debug_tlb = 0;

uint64_t MEGABYTE = 1048576; // 1MB

uint64_t VIRTUALMEMORYSIZE = 4294967296; // 4GB of virtual memory

uint64_t PAGESIZE = 4096; // 4KB virtual pages

uint64_t NUMBEROFPAGES = 1048576; // VIRTUALMEMORYSIZE / PAGESIZE

uint64_t NUMBEROFLEAFPTES = 512; // number of leaf page table entries == PAGESIZE / SIZEOFUINT64STAR

uint64_t PAGETABLETREE = 1; // two-level page table is default

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t total_page_frame_memory = 0; // total amount of memory available for frames

uint64_t mc_brk = 0; // memory counter for brk syscall

uint64_t mc_mapped_heap = 0; // memory counter for mapped heap

// ------------------------- INITIALIZATION ------------------------

void init_memory(uint64_t megabytes) {
  if (megabytes > 4096)
    megabytes = 4096;

  total_page_frame_memory = megabytes * MEGABYTE;
}

// -----------------------------------------------------------------
// ---------------------- GARBAGE COLLECTOR ------------------------
// -----------------------------------------------------------------

// bootstrapped to actual functions during compilation ...
uint64_t fetch_stack_pointer()     { return 0; } // indicate that gc is unavailable
uint64_t fetch_global_pointer()    { return 0; }
uint64_t fetch_data_segment_size() { return 0; }

// ... here, not available on boot level 0 - only for compilation
void emit_fetch_stack_pointer();
void emit_fetch_global_pointer();
void emit_fetch_data_segment_size_interface();
void emit_fetch_data_segment_size_implementation(uint64_t fetch_dss_code_location);

void implement_gc_brk(uint64_t* context);

uint64_t is_gc_library(uint64_t* context);

// metadata entry:
// +----+---------+
// |  0 | next    | pointer to next entry
// |  1 | memory  | pointer to allocated memory
// |  2 | size    | size of allocated memory (in bytes!)
// |  3 | markbit | markbit indicating reachability of allocated memory
// +----+---------+

uint64_t* allocate_metadata(uint64_t* context);

uint64_t* get_metadata_next(uint64_t* entry)    { return (uint64_t*) *entry; }
uint64_t* get_metadata_memory(uint64_t* entry)  { return (uint64_t*) *(entry + 1); }
uint64_t  get_metadata_size(uint64_t* entry)    { return             *(entry + 2); }
uint64_t  get_metadata_markbit(uint64_t* entry) { return             *(entry + 3); }

void set_metadata_next(uint64_t* entry, uint64_t* next)      { *entry       = (uint64_t) next; }
void set_metadata_memory(uint64_t* entry, uint64_t* memory)  { *(entry + 1) = (uint64_t) memory; }
void set_metadata_size(uint64_t* entry, uint64_t size)       { *(entry + 2) = size; }
void set_metadata_markbit(uint64_t* entry, uint64_t markbit) { *(entry + 3) = markbit; }

// getters and setters with different access in library/kernel

uint64_t  get_stack_start_gc(uint64_t* context);
uint64_t  get_data_seg_start_gc(uint64_t* context);
uint64_t  get_data_seg_end_gc(uint64_t* context);
uint64_t  get_heap_seg_start_gc(uint64_t* context);
uint64_t  get_heap_seg_end_gc(uint64_t* context);
uint64_t* get_used_list_head_gc(uint64_t* context);
uint64_t* get_free_list_head_gc(uint64_t* context);
uint64_t  get_gcs_in_period_gc(uint64_t* context);
uint64_t  get_gc_enabled_gc(uint64_t* context);

void set_data_and_heap_segments_gc(uint64_t* context);
void set_used_list_head_gc(uint64_t* context, uint64_t* used_list_head);
void set_free_list_head_gc(uint64_t* context, uint64_t* free_list_head);
void set_gcs_in_period_gc(uint64_t* context, uint64_t gcs);
void set_gc_enabled_gc(uint64_t* context);

void gc_init(uint64_t* context);

// this function performs first-fit retrieval of free memory in O(n) where n is memory size
// TODO: push O(n) down to O(1), e.g. using Boehm's chunk allocator, or even compact fit
// see https://github.com/cksystemsgroup/compact-fit
uint64_t* retrieve_from_free_list(uint64_t* context, uint64_t size);

uint64_t gc_load_memory(uint64_t* context, uint64_t address);
void     gc_store_memory(uint64_t* context, uint64_t address, uint64_t value);

void zero_object(uint64_t* context, uint64_t* metadata);

uint64_t* allocate_memory(uint64_t* context, uint64_t size);
uint64_t* reuse_memory(uint64_t* context, uint64_t size);
uint64_t* gc_malloc_implementation(uint64_t* context, uint64_t size);

// this function performs an O(n) list search where n is memory size
// TODO: push O(n) down to O(1), e.g. using Boehm's chunk allocator
uint64_t* find_metadata_of_word_at_address(uint64_t* context, uint64_t address);

void mark_object(uint64_t* context, uint64_t address);
void mark_segment(uint64_t* context, uint64_t segment_start, uint64_t segment_end);

// this function scans the heap from two roots (data segment and stack) in O(n^2)
// where n is memory size; checking if a value is a pointer takes O(n), see above
// TODO: push O(n^2) down to O(n)
void mark(uint64_t* context);

void free_object(uint64_t* context, uint64_t* metadata, uint64_t* prev_metadata);
void sweep(uint64_t* context);

void gc_collect(uint64_t* context);

void print_gc_profile(uint64_t* context);

void gc_arguments();

// ----------------------- LIBRARY FUNCTIONS -----------------------

uint64_t* gc_malloc(uint64_t size) {
    return gc_malloc_implementation((uint64_t*) 0, size);
}

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t GC_DISABLED = 0;
uint64_t GC_ENABLED  = 1;

uint64_t GC_ON = 0; // turn on kernel variant of gc, generate gc library code

uint64_t USE_GC_LIBRARY = 0; // use library variant of gc or not

uint64_t GC_PERIOD = 1000; // gc every so often

uint64_t GC_REUSE = 1; // reuse memory with freelist by default

uint64_t GC_METADATA_SIZE = 32; // SIZEOFUINT64 * 2 + SIZEOFUINT64STAR * 2

uint64_t GC_MARKBIT_UNREACHABLE = 0; // indicating that an object is not reachable
uint64_t GC_MARKBIT_REACHABLE   = 1; // indicating that an object is reachable by root or other reachable object

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t gc_data_seg_start = 0;
uint64_t gc_data_seg_end   = 0;
uint64_t gc_heap_seg_start = 0;
uint64_t gc_heap_seg_end   = 0;

uint64_t* gc_used_list = (uint64_t*) 0; // pointer to used-list head
uint64_t* gc_free_list = (uint64_t*) 0; // pointer to free-list head

uint64_t gc_num_gcs_in_period = 0;

uint64_t gc_num_mallocated     = 0;
uint64_t gc_num_gced_mallocs   = 0;
uint64_t gc_num_ungced_mallocs = 0;
uint64_t gc_num_reused_mallocs = 0;
uint64_t gc_num_collects       = 0;
uint64_t gc_mem_mallocated     = 0;
uint64_t gc_mem_objects        = 0;
uint64_t gc_mem_metadata       = 0;
uint64_t gc_mem_reused         = 0;
uint64_t gc_mem_collected      = 0;

// ------------------------- INITIALIZATION ------------------------

void reset_gc_counters() {
  gc_num_mallocated     = 0;
  gc_num_gced_mallocs   = 0;
  gc_num_ungced_mallocs = 0;
  gc_num_reused_mallocs = 0;
  gc_num_collects       = 0;
  gc_mem_mallocated     = 0;
  gc_mem_objects        = 0;
  gc_mem_metadata       = 0;
  gc_mem_reused         = 0;
  gc_mem_collected      = 0;
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

void print_code_line_number_for_instruction(uint64_t address, uint64_t offset);
void print_code_context_for_instruction(uint64_t address);

void print_lui();
void print_lui_before();
void print_lui_after();
void record_lui_addi_add_sub_mul_divu_remu_sltu_jal_jalr();
void do_lui();
void undo_lui_addi_add_sub_mul_divu_remu_sltu_ld_jal_jalr();

void print_addi();
void print_addi_before();
void print_addi_add_sub_mul_divu_remu_sltu_after();
void do_addi();

void print_add_sub_mul_divu_remu_sltu(char *mnemonics);
void print_add_sub_mul_divu_remu_sltu_before();

void do_add();
void do_sub();
void do_mul();
void do_divu();
void do_remu();

void do_sltu();

void     print_ld();
void     print_ld_before();
void     print_ld_after(uint64_t vaddr);
void     record_ld();
uint64_t do_ld();

void     print_sd();
void     print_sd_before();
void     print_sd_after(uint64_t vaddr);
void     record_sd();
uint64_t do_sd();
void     undo_sd();

void print_beq();
void print_beq_before();
void print_beq_after();
void record_beq();
void do_beq();

void print_jal();
void print_jal_before();
void print_jal_jalr_after();
void do_jal();

void print_jalr();
void print_jalr_before();
void do_jalr();

void print_ecall();
void record_ecall();
void do_ecall();
void undo_ecall();

void print_data_line_number();
void print_data_context(uint64_t data);
void print_data(uint64_t data);

// -----------------------------------------------------------------
// -------------------------- DISASSEMBLER -------------------------
// -----------------------------------------------------------------

void print_instruction();

void selfie_disassemble(uint64_t verbose);

// ------------------------ GLOBAL VARIABLES -----------------------

char*    assembly_name = (char*) 0; // name of assembly file
uint64_t assembly_fd   = 0;         // file descriptor of open assembly file

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
  pcs    = zmalloc(MAX_REPLAY_LENGTH * SIZEOFUINT64);
  values = zmalloc(MAX_REPLAY_LENGTH * SIZEOFUINT64);
}

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void init_interpreter();
void reset_interpreter();

void reset_nop_counters();
void reset_profiler();

void print_register_hexadecimal(uint64_t reg);
void print_register_octal(uint64_t reg);
void print_register_value(uint64_t reg);

void print_exception(uint64_t exception, uint64_t fault);
void throw_exception(uint64_t exception, uint64_t fault);

void fetch();
void decode();
void execute();

void execute_record();
void execute_undo();
void execute_debug();

void interrupt();

void run_until_exception();

uint64_t instruction_with_max_counter(uint64_t* counters, uint64_t max);
uint64_t print_per_instruction_counter(uint64_t total, uint64_t* counters, uint64_t max);
void     print_per_instruction_profile(char* message, uint64_t total, uint64_t* counters);

void print_access_profile(char* message, char* padding, uint64_t reads, uint64_t writes);
void print_per_register_profile(uint64_t reg);

void print_register_memory_profile();

void print_profile(uint64_t* context);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t INSTRUCTIONSIZE = 4; // in bytes

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

uint64_t EXCEPTION_NOEXCEPTION           = 0;
uint64_t EXCEPTION_PAGEFAULT             = 1;
uint64_t EXCEPTION_SEGMENTATIONFAULT     = 2;
uint64_t EXCEPTION_SYSCALL               = 3;
uint64_t EXCEPTION_TIMER                 = 4;
uint64_t EXCEPTION_DIVISIONBYZERO        = 5;
uint64_t EXCEPTION_INVALIDADDRESS        = 6;
uint64_t EXCEPTION_UNKNOWNINSTRUCTION    = 7;
uint64_t EXCEPTION_UNINITIALIZEDREGISTER = 8;
uint64_t EXCEPTION_SYMBOLICSCHEDULE      = 9; // for symbolic execution

uint64_t* EXCEPTIONS; // strings representing exceptions

uint64_t debug_exception = 0;

uint64_t run = 0; // flag for running code

uint64_t debug = 0; // // flag for recording and debugging code

uint64_t debug_syscalls = 0; // flag for debugging syscalls

uint64_t record = 0; // flag for recording code execution
uint64_t redo   = 0; // flag for redoing code execution

uint64_t disassemble_verbose = 0; // flag for disassembling code in more detail

uint64_t symbolic = 0; // flag for symbolically executing code
uint64_t model    = 0; // flag for modeling code

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

// effective nop counters

uint64_t nopc_lui  = 0;
uint64_t nopc_addi = 0;
uint64_t nopc_add  = 0;
uint64_t nopc_sub  = 0;
uint64_t nopc_mul  = 0;
uint64_t nopc_divu = 0;
uint64_t nopc_remu = 0;
uint64_t nopc_sltu = 0;
uint64_t nopc_ld   = 0;
uint64_t nopc_sd   = 0;
uint64_t nopc_beq  = 0;
uint64_t nopc_jal  = 0;
uint64_t nopc_jalr = 0;

// source profile

uint64_t  calls               = 0;             // total number of executed procedure calls
uint64_t* calls_per_procedure = (uint64_t*) 0; // number of executed calls of each procedure

uint64_t  iterations          = 0;             // total number of executed loop iterations
uint64_t* iterations_per_loop = (uint64_t*) 0; // number of executed iterations of each loop

uint64_t* loads_per_instruction  = (uint64_t*) 0; // number of executed loads per load instruction
uint64_t* stores_per_instruction = (uint64_t*) 0; // number of executed stores per store instruction

// register access counters

uint64_t* reads_per_register  = (uint64_t*) 0;
uint64_t* writes_per_register = (uint64_t*) 0;

uint64_t stack_register_reads  = 0;
uint64_t stack_register_writes = 0;

uint64_t argument_register_reads  = 0;
uint64_t argument_register_writes = 0;

uint64_t temporary_register_reads  = 0;
uint64_t temporary_register_writes = 0;

// segments access counters

uint64_t data_reads  = 0;
uint64_t data_writes = 0;

uint64_t stack_reads  = 0;
uint64_t stack_writes = 0;

uint64_t heap_reads  = 0;
uint64_t heap_writes = 0;

// ------------------------- INITIALIZATION ------------------------

void init_interpreter() {
  EXCEPTIONS = smalloc((EXCEPTION_SYMBOLICSCHEDULE + 1) * SIZEOFUINT64STAR);

  *(EXCEPTIONS + EXCEPTION_NOEXCEPTION)           = (uint64_t) "no exception";
  *(EXCEPTIONS + EXCEPTION_PAGEFAULT)             = (uint64_t) "page fault";
  *(EXCEPTIONS + EXCEPTION_SEGMENTATIONFAULT)     = (uint64_t) "segmentation fault";
  *(EXCEPTIONS + EXCEPTION_SYSCALL)               = (uint64_t) "syscall";
  *(EXCEPTIONS + EXCEPTION_TIMER)                 = (uint64_t) "timer interrupt";
  *(EXCEPTIONS + EXCEPTION_DIVISIONBYZERO)        = (uint64_t) "division by zero";
  *(EXCEPTIONS + EXCEPTION_INVALIDADDRESS)        = (uint64_t) "invalid address";
  *(EXCEPTIONS + EXCEPTION_UNKNOWNINSTRUCTION)    = (uint64_t) "unknown instruction";
  *(EXCEPTIONS + EXCEPTION_UNINITIALIZEDREGISTER) = (uint64_t) "uninitialized register";
  *(EXCEPTIONS + EXCEPTION_SYMBOLICSCHEDULE)      = (uint64_t) "symbolic schedule";
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

void reset_nop_counters() {
  nopc_lui  = 0;
  nopc_addi = 0;
  nopc_add  = 0;
  nopc_sub  = 0;
  nopc_mul  = 0;
  nopc_divu = 0;
  nopc_remu = 0;
  nopc_sltu = 0;
  nopc_ld   = 0;
  nopc_sd   = 0;
  nopc_beq  = 0;
  nopc_jal  = 0;
  nopc_jalr = 0;
}

void reset_source_profile() {
  calls               = 0;
  calls_per_procedure = zmalloc(code_length / INSTRUCTIONSIZE * SIZEOFUINT64);

  iterations          = 0;
  iterations_per_loop = zmalloc(code_length / INSTRUCTIONSIZE * SIZEOFUINT64);

  loads_per_instruction  = zmalloc(code_length / INSTRUCTIONSIZE * SIZEOFUINT64);
  stores_per_instruction = zmalloc(code_length / INSTRUCTIONSIZE * SIZEOFUINT64);
}

void reset_register_access_counters() {
  reads_per_register  = zmalloc(NUMBEROFREGISTERS * SIZEOFUINT64);
  writes_per_register = zmalloc(NUMBEROFREGISTERS * SIZEOFUINT64);

  // stack and frame pointer registers are initialized by boot loader
  *(writes_per_register + REG_SP) = 1;
  *(writes_per_register + REG_S0) = 1;

  // a6 register is written to by the kernel
  *(writes_per_register + REG_A6) = 1;

  stack_register_reads      = 0;
  stack_register_writes     = 0;
  argument_register_reads   = 0;
  argument_register_writes  = 0;
  temporary_register_reads  = 0;
  temporary_register_writes = 0;
}

void reset_segments_access_counters() {
  data_reads   = 0;
  data_writes  = 0;
  stack_reads  = 0;
  stack_writes = 0;
  heap_reads   = 0;
  heap_writes  = 0;
}

void reset_profiler() {
  reset_instruction_counters();
  reset_nop_counters();
  reset_memory_counters();
  reset_source_profile();
  reset_register_access_counters();
  reset_segments_access_counters();
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

void init_context(uint64_t* context, uint64_t* parent, uint64_t* vctxt);

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
// |  5 | lowest lo page  | lowest low uncached page (code, data, heap)
// |  6 | highest lo page | highest low uncached page (code, data, heap)
// |  7 | lowest hi page  | lowest high uncached page (stack)
// |  8 | highest hi page | highest high uncached page (stack)
// |  9 | code segment    | start of code segment
// | 10 | data segment    | end of code segment, start of data segment
// | 11 | heap segment    | end of data segment, start of heap segment
// | 12 | program break   | current program break
// | 13 | exception       | exception ID
// | 14 | faulting page   | faulting page
// | 15 | exit code       | exit code
// | 16 | parent          | context that created this context
// | 17 | virtual context | virtual context address
// | 18 | name            | binary name loaded into context
// +----+-----------------+
// | 19 | used-list head  | pointer to head of used list
// | 20 | free-list head  | pointer to head of free list
// | 21 | gcs counter     | number of gc runs in gc period
// | 22 | gc enabled      | flag indicating whether to use gc or not
// +----+-----------------+

// CAUTION: contexts are extended in the symbolic execution engine!

uint64_t* allocate_context() {
  return smalloc(9 * SIZEOFUINT64STAR + 14 * SIZEOFUINT64);
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
uint64_t code_seg_start(uint64_t* context)  { return (uint64_t) (context + 9); }
uint64_t data_seg_start(uint64_t* context)  { return (uint64_t) (context + 10); }
uint64_t heap_seg_start(uint64_t* context)  { return (uint64_t) (context + 11); }
uint64_t program_break(uint64_t* context)   { return (uint64_t) (context + 12); }
uint64_t exception(uint64_t* context)       { return (uint64_t) (context + 13); }
uint64_t fault(uint64_t* context)           { return (uint64_t) (context + 14); }
uint64_t exit_code(uint64_t* context)       { return (uint64_t) (context + 15); }
uint64_t parent(uint64_t* context)          { return (uint64_t) (context + 16); }
uint64_t virtual_context(uint64_t* context) { return (uint64_t) (context + 17); }
uint64_t name(uint64_t* context)            { return (uint64_t) (context + 18); }

uint64_t used_list_head(uint64_t* context)   { return (uint64_t) (context + 19); }
uint64_t free_list_head(uint64_t* context)   { return (uint64_t) (context + 20); }
uint64_t gcs_in_period(uint64_t* context)    { return (uint64_t) (context + 21); }
uint64_t use_gc_kernel(uint64_t* context)    { return (uint64_t) (context + 22); }

uint64_t* get_next_context(uint64_t* context)    { return (uint64_t*) *context; }
uint64_t* get_prev_context(uint64_t* context)    { return (uint64_t*) *(context + 1); }
uint64_t  get_pc(uint64_t* context)              { return             *(context + 2); }
uint64_t* get_regs(uint64_t* context)            { return (uint64_t*) *(context + 3); }
uint64_t* get_pt(uint64_t* context)              { return (uint64_t*) *(context + 4); }
uint64_t  get_lowest_lo_page(uint64_t* context)  { return             *(context + 5); }
uint64_t  get_highest_lo_page(uint64_t* context) { return             *(context + 6); }
uint64_t  get_lowest_hi_page(uint64_t* context)  { return             *(context + 7); }
uint64_t  get_highest_hi_page(uint64_t* context) { return             *(context + 8); }
uint64_t  get_code_seg_start(uint64_t* context)  { return             *(context + 9); }
uint64_t  get_data_seg_start(uint64_t* context)  { return             *(context + 10); }
uint64_t  get_heap_seg_start(uint64_t* context)  { return             *(context + 11); }
uint64_t  get_program_break(uint64_t* context)   { return             *(context + 12); }
uint64_t  get_exception(uint64_t* context)       { return             *(context + 13); }
uint64_t  get_fault(uint64_t* context)           { return             *(context + 14); }
uint64_t  get_exit_code(uint64_t* context)       { return             *(context + 15); }
uint64_t* get_parent(uint64_t* context)          { return (uint64_t*) *(context + 16); }
uint64_t* get_virtual_context(uint64_t* context) { return (uint64_t*) *(context + 17); }
char*     get_name(uint64_t* context)            { return (char*)     *(context + 18); }

uint64_t* get_used_list_head(uint64_t* context)   { return (uint64_t*) *(context + 19); }
uint64_t* get_free_list_head(uint64_t* context)   { return (uint64_t*) *(context + 20); }
uint64_t  get_gcs_in_period(uint64_t* context)    { return             *(context + 21); }
uint64_t  get_use_gc_kernel(uint64_t* context)    { return             *(context + 22); }

void set_next_context(uint64_t* context, uint64_t* next)      { *context        = (uint64_t) next; }
void set_prev_context(uint64_t* context, uint64_t* prev)      { *(context + 1)  = (uint64_t) prev; }
void set_pc(uint64_t* context, uint64_t pc)                   { *(context + 2)  = pc; }
void set_regs(uint64_t* context, uint64_t* regs)              { *(context + 3)  = (uint64_t) regs; }
void set_pt(uint64_t* context, uint64_t* pt)                  { *(context + 4)  = (uint64_t) pt; }
void set_lowest_lo_page(uint64_t* context, uint64_t page)     { *(context + 5)  = page; }
void set_highest_lo_page(uint64_t* context, uint64_t page)    { *(context + 6)  = page; }
void set_lowest_hi_page(uint64_t* context, uint64_t page)     { *(context + 7)  = page; }
void set_highest_hi_page(uint64_t* context, uint64_t page)    { *(context + 8)  = page; }
void set_code_seg_start(uint64_t* context, uint64_t start)    { *(context + 9)  = start; }
void set_data_seg_start(uint64_t* context, uint64_t start)    { *(context + 10) = start; }
void set_heap_seg_start(uint64_t* context, uint64_t start)    { *(context + 11) = start; }
void set_program_break(uint64_t* context, uint64_t brk)       { *(context + 12) = brk; }
void set_exception(uint64_t* context, uint64_t exception)     { *(context + 13) = exception; }
void set_fault(uint64_t* context, uint64_t page)              { *(context + 14) = page; }
void set_exit_code(uint64_t* context, uint64_t code)          { *(context + 15) = code; }
void set_parent(uint64_t* context, uint64_t* parent)          { *(context + 16) = (uint64_t) parent; }
void set_virtual_context(uint64_t* context, uint64_t* vctxt)  { *(context + 17) = (uint64_t) vctxt; }
void set_name(uint64_t* context, char* name)                  { *(context + 18) = (uint64_t) name; }

void set_used_list_head(uint64_t* context, uint64_t* used_list_head) { *(context + 19) = (uint64_t) used_list_head; }
void set_free_list_head(uint64_t* context, uint64_t* free_list_head) { *(context + 20) = (uint64_t) free_list_head; }
void set_gcs_in_period(uint64_t* context, uint64_t gcs)              { *(context + 21) = gcs; }
void set_use_gc_kernel(uint64_t* context, uint64_t use)              { *(context + 22) = use; }

// -----------------------------------------------------------------
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

void reset_microkernel();

uint64_t* create_context(uint64_t* parent, uint64_t* vctxt);
uint64_t* cache_context(uint64_t* vctxt);

void save_context(uint64_t* context);

uint64_t lowest_page(uint64_t page, uint64_t lo);
uint64_t highest_page(uint64_t page, uint64_t hi);
void     map_page(uint64_t* context, uint64_t page, uint64_t frame);

void restore_region(uint64_t* context, uint64_t* table, uint64_t* parent_table, uint64_t lo, uint64_t hi);
void restore_context(uint64_t* context);

uint64_t is_valid_code_address(uint64_t* context, uint64_t vaddr);
uint64_t is_valid_data_address(uint64_t* context, uint64_t vaddr);
uint64_t is_valid_stack_address(uint64_t* context, uint64_t vaddr);
uint64_t is_valid_heap_address(uint64_t* context, uint64_t vaddr);
uint64_t is_valid_data_stack_heap_address(uint64_t* context, uint64_t vaddr);

uint64_t is_valid_segment_read(uint64_t vaddr);
uint64_t is_valid_segment_write(uint64_t vaddr);

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
uint64_t handle_exception(uint64_t* context);

uint64_t mipster(uint64_t* to_context);
uint64_t hypster(uint64_t* to_context);

uint64_t mixter(uint64_t* to_context, uint64_t mix);

uint64_t minmob(uint64_t* to_context);
void     map_unmapped_pages(uint64_t* context);
uint64_t minster(uint64_t* to_context);
uint64_t mobster(uint64_t* to_context);

char* replace_extension(char* filename, char* extension);

void boot_loader(uint64_t* context);

uint64_t selfie_run(uint64_t machine);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t* MY_CONTEXT = (uint64_t*) 0;

uint64_t DONOTEXIT = 0;
uint64_t EXIT      = 1;
uint64_t SCHEDULE  = 2; // for symbolic execution

uint64_t EXITCODE_NOERROR                = 0;
uint64_t EXITCODE_NOARGUMENTS            = 11; // leaving 1-10 for apps
uint64_t EXITCODE_BADARGUMENTS           = 12;
uint64_t EXITCODE_MOREARGUMENTS          = 13;
uint64_t EXITCODE_IOERROR                = 14;
uint64_t EXITCODE_SCANNERERROR           = 15;
uint64_t EXITCODE_PARSERERROR            = 16;
uint64_t EXITCODE_COMPILERERROR          = 17;
uint64_t EXITCODE_OUTOFVIRTUALMEMORY     = 18;
uint64_t EXITCODE_OUTOFPHYSICALMEMORY    = 19;
uint64_t EXITCODE_DIVISIONBYZERO         = 20;
uint64_t EXITCODE_UNKNOWNINSTRUCTION     = 21;
uint64_t EXITCODE_UNKNOWNSYSCALL         = 22;
uint64_t EXITCODE_UNSUPPORTEDSYSCALL     = 23;
uint64_t EXITCODE_MULTIPLEEXCEPTIONERROR = 24;
uint64_t EXITCODE_SYMBOLICEXECUTIONERROR = 25; // for symbolic execution
uint64_t EXITCODE_MODELINGERROR          = 26; // for model generation
uint64_t EXITCODE_UNCAUGHTEXCEPTION      = 27;

uint64_t SYSCALL_BITWIDTH = 32; // integer bit width for system calls

uint64_t MIPSTER = 1;
uint64_t DIPSTER = 2;
uint64_t RIPSTER = 3;

uint64_t HYPSTER = 4;

uint64_t MINSTER = 5;
uint64_t MOBSTER = 6;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t next_page_frame = 0;

uint64_t allocated_page_frame_memory = 0;
uint64_t free_page_frame_memory      = 0;

// -----------------------------------------------------------------
// ------------------- CONSOLE ARGUMENT SCANNER --------------------
// -----------------------------------------------------------------

uint64_t  number_of_remaining_arguments();
uint64_t* remaining_arguments();

char* peek_argument(uint64_t lookahead);

char* get_argument();
void  set_argument(char* argv);

uint64_t no_or_bad_or_more_arguments(uint64_t exit_code);

void print_synopsis(char* extras);

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t  selfie_argc = 0;
uint64_t* selfie_argv = (uint64_t*) 0;

char* argument = (char*) 0;

// -----------------------------------------------------------------
// ----------------------------- SELFIE ----------------------------
// -----------------------------------------------------------------

void init_selfie(uint64_t argc, uint64_t* argv);

void init_system();

void turn_on_gc_library(uint64_t period, char* name);

// ------------------------ GLOBAL CONSTANTS -----------------------

char* selfie_name = (char*) 0; // name of running selfie executable

uint64_t BOOTLEVELZERO = 0; // flag for indicating boot level

uint64_t WINDOWS = 0; // indicates if we are likely running on Windows

// ------------------------- INITIALIZATION ------------------------

void init_selfie(uint64_t argc, uint64_t* argv) {
  selfie_argc = argc;
  selfie_argv = argv;

  selfie_name = get_argument();
}

void init_system() {
  if (is_boot_level_zero()) {
    BOOTLEVELZERO = 1;

    // Caution: the name of the executable must not have an extension to make this work
    // try opening executable with zeroed flags which likely fails but just on Windows
    if (signed_less_than(sign_extend(open(selfie_name, 0, 0), SYSCALL_BITWIDTH), 0))
      WINDOWS = 1;
  }
}

void turn_on_gc_library(uint64_t period, char* name) {
  if (fetch_stack_pointer() != 0) {
    gc_init((uint64_t*) 0);

    GC_PERIOD = period;

    selfie_name = name;
  } else
    USE_GC_LIBRARY = GC_DISABLED;
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
  // assert: 0 <= p < WORDSIZEINBITS
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
  // assert: 0 <= b < WORDSIZEINBITS
  return n * two_to_the_power_of(b);
}

uint64_t right_shift(uint64_t n, uint64_t b) {
  // assert: 0 <= b < WORDSIZEINBITS
  return n / two_to_the_power_of(b);
}

uint64_t get_bits(uint64_t n, uint64_t i, uint64_t b) {
  // assert: 0 < b <= i + b < WORDSIZEINBITS
  if (i == 0)
    return n % two_to_the_power_of(b);
  else
    // shift to-be-loaded bits all the way to the left
    // to reset all bits to the left of them, then
    // shift to-be-loaded bits all the way to the right and return
    return right_shift(left_shift(n, WORDSIZEINBITS - (i + b)), WORDSIZEINBITS - b);
}

uint64_t get_low_word(uint64_t n) {
  return get_bits(n, 0, SINGLEWORDSIZEINBITS);
}

uint64_t get_high_word(uint64_t n) {
  return get_bits(n, SINGLEWORDSIZEINBITS, SINGLEWORDSIZEINBITS);
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
  // assert: 0 < b <= WORDSIZEINBITS
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
  // assert: 0 < b < WORDSIZEINBITS
  if (n < two_to_the_power_of(b - 1))
    return n;
  else
    return n - two_to_the_power_of(b);
}

uint64_t sign_shrink(uint64_t n, uint64_t b) {
  // assert: -2^(b - 1) <= n < 2^(b - 1)
  // assert: 0 < b < WORDSIZEINBITS
  return get_bits(n, 0, b);
}

uint64_t load_character(char* s, uint64_t i) {
  // assert: i >= 0
  uint64_t a;

  // a is the index of the double word where
  // the to-be-loaded i-th character in s is
  a = i / SIZEOFUINT64;

  // CAUTION: at boot levels higher than 0, s is only accessible
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

  // CAUTION: at boot levels higher than 0, s is only accessible
  // in C* at machine word granularity, not individual characters

  // subtract the to-be-overwritten character to reset its bits in s
  // then add c to set its bits at the i-th position in s
  *((uint64_t*) s + a) = (*((uint64_t*) s + a) - left_shift(load_character(s, i), (i % SIZEOFUINT64) * 8)) + left_shift(c, (i % SIZEOFUINT64) * 8);

  return s;
}

char* string_alloc(uint64_t l) {
  // allocates zeroed memory for a string of l characters
  // plus a null terminator aligned to machine word size
  return (char*) zmalloc(l + 1);
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

      exit(EXITCODE_SCANNERERROR);
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

        exit(EXITCODE_SCANNERERROR);
      }
    else {
      // s contains a decimal number larger than UINT64_MAX
      printf2("%s: cannot convert out-of-bound number %s\n", selfie_name, s);

      exit(EXITCODE_SCANNERERROR);
    }

    // go to the next digit
    i = i + 1;

    // load character (one byte) at index i in s from memory requires
    // bit shifting since memory access can only be done in double words
    c = load_character(s, i);
  }

  return n;
}

char* itoa(uint64_t n, char* s, uint64_t b, uint64_t d, uint64_t a) {
  // assert: b in {2,4,8,10,16}

  uint64_t i;
  uint64_t sign;

  // conversion of the integer n to an ASCII string in s with base b,
  // sign d, and alignment a begins with the leftmost digit in s
  i = 0;

  // for now assuming n is positive
  sign = 0;

  if (n == 0) {
    store_character(s, 0, '0');

    i = 1;
  } else if (d)
    if (signed_less_than(n, 0))
      if (b == 10) {
        // n is represented as two's complement
        // convert n to a positive number but remember the sign
        n = -n;

        sign = 1;
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
      store_character(s, i, 'o'); // octal numbers start with 0o
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
  } else if (character_buffer) {
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
  } else
    // character_buffer has not been successfully allocated yet
    exit(EXITCODE_IOERROR);
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

void print_unsigned_integer(uint64_t n) {
  print(itoa(n, integer_buffer, 10, 0, 0));
}

void print_integer(uint64_t n) {
  print(itoa(n, integer_buffer, 10, 1, 0));
}

void unprint_integer(uint64_t n) {
  n = string_length(itoa(n, integer_buffer, 10, 1, 0));

  while (n > 0) {
    put_character(CHAR_BACKSPACE);

    n = n - 1;
  }
}

void print_hexadecimal(uint64_t n, uint64_t a) {
  print(itoa(n, integer_buffer, 16, 0, a));
}

void print_octal(uint64_t n, uint64_t a) {
  print(itoa(n, integer_buffer, 8, 0, a));
}

void print_binary(uint64_t n, uint64_t a) {
  print(itoa(n, integer_buffer, 2, 0, a));
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
      } else if (load_character(s, i + 1) == 'u') {
        print_unsigned_integer((uint64_t) a);

        return i + 2;
      } else if (load_character(s, i + 1) == 'd') {
        print_integer((uint64_t) a);

        return i + 2;
      } else if (load_character(s, i + 1) == '.') {
        // for simplicity we support a single digit only
        p = load_character(s, i + 2) - '0';

        if (p < 10) {
          // the character at i + 2 is in fact a digit
          if (load_character(s, i + 3) == 'u')
            print_unsigned_integer((uint64_t) a / ten_to_the_power_of(p));
          else if (load_character(s, i + 3) == 'd')
            print_integer((uint64_t) a / ten_to_the_power_of(p));
          else
            // precision only supported for %u and %d
            return i + 4;

          if (p > 0) {
            // using integer_buffer here is ok since we are not using print_integer
            itoa((uint64_t) a % ten_to_the_power_of(p), integer_buffer, 10, 0, 0);
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

void printf7(char* s, char* a1, char* a2, char* a3, char* a4, char* a5, char* a6, char* a7) {
  print_format0(s, print_format1(s, print_format1(s, print_format1(s, print_format1(s, print_format1(s, print_format1(s, print_format1(s, 0, a1), a2), a3), a4), a5), a6), a7));
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

void zero_memory(uint64_t* memory, uint64_t size) {
  uint64_t i;

  size = round_up(size, SIZEOFUINT64) / SIZEOFUINT64;

  i = 0;

  while (i < size) {
    // erase memory by setting it to 0
    *(memory + i) = 0;

    i = i + 1;
  }
}

uint64_t* smalloc(uint64_t size) {
  // this procedure ensures a defined program exit
  // if no memory can be allocated
  uint64_t* memory;

  if (USE_GC_LIBRARY)
    memory = gc_malloc(size);
  else
    memory = malloc(size);

  if (size == 0)
    // any address including 0
    return memory;
  else if (memory == (uint64_t*) 0) {
    if (character_buffer)
      // can only print error message if character_buffer has been successfully allocated
      printf1("%s: malloc out of memory\n", selfie_name);

    exit(EXITCODE_OUTOFVIRTUALMEMORY);
  }

  return memory;
}

uint64_t* smalloc_system(uint64_t size) {
  // internal use only!

  uint64_t gc;
  uint64_t* memory;

  gc = USE_GC_LIBRARY;

  USE_GC_LIBRARY = GC_DISABLED;

  memory = smalloc(size);

  USE_GC_LIBRARY = gc;

  return memory;
}

uint64_t* zalloc(uint64_t size) {
  // internal use only!

  // this procedure is only executed at boot level 0
  // zalloc allocates size bytes rounded up to word size
  // and then zeroes that memory, similar to calloc, but
  // called zalloc to avoid redeclaring calloc
  uint64_t* memory;

  size = round_up(size, SIZEOFUINT64);

  memory = smalloc(size);

  zero_memory(memory, size);

  return memory;
}

uint64_t* zmalloc(uint64_t size) {
  if (USE_GC_LIBRARY)
    // assert: on boot level 1 or above where mallocated memory is zeroed
    return gc_malloc(size);
  else
    return zalloc(size);
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
  printf4("%s: %s in %s in line %u: ", selfie_name, message, source_name, (char*) line);
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
      if (is_character_new_line())
        // single-line comments end with new line
        in_single_line_comment = 0;
      else if (character == CHAR_EOF)
        // or end of file
        return character;
      else {
        // count the characters in comments as ignored characters
        number_of_ignored_characters = number_of_ignored_characters + 1;

        get_character();
      }

    } else if (in_multi_line_comment) {
      while (character == CHAR_ASTERISK) {
        // look for "*/" by looping over consecutive '*' counting them as ignored characters
        number_of_ignored_characters = number_of_ignored_characters + 1;

        get_character();

        if (character == CHAR_SLASH)
          // multi-line comments end with "*/"
          in_multi_line_comment = 0;
      }

      if (in_multi_line_comment) {
        // keep track of line numbers for error reporting and code annotation
        if (character == CHAR_LF)
          // only line feeds count towards line numbers, not carriage returns
          line_number = line_number + 1;
        else if (character == CHAR_EOF) {
          // multi-line comment is not terminated
          syntax_error_message("runaway multi-line comment");

          exit(EXITCODE_SCANNERERROR);
        }
      }

      // count the characters in comments as ignored characters including '/' in "*/"
      number_of_ignored_characters = number_of_ignored_characters + 1;

      get_character();

    } else if (is_character_whitespace()) {
      // keep track of line numbers for error reporting and code annotation
      if (character == CHAR_LF)
        // only line feeds count towards line numbers, not carriage returns
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

        get_character();

      } else if (character == CHAR_ASTERISK) {
        // "/*" begins a multi-line comment
        in_multi_line_comment = 1;

        // count both slash and asterisk as ignored characters
        number_of_ignored_characters = number_of_ignored_characters + 2;

        number_of_comments = number_of_comments + 1;

        get_character();

      } else {
        // while looking for "//" and "/*" we actually found '/'
        symbol = SYM_DIVISION;

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
    if (symbol != SYM_DIVISION) {
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

        symbol = SYM_REMAINDER;

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
    set_scope(new_entry, REG_S0);
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

uint64_t is_int_or_char_literal() {
  if (symbol == SYM_INTEGER)
    return 1;
  else if (symbol == SYM_CHARACTER)
    return 1;
  else
    return 0;
}

uint64_t is_mult_or_div_or_rem() {
  if (symbol == SYM_ASTERISK)
    return 1;
  else if (symbol == SYM_DIVISION)
    return 1;
  else if (symbol == SYM_REMAINDER)
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
    emit_addi(REG_SP, REG_SP, -WORDSIZE);
    emit_sd(REG_SP, 0, current_temporary());

    tfree(1);
  }
}

void restore_temporaries(uint64_t number_of_temporaries) {
  while (allocated_temporaries < number_of_temporaries) {
    talloc();

    // restore temporary from stack
    emit_ld(current_temporary(), REG_SP, 0);
    emit_addi(REG_SP, REG_SP, WORDSIZE);
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

void load_small_and_medium_integer(uint64_t reg, uint64_t value) {
  uint64_t lower;
  uint64_t upper;

  // assert: -2^31 <= value < 2^31

  if (is_signed_integer(value, 12)) {
    // integers with -2^11 <= value < 2^11
    // are loaded with one addi into a register

    emit_addi(reg, REG_ZR, value);
  } else {
    // integers with -2^31 <= value < -2^11 and 2^11 <= value < 2^31
    // are loaded with one lui and one addi into a register plus
    // an additional sub to cancel sign extension if necessary

    lower = get_bits(value,  0, 12);
    upper = get_bits(value, 12, 20);

    if (lower >= two_to_the_power_of(11)) {
      // add 1 which is effectively 2^12 to cancel sign extension of lower
      upper = upper + 1;

      // assert: 0 < upper <= 2^(32-12)
      emit_lui(reg, sign_extend(upper, 20));

      if (upper == two_to_the_power_of(19))
        // upper overflowed, cancel sign extension
        emit_sub(reg, REG_ZR, reg);
    } else
      // assert: 0 < upper < 2^(32-12)
      emit_lui(reg, sign_extend(upper, 20));

    emit_addi(reg, reg, sign_extend(lower, 12));
  }
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
  uint64_t* entry;

  // assert: n = allocated_temporaries

  if (is_signed_integer(value, 32)) {
    // integers with -2^31 <= value < 2^31 are loaded as immediate values
    talloc();

    load_small_and_medium_integer(current_temporary(), value);
  } else {
    // integers with value < -2^31 or value >= 2^31 are stored in data segment
    entry = search_global_symbol_table(integer, BIGINT);

    if (entry == (uint64_t*) 0) {
      allocated_memory = allocated_memory + WORDSIZE;

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

  allocated_memory = allocated_memory + round_up(length, WORDSIZE);

  create_symbol_table_entry(GLOBAL_TABLE, string, line_number, STRING, UINT64STAR_T, 0, -allocated_memory);

  load_integer(-allocated_memory);

  emit_add(current_temporary(), REG_GP, current_temporary());

  // assert: allocated_temporaries == n + 1
}

uint64_t procedure_call(uint64_t* entry, char* procedure) {
  uint64_t type;

  if (entry == (uint64_t*) 0) {
    // procedure never called nor declared nor defined

    // default return type is "uint64_t"
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

void procedure_prologue(uint64_t number_of_local_variable_bytes) {
  // allocate memory for return address
  emit_addi(REG_SP, REG_SP, -WORDSIZE);

  // save return address
  emit_sd(REG_SP, 0, REG_RA);

  // allocate memory for caller's frame pointer
  emit_addi(REG_SP, REG_SP, -WORDSIZE);

  // save caller's frame pointer
  emit_sd(REG_SP, 0, REG_S0);

  // set callee's frame pointer
  emit_addi(REG_S0, REG_SP, 0);

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

void procedure_epilogue(uint64_t number_of_parameter_bytes) {
  // deallocate memory for callee's frame pointer and local variables
  emit_addi(REG_SP, REG_S0, 0);

  // restore caller's frame pointer
  emit_ld(REG_S0, REG_SP, 0);

  // deallocate memory for caller's frame pointer
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  // restore return address
  emit_ld(REG_RA, REG_SP, 0);

  // deallocate memory for return address and parameters
  emit_addi(REG_SP, REG_SP, WORDSIZE + number_of_parameter_bytes);

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
    emit_addi(REG_SP, REG_SP, -WORDSIZE);
    emit_sd(REG_SP, 0, current_temporary());

    tfree(1);

    while (symbol == SYM_COMMA) {
      get_symbol();

      compile_expression();

      // push more parameters onto stack
      emit_addi(REG_SP, REG_SP, -WORDSIZE);
      emit_sd(REG_SP, 0, current_temporary());

      tfree(1);
    }

    if (symbol == SYM_RPARENTHESIS) {
      get_symbol();

      type = procedure_call(entry, procedure);
    } else {
      syntax_error_symbol(SYM_RPARENTHESIS);

      type = UINT64_T;
    }
  } else if (symbol == SYM_RPARENTHESIS) {
    get_symbol();

    type = procedure_call(entry, procedure);
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

  // variable or call?
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

  // integer literal?
  } else if (symbol == SYM_INTEGER) {
    load_integer(literal);

    get_symbol();

    type = UINT64_T;

  // character literal?
  } else if (symbol == SYM_CHARACTER) {
    talloc();

    emit_addi(current_temporary(), REG_ZR, literal);

    get_symbol();

    type = UINT64_T;

  // string literal?
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
  while (is_mult_or_div_or_rem()) {
    operator_symbol = symbol;

    get_symbol();

    rtype = compile_factor();

    // assert: allocated_temporaries == n + 2

    if (ltype != rtype)
      type_warning(ltype, rtype);

    if (operator_symbol == SYM_ASTERISK)
      emit_mul(previous_temporary(), previous_temporary(), current_temporary());
    else if (operator_symbol == SYM_DIVISION)
      emit_divu(previous_temporary(), previous_temporary(), current_temporary());
    else if (operator_symbol == SYM_REMAINDER)
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

    // "*" variable
    if (symbol == SYM_IDENTIFIER) {
      ltype = load_variable_or_big_int(identifier, VARIABLE);

      if (ltype != UINT64STAR_T)
        type_warning(UINT64STAR_T, ltype);

      get_symbol();

      // "*" variable "="
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
  // variable "=" expression | call
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

    // variable = expression
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

    if (is_int_or_char_literal())
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
        // 2 * WORDSIZE offset to skip frame pointer and link
        set_address(entry, parameters * WORDSIZE + 2 * WORDSIZE);

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
      number_of_local_variable_bytes = number_of_local_variable_bytes + WORDSIZE;

      // offset of local variables relative to frame pointer is negative
      compile_variable(-number_of_local_variable_bytes);

      if (symbol == SYM_SEMICOLON)
        get_symbol();
      else
        syntax_error_symbol(SYM_SEMICOLON);
    }

    procedure_prologue(number_of_local_variable_bytes);

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

    procedure_epilogue(number_of_parameters * WORDSIZE);

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
            allocated_memory = allocated_memory + WORDSIZE;

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

  // make sure gp is machine-word-aligned
  padding = gp % WORDSIZE;
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
    //    sp + WORDSIZE
    //            |
    //            V
    // | argc | argv[0] | argv[1] | ... | argv[n]
    emit_addi(current_temporary(), REG_SP, WORDSIZE);

    // then push argv pointer onto the stack
    //      ______________
    //     |              V
    // | &argv | argc | argv[0] | argv[1] | ... | argv[n]
    emit_addi(REG_SP, REG_SP, -WORDSIZE);
    emit_sd(REG_SP, 0, current_temporary());

    tfree(1);

    // assert: global, _bump, and stack pointers are set up
    //         with all other non-temporary registers zeroed

    // copy "main" string into zeroed double word to obtain unique hash
    entry = get_scoped_symbol_table_entry(string_copy("main"), PROCEDURE);

    procedure_call(entry, "main");
  }

  // we exit with exit code in return register pushed onto the stack
  emit_addi(REG_SP, REG_SP, -WORDSIZE);
  emit_sd(REG_SP, 0, REG_A0);

  // discount NOPs in profile that were generated for program entry
  ic_addi = ic_addi - binary_length / INSTRUCTIONSIZE;

  // wrapper code for exit must follow here

  // restore original binary length
  binary_length = code_length;
}

// -----------------------------------------------------------------
// --------------------------- COMPILER ----------------------------
// -----------------------------------------------------------------

void selfie_compile() {
  uint64_t link;
  uint64_t number_of_source_files;
  uint64_t fetch_dss_code_location;

  fetch_dss_code_location = 0;

  // link until next console option
  link = 1;

  number_of_source_files = 0;

  source_name = "library";

  binary_name = source_name;

  // allocate memory for storing binary
  binary        = zmalloc(MAX_BINARY_LENGTH);
  binary_length = 0;

  // reset code length
  code_length = 0;

  // allocate zeroed memory for storing source code line numbers
  code_line_number = zmalloc(MAX_CODE_LENGTH / INSTRUCTIONSIZE * SIZEOFUINT64);
  data_line_number = zmalloc(MAX_DATA_LENGTH / WORDSIZE * SIZEOFUINT64);

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

  if (GC_ON) {
    emit_fetch_stack_pointer();
    emit_fetch_global_pointer();

    // save code location of eventual fetch_data_segment_size implementation
    fetch_dss_code_location = binary_length;

    emit_fetch_data_segment_size_interface();
  }

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

      printf4("%s: %u characters read in %u lines and %u comments\n", selfie_name,
        (char*) number_of_read_characters,
        (char*) line_number,
        (char*) number_of_comments);

      printf4("%s: with %u(%.2u%%) characters in %u actual symbols\n", selfie_name,
        (char*) (number_of_read_characters - number_of_ignored_characters),
        (char*) fixed_point_percentage(fixed_point_ratio(number_of_read_characters, number_of_read_characters - number_of_ignored_characters, 4), 4),
        (char*) number_of_scanned_symbols);

      printf4("%s: %u global variables, %u procedures, %u string literals\n", selfie_name,
        (char*) number_of_global_variables,
        (char*) number_of_procedures,
        (char*) number_of_strings);

      printf6("%s: %u calls, %u assignments, %u while, %u if, %u return\n", selfie_name,
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

  if (GC_ON)
    emit_fetch_data_segment_size_implementation(fetch_dss_code_location);

  emit_data_segment();

  ELF_header = create_elf_header(binary_length, code_length);

  entry_point = ELF_ENTRY_POINT;

  printf3("%s: symbol table search time was %u iterations on average and %u in total\n", selfie_name,
    (char*) (total_search_time / number_of_searches),
    (char*) total_search_time);

  printf4("%s: %u bytes generated with %u instructions and %u bytes of data\n", selfie_name,
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

uint64_t is_stack_register(uint64_t reg) {
  if (reg == REG_SP)
    return 1;
  else if (reg == REG_S0)
    return 1;
  else if (reg == REG_RA)
    return 1;
  else
    return 0;
}

uint64_t is_system_register(uint64_t reg) {
  if (reg == REG_GP)
    return 1;
  else
    return is_stack_register(reg);
}

uint64_t is_argument_register(uint64_t reg) {
  if (reg >= REG_A0)
    if (reg <= REG_A7)
      return 1;

  return 0;
}

uint64_t is_temporary_register(uint64_t reg) {
  if (reg >= REG_T0)
    if (reg <= REG_T2)
      return 1;
    else if (reg >= REG_T3)
      return 1;
    else
      return 0;
  else
    return 0;
}

uint64_t read_register(uint64_t reg) {
  if (reg != REG_ZR) {
    if (*(writes_per_register + reg) > 0)
      // register has been written to before
      *(reads_per_register + reg) = *(reads_per_register + reg) + 1;
    else {
      print_instruction();
      print(": reading from uninitialized register ");
      print_register_name(reg);
      println();

      throw_exception(EXCEPTION_UNINITIALIZEDREGISTER, reg);

      return 0;
    }
  }

  return 1;
}

void write_register(uint64_t reg) {
  *(writes_per_register + reg) = *(writes_per_register + reg) + 1;
}

void update_register_counters() {
  if (read_register(rs1))
    if (read_register(rs2))
      write_register(rd);
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
      (char*) (two_to_the_power_of(bits - 1) - 1));

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
  rs2    = REG_ZR;
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
  rd     = REG_ZR;
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
  rd     = REG_ZR;
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
  rs2    = REG_ZR;
  rs1    = REG_ZR;
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
  rs2    = REG_ZR;
  rs1    = REG_ZR;
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

uint64_t get_total_percentage_of_nops() {
  return fixed_point_percentage(fixed_point_ratio(get_total_number_of_instructions(),
    nopc_lui + nopc_addi + nopc_add + nopc_sub + nopc_mul + nopc_divu + nopc_remu + nopc_sltu + nopc_ld + nopc_sd + nopc_beq + nopc_jal + nopc_jalr, 4), 4);
}

void print_instruction_counter(uint64_t total, uint64_t counter, char* mnemonics) {
  printf3("%s: %u(%.2u%%)",
    mnemonics,
    (char*) counter,
    (char*) fixed_point_percentage(fixed_point_ratio(total, counter, 4), 4));
}

void print_instruction_counter_with_nops(uint64_t total, uint64_t counter, uint64_t nops, char* mnemonics) {
  print_instruction_counter(total, counter, mnemonics);

  if (run)
    printf1("[%.2u%%]", (char*) fixed_point_percentage(fixed_point_ratio(counter, nops, 4), 4));
}

void print_instruction_counters() {
  uint64_t ic;

  ic = get_total_number_of_instructions();

  printf1("%s: init:    ", selfie_name);
  print_instruction_counter_with_nops(ic, ic_lui, nopc_lui, "lui");
  print(", ");
  print_instruction_counter_with_nops(ic, ic_addi, nopc_addi, "addi");
  println();

  printf1("%s: memory:  ", selfie_name);
  print_instruction_counter_with_nops(ic, ic_ld, nopc_ld, "ld");
  print(", ");
  print_instruction_counter_with_nops(ic, ic_sd, nopc_sd, "sd");
  println();

  printf1("%s: compute: ", selfie_name);
  print_instruction_counter_with_nops(ic, ic_add, nopc_add, "add");
  print(", ");
  print_instruction_counter_with_nops(ic, ic_sub, nopc_sub, "sub");
  print(", ");
  print_instruction_counter_with_nops(ic, ic_mul, nopc_mul, "mul");
  println();

  printf1("%s: compute: ", selfie_name);
  print_instruction_counter_with_nops(ic, ic_divu, nopc_divu, "divu");
  print(", ");
  print_instruction_counter_with_nops(ic, ic_remu, nopc_remu, "remu");
  println();

  printf1("%s: compare: ", selfie_name);
  print_instruction_counter_with_nops(ic, ic_sltu, nopc_sltu, "sltu");
  println();

  printf1("%s: control: ", selfie_name);
  print_instruction_counter_with_nops(ic, ic_beq, nopc_beq, "beq");
  print(", ");
  print_instruction_counter_with_nops(ic, ic_jal, nopc_jal, "jal");
  print(", ");
  print_instruction_counter_with_nops(ic, ic_jalr, nopc_jalr, "jalr");
  println();

  printf1("%s: system:  ", selfie_name);
  print_instruction_counter(ic, ic_ecall, "ecall");
  println();
}

uint64_t load_instruction(uint64_t baddr) {
  if (baddr % WORDSIZE == 0)
    return get_low_word(*(binary + baddr / WORDSIZE));
  else
    return get_high_word(*(binary + baddr / WORDSIZE));
}

void store_instruction(uint64_t baddr, uint64_t instruction) {
  uint64_t word;

  if (baddr >= MAX_CODE_LENGTH) {
    syntax_error_message("maximum code length exceeded");

    exit(EXITCODE_COMPILERERROR);
  }

  word = *(binary + baddr / WORDSIZE);

  if (baddr % WORDSIZE == 0)
    // replace low word
    word = left_shift(get_high_word(word), SINGLEWORDSIZEINBITS) + instruction;
  else
    // replace high word
    word = left_shift(instruction, SINGLEWORDSIZEINBITS) + get_low_word(word);

  *(binary + baddr / WORDSIZE) = word;
}

uint64_t load_data(uint64_t baddr) {
  return *(binary + baddr / WORDSIZE);
}

void store_data(uint64_t baddr, uint64_t data) {
  if (baddr - code_length >= MAX_DATA_LENGTH) {
    syntax_error_message("maximum data length exceeded");

    exit(EXITCODE_COMPILERERROR);
  }

  *(binary + baddr / WORDSIZE) = data;
}

void emit_instruction(uint64_t instruction) {
  store_instruction(binary_length, instruction);

  if (code_line_number != (uint64_t*) 0)
    if (*(code_line_number + binary_length / INSTRUCTIONSIZE) == 0)
      *(code_line_number + binary_length / INSTRUCTIONSIZE) = line_number;

  binary_length = binary_length + INSTRUCTIONSIZE;
}

uint64_t encode_nop() {
  return encode_i_format(0, REG_ZR, F3_NOP, REG_ZR, OP_IMM);
}

void emit_nop() {
  emit_instruction(encode_nop());

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
    *(data_line_number + (allocated_memory + offset) / WORDSIZE) = source_line_number;
}

void emit_string_data(uint64_t* entry) {
  char* s;
  uint64_t i;
  uint64_t l;

  s = get_string(entry);

  i = 0;

  l = round_up(string_length(s) + 1, WORDSIZE);

  while (i < l) {
    // CAUTION: at boot levels higher than 0, s is only accessible
    // in C* at machine word granularity, not individual characters
    emit_data_word(*((uint64_t*) s), get_address(entry) + i, get_line_number(entry));

    s = (char*) ((uint64_t*) s + 1);

    i = i + WORDSIZE;
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
  return touch(zmalloc(ELF_HEADER_LEN), ELF_HEADER_LEN);
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

  if (WINDOWS)
    // use Windows flags
    fd = sign_extend(open(name, WINDOWS_O_BINARY_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH), SYSCALL_BITWIDTH);
  else {
    // try Mac flags first as default
    fd = sign_extend(open(name, MAC_O_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH), SYSCALL_BITWIDTH);

    if (signed_less_than(fd, 0))
      // then try Linux flags
      fd = sign_extend(open(name, LINUX_O_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH), SYSCALL_BITWIDTH);
  }

  return fd;
}

void selfie_output(char* filename) {
  uint64_t fd;

  binary_name = filename;

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

  printf5("%s: %u bytes with %u instructions and %u bytes of data written into %s\n", selfie_name,
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

    m = m + PAGESIZE / SIZEOFUINT64;

    // touch every following page
    n = *m;
  }

  if (length > 0) {
    m = m + (length - 1) / SIZEOFUINT64;

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

  entry_point   = 0;
  binary_length = 0;
  code_length   = 0;

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
            printf5("%s: %u bytes with %u instructions and %u bytes of data loaded from %s\n",
              selfie_name,
              (char*) (ELF_HEADER_LEN + binary_length),
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
  emit_addi(REG_SP, REG_SP, WORDSIZE);

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

  printf1("%s: <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<\n", selfie_name);
  printf3("%s: %s exiting with exit code %d\n", selfie_name,
    get_name(context),
    (char*) sign_extend(get_exit_code(context), SYSCALL_BITWIDTH));
}

void emit_read() {
  create_symbol_table_entry(LIBRARY_TABLE, "read", 0, PROCEDURE, UINT64_T, 0, binary_length);

  emit_ld(REG_A2, REG_SP, 0); // size
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  emit_ld(REG_A1, REG_SP, 0); // *buffer
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  emit_ld(REG_A0, REG_SP, 0); // fd
  emit_addi(REG_SP, REG_SP, WORDSIZE);

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
    printf4("%s: trying to read %u bytes from file with descriptor %u into buffer at virtual address %p\n", selfie_name,
      (char*) size,
      (char*) fd,
      (char*) vbuffer);

  read_total = 0;

  bytes_to_read = SIZEOFUINT64;

  failed = 0;

  while (size > 0) {
    if (size < bytes_to_read)
      bytes_to_read = size;

    if (is_valid_virtual_address(vbuffer))
      if (is_valid_data_stack_heap_address(context, vbuffer))
        if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
          buffer = tlb(get_pt(context), vbuffer);

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

          printf2("%s: reading into virtual address %p failed because the address is unmapped\n", selfie_name, (char*) vbuffer);
        }
      else {
        failed = 1;

        size = 0;

        printf2("%s: reading into virtual address %p failed because the address is in an invalid segment\n", selfie_name, (char*) vbuffer);
      }
    else {
      failed = 1;

      size = 0;

      printf2("%s: reading into virtual address %p failed because the address is invalid\n", selfie_name, (char*) vbuffer);
    }
  }

  if (failed)
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);
  else
    *(get_regs(context) + REG_A0) = read_total;

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);

  if (debug_read)
    printf3("%s: actually read %u bytes from file with descriptor %u\n", selfie_name, (char*) read_total, (char*) fd);

  if (debug_syscalls) {
    print(" -> ");
    print_register_value(REG_A0);
    println();
  }
}

void emit_write() {
  create_symbol_table_entry(LIBRARY_TABLE, "write", 0, PROCEDURE, UINT64_T, 0, binary_length);

  emit_ld(REG_A2, REG_SP, 0); // size
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  emit_ld(REG_A1, REG_SP, 0); // *buffer
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  emit_ld(REG_A0, REG_SP, 0); // fd
  emit_addi(REG_SP, REG_SP, WORDSIZE);

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
    printf4("%s: trying to write %u bytes from buffer at virtual address %p into file with descriptor %u\n", selfie_name,
      (char*) size,
      (char*) vbuffer,
      (char*) fd);

  written_total = 0;

  bytes_to_write = SIZEOFUINT64;

  failed = 0;

  while (size > 0) {
    if (size < bytes_to_write)
      bytes_to_write = size;

    if (is_valid_virtual_address(vbuffer))
      if (is_valid_data_stack_heap_address(context, vbuffer))
        if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
          buffer = tlb(get_pt(context), vbuffer);

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

          printf2("%s: writing from virtual address %p failed because the address is unmapped\n", selfie_name, (char*) vbuffer);
        }
      else {
        failed = 1;

        size = 0;

        printf2("%s: writing from virtual address %p failed because the address is in an invalid segment\n", selfie_name, (char*) vbuffer);
      }
    else {
      failed = 1;

      size = 0;

      printf2("%s: writing from virtual address %p failed because the address is invalid\n", selfie_name, (char*) vbuffer);
    }
  }

  if (failed)
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);
  else
    *(get_regs(context) + REG_A0) = written_total;

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);

  if (debug_write)
    printf3("%s: actually wrote %u bytes into file with descriptor %u\n", selfie_name, (char*) written_total, (char*) fd);

  if (debug_syscalls) {
    print(" -> ");
    print_register_value(REG_A0);
    println();
  }
}

void emit_open() {
  create_symbol_table_entry(LIBRARY_TABLE, "open", 0, PROCEDURE, UINT64_T, 0, binary_length);

  emit_ld(REG_A3, REG_SP, 0); // mode
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  emit_ld(REG_A2, REG_SP, 0); // flags
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  emit_ld(REG_A1, REG_SP, 0); // filename
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  // DIRFD_AT_FDCWD makes sure that openat behaves like open
  emit_addi(REG_A0, REG_ZR, DIRFD_AT_FDCWD);

  emit_addi(REG_A7, REG_ZR, SYSCALL_OPENAT);

  emit_ecall();

  emit_jalr(REG_ZR, REG_RA, 0);
}

uint64_t down_load_string(uint64_t* context, uint64_t vaddr, char* s) {
  uint64_t i;
  uint64_t j;

  i = 0;

  while (i < MAX_FILENAME_LENGTH / SIZEOFUINT64) {
    if (is_valid_virtual_address(vaddr))
      if (is_valid_data_stack_heap_address(context, vaddr)) {
        if (is_virtual_address_mapped(get_pt(context), vaddr))
          *((uint64_t*) s + i) = load_virtual_memory(get_pt(context), vaddr);
        else {
          printf2("%s: opening file failed because the file name address %p is unmapped\n", selfie_name, (char*) vaddr);

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
        printf2("%s: opening file failed because the file name address %p is in an invalid segment\n", selfie_name, (char*) vaddr);

        return 0;
      }
    else {
      printf2("%s: opening file failed because the file name address %p is invalid\n", selfie_name, (char*) vaddr);

      return 0;
    }
  }

  printf2("%s: opening file failed because the file name is too long at address %p\n", selfie_name, (char*) vaddr);

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

  if (down_load_string(context, vfilename, filename_buffer)) {
    if (flags == MAC_O_CREAT_TRUNC_WRONLY)
      // default for opening write-only files
      fd = open_write_only(filename_buffer);
    else
      fd = sign_extend(open(filename_buffer, flags, mode), SYSCALL_BITWIDTH);

    *(get_regs(context) + REG_A0) = fd;

    if (debug_open)
      printf5("%s: opened file %s with flags %x and mode %o returning file descriptor %u\n", selfie_name,
        filename_buffer,
        (char*) flags,
        (char*) mode,
        (char*) fd);
  } else
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);

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

  // on boot levels higher than 0, zalloc falls back to malloc
  // assuming that page frames are zeroed on boot level zero
  create_symbol_table_entry(LIBRARY_TABLE, "zalloc", 0, PROCEDURE, UINT64STAR_T, 0, binary_length);

  // allocate memory in data segment for recording state of
  // malloc (bump pointer) in compiler-declared global variable
  allocated_memory = allocated_memory + WORDSIZE;

  // define global variable _bump for storing malloc's bump pointer
  // copy "_bump" string into zeroed double word to obtain unique hash
  create_symbol_table_entry(GLOBAL_TABLE, string_copy("_bump"), 1, VARIABLE, UINT64_T, 0, -allocated_memory);

  // do not account for _bump as global variable
  number_of_global_variables = number_of_global_variables - 1;

  entry = search_global_symbol_table(string_copy("_bump"), VARIABLE);

  // allocate register for size parameter
  talloc();

  emit_ld(current_temporary(), REG_SP, 0); // size
  emit_addi(REG_SP, REG_SP, WORDSIZE);

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

  // caution: if mipster runs with garbage collection enabled,
  // the brk syscall is redirected to the gc_brk syscall which
  // skips the next seven instructions, see implement_gc_brk

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

uint64_t try_brk(uint64_t* context, uint64_t new_program_break) {
  uint64_t current_program_break;

  current_program_break = get_program_break(context);

  if (is_valid_virtual_address(new_program_break))
    if (new_program_break >= current_program_break)
      if (new_program_break < *(get_regs(context) + REG_SP)) {
        if (debug_brk)
          printf2("%s: setting program break to %p\n", selfie_name, (char*) new_program_break);

        set_program_break(context, new_program_break);

        // account for memory allocated by brk
        mc_brk = mc_brk + (new_program_break - current_program_break);

        return new_program_break;
      }

  // setting new program break failed, return current program break

  if (debug_brk)
    printf2("%s: retrieving current program break %p\n", selfie_name, (char*) current_program_break);

  return current_program_break;
}

void implement_brk(uint64_t* context) {
  // parameter
  uint64_t new_program_break;

  // local variable
  uint64_t previous_program_break;

  new_program_break = *(get_regs(context) + REG_A0);

  previous_program_break = get_program_break(context);

  // attempt to update program break

  new_program_break = try_brk(context, new_program_break);

  if (debug_syscalls) {
    print("(brk): ");
    print_register_hexadecimal(REG_A0);
    print(" |- ");
    print_register_hexadecimal(REG_A0);
  }

  if (new_program_break == *(get_regs(context) + REG_A0)) {
    // attempt to update program break succeeded
    if (*(get_regs(context) + REG_A0) != previous_program_break)
      // account for brk syscall if program break actually changed
      sc_brk = sc_brk + 1;
  } else
    // attempt to update program break failed
    *(get_regs(context) + REG_A0) = previous_program_break;

  if (debug_syscalls) {
    print(" -> ");
    print_register_hexadecimal(REG_A0);
    println();
  }

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
}

uint64_t is_boot_level_zero() {
  // C99 malloc(0) returns either a null pointer or a unique pointer,
  // see http://pubs.opengroup.org/onlinepubs/9699919799
  // in contrast, selfie's malloc(0) returns the same not null address,
  // if malloc(0) is called consecutively.
  uint64_t first_malloc;
  uint64_t second_malloc;

  first_malloc = (uint64_t) malloc(0);
  second_malloc = (uint64_t) malloc(0);

  if (first_malloc == 0)
    return 1;
  if (first_malloc != second_malloc)
    return 1;

  // it is selfie's malloc, so it cannot be boot level zero.
  return 0;
}

// -----------------------------------------------------------------
// ----------------------- HYPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emit_switch() {
  create_symbol_table_entry(LIBRARY_TABLE, "hypster_switch", 0, PROCEDURE, UINT64STAR_T, 0, binary_length);

  emit_ld(REG_A1, REG_SP, 0); // number of instructions to execute
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  emit_ld(REG_A0, REG_SP, 0); // context to which we switch
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  emit_addi(REG_A7, REG_ZR, SYSCALL_SWITCH);

  emit_ecall();

  // save context from which we are switching here in return register
  emit_addi(REG_A0, REG_A6, 0);

  emit_jalr(REG_ZR, REG_RA, 0);
}

uint64_t* do_switch(uint64_t* from_context, uint64_t* to_context, uint64_t timeout) {
  restore_context(to_context);

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
      printf1(" to execute %u instructions", (char*) timer);
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

void reset_memory_counters() {
  mc_brk = 0;
  sc_brk = 0;

  mc_mapped_heap = 0;
}

uint64_t load_physical_memory(uint64_t* paddr) {
  return *paddr;
}

void store_physical_memory(uint64_t* paddr, uint64_t data) {
  *paddr = data;
}

uint64_t get_root_PDE_offset(uint64_t page) {
  // with 4GB (2^32B) virtual memory there are 2^(32-12) 4KB (2^12B) pages;
  // in a two-level page table with 4KB (2^12B) pages as leaf nodes and
  // 64-bit pointers (2^3B), each leaf node accommodates 2^(12-3) PTEs;
  // thus bits 9 through 19 encode the root PDE (page directory entry) offset
  return page / NUMBEROFLEAFPTES; // right shift by 9 bits
}

uint64_t get_leaf_PTE_offset(uint64_t page) {
  // bits 0 through 8 encode the leaf PTE (page table entry) offset
  return page - get_root_PDE_offset(page) * NUMBEROFLEAFPTES; // extract the 9 LSBs
}

uint64_t* get_PTE_address_for_page(uint64_t* parent_table, uint64_t* table, uint64_t page) {
  uint64_t* leaf_pt;

  // assert: 0 <= page < NUMBEROFPAGES

  if (PAGETABLETREE == 0)
    // just pointer arithmetic, no access!
    return table + page;
  else {
    // to get leaf page table, root page directory access is required!
    if (parent_table == (uint64_t*) 0)
      leaf_pt = (uint64_t*) *(table + get_root_PDE_offset(page));
    else
      // table is in address space of parent_table
      leaf_pt = (uint64_t*) load_virtual_memory(parent_table, (uint64_t) (table + get_root_PDE_offset(page)));

    if (leaf_pt == (uint64_t*) 0)
      return (uint64_t*) 0;
    else
      // again, just pointer arithmetic, no access!
      return leaf_pt + get_leaf_PTE_offset(page);
  }
}

uint64_t get_frame_for_page(uint64_t* table, uint64_t page) {
  uint64_t* PTE_address;

  PTE_address = get_PTE_address_for_page(0, table, page);

  if (PTE_address == (uint64_t*) 0)
    return 0;
  else
    return (uint64_t) *PTE_address;
}

void set_PTE_for_page(uint64_t* table, uint64_t page, uint64_t frame) {
  uint64_t  root_PDE_offset;
  uint64_t* leaf_pt;

  // assert: 0 <= page < NUMBEROFPAGES

  if (PAGETABLETREE == 0)
    *(table + page) = frame;
  else {
    root_PDE_offset = get_root_PDE_offset(page);

    leaf_pt = (uint64_t*) *(table + root_PDE_offset);

    if (leaf_pt == (uint64_t*) 0) {
      leaf_pt = palloc(); // 4KB leaf page table

      *(table + root_PDE_offset) = (uint64_t) leaf_pt;
    }

    *(leaf_pt + get_leaf_PTE_offset(page)) = frame;
  }
}

uint64_t is_page_mapped(uint64_t* table, uint64_t page) {
  if (get_frame_for_page(table, page) != 0)
    return 1;
  else
    return 0;
}

uint64_t is_valid_virtual_address(uint64_t vaddr) {
  if (vaddr <= VIRTUALMEMORYSIZE - WORDSIZE)
    // memory access must be machine-word-aligned
    if (vaddr % WORDSIZE == 0)
      return 1;

  return 0;
}

uint64_t get_page_of_virtual_address(uint64_t vaddr) {
  return vaddr / PAGESIZE;
}

uint64_t get_virtual_address_of_page_start(uint64_t page) {
  return page * PAGESIZE;
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
// ---------------------- GARBAGE COLLECTOR ------------------------
// -----------------------------------------------------------------

void emit_fetch_stack_pointer() {
  create_symbol_table_entry(LIBRARY_TABLE, "fetch_stack_pointer", 0, PROCEDURE, UINT64_T, 0, binary_length);

  emit_add(REG_A0, REG_ZR, REG_SP);

  emit_jalr(REG_ZR, REG_RA, 0);
}

void emit_fetch_global_pointer() {
  create_symbol_table_entry(LIBRARY_TABLE, "fetch_global_pointer", 0, PROCEDURE, UINT64_T, 0, binary_length);

  emit_add(REG_A0, REG_ZR, REG_GP);

  emit_jalr(REG_ZR, REG_RA, 0);
}

void emit_fetch_data_segment_size_interface() {
  create_symbol_table_entry(LIBRARY_TABLE, "fetch_data_segment_size", 0, PROCEDURE, UINT64_T, 0, binary_length);

  // up to three instructions needed to load data segment size but is not yet known

  emit_nop();
  emit_nop();
  emit_nop();

  emit_jalr(REG_ZR, REG_RA, 0);
}

void emit_fetch_data_segment_size_implementation(uint64_t fetch_dss_code_location) {
  // set code emission to fetch_data_segment_size
  binary_length = fetch_dss_code_location;

  // assert: emitting no more than 3 instructions

  // load data segment size into A0 (size is independent of entry point)
  load_small_and_medium_integer(REG_A0, allocated_memory);

  // discount NOPs in profile that were generated for fetch_data_segment_size
  ic_addi = ic_addi - (binary_length - fetch_dss_code_location) / INSTRUCTIONSIZE;

  // restore original binary length
  binary_length = code_length;
}

void implement_gc_brk(uint64_t* context) {
  // parameter
  uint64_t program_break;

  // local variable
  uint64_t size;

  program_break = *(get_regs(context) + REG_A0);

  // check if malloc actually asks for more memory
  // if not, fall back to the default brk syscall
  if (program_break > get_program_break(context)) {
    if (debug_syscalls) {
      print("(gc_brk): ");
      print_register_hexadecimal(REG_A0);
    }

    // calculate size by subtracting the current from the new program break
    size = program_break - get_program_break(context);

    if (debug_syscalls) {
      print(" |- ");
      print_register_hexadecimal(REG_A0);
    }

    // yields the pointer to the newly/reused memory (or 0 if failed)
    *(get_regs(context) + REG_A0) = (uint64_t) gc_malloc_implementation(context, size);

    if (debug_syscalls) {
      print(" -> ");
      print_register_hexadecimal(REG_A0);
      println();
    }

    // assert: _bump pointer is last entry in data segment

    // updating the _bump pointer of the program (for consistency)
    store_virtual_memory(get_pt(context), get_heap_seg_start(context) - SIZEOFUINT64, get_program_break(context));

    sc_brk = sc_brk + 1;

    // assert: gc_brk syscall is invoked by selfie's malloc

    // skip next seven instructions of selfie's malloc
    // to avoid using its bump pointer allocator
    set_pc(context, get_pc(context) + 8 * INSTRUCTIONSIZE);
  } else
    implement_brk(context);
}

uint64_t is_gc_library(uint64_t* context) {
  if (context == (uint64_t*) 0)
    return 1;
  else
    return 0;
}

uint64_t* allocate_metadata(uint64_t* context) {
  if (is_gc_library(context))
    return allocate_memory(context, GC_METADATA_SIZE);
  else
    return smalloc(GC_METADATA_SIZE);
}

uint64_t get_stack_start_gc(uint64_t* context) {
  if (is_gc_library(context))
    return fetch_stack_pointer();
  else
    return *(get_regs(context) + REG_SP);
}

uint64_t get_data_seg_start_gc(uint64_t* context) {
  if (is_gc_library(context))
    return gc_data_seg_start;
  else
    return get_data_seg_start(context);
}

uint64_t get_data_seg_end_gc(uint64_t* context) {
  if (is_gc_library(context))
    return gc_data_seg_end;
  else
    // data segment end is here equal to heap segment start
    return get_heap_seg_start(context);
}

uint64_t get_heap_seg_start_gc(uint64_t* context) {
  if (is_gc_library(context))
    return gc_heap_seg_start;
  else
    return get_heap_seg_start(context);
}

uint64_t get_heap_seg_end_gc(uint64_t* context) {
  if (is_gc_library(context))
    return gc_heap_seg_end;
  else
    return get_program_break(context);
}

uint64_t* get_used_list_head_gc(uint64_t* context) {
  if (is_gc_library(context))
    return gc_used_list;
  else
    return get_used_list_head(context);
}

uint64_t* get_free_list_head_gc(uint64_t* context) {
  if (is_gc_library(context))
    return gc_free_list;
  else
    return get_free_list_head(context);
}

uint64_t get_gcs_in_period_gc(uint64_t* context) {
  if (is_gc_library(context))
    return gc_num_gcs_in_period;
  else
    return get_gcs_in_period(context);
}

uint64_t get_gc_enabled_gc(uint64_t* context) {
  if (is_gc_library(context))
    return USE_GC_LIBRARY;
  else
    return get_use_gc_kernel(context);
}

void set_data_and_heap_segments_gc(uint64_t* context) {
  if (is_gc_library(context)) {
    // we use fetch_global_pointer rather than smalloc_system(0)
    // to be accurate even if smalloc has been called before
    gc_data_seg_end   = fetch_global_pointer();
    gc_data_seg_start = gc_data_seg_end - fetch_data_segment_size();

    // assert: smalloc_system(0) returns program break
    gc_heap_seg_start = (uint64_t) smalloc_system(0);
    gc_heap_seg_end   = gc_heap_seg_start;
  }
}

void set_used_list_head_gc(uint64_t* context, uint64_t* used_list_head){
  if (is_gc_library(context))
    gc_used_list = used_list_head;
  else
    set_used_list_head(context, used_list_head);
}

void set_free_list_head_gc(uint64_t* context, uint64_t* free_list_head) {
  if (is_gc_library(context))
    gc_free_list = free_list_head;
  else
    set_free_list_head(context, free_list_head);
}

void set_gcs_in_period_gc(uint64_t* context, uint64_t gcs) {
  if (is_gc_library(context))
    gc_num_gcs_in_period = gcs;
  else
    set_gcs_in_period(context, gcs);
}

void set_gc_enabled_gc(uint64_t* context) {
  if (is_gc_library(context))
    USE_GC_LIBRARY = GC_ENABLED;
  else
    set_use_gc_kernel(context, GC_ENABLED);
}

void gc_init(uint64_t* context) {
  reset_memory_counters();
  reset_gc_counters();

  set_data_and_heap_segments_gc(context);

  set_used_list_head_gc(context, (uint64_t*) 0);
  set_free_list_head_gc(context, (uint64_t*) 0);
  set_gcs_in_period_gc(context, 0);
  set_gc_enabled_gc(context);
}

uint64_t* retrieve_from_free_list(uint64_t* context, uint64_t size) {
  uint64_t* prev_node;
  uint64_t* node;

  prev_node = (uint64_t*) 0;

  node = get_free_list_head_gc(context);

  while (node != (uint64_t*) 0) {
    if (get_metadata_size(node) == size) {
      if (prev_node == (uint64_t*) 0)
        set_free_list_head_gc(context, get_metadata_next(node));
      else
        set_metadata_next(prev_node, get_metadata_next(node));

      set_metadata_next(node, get_used_list_head_gc(context));

      set_used_list_head_gc(context, node);

      return node;
    }

    prev_node = node;

    node = get_metadata_next(node);
  }

  return (uint64_t*) 0;
}

uint64_t gc_load_memory(uint64_t* context, uint64_t address) {
  if (is_gc_library(context))
    return *((uint64_t*) address);
  else
    // assert: is_valid_virtual_address(address) == 1
    if (is_virtual_address_mapped(get_pt(context), address))
      return load_virtual_memory(get_pt(context), address);
    else
      return 0;
}

void gc_store_memory(uint64_t* context, uint64_t address, uint64_t value) {
  if (is_gc_library(context))
    *((uint64_t*) address) = value;
  else
    // assert: is_valid_virtual_address(address) == 1
    if (is_virtual_address_mapped(get_pt(context), address))
      store_virtual_memory(get_pt(context), address, value);
}

void zero_object(uint64_t* context, uint64_t* metadata) {
  uint64_t object_start;
  uint64_t object_end;

  // zero object memory
  object_start = (uint64_t) get_metadata_memory(metadata);
  object_end   = object_start + get_metadata_size(metadata);

  while (object_start < object_end) {
    gc_store_memory(context, object_start, 0);

    object_start = object_start + SIZEOFUINT64;
  }
}

uint64_t* allocate_memory(uint64_t* context, uint64_t size) {
  uint64_t object;
  uint64_t new_program_break;

  if (is_gc_library(context)) {
    object = (uint64_t) smalloc_system(size);

    // assert: smalloc_system is a bump pointer allocator that may reuse memory

    if (object + size > gc_heap_seg_end)
      gc_heap_seg_end = object + size;

    return (uint64_t*) object;
  } else {
    object = get_program_break(context);

    // attempt to update program break

    new_program_break = try_brk(context, object + size);

    if (new_program_break == object + size)
      // attempt to update program break succeeded
      return (uint64_t*) object;
  }

  return (uint64_t*) 0;
}

uint64_t* reuse_memory(uint64_t* context, uint64_t size) {
  uint64_t* metadata;

  // check if reusable memory is available in free list
  metadata = retrieve_from_free_list(context, size);

  if (metadata != (uint64_t*) 0) {
    // zeroing reused memory is optional!
    zero_object(context, metadata);

    return get_metadata_memory(metadata);
  }

  return (uint64_t*) 0;
}

uint64_t* gc_malloc_implementation(uint64_t* context, uint64_t size) {
  uint64_t* object;
  uint64_t* metadata;

  // stack is not zeroed! using two successive gc_malloc calls (library variant)
  // leads to having the same variables as with the previous call and therefore
  // we might have a reachable pointer which is not actually reachable. to fix
  // this, we set these variables to 0.
  object   = (uint64_t*) 0;
  metadata = (uint64_t*) 0;

  // garbage collect
  if (get_gcs_in_period_gc(context) >= GC_PERIOD) {
    gc_collect(context);

    set_gcs_in_period_gc(context, 0);
  } else
    set_gcs_in_period_gc(context, get_gcs_in_period_gc(context) + 1);

  size = round_up(size, SIZEOFUINT64);

  gc_num_mallocated = gc_num_mallocated + 1;
  gc_mem_mallocated = gc_mem_mallocated + size;

  // try reusing memory first
  object = reuse_memory(context, size);

  if (object != (uint64_t*) 0) {
    gc_num_reused_mallocs = gc_num_reused_mallocs + 1;
    gc_mem_reused         = gc_mem_reused + size;

    return object;
  }

  // allocate new object memory if there is no reusable memory
  object = allocate_memory(context, size);

  if (object != (uint64_t*) 0) {
    // allocate metadata for managing object
    metadata = allocate_metadata(context);

    if (metadata != (uint64_t*) 0) {
      set_metadata_next(metadata, get_used_list_head_gc(context));
      set_used_list_head_gc(context, metadata);

      set_metadata_memory(metadata, object);
      set_metadata_size(metadata, size);
      set_metadata_markbit(metadata, GC_MARKBIT_UNREACHABLE);

      gc_num_gced_mallocs   = gc_num_gced_mallocs + 1;
      gc_num_ungced_mallocs = gc_num_ungced_mallocs + 1;

      gc_mem_objects  = gc_mem_objects + size;
      gc_mem_metadata = gc_mem_metadata + GC_METADATA_SIZE;
    } else
      return (uint64_t*) 0;
  } else
    // if object allocation failed discount memory from mallocated total
    gc_mem_mallocated = gc_mem_mallocated - size;

  return object;
}

uint64_t* find_metadata_of_word_at_address(uint64_t* context, uint64_t address) {
  uint64_t* node;
  uint64_t  object;

  // get word at address and check if it may be a pointer
  address = gc_load_memory(context, address);

  if (is_valid_virtual_address(address) == 0)
    return (uint64_t*) 0;

  // pointer below gced heap
  if (address < get_heap_seg_start_gc(context))
    return (uint64_t*) 0;

  // pointer above gced heap
  if (address >= get_heap_seg_end_gc(context))
    return (uint64_t*) 0;

  node = get_used_list_head_gc(context);

  while (node != (uint64_t*) 0) {
    if (address >= (uint64_t) node)
      if (address < ((uint64_t) node + GC_METADATA_SIZE))
        // address points to metadata
        return (uint64_t*) 0;

    object = (uint64_t) get_metadata_memory(node);

    if (address >= object)
      if (address < object + get_metadata_size(node))
        // address points into a gced object
        return node;

    node = get_metadata_next(node);
  }

  return (uint64_t*) 0;
}

void mark_object(uint64_t* context, uint64_t address) {
  uint64_t* metadata;
  uint64_t object_start;
  uint64_t object_end;

  metadata = find_metadata_of_word_at_address(context, address);

  if (metadata == (uint64_t*) 0)
    // address is not a pointer to a gced object
    return;
  else if (get_metadata_markbit(metadata) == GC_MARKBIT_UNREACHABLE)
    set_metadata_markbit(metadata, GC_MARKBIT_REACHABLE);
  else
    // object has already been marked as reachable
    return;

  object_start = (uint64_t) get_metadata_memory(metadata);
  object_end   = object_start + get_metadata_size(metadata);

  while (object_start < object_end) {
    mark_object(context, object_start);

    object_start = object_start + SIZEOFUINT64;
  }
}

void mark_segment(uint64_t* context, uint64_t segment_start, uint64_t segment_end) {
  // assert: segment is not heap

  while (segment_start <= segment_end - WORDSIZE) {
    // assert: is_valid_virtual_address(segment_start) == 1
    // assert: is_virtual_address_mapped(segment_start) == 1
    mark_object(context, segment_start);

    segment_start = segment_start + SIZEOFUINT64;
  }
}

void mark(uint64_t* context) {
  if (get_used_list_head_gc(context) == (uint64_t*) 0)
    return; // if there is no used memory skip collection

  // not traversing registers

  // assert: temporary registers do not contain any reference to gc_heap memory
  // selfie saves all relevant temporary registers on stack, see procedure_prologue().

  // root segments: call stack and data segment

  // traverse call stack
  mark_segment(context, get_stack_start_gc(context), VIRTUALMEMORYSIZE);

  // traverse data segment
  mark_segment(context, get_data_seg_start_gc(context), get_data_seg_end_gc(context));
}

void free_object(uint64_t* context, uint64_t* metadata, uint64_t* prev_metadata) {
  if (prev_metadata == (uint64_t*) 0)
    set_used_list_head_gc(context, get_metadata_next(metadata));
  else
    set_metadata_next(prev_metadata, get_metadata_next(metadata));

  if (GC_REUSE) {
    set_metadata_next(metadata, get_free_list_head_gc(context));

    set_free_list_head_gc(context, metadata);
  }

  gc_mem_collected = gc_mem_collected + get_metadata_size(metadata);
}

void sweep(uint64_t* context) {
  uint64_t* prev_node;
  uint64_t* node;
  uint64_t* next_node;

  prev_node = (uint64_t*) 0;

  node = get_used_list_head_gc(context);

  while (node != (uint64_t*) 0) {
    // next node changes when object is reused
    next_node = get_metadata_next(node);

    if (get_metadata_markbit(node) == GC_MARKBIT_UNREACHABLE)
      free_object(context, node, prev_node);
    else {
      // clear mark bit for next marking
      set_metadata_markbit(node, GC_MARKBIT_UNREACHABLE);

      prev_node = node;
    }

    node = next_node;
  }
}

void gc_collect(uint64_t* context) {
  mark(context);
  sweep(context);

  gc_num_collects = gc_num_collects + 1;
}

void print_gc_profile(uint64_t* context) {
  printf1("%s: --------------------------------------------------------------------------------\n", selfie_name);
  printf5("%s: gc:      %.2uMB requested in %u mallocs (%u gced, %u reuses)\n", selfie_name,
    (char*) fixed_point_ratio(gc_mem_mallocated, MEGABYTE, 2),
    (char*) gc_num_mallocated,
    (char*) gc_num_gced_mallocs,
    (char*) gc_num_reused_mallocs);
  printf4("%s: gc:      %.2uMB(%.2u%%) reused in %u reused mallocs\n", selfie_name,
    (char*) fixed_point_ratio(gc_mem_reused, MEGABYTE, 2),
    (char*) fixed_point_percentage(fixed_point_ratio(gc_mem_mallocated, gc_mem_reused, 4), 4),
    (char*) gc_num_reused_mallocs);
  printf3("%s: gc:      %.2uMB collected in %u gc runs\n", selfie_name,
    (char*) fixed_point_ratio(gc_mem_collected, MEGABYTE, 2),
    (char*) gc_num_collects);
  printf6("%s: gc:      %.2uMB(%.2u%%) allocated in %u mallocs (%u gced, %u ungced)\n", selfie_name,
    (char*) fixed_point_ratio(gc_mem_objects + gc_mem_metadata, MEGABYTE, 2),
    (char*) fixed_point_percentage(fixed_point_ratio(gc_mem_mallocated, gc_mem_objects + gc_mem_metadata, 4), 4),
    (char*) (gc_num_gced_mallocs + gc_num_ungced_mallocs),
    (char*) gc_num_gced_mallocs,
    (char*) gc_num_ungced_mallocs);
  printf4("%s: gc:      %.2uMB(%.2u%%) allocated in %u gced mallocs\n", selfie_name,
    (char*) fixed_point_ratio(gc_mem_objects, MEGABYTE, 2),
    (char*) fixed_point_percentage(fixed_point_ratio(gc_mem_mallocated, gc_mem_objects, 4), 4),
    (char*) gc_num_gced_mallocs);
  printf4("%s: gc:      %.2uMB(%.2u%%) allocated in %u ungced mallocs", selfie_name,
    (char*) fixed_point_ratio(gc_mem_metadata, MEGABYTE, 2),
    (char*) fixed_point_percentage(fixed_point_ratio(gc_mem_mallocated, gc_mem_metadata, 4), 4),
    (char*) gc_num_ungced_mallocs);
  if (is_gc_library(context) == 0)
    print(" (external)");
  println();
}

void gc_arguments() {
  if (string_compare(argument, "-gc")) {
    GC_ON = GC_ENABLED;

    get_argument();
  } else if (string_compare(argument, "-nrgc")) {
    GC_ON    = GC_ENABLED;
    GC_REUSE = GC_DISABLED;

    get_argument();
  } else if (string_compare(argument, "-nr")) {
    GC_REUSE = GC_DISABLED;

    get_argument();
  } else
    GC_ON = GC_DISABLED;
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

void print_code_line_number_for_instruction(uint64_t address, uint64_t offset) {
  if (code_line_number != (uint64_t*) 0)
    printf1("(~%u)", (char*) *(code_line_number + (address - offset) / INSTRUCTIONSIZE));
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
    if (model) {
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

void record_lui_addi_add_sub_mul_divu_remu_sltu_jal_jalr() {
  record_state(*(registers + rd));
}

void do_lui() {
  // load upper immediate

  uint64_t next_rd_value;

  update_register_counters();

  if (rd != REG_ZR) {
    // semantics of lui
    next_rd_value = left_shift(imm, 12);

    if (*(registers + rd) != next_rd_value)
      *(registers + rd) = next_rd_value;
    else
      nopc_lui = nopc_lui + 1;
  } else
    nopc_lui = nopc_lui + 1;

  pc = pc + INSTRUCTIONSIZE;

  ic_lui = ic_lui + 1;
}

void undo_lui_addi_add_sub_mul_divu_remu_sltu_ld_jal_jalr() {
  *(registers + rd) = *(values + (tc % MAX_REPLAY_LENGTH));
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

  uint64_t next_rd_value;

  update_register_counters();

  if (rd != REG_ZR) {
    // semantics of addi
    next_rd_value = *(registers + rs1) + imm;

    if (*(registers + rd) != next_rd_value)
      *(registers + rd) = next_rd_value;
    else
      nopc_addi = nopc_addi + 1;
  } else
    nopc_addi = nopc_addi + 1;

  pc = pc + INSTRUCTIONSIZE;

  ic_addi = ic_addi + 1;
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
  uint64_t next_rd_value;

  update_register_counters();

  if (rd != REG_ZR) {
    // semantics of add
    next_rd_value = *(registers + rs1) + *(registers + rs2);

    if (*(registers + rd) != next_rd_value)
      *(registers + rd) = next_rd_value;
    else
      nopc_add = nopc_add + 1;
  } else
    nopc_add = nopc_add + 1;

  pc = pc + INSTRUCTIONSIZE;

  ic_add = ic_add + 1;
}

void do_sub() {
  uint64_t next_rd_value;

  update_register_counters();

  if (rd != REG_ZR) {
    // semantics of sub
    next_rd_value = *(registers + rs1) - *(registers + rs2);

    if (*(registers + rd) != next_rd_value)
      *(registers + rd) = next_rd_value;
    else
      nopc_sub = nopc_sub + 1;
  } else
    nopc_sub = nopc_sub + 1;

  pc = pc + INSTRUCTIONSIZE;

  ic_sub = ic_sub + 1;
}

void do_mul() {
  uint64_t next_rd_value;

  update_register_counters();

  if (rd != REG_ZR) {
    // semantics of mul
    next_rd_value = *(registers + rs1) * *(registers + rs2);

    // TODO: support of 128-bit resolution

    if (*(registers + rd) != next_rd_value)
      *(registers + rd) = next_rd_value;
    else
      nopc_mul = nopc_mul + 1;
  } else
    nopc_mul = nopc_mul + 1;

  pc = pc + INSTRUCTIONSIZE;

  ic_mul = ic_mul + 1;
}

void do_divu() {
  // division unsigned

  uint64_t next_rd_value;

  if (*(registers + rs2) != 0) {
    update_register_counters();

    if (rd != REG_ZR) {
      // semantics of divu
      next_rd_value = *(registers + rs1) / *(registers + rs2);

      if (*(registers + rd) != next_rd_value)
        *(registers + rd) = next_rd_value;
      else
        nopc_divu = nopc_divu + 1;
    } else
      nopc_divu = nopc_divu + 1;

    pc = pc + INSTRUCTIONSIZE;

    ic_divu = ic_divu + 1;
  } else
    throw_exception(EXCEPTION_DIVISIONBYZERO, pc);
}

void do_remu() {
  // remainder unsigned

  uint64_t next_rd_value;

  if (*(registers + rs2) != 0) {
    update_register_counters();

    if (rd != REG_ZR) {
      // semantics of remu
      next_rd_value = *(registers + rs1) % *(registers + rs2);

      if (*(registers + rd) != next_rd_value)
        *(registers + rd) = next_rd_value;
      else
        nopc_remu = nopc_remu + 1;
    } else
      nopc_remu = nopc_remu + 1;

    pc = pc + INSTRUCTIONSIZE;

    ic_remu = ic_remu + 1;
  } else
    throw_exception(EXCEPTION_DIVISIONBYZERO, pc);
}

void do_sltu() {
  // set on less than unsigned

  uint64_t next_rd_value;

  update_register_counters();

  if (rd != REG_ZR) {
    // semantics of sltu
    if (*(registers + rs1) < *(registers + rs2))
      next_rd_value = 1;
    else
      next_rd_value = 0;

    if (*(registers + rd) != next_rd_value)
      *(registers + rd) = next_rd_value;
    else
      nopc_sltu = nopc_sltu + 1;
  } else
    nopc_sltu = nopc_sltu + 1;

  pc = pc + INSTRUCTIONSIZE;

  ic_sltu = ic_sltu + 1;
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
  uint64_t next_rd_value;
  uint64_t a;

  // load double word

  vaddr = *(registers + rs1) + imm;

  if (is_valid_virtual_address(vaddr)) {
    if (is_valid_segment_read(vaddr)) {
      if (is_virtual_address_mapped(pt, vaddr)) {
        update_register_counters();

        if (rd != REG_ZR) {
          // semantics of ld
          next_rd_value = load_virtual_memory(pt, vaddr);

          if (*(registers + rd) != next_rd_value)
            *(registers + rd) = next_rd_value;
          else
            nopc_ld = nopc_ld + 1;
        } else
          nopc_ld = nopc_ld + 1;

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
      throw_exception(EXCEPTION_SEGMENTATIONFAULT, vaddr);
  } else
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);

  return vaddr;
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
    if (is_valid_segment_write(vaddr)) {
      if (is_virtual_address_mapped(pt, vaddr)) {
        update_register_counters();

        // semantics of sd
        if (load_virtual_memory(pt, vaddr) != *(registers + rs2))
          store_virtual_memory(pt, vaddr, *(registers + rs2));
        else
          nopc_sd = nopc_sd + 1;

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
      throw_exception(EXCEPTION_SEGMENTATIONFAULT, vaddr);
  } else
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);

  return vaddr;
}

void undo_sd() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  store_virtual_memory(pt, vaddr, *(values + (tc % MAX_REPLAY_LENGTH)));
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

  update_register_counters();

  // semantics of beq
  if (*(registers + rs1) == *(registers + rs2))
    pc = pc + imm;
  else {
    pc = pc + INSTRUCTIONSIZE;

    nopc_beq = nopc_beq + 1;
  }

  ic_beq = ic_beq + 1;
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

  update_register_counters();

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
  } else {
    // just jump forward
    pc = pc + imm;

    if (imm == INSTRUCTIONSIZE)
      nopc_jal = nopc_jal + 1;
  }

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

  update_register_counters();

  // prepare jump rs1-relative with LSB reset
  next_pc = left_shift(right_shift(*(registers + rs1) + imm, 1), 1);

  if (rd == REG_ZR) {
    // just jump
    if (next_pc == pc + INSTRUCTIONSIZE)
      nopc_jalr = nopc_jalr + 1;

    pc = next_pc;
  } else {
    // first link, then jump

    // link to next instruction (works even if rd == rs1)
    *(registers + rd) = pc + INSTRUCTIONSIZE;

    // jump
    pc = next_pc;
  }

  ic_jalr = ic_jalr + 1;
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

    // TODO: print ecall details
    println();

    pc = pc + INSTRUCTIONSIZE;
  } else if (*(registers + REG_A7) == SYSCALL_SWITCH)
    if (record) {
      printf1("%s: context switching during recording is unsupported\n", selfie_name);

      exit(EXITCODE_UNSUPPORTEDSYSCALL);
    } else if (symbolic) {
      printf1("%s: context switching during symbolic execution is unsupported\n", selfie_name);

      exit(EXITCODE_UNSUPPORTEDSYSCALL);
    } else {
      pc = pc + INSTRUCTIONSIZE;

      implement_switch();
    }
  else
    // all system calls other than switch are handled by exception
    throw_exception(EXCEPTION_SYSCALL, *(registers + REG_A7));
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
    printf1("(~%u)", (char*) *(data_line_number + (pc - code_length) / SIZEOFUINT64));
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
// -------------------------- DISASSEMBLER -------------------------
// -----------------------------------------------------------------

void print_instruction() {
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
    print_instruction();
    println();

    pc = pc + INSTRUCTIONSIZE;
  }

  while (pc < binary_length) {
    data = load_data(pc);

    print_data(data);
    println();

    pc = pc + WORDSIZE;
  }

  disassemble_verbose = 0;

  output_name = (char*) 0;
  output_fd   = 1;

  printf5("%s: %u characters of assembly with %u instructions and %u bytes of data written into %s\n", selfie_name,
    (char*) number_of_written_characters,
    (char*) (code_length / INSTRUCTIONSIZE),
    (char*) (binary_length - code_length),
    assembly_name);
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

  redo   = 0;
  record = 1;
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

void print_register_value(uint64_t reg) {
  if (is_system_register(reg))
    print_register_hexadecimal(reg);
  else
    printf3("%s=%d(%x)", get_register_name(reg), (char*) *(registers + reg), (char*) *(registers + reg));
}

void print_exception(uint64_t exception, uint64_t fault) {
  print((char*) *(EXCEPTIONS + exception));

  if (exception == EXCEPTION_PAGEFAULT)
    printf1(" at page %p", (char*) fault);
  else if (exception == EXCEPTION_SEGMENTATIONFAULT)
    printf1(" at address %p", (char*) fault);
  else if (exception == EXCEPTION_SYSCALL)
    printf1(" ID %u", (char*) fault);
  else if (exception == EXCEPTION_DIVISIONBYZERO)
    printf1(" at address %p", (char*) fault);
  else if (exception == EXCEPTION_INVALIDADDRESS)
    printf1(" %p", (char*) fault);
  else if (exception == EXCEPTION_UNKNOWNINSTRUCTION)
    printf1(" at address %p", (char*) fault);
  else if (exception == EXCEPTION_UNINITIALIZEDREGISTER) {
    print(" ");print_register_name(fault);
  }
}

void throw_exception(uint64_t exception, uint64_t fault) {
  if (get_exception(current_context) != EXCEPTION_NOEXCEPTION)
    if (get_exception(current_context) != exception) {
      printf2("%s: context %p throws exception: ", selfie_name, (char*) current_context);
      print_exception(exception, fault);
      print(" in presence of existing exception: ");
      print_exception(get_exception(current_context), get_fault(current_context));
      println();

      exit(EXITCODE_MULTIPLEEXCEPTIONERROR);
    }

  set_exception(current_context, exception);
  set_fault(current_context, fault);

  trap = 1;

  if (debug_exception) {
    printf2("%s: context %p throws exception: ", selfie_name, (char*) current_context);
    print_exception(exception, fault);
    println();
  }
}

void fetch() {
  // assert: is_virtual_address_mapped(pt, pc) == 1

  if (is_valid_code_address(current_context, pc))
    if (pc % WORDSIZE == 0)
      ir = get_low_word(load_virtual_memory(pt, pc));
    else
      ir = get_high_word(load_virtual_memory(pt, pc - INSTRUCTIONSIZE));
  else {
    ir = encode_nop();

    throw_exception(EXCEPTION_SEGMENTATIONFAULT, pc);
  }
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
      throw_exception(EXCEPTION_UNKNOWNINSTRUCTION, pc);
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
    record_lui_addi_add_sub_mul_divu_remu_sltu_jal_jalr();
    do_addi();
  } else if (is == LD) {
    record_ld();
    do_ld();
  } else if (is == SD) {
    record_sd();
    do_sd();
  } else if (is == ADD) {
    record_lui_addi_add_sub_mul_divu_remu_sltu_jal_jalr();
    do_add();
  } else if (is == SUB) {
    record_lui_addi_add_sub_mul_divu_remu_sltu_jal_jalr();
    do_sub();
  } else if (is == MUL) {
    record_lui_addi_add_sub_mul_divu_remu_sltu_jal_jalr();
    do_mul();
  } else if (is == DIVU) {
    record_lui_addi_add_sub_mul_divu_remu_sltu_jal_jalr();
    do_divu();
  } else if (is == REMU) {
    record_lui_addi_add_sub_mul_divu_remu_sltu_jal_jalr();
    do_remu();
  } else if (is == SLTU) {
    record_lui_addi_add_sub_mul_divu_remu_sltu_jal_jalr();
    do_sltu();
  } else if (is == BEQ) {
    record_beq();
    do_beq();
  } else if (is == JAL) {
    record_lui_addi_add_sub_mul_divu_remu_sltu_jal_jalr();
    do_jal();
  } else if (is == JALR) {
    record_lui_addi_add_sub_mul_divu_remu_sltu_jal_jalr();
    do_jalr();
  } else if (is == LUI) {
    record_lui_addi_add_sub_mul_divu_remu_sltu_jal_jalr();
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
  print_instruction();

  // assert: 1 <= is <= number of RISC-U instructions
  if (is == ADDI) {
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

    printf3(",%u(%.2u%%)@%x", (char*) c, (char*) fixed_point_percentage(fixed_point_ratio(total, c, 4), 4), (char*) a);
    print_code_line_number_for_instruction(a, 0);

    return c;
  } else {
    print(",0(0.00%)");

    return 0;
  }
}

void print_per_instruction_profile(char* message, uint64_t total, uint64_t* counters) {
  printf3("%s: %s%u", selfie_name, message, (char*) total);
  print_per_instruction_counter(total, counters, print_per_instruction_counter(total, counters, print_per_instruction_counter(total, counters, UINT64_MAX)));
  println();
}

void print_access_profile(char* message, char* padding, uint64_t reads, uint64_t writes) {
  if (reads + writes > 0) {
    if (writes == 0)
      // may happen in read-only memory segments
      writes = 1;

    printf7("%s: %s%s%d,%d,%d[%.2u]\n", selfie_name, message, padding,
      (char*) (reads + writes), (char*) reads, (char*) writes, (char*) fixed_point_ratio(reads, writes, 2));
  }
}

void print_per_register_profile(uint64_t reg) {
  print_access_profile(get_register_name(reg), " register:   ", *(reads_per_register + reg), *(writes_per_register + reg));
}

void print_register_memory_profile() {
  uint64_t reg;

  printf1("%s: CPU+memory:    reads+writes,reads,writes[reads/writes]\n", selfie_name);

  print_access_profile("heap segment:  ", "", heap_reads, heap_writes);

  print_per_register_profile(REG_GP);
  print_access_profile("data segment:  ", "", data_reads, data_writes);

  reg = 1;

  while (reg < NUMBEROFREGISTERS) {
    if (is_stack_register(reg)) {
      stack_register_reads  = stack_register_reads + *(reads_per_register + reg);
      stack_register_writes = stack_register_writes + *(writes_per_register + reg);

      print_per_register_profile(reg);
    }

    reg = reg + 1;
  }

  print_access_profile("stack total:   ", "", stack_register_reads, stack_register_writes);
  print_access_profile("stack segment: ", "", stack_reads, stack_writes);

  reg = 1;

  while (reg < NUMBEROFREGISTERS) {
    if (is_argument_register(reg)) {
      argument_register_reads  = argument_register_reads + *(reads_per_register + reg);
      argument_register_writes = argument_register_writes + *(writes_per_register + reg);

      print_per_register_profile(reg);
    }

    reg = reg + 1;
  }

  print_access_profile("args total:    ", "", argument_register_reads, argument_register_writes);

  reg = 1;

  while (reg < NUMBEROFREGISTERS) {
    if (is_temporary_register(reg)) {
      temporary_register_reads  = temporary_register_reads + *(reads_per_register + reg);
      temporary_register_writes = temporary_register_writes + *(writes_per_register + reg);

      print_per_register_profile(reg);
    }

    reg = reg + 1;
  }

  print_access_profile("temps total:   ", "", temporary_register_reads, temporary_register_writes);
}

void print_profile(uint64_t* context) {
  printf1("%s: --------------------------------------------------------------------------------\n", selfie_name);
  printf3("%s: summary: %u executed instructions [%.2u%% nops]\n", selfie_name,
    (char*) get_total_number_of_instructions(),
    (char*) get_total_percentage_of_nops());
  printf3("%s:          %.2uMB allocated in %u mallocs\n", selfie_name,
    (char*) fixed_point_ratio(mc_brk, MEGABYTE, 2),
    (char*) sc_brk);
  printf4("%s:          %.2uMB(%.2u%% of %.2uMB) actually accessed\n", selfie_name,
    (char*) fixed_point_ratio(mc_mapped_heap, MEGABYTE, 2),
    (char*) fixed_point_percentage(fixed_point_ratio(round_up(mc_brk, PAGESIZE), mc_mapped_heap, 4), 4),
    (char*) fixed_point_ratio(mc_brk, MEGABYTE, 2));
  printf4("%s:          %.2uMB(%.2u%% of %uMB) mapped memory\n", selfie_name,
    (char*) fixed_point_ratio(pused(), MEGABYTE, 2),
    (char*) fixed_point_percentage(fixed_point_ratio(total_page_frame_memory, pused(), 4), 4),
    (char*) (total_page_frame_memory / MEGABYTE));

  if (GC_ON)
    print_gc_profile(context);

  if (get_total_number_of_instructions() > 0) {
    printf1("%s: --------------------------------------------------------------------------------\n", selfie_name);
    print_instruction_counters();

    if (code_line_number != (uint64_t*) 0)
      printf1("%s: profile: total,max(ratio%%)@addr(line#),2max,3max\n", selfie_name);
    else
      printf1("%s: profile: total,max(ratio%%)@addr,2max,3max\n", selfie_name);

    print_per_instruction_profile("calls:   ", calls, calls_per_procedure);
    print_per_instruction_profile("loops:   ", iterations, iterations_per_loop);
    print_per_instruction_profile("loads:   ", ic_ld, loads_per_instruction);
    print_per_instruction_profile("stores:  ", ic_sd, stores_per_instruction);

    print_register_memory_profile();
  }

  printf1("%s: --------------------------------------------------------------------------------\n", selfie_name);
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
  // some fields are set in boot loader or when context switching

  // allocate zeroed memory for general purpose registers
  // TODO: reuse memory
  set_regs(context, zmalloc(NUMBEROFREGISTERS * SIZEOFUINT64));

  // allocate zeroed memory for page table
  // TODO: save and reuse memory for page table
  if (PAGETABLETREE == 0)
    // for a 4GB-virtual-memory page table with
    // 4KB pages and 64-bit pointers, allocate
    // 8MB = 2^23 ((2^32 / 2^12) * 2^3) bytes to
    // accommodate 2^20 (2^32 / 2^12) PTEs
    set_pt(context, zmalloc(NUMBEROFPAGES * SIZEOFUINT64STAR));
  else
    // for the root node (page directory), allocate
    // 16KB = 2^14 (2^32 / 2^12 / 2^9 * 2^3) bytes to
    // accommodate 2^11 ((2^32 / 2^12) / 2^9) root PDEs
    // pointing to 4KB leaf nodes (page tables) that
    // each accommodate 2^9 (2^12 / 2^3) leaf PTEs
    set_pt(context, zmalloc(NUMBEROFPAGES / NUMBEROFLEAFPTES * SIZEOFUINT64STAR));

  // reset page table cache
  set_lowest_lo_page(context, 0);
  set_highest_lo_page(context, get_lowest_lo_page(context));
  set_lowest_hi_page(context, get_page_of_virtual_address(VIRTUALMEMORYSIZE - WORDSIZE));
  set_highest_hi_page(context, get_lowest_hi_page(context));

  if (parent != MY_CONTEXT) {
    set_code_seg_start(context, load_virtual_memory(get_pt(parent), code_seg_start(vctxt)));
    set_data_seg_start(context, load_virtual_memory(get_pt(parent), data_seg_start(vctxt)));
    set_heap_seg_start(context, load_virtual_memory(get_pt(parent), heap_seg_start(vctxt)));

    // TODO: cache name
    set_name(context, (char*) 0);
  } else {
    set_exception(context, EXCEPTION_NOEXCEPTION);
    set_fault(context, 0);

    set_exit_code(context, EXITCODE_NOERROR);
  }

  set_parent(context, parent);
  set_virtual_context(context, vctxt);

  // garbage collector
  set_used_list_head(context, (uint64_t*) 0);
  set_free_list_head(context, (uint64_t*) 0);
  set_gcs_in_period(context, 0);
  set_use_gc_kernel(context, GC_DISABLED);
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

  if (get_parent(context) != MY_CONTEXT) {
    // upload changes in context to virtual context in parent address space
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
    store_virtual_memory(parent_table, fault(vctxt), get_fault(context));
    store_virtual_memory(parent_table, exit_code(vctxt), get_exit_code(context));

    // garbage collector state (only necessary if context is gced by different gcs)

    store_virtual_memory(parent_table, used_list_head(vctxt), (uint64_t) get_used_list_head(context));
    store_virtual_memory(parent_table, free_list_head(vctxt), (uint64_t) get_free_list_head(context));
    store_virtual_memory(parent_table, gcs_in_period(vctxt), get_gcs_in_period(context));
    store_virtual_memory(parent_table, use_gc_kernel(vctxt), get_use_gc_kernel(context));
  }
}

uint64_t lowest_page(uint64_t page, uint64_t lo) {
  if (page < lo)
    return page;
  else
    return lo;
}

uint64_t highest_page(uint64_t page, uint64_t hi) {
  if (page >= hi)
    // only lo <= page < hi will be cached
    return page + 1;
  else
    return hi;
}

void map_page(uint64_t* context, uint64_t page, uint64_t frame) {
  uint64_t* table;

  if (frame != 0) {
    table = get_pt(context);

    if (get_frame_for_page(table, page) == 0) {
      set_PTE_for_page(table, page, frame);

      // exploit spatial locality in page table caching
      if (page <= get_page_of_virtual_address(get_program_break(context) - WORDSIZE)) {
        set_lowest_lo_page(context, lowest_page(page, get_lowest_lo_page(context)));
        set_highest_lo_page(context, highest_page(page, get_highest_lo_page(context)));
      } else {
        set_lowest_hi_page(context, lowest_page(page, get_lowest_hi_page(context)));
        set_highest_hi_page(context, highest_page(page, get_highest_hi_page(context)));
      }
    } // else assert: frame == get_frame_for_page(table, page)
  }

  if (debug_map) {
    printf1("%s: page ", selfie_name);
    print_hexadecimal(page, 4);
    printf2(" mapped to frame %p in context %p\n", (char*) frame, (char*) context);
  }
}

void restore_region(uint64_t* context, uint64_t* table, uint64_t* parent_table, uint64_t lo, uint64_t hi) {
  uint64_t frame;

  while (lo < hi) {
    if (is_virtual_address_mapped(parent_table, (uint64_t) get_PTE_address_for_page(parent_table, table, lo))) {
      frame = load_virtual_memory(parent_table, (uint64_t) get_PTE_address_for_page(parent_table, table, lo));

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
    // download changes in virtual context in parent address space to context
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
    set_fault(context, load_virtual_memory(parent_table, fault(vctxt)));

    set_exit_code(context, load_virtual_memory(parent_table, exit_code(vctxt)));

    table = (uint64_t*) load_virtual_memory(parent_table, page_table(vctxt));

    // assert: virtual context page table is only mapped from beginning up and end down

    lo = load_virtual_memory(parent_table, lowest_lo_page(vctxt));
    hi = load_virtual_memory(parent_table, highest_lo_page(vctxt));

    restore_region(context, table, parent_table, lo, hi);

    store_virtual_memory(parent_table, lowest_lo_page(vctxt), hi);

    lo = load_virtual_memory(parent_table, lowest_hi_page(vctxt));
    hi = load_virtual_memory(parent_table, highest_hi_page(vctxt));

    restore_region(context, table, parent_table, lo, hi);

    store_virtual_memory(parent_table, highest_hi_page(vctxt), lo);

    // garbage collector state (only necessary if context is gced by different gcs)

    set_used_list_head(context, (uint64_t*) load_virtual_memory(parent_table, used_list_head(vctxt)));
    set_free_list_head(context, (uint64_t*) load_virtual_memory(parent_table, free_list_head(vctxt)));
    set_gcs_in_period(context, load_virtual_memory(parent_table, gcs_in_period(vctxt)));
    set_use_gc_kernel(context, load_virtual_memory(parent_table, use_gc_kernel(vctxt)));
  }

  // restore machine state
  pc        = get_pc(context);
  registers = get_regs(context);
  pt        = get_pt(context);
}

uint64_t is_valid_code_address(uint64_t* context, uint64_t vaddr) {
  // is address in code segment?
  if (vaddr >= get_code_seg_start(context))
    if (vaddr < get_data_seg_start(context))
      // code must be single-word-addressed
      if (vaddr % INSTRUCTIONSIZE == 0)
        return 1;

  return 0;
}

uint64_t is_valid_data_address(uint64_t* context, uint64_t vaddr) {
  // is address in data segment?
  if (vaddr >= get_data_seg_start(context))
    if (vaddr < get_heap_seg_start(context))
      // assert: is_valid_virtual_address(vaddr) == 1
      return 1;

  return 0;
}

uint64_t is_valid_stack_address(uint64_t* context, uint64_t vaddr) {
  // is address in the stack?
  if (vaddr >= *(get_regs(context) + REG_SP))
    if (vaddr <= VIRTUALMEMORYSIZE - WORDSIZE)
      // assert: is_valid_virtual_address(vaddr) == 1
      return 1;

  return 0;
}

uint64_t is_valid_heap_address(uint64_t* context, uint64_t vaddr) {
  // is address in the heap?
  if (vaddr >= get_heap_seg_start(context))
    if (vaddr < get_program_break(context))
      // assert: is_valid_virtual_address(vaddr) == 1
      return 1;

  return 0;
}

uint64_t is_valid_data_stack_heap_address(uint64_t* context, uint64_t vaddr) {
  if (is_valid_data_address(context, vaddr))
    return 1;
  else if (is_valid_stack_address(context, vaddr))
    return 1;
  else if (is_valid_heap_address(context, vaddr))
    return 1;
  else
    return 0;
}

uint64_t is_valid_segment_read(uint64_t vaddr) {
  if (is_valid_data_address(current_context, vaddr)) {
    data_reads = data_reads + 1;

    return 1;
  } else if (is_valid_stack_address(current_context, vaddr)) {
    stack_reads = stack_reads + 1;

    return 1;
  } else if (is_valid_heap_address(current_context, vaddr)) {
    heap_reads = heap_reads + 1;

    return 1;
  } else
    return 0;
}

uint64_t is_valid_segment_write(uint64_t vaddr) {
  if (is_valid_data_address(current_context, vaddr)) {
    data_writes = data_writes + 1;

    return 1;
  } else if (is_valid_stack_address(current_context, vaddr)) {
    stack_writes = stack_writes + 1;

    return 1;
  } else if (is_valid_heap_address(current_context, vaddr)) {
    heap_writes = heap_writes + 1;

    return 1;
  } else
    return 0;
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

uint64_t pavailable() {
  if (free_page_frame_memory > 0)
    return 1;
  else if (allocated_page_frame_memory + MEGABYTE <= total_page_frame_memory)
    return 1;
  else
    return 0;
}

uint64_t pexcess() {
  if (pavailable())
    return 1;
  else if (allocated_page_frame_memory + MEGABYTE <= 2 * total_page_frame_memory)
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

  // assert: total_page_frame_memory is equal to or a multiple of MEGABYTE
  // assert: PAGESIZE is a factor of MEGABYTE strictly less than MEGABYTE

  if (free_page_frame_memory == 0) {
    if (pexcess()) {
      free_page_frame_memory = MEGABYTE;

      // on boot level zero allocate zeroed memory
      block = (uint64_t) zmalloc(free_page_frame_memory);

      allocated_page_frame_memory = allocated_page_frame_memory + free_page_frame_memory;

      // page frames must be page-aligned to work as page table index
      next_page_frame = round_up(block, PAGESIZE);

      if (next_page_frame > block)
        // losing one page frame to fragmentation
        free_page_frame_memory = free_page_frame_memory - PAGESIZE;
    } else {
      printf1("%s: palloc out of physical memory\n", selfie_name);

      exit(EXITCODE_OUTOFPHYSICALMEMORY);
    }
  }

  frame = next_page_frame;

  next_page_frame = next_page_frame + PAGESIZE;

  free_page_frame_memory = free_page_frame_memory - PAGESIZE;

  // strictly, touching is only necessary on boot levels higher than 0
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

  // assert: entry_point is multiple of PAGESIZE and WORDSIZE

  set_pc(context, entry_point);

  // setting up page table cache

  set_lowest_lo_page(context, get_page_of_virtual_address(entry_point));
  set_highest_lo_page(context, get_lowest_lo_page(context));

  // setting up memory segments

  set_code_seg_start(context, entry_point);
  set_data_seg_start(context, entry_point + code_length);
  set_heap_seg_start(context, entry_point + binary_length);
  set_program_break(context, get_heap_seg_start(context));

  baddr = 0;

  while (baddr < binary_length) {
    map_and_store(context, entry_point + baddr, load_data(baddr));

    baddr = baddr + WORDSIZE;
  }

  set_name(context, binary_name);
}

uint64_t up_load_string(uint64_t* context, char* s, uint64_t SP) {
  uint64_t bytes;
  uint64_t i;

  bytes = round_up(string_length(s) + 1, WORDSIZE);

  // allocate memory for storing string
  SP = SP - bytes;

  i = 0;

  while (i < bytes) {
    // CAUTION: at boot levels higher than 0, s is only accessible
    // in C* at machine word granularity, not individual characters
    map_and_store(context, SP + i, *((uint64_t*) s));

    s = (char*) ((uint64_t*) s + 1);

    i = i + WORDSIZE;
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
  SP = SP - WORDSIZE;

  // push null value to terminate env table
  map_and_store(context, SP, 0);

  // allocate memory for termination of argv table
  SP = SP - WORDSIZE;

  // push null value to terminate argv table
  map_and_store(context, SP, 0);

  // assert: i == argc

  // push argv table onto the stack
  while (i > 0) {
    // allocate memory for argv table entry
    SP = SP - WORDSIZE;

    i = i - 1;

    // push argv table entry
    map_and_store(context, SP, *(vargv + i));
  }

  // allocate memory for argc
  SP = SP - WORDSIZE;

  // push argc
  map_and_store(context, SP, argc);

  // store stack pointer value in stack pointer register
  *(get_regs(context) + REG_SP) = SP;

  // initialize frame pointer register for completeness (redundant)
  *(get_regs(context) + REG_S0) = 0;
}

uint64_t handle_system_call(uint64_t* context) {
  uint64_t a7;

  set_exception(context, EXCEPTION_NOEXCEPTION);

  a7 = *(get_regs(context) + REG_A7);

  if (a7 == SYSCALL_BRK) {
    if (get_gc_enabled_gc(context))
      implement_gc_brk(context);
    else
      implement_brk(context);
  } else if (a7 == SYSCALL_READ)
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
    printf2("%s: unknown system call %u\n", selfie_name, (char*) a7);

    set_exit_code(context, EXITCODE_UNKNOWNSYSCALL);

    return EXIT;
  }

  return DONOTEXIT;
}

uint64_t handle_page_fault(uint64_t* context) {
  uint64_t page;

  set_exception(context, EXCEPTION_NOEXCEPTION);

  page = get_fault(context);

  // TODO: reuse frames
  map_page(context, page, (uint64_t) palloc());

  if (is_valid_heap_address(context, get_virtual_address_of_page_start(page)))
    mc_mapped_heap = mc_mapped_heap + PAGESIZE;

  return DONOTEXIT;
}

uint64_t handle_division_by_zero(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  if (record) {
    printf1("%s: division by zero, replaying...\n", selfie_name);

    replay_trace();

    set_exit_code(context, EXITCODE_NOERROR);
  } else {
    printf1("%s: division by zero\n", selfie_name);

    set_exit_code(context, EXITCODE_DIVISIONBYZERO);
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
  else if (exception == EXCEPTION_TIMER)
    return handle_timer(context);
  else {
    printf2("%s: context %s threw uncaught exception: ", selfie_name, get_name(context));
    print_exception(exception, get_fault(context));
    println();

    set_exit_code(context, EXITCODE_UNCAUGHTEXCEPTION);

    return EXIT;
  }
}

uint64_t mipster(uint64_t* to_context) {
  uint64_t timeout;
  uint64_t* from_context;

  print("mipster\n");
  printf1("%s: >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n", selfie_name);

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
  printf1("%s: >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n", selfie_name);

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

  printf2("mixter (%u%% mipster/%u%% hypster)\n", (char*) mix, (char*) (100 - mix));
  printf1("%s: >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n", selfie_name);

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
        printf2("%s: context %s threw uncaught exception: ", selfie_name, get_name(from_context));
        print_exception(get_exception(from_context), get_fault(from_context));
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
  printf1("%s: >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n", selfie_name);

  // virtual is like physical memory in initial context up to memory size
  // by mapping unmapped pages (for the heap) to all available page frames
  // CAUTION: consumes memory even when not accessed
  map_unmapped_pages(to_context);

  // does not handle page faults, works only until running out of mapped pages
  return minmob(to_context);
}

uint64_t mobster(uint64_t* to_context) {
  print("mobster\n");
  printf1("%s: >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n", selfie_name);

  // does not handle page faults, relies on fancy hypsters to do that
  return minmob(to_context);
}

char* replace_extension(char* filename, char* extension) {
  char* s;
  uint64_t i;
  uint64_t c;

  // assert: string_length(filename) + 1 + string_length(extension) < MAX_FILENAME_LENGTH

  s = string_alloc(string_length(filename) + 1 + string_length(extension));

  // start reading at end of filename
  i = string_length(filename);

  c = load_character(filename, i);

  // look for extension
  while (c != '.') {
    if (c == '/')
      i = 0;

    if (i > 0) {
      i = i - 1;

      c = load_character(filename, i);
    } else
      c = '.';
  }

  // filename has no extension
  if (i == 0)
    // writing filename plus extension into s
    sprintf2(s, "%s.%s", filename, extension);
  else {
    // assert: s is zeroed and thus null-terminated

    // copy filename without extension and null-terminator into s
    while (i > 0) {
      i = i - 1;

      store_character(s, i, load_character(filename, i));
    }

    // writing s plus extension into s
    sprintf2(s, "%s.%s", s, extension);
  }

  return s;
}

void boot_loader(uint64_t* context) {
  up_load_binary(context);

  // pass binary name as first argument by replacing next argument
  set_argument(binary_name);

  up_load_arguments(context, number_of_remaining_arguments(), remaining_arguments());
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

  init_memory(atoi(peek_argument(0)));

  current_context = create_context(MY_CONTEXT, 0);

  // assert: number_of_remaining_arguments() > 0

  boot_loader(current_context);

  printf3("%s: selfie executing %s with %uMB physical memory", selfie_name,
    binary_name,
    (char*) (total_page_frame_memory / MEGABYTE));

  if (GC_ON) {
    gc_init(current_context);

    printf1(", gcing every %d mallocs, ", (char*) GC_PERIOD);
    if (GC_REUSE) print("reusing memory"); else print("not reusing memory");
  }

  if (machine == DIPSTER) {
    debug          = 1;
    debug_syscalls = 1;
    print(", debugger");
  } else if (machine == RIPSTER) {
    debug  = 1;
    record = 1;
    init_replay_engine();
    print(", replay");
  } else if (machine == HYPSTER) {
    if (BOOTLEVELZERO)
      // no hypster on boot level zero
      machine = MIPSTER;
  }

  print(" on ");

  run = 1;

  if (machine == MIPSTER)
    exit_code = mipster(current_context);
  else if (machine == DIPSTER)
    exit_code = mipster(current_context);
  else if (machine == RIPSTER)
    exit_code = mipster(current_context);
  else if (machine == MINSTER)
    exit_code = minster(current_context);
  else if (machine == MOBSTER)
    exit_code = mobster(current_context);
  else if (machine == HYPSTER)
    exit_code = hypster(current_context);
  else
    // change 0 to anywhere between 0% to 100% mipster
    exit_code = mixter(current_context, 0);

  run = 0;

  record = 0;

  debug_syscalls = 0;
  debug          = 0;

  printf3("%s: selfie terminating %s with exit code %d\n", selfie_name,
    get_name(current_context),
    (char*) sign_extend(exit_code, SYSCALL_BITWIDTH));

  if (machine != HYPSTER)
    print_profile(current_context);
  else if (GC_ON)
    print_gc_profile(current_context);

  return exit_code;
}

// -----------------------------------------------------------------
// ------------------- CONSOLE ARGUMENT SCANNER --------------------
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

uint64_t no_or_bad_or_more_arguments(uint64_t exit_code) {
  if (exit_code == EXITCODE_NOARGUMENTS)
    return 1;
  else if (exit_code == EXITCODE_BADARGUMENTS)
    return 1;
  else if (exit_code == EXITCODE_MOREARGUMENTS)
    return 1;
  else
    return 0;
}

void print_synopsis(char* extras) {
  printf2("synopsis: %s { -c { source } | -o binary | [ -s | -S ] assembly | -l binary }%s\n", selfie_name, extras);
}

// -----------------------------------------------------------------
// ----------------------------- SELFIE ----------------------------
// -----------------------------------------------------------------

uint64_t selfie(uint64_t extras) {
  if (number_of_remaining_arguments() == 0)
    return EXITCODE_NOARGUMENTS;
  else {
    init_scanner();
    init_register();
    init_interpreter();

    while (number_of_remaining_arguments() > 0) {
      get_argument();

      gc_arguments();

      if (string_compare(argument, "-c"))
        selfie_compile();
      else if (number_of_remaining_arguments() == 0)
        // remaining options have at least one argument
        return EXITCODE_BADARGUMENTS;
      else if (string_compare(argument, "-o"))
        selfie_output(get_argument());
      else if (string_compare(argument, "-s"))
        selfie_disassemble(0);
      else if (string_compare(argument, "-S"))
        selfie_disassemble(1);
      else if (string_compare(argument, "-l"))
        selfie_load();
      else if (extras == 0) {
        if (string_compare(argument, "-m"))
          return selfie_run(MIPSTER);
        else if (string_compare(argument, "-d"))
          return selfie_run(DIPSTER);
        else if (string_compare(argument, "-r"))
          return selfie_run(RIPSTER);
        else if (string_compare(argument, "-y"))
          return selfie_run(HYPSTER);
        else if (string_compare(argument, "-min"))
          return selfie_run(MINSTER);
        else if (string_compare(argument, "-mob"))
          return selfie_run(MOBSTER);
        else
          return EXITCODE_BADARGUMENTS;
      } else
        return EXITCODE_MOREARGUMENTS;
    }

    return EXITCODE_NOERROR;
  }
}

uint64_t exit_selfie(uint64_t exit_code, char* extras) {
  if (no_or_bad_or_more_arguments(exit_code))
    print_synopsis(extras);

  if (exit_code == EXITCODE_MOREARGUMENTS)
    return EXITCODE_BADARGUMENTS;
  else if (exit_code == EXITCODE_NOARGUMENTS)
    return EXITCODE_NOERROR;
  else
    return exit_code;
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

// selfie bootstraps int and char** to uint64_t and uint64_t*, respectively!
int main(int argc, char** argv) {
  uint64_t exit_code;

  init_selfie((uint64_t) argc, (uint64_t*) argv);

  init_library();

  init_system();

  exit_code = selfie(0);

  return exit_selfie(exit_code, " [ ( -m | -d | -r | -y ) 0-4096 ... ]");
}