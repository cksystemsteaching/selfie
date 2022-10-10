/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information please refer to:

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

All of selfie including its source code is available at:

https://github.com/cksystemsteaching/selfie

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

// selfie bootstraps char to uint64_t and ignores ellipsis!
uint64_t open(char* filename, uint64_t flags, ...);

// selfie bootstraps void* to uint64_t* and unsigned to uint64_t!
void* malloc(unsigned long);

// selfie bootstraps the following *printf procedures
int printf(const char* format, ...);
int sprintf(char* str, const char* format, ...);
int dprintf(int fd, const char* format, ...);

// -----------------------------------------------------------------
// ----------------------- LIBRARY PROCEDURES ----------------------
// -----------------------------------------------------------------

void init_library();
void reset_library();

uint64_t two_to_the_power_of(uint64_t p);
uint64_t log_two(uint64_t n);

uint64_t ten_to_the_power_of(uint64_t p);
uint64_t log_ten(uint64_t n);

uint64_t left_shift(uint64_t n, uint64_t b);
uint64_t right_shift(uint64_t n, uint64_t b);

uint64_t get_bits(uint64_t n, uint64_t i, uint64_t b);

uint64_t absolute(uint64_t n);
uint64_t max(uint64_t a, uint64_t b);

uint64_t signed_less_than(uint64_t a, uint64_t b);
uint64_t signed_division(uint64_t a, uint64_t b);

uint64_t is_signed_integer(uint64_t n, uint64_t b);
uint64_t sign_extend(uint64_t n, uint64_t b);
uint64_t sign_shrink(uint64_t n, uint64_t b);

char  load_character(char* s, uint64_t i);
char* store_character(char* s, uint64_t i, char c);

uint64_t is_letter(char c);
uint64_t is_digit(char c);

char*    string_alloc(uint64_t l);
uint64_t string_length(char* s);
char*    string_shrink(char* s);
void     string_reverse(char* s);
uint64_t string_compare(char* s, char* t);

uint64_t atoi(char* s);
char*    itoa(uint64_t n, char* s, uint64_t b, uint64_t d, uint64_t a);

uint64_t fixed_point_ratio(uint64_t a, uint64_t b, uint64_t f);
uint64_t fixed_point_percentage(uint64_t r, uint64_t f);

uint64_t fixed_point_integral(uint64_t a, uint64_t f);
uint64_t fixed_point_fractional(uint64_t a, uint64_t f);

uint64_t ratio_format_integral_2(uint64_t a, uint64_t b);
uint64_t ratio_format_fractional_2(uint64_t a, uint64_t b);

uint64_t percentage_format_integral_2(uint64_t a, uint64_t b);
uint64_t percentage_format_fractional_2(uint64_t a, uint64_t b);

void put_character(char c);

void print(char* s);
void println();

void print_character(char c);
void print_string(char* s);
void print_unsigned_integer(uint64_t n);
void print_integer(uint64_t n);
void print_fractional(uint64_t n, uint64_t p);
void unprint_integer(uint64_t n);
void print_hexadecimal_no_prefix(uint64_t n, uint64_t a);
void print_hexadecimal(uint64_t n, uint64_t a);
void print_octal_no_prefix(uint64_t n, uint64_t a);
void print_octal(uint64_t n, uint64_t a);
void print_binary_no_prefix(uint64_t n, uint64_t a);
void print_binary(uint64_t n, uint64_t a);

// printf

uint64_t print_format(char* s, uint64_t i, char* a);

uint64_t vdsprintf(uint64_t fd, char* buffer, char* format, uint64_t* args);

// selfie implementation of *printf procedures
uint64_t selfie_printf(char* format, ...);
uint64_t selfie_sprintf(char* str, char* format, ...);
uint64_t selfie_dprintf(uint64_t fd, char* format, ...);

// during bootstrapping the "selfie_" prefix of *printf procedures is removed
char* remove_prefix_from_printf_procedures(char* procedure);

// selfie's malloc interface

uint64_t round_up(uint64_t n, uint64_t m);

uint64_t* smalloc(uint64_t size); // use this to allocate memory, not malloc
uint64_t* smalloc_system(uint64_t size); // internal use only!

void zero_memory(uint64_t* memory, uint64_t size);

uint64_t* zalloc(uint64_t size);  // internal use only!
uint64_t* zmalloc(uint64_t size); // use this to allocate zeroed memory

// ------------------------ GLOBAL CONSTANTS -----------------------

char* SELFIE_URL = (char*) 0;

uint64_t IS64BITSYSTEM = 1; // flag indicating 64-bit selfie
uint64_t IS64BITTARGET = 1; // flag indicating 64-bit target

uint64_t SIZEOFUINT64       = 8;  // in bytes
uint64_t SIZEOFUINT64INBITS = 64; // SIZEOFUINT64 * 8

uint64_t SIZEOFUINT64STAR       = 8;  // in bytes, must be the same as SIZEOFUINT64
uint64_t SIZEOFUINT64STARINBITS = 64; // SIZEOFUINT64STAR * 8

uint64_t* power_of_two_table;

uint64_t UINT64_MAX; // maximum numerical value of an unsigned 64-bit integer

uint64_t INT64_MAX; // maximum numerical value of a signed 64-bit integer
uint64_t INT64_MIN; // minimum numerical value of a signed 64-bit integer

uint64_t SINGLEWORDSIZE       = 4;  // single-word size in bytes
uint64_t SINGLEWORDSIZEINBITS = 32; // single-word size in bits

uint64_t SIZEOFUINT = 8; // size of target-dependent unsigned integer in bytes
uint64_t UINT_MAX;       // maximum numerical value of target-dependent unsigned integer

uint64_t WORDSIZE       = 8;  // target-dependent word size in bytes
uint64_t WORDSIZEINBITS = 64; // WORDSIZE * 8

char* character_buffer; // buffer for reading and writing characters

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
// LINUX: 577 = 0x0241 = O_CREAT (0x0040) | O_TRUNC (0x0200) | O_WRONLY (0x0001)
uint64_t LINUX_O_CREAT_TRUNC_WRONLY = 577;

// MAC: 1537 = 0x0601 = O_CREAT (0x0200) | O_TRUNC (0x0400) | O_WRONLY (0x0001)
uint64_t MAC_O_CREAT_TRUNC_WRONLY = 1537;

// WINDOWS: 33537 = 0x8301 = _O_BINARY (0x8000) | _O_CREAT (0x0100) | _O_TRUNC (0x0200) | _O_WRONLY (0x0001)
uint64_t WINDOWS_O_BINARY_CREAT_TRUNC_WRONLY = 33537;

// default is LINUX, re-initialized in init_system
uint64_t O_CREAT_TRUNC_WRONLY = 577; // write-only flags for host operating system

// flags for rw-r--r-- (text) file permissions
// 420 = 00644 = S_IRUSR (00400) | S_IWUSR (00200) | S_IRGRP (00040) | S_IROTH (00004)
// these flags seem to be working for LINUX, MAC, and WINDOWS
uint64_t S_IRUSR_IWUSR_IRGRP_IROTH = 420;

// flags for rwxr-xr-x (binary) file permissions
// 493 = 00755 = S_IRUSR_IWUSR_IRGRP_IROTH | S_IXUSR (00100) | S_IXGRP (00010) | S_IXOTH (00001)
// these flags also seem to be working for LINUX, MAC, and WINDOWS
uint64_t S_IRUSR_IWUSR_IXUSR_IRGRP_IXGRP_IROTH_IXOTH = 493;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t number_of_written_characters = 0;
uint64_t number_of_put_characters     = 0;

char*    output_name = (char*) 0;
uint64_t output_fd   = 1; // 1 is file descriptor of standard output

char*    output_buffer = (char*) 0;
uint64_t output_cursor = 0; // cursor for output buffer

// ------------------------- INITIALIZATION ------------------------

void init_library() {
  uint64_t i;

  if (SELFIE_URL)
    // avoid repeated initialization in tools
    return;

  SELFIE_URL = "selfie.cs.uni-salzburg.at";

  // determine actual size of uint64_t
  SIZEOFUINT64       = (uint64_t) ((uint64_t*) SELFIE_URL + 1) - (uint64_t) SELFIE_URL;
  SIZEOFUINT64INBITS = SIZEOFUINT64 * 8;

  // determine actual size of uint64_t*
  SIZEOFUINT64STAR       = (uint64_t) ((uint64_t**) SELFIE_URL + 1) - (uint64_t) SELFIE_URL;
  SIZEOFUINT64STARINBITS = SIZEOFUINT64STAR * 8;

  // powers of two table with SIZEOFUINT64INBITS entries for 2^0 to 2^(SIZEOFUINT64INBITS - 1)
  power_of_two_table = smalloc(SIZEOFUINT64INBITS * SIZEOFUINT64);

  *power_of_two_table = 1; // 2^0 == 1

  i = 1;

  while (i < SIZEOFUINT64INBITS) {
    // compute powers of two incrementally using this recurrence relation
    *(power_of_two_table + i) = *(power_of_two_table + (i - 1)) * 2;

    i = i + 1;
  }

  // compute 64-bit unsigned integer range using signed integer arithmetic
  UINT64_MAX = -1;

  // compute 64-bit signed integer range using unsigned integer arithmetic
  INT64_MIN = two_to_the_power_of(SIZEOFUINT64INBITS - 1);
  INT64_MAX = INT64_MIN - 1;

  // target-dependent, see init_target()
  SIZEOFUINT     = SIZEOFUINT64;
  UINT_MAX       = UINT64_MAX;
  WORDSIZE       = SIZEOFUINT64;
  WORDSIZEINBITS = WORDSIZE * 8;

  // allocate and touch to make sure memory is mapped for read calls
  character_buffer  = (char*) smalloc(1);
  *character_buffer = (char) 0;

  // accommodate at least SIZEOFUINT64INBITS numbers for itoa, no mapping needed
  integer_buffer = string_alloc(SIZEOFUINT64INBITS);

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
void syntax_error_expected_character(char character);

void get_character();

uint64_t is_character_new_line();
uint64_t is_character_whitespace();

char find_next_character();

uint64_t is_character_letter_or_digit_or_underscore();
uint64_t is_character_not_double_quote_or_new_line_or_eof();

uint64_t identifier_string_match(uint64_t string_index);
uint64_t identifier_or_keyword();

void get_symbol();

void handle_escape_sequence();

// ------------------------ GLOBAL CONSTANTS -----------------------

char CHAR_EOF          =  -1; // end of file
char CHAR_BACKSPACE    =   8; // ASCII code 8  = backspace
char CHAR_TAB          =   9; // ASCII code 9  = tabulator
char CHAR_LF           =  10; // ASCII code 10 = line feed
char CHAR_CR           =  13; // ASCII code 13 = carriage return
char CHAR_SPACE        = ' ';
char CHAR_UNDERSCORE   = '_';
char CHAR_SINGLEQUOTE  =  39; // ASCII code 39 = '
char CHAR_DOUBLEQUOTE  = '"';
char CHAR_COMMA        = ',';
char CHAR_SEMICOLON    = ';';
char CHAR_LPARENTHESIS = '(';
char CHAR_RPARENTHESIS = ')';
char CHAR_LBRACE       = '{';
char CHAR_RBRACE       = '}';
char CHAR_PLUS         = '+';
char CHAR_DASH         = '-';
char CHAR_ASTERISK     = '*';
char CHAR_SLASH        = '/';
char CHAR_PERCENTAGE   = '%';
char CHAR_EQUAL        = '=';
char CHAR_EXCLAMATION  = '!';
char CHAR_LT           = '<';
char CHAR_GT           = '>';
char CHAR_BACKSLASH    =  92; // ASCII code 92 = backslash
char CHAR_DOT          = '.';

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
uint64_t SYM_ELLIPSIS     = 28; // ...

// symbols for bootstrapping

uint64_t SYM_INT      = 29; // int
uint64_t SYM_CHAR     = 30; // char
uint64_t SYM_UNSIGNED = 31; // unsigned
uint64_t SYM_CONST    = 32; // const

uint64_t* SYMBOLS; // strings representing symbols

uint64_t MAX_IDENTIFIER_LENGTH = 64;  // maximum number of characters in an identifier
uint64_t MAX_INTEGER_LENGTH    = 20;  // maximum number of characters in an unsigned integer
uint64_t MAX_STRING_LENGTH     = 128; // maximum number of characters in a string

// ------------------------ GLOBAL VARIABLES -----------------------

char character; // most recently read character

uint64_t number_of_read_characters = 0;

uint64_t line_number = 1; // current line number for error reporting

uint64_t number_of_ignored_characters = 0;
uint64_t number_of_comments           = 0;
uint64_t number_of_scanned_symbols    = 0;

uint64_t number_of_syntax_errors = 0; // the number of encountered syntax errors

char* identifier = (char*) 0; // stores scanned identifier as string
char* integer    = (char*) 0; // stores scanned integer as string
char* string     = (char*) 0; // stores scanned string

uint64_t literal = 0; // numerical value of most recently scanned integer or character

uint64_t integer_is_signed = 0; // enforce INT64_MIN limit if '-' was scanned before

uint64_t symbol; // most recently recognized symbol

char*    source_name = (char*) 0; // name of source file
uint64_t source_fd   = 0; // file descriptor of open source file

// ------------------------- INITIALIZATION ------------------------

void init_scanner () {
  SYMBOLS = smalloc((SYM_CONST + 1) * SIZEOFUINT64STAR);

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
  *(SYMBOLS + SYM_ELLIPSIS)     = (uint64_t) "...";

  *(SYMBOLS + SYM_INT)      = (uint64_t) "int";
  *(SYMBOLS + SYM_CHAR)     = (uint64_t) "char";
  *(SYMBOLS + SYM_UNSIGNED) = (uint64_t) "unsigned";
  *(SYMBOLS + SYM_CONST)    = (uint64_t) "const";

  character = CHAR_EOF;
  symbol    = SYM_EOF;
}

void reset_scanner() {
  number_of_read_characters = 0;

  line_number = 1;

  get_character();

  number_of_ignored_characters = 0;
  number_of_comments           = 0;
  number_of_scanned_symbols    = 0;

  number_of_syntax_errors = 0;
}

// -----------------------------------------------------------------
// ------------------------- SYMBOL TABLE --------------------------
// -----------------------------------------------------------------

void reset_symbol_tables();

uint64_t hash(uint64_t* key);

uint64_t* create_symbol_table_entry(uint64_t table, char* string,
  uint64_t line, uint64_t class, uint64_t type, uint64_t value, uint64_t address);

uint64_t* search_symbol_table(uint64_t* entry, char* string, uint64_t class);
uint64_t* search_global_symbol_table(char* string, uint64_t class);
uint64_t* get_scoped_symbol_table_entry(char* string, uint64_t class);

uint64_t is_undefined_procedure(uint64_t* entry);
uint64_t is_library_procedure(char* name);
uint64_t report_undefined_procedures();

// symbol table entry
// +---+---------+
// | 0 | next    | pointer to next entry
// | 1 | string  | identifier string, big integer as string, string literal
// | 2 | line#   | source line number
// | 3 | class   | VARIABLE, BIGINT, STRING, PROCEDURE
// | 4 | type    | UINT64_T, UINT64STAR_T, VOID_T
// | 5 | value   | VARIABLE: initial value
// | 6 | address | VARIABLE, BIGINT, STRING: offset, PROCEDURE: address
// | 7 | scope   | REG_GP (global), REG_S0 (local)
// +---+---------+

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

void set_next_entry(uint64_t* entry, uint64_t* next) { *entry       = (uint64_t) next; }
void set_string(uint64_t* entry, char* identifier)   { *(entry + 1) = (uint64_t) identifier; }
void set_line_number(uint64_t* entry, uint64_t line) { *(entry + 2) = line; }
void set_class(uint64_t* entry, uint64_t class)      { *(entry + 3) = class; }
void set_type(uint64_t* entry, uint64_t type)        { *(entry + 4) = type; }
void set_value(uint64_t* entry, uint64_t value)      { *(entry + 5) = value; }
void set_address(uint64_t* entry, uint64_t address)  { *(entry + 6) = address; }
void set_scope(uint64_t* entry, uint64_t scope)      { *(entry + 7) = scope; }

// ------------------------ GLOBAL CONSTANTS -----------------------

// classes
uint64_t VARIABLE  = 1;
uint64_t BIGINT    = 2;
uint64_t STRING    = 3;
uint64_t PROCEDURE = 4;
uint64_t MACRO     = 5;

// types
uint64_t UINT64_T     = 1;
uint64_t UINT64STAR_T = 2;
uint64_t VOID_T       = 3;
uint64_t UNDECLARED_T = 4;

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
// ---------------------- REGISTER ALLOCATOR -----------------------
// -----------------------------------------------------------------

void     talloc();
uint64_t current_temporary();
uint64_t previous_temporary();
uint64_t next_temporary();
void     tfree(uint64_t number_of_temporaries);

// -----------------------------------------------------------------
// ---------------------------- PARSER -----------------------------
// -----------------------------------------------------------------

void reset_parser();

uint64_t is_type();
uint64_t is_value();
uint64_t is_expression();
uint64_t is_comparison();
uint64_t is_plus_or_minus();
uint64_t is_mult_or_div_or_rem();
uint64_t is_factor();
uint64_t is_literal();

uint64_t is_neither_rbrace_nor_eof();
uint64_t is_possibly_parameter(uint64_t is_already_variadic);

uint64_t is_neither_type_nor_void();
uint64_t is_not_statement();
uint64_t is_not_factor();

void syntax_error_expected_symbol(uint64_t expected);
void syntax_error_unexpected_symbol();

uint64_t get_expected_symbol(uint64_t expected_symbol);
void     get_required_symbol(uint64_t required_symbol);

void syntax_error_undeclared_identifier(char* name);
void syntax_error_unexpected_identifier(char* expected);

void print_type(uint64_t type);
void type_warning(uint64_t expected, uint64_t found);

void compile_cstar(); // grammar top symbol, parser entry

uint64_t* compile_variable(char* variable, uint64_t type, uint64_t offset); // returns variable entry

uint64_t compile_type(); // returns type

uint64_t compile_initialize(uint64_t type); // returns initial value
uint64_t compile_value(); // returns value

void compile_statement();

uint64_t load_upper_value(uint64_t reg, uint64_t value);
uint64_t load_upper_address(uint64_t* entry);

uint64_t load_value(uint64_t* entry);

uint64_t* get_variable_entry(char* variable);
uint64_t  load_variable(char* variable);

void compile_assignment(char* variable);

uint64_t compile_expression(); // returns type
uint64_t compile_arithmetic(); // returns type
uint64_t compile_term();       // returns type
uint64_t compile_factor();     // returns type

void     load_small_and_medium_integer(uint64_t reg, uint64_t value);
uint64_t load_big_integer(char* big_integer);
void     load_integer(uint64_t value);
void     load_string(char* string);

uint64_t compile_literal(); // returns type

void compile_if();
void compile_while();

void procedure_prologue(uint64_t number_of_local_variable_bytes);
void procedure_epilogue(uint64_t number_of_parameter_bytes);

void compile_procedure(char* procedure, uint64_t type);

uint64_t save_temporaries();
void     restore_temporaries(uint64_t number_of_temporaries);

uint64_t macro_expand(uint64_t* entry);
uint64_t procedure_call(uint64_t* entry, char* procedure, uint64_t number_of_actual_parameters);

uint64_t compile_call(char* procedure); // returns type
void     compile_return();

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t allocated_temporaries = 0; // number of allocated temporaries

uint64_t* current_procedure = (uint64_t*) 0; // currently parsed procedure definition

uint64_t return_jumps = 0; // fixup chain for return statements

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

  number_of_syntax_errors = 0;

  get_symbol();
}

// -----------------------------------------------------------------
// ---------------------------- MACROS -----------------------------
// -----------------------------------------------------------------

// these C macros are seen as procedures by the bootstrapping compiler ...
void  var_start(uint64_t* args);
char* var_arg(uint64_t* args);
void  var_end(uint64_t* args);

// ... and need a dummy definition using all arguments to avoid compiler warnings
void  var_start(uint64_t* args) { *args = *args; }
char* var_arg(uint64_t* args)   { *args = *args; return ""; }
void  var_end(uint64_t* args)   { *args = *args; }

// these procedures are the actual selfie implementation of the above C macros
void macro_var_start();
void macro_var_arg();
void macro_var_end();

// -----------------------------------------------------------------
// ---------------------- MACHINE CODE LIBRARY ---------------------
// -----------------------------------------------------------------

void init_bootstrapping();

void emit_round_up(uint64_t reg, uint64_t m);
void emit_multiply_by(uint64_t reg, uint64_t m);

// bootstrapping binary

void emit_program_entry();
void emit_bootstrapping();

// ------------------------ GLOBAL CONSTANTS -----------------------

char* main_name = (char*) 0;
char* bump_name = (char*) 0;

// ------------------------- INITIALIZATION ------------------------

void init_bootstrapping() {
  // caution: length of string literals used as identifiers must be
  // multiple of SIZEOFUINT64 to avoid out-of-bound array access warnings
  // during bootstrapping; trailing spaces are removed by string_shrink
  // resulting in unique hash for global symbol table
  main_name = string_shrink("main   ");
  bump_name = string_shrink("_bump  ");
}

// -----------------------------------------------------------------
// --------------------------- COMPILER ----------------------------
// -----------------------------------------------------------------

uint64_t open_read_only(char* name);

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

void read_register_wrap(uint64_t reg, uint64_t wrap);
void read_register(uint64_t reg);

void write_register_wrap(uint64_t reg, uint64_t wrap);
void write_register(uint64_t reg);

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
uint64_t OP_LOAD   = 3;   // 0000011, I format (LD,LW)
uint64_t OP_IMM    = 19;  // 0010011, I format (ADDI, NOP)
uint64_t OP_STORE  = 35;  // 0100011, S format (SD,SW)
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
uint64_t F3_LW    = 2; // 010
uint64_t F3_SW    = 2; // 010
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

void reset_binary();
void reset_instruction_counters();

uint64_t get_total_number_of_instructions();
uint64_t get_total_number_of_nops();

void print_instruction_counter(uint64_t counter, uint64_t ins);
void print_instruction_counter_with_nops(uint64_t counter, uint64_t nops, uint64_t ins);

void print_instruction_counters();

uint64_t get_low_word(uint64_t word);
uint64_t get_high_word(uint64_t word);

uint64_t load_word(uint64_t* memory, uint64_t waddr, uint64_t is_double_word);
void     store_word(uint64_t* memory, uint64_t waddr, uint64_t is_double_word, uint64_t word);

uint64_t load_instruction(uint64_t caddr);
void     store_instruction(uint64_t caddr, uint64_t instruction);

uint64_t load_code(uint64_t caddr);

uint64_t load_data(uint64_t daddr);
void     store_data(uint64_t daddr, uint64_t data);

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

void emit_load(uint64_t rd, uint64_t rs1, uint64_t immediate);
void emit_store(uint64_t rs1, uint64_t immediate, uint64_t rs2);

void emit_beq(uint64_t rs1, uint64_t rs2, uint64_t immediate);

void emit_jal(uint64_t rd, uint64_t immediate);
void emit_jalr(uint64_t rd, uint64_t rs1, uint64_t immediate);

void emit_ecall();

void fixup_relative_BFormat(uint64_t from_address);
void fixup_relative_JFormat(uint64_t from_address, uint64_t to_address);
void fixup_IFormat(uint64_t from_address, uint64_t immediate);
void fixlink_relative(uint64_t from_address, uint64_t to_address);

void emit_data_word(uint64_t data, uint64_t offset, uint64_t source_line_number);
void emit_string_data(uint64_t* entry);

void emit_data_segment();

uint64_t* allocate_elf_header();

uint64_t* encode_elf_header();

uint64_t get_elf_program_header_offset(uint64_t ph_index);
void     encode_elf_program_header(uint64_t* header, uint64_t ph_index);
void     decode_elf_program_header(uint64_t* header, uint64_t ph_index);

uint64_t validate_elf_header(uint64_t* header);

uint64_t open_write_only(char* name, uint64_t mode);

void selfie_output(char* filename);

uint64_t* touch(uint64_t* memory, uint64_t bytes);

void selfie_load();

// ------------------------ GLOBAL CONSTANTS -----------------------

// page-aligned ELF header size for storing file header, program header, code size
uint64_t ELF_HEADER_SIZE = 4096;

uint64_t ELFCLASS64 = 2;
uint64_t ELFCLASS32 = 1;

uint64_t MAX_CODE_SIZE = 524288; // 512KB
uint64_t MAX_DATA_SIZE = 65536;  // 64KB

uint64_t PK_CODE_START = 65536; // start of code segment at 0x10000 (according to RISC-V pk)

// ELF file header

uint64_t EI_MAG0 = 127; // magic number part 0 is 0x7F
uint64_t EI_MAG1 = 'E'; // magic number part 1
uint64_t EI_MAG2 = 'L'; // magic number part 2
uint64_t EI_MAG3 = 'F'; // magic number part 3

uint64_t MACHO_MAG0 = 207; // first byte of magic number of Mach-O executables

uint64_t EI_CLASS   = 2; // file class is 2 (ELFCLASS64) or 1 (ELFCLASS32)
uint64_t EI_DATA    = 1; // object file data structures endianness is 1 (ELFDATA2LSB)
uint64_t EI_VERSION = 1; // version of the object file format
uint64_t EI_OSABI   = 0; // target OS ABI is usually set to 0

uint64_t EI_ABIVERSION = 0; // ABI version
uint64_t EI_PAD        = 0; // start of padding bytes

uint64_t e_type    = 2;   // object file type is 0x02 (ET_EXEC)
uint64_t e_machine = 243; // target architecture is 0xF3 (RISC-V)
uint64_t e_version = 1;   // version of the object file format

uint64_t e_entry = 65536; // entry point address 0x10000 (according to RISC-V pk)

uint64_t e_phoff = 64; // program header offset 0x40 (ELFCLASS64) or 0x34 (ELFCLASS32)
uint64_t e_shoff = 0;  // section header offset

uint64_t e_flags     = 0;  // ignored
uint64_t e_ehsize    = 64; // elf header size 64 bytes (ELFCLASS64) or 52 bytes (ELFCLASS32)
uint64_t e_phentsize = 56; // size of program header entry 56 bytes (ELFCLASS64) or 32 bytes (ELFCLASS32)

uint64_t e_phnum = 2; // number of program header entries (code and data segment)

uint64_t e_shentsize = 0; // size of section header entry
uint64_t e_shnum     = 0; // number of section header entries
uint64_t e_shstrndx  = 0; // section header offset

// ELF program header

uint64_t p_type  = 1; // type of segment is PT_LOAD
uint64_t p_flags = 0; // segment attributes

uint64_t p_offset = 0; // segment offset in file (must be a multiple of p_align)

uint64_t p_vaddr = 0; // start of segment in virtual memory
uint64_t p_paddr = 0; // start of segment in physical memory (ignored)

uint64_t p_filesz = 0; // size of segment in file
uint64_t p_memsz  = 0; // size of segment in memory

uint64_t p_align = 4096; // alignment of segment: p_vaddr % p_align == p_offset % p_align

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
uint64_t ic_load  = 0;
uint64_t ic_store = 0;
uint64_t ic_beq   = 0;
uint64_t ic_jal   = 0;
uint64_t ic_jalr  = 0;
uint64_t ic_ecall = 0;

char* binary_name = (char*) 0; // file name of binary

uint64_t* ELF_header = (uint64_t*) 0;

uint64_t* code_binary = (uint64_t*) 0; // code binary
uint64_t  code_start  = 0;             // start of code segment in virtual memory
uint64_t  code_size   = 0;             // size of code binary in bytes

uint64_t* data_binary = (uint64_t*) 0; // data binary
uint64_t  data_start  = 0;             // start of data segment in virtual memory
uint64_t  data_size   = 0;             // size of data binary in bytes

uint64_t* code_line_number = (uint64_t*) 0; // code line number per emitted instruction
uint64_t* data_line_number = (uint64_t*) 0; // data line number per emitted data word

// ------------------------- INITIALIZATION ------------------------

void reset_binary() {
  ELF_header = (uint64_t*) 0;

  code_binary = (uint64_t*) 0;
  code_start  = 0;
  code_size   = 0;

  data_binary = (uint64_t*) 0;
  data_start  = 0;
  data_size   = 0;

  code_line_number = (uint64_t*) 0;
  data_line_number = (uint64_t*) 0;
}

void reset_instruction_counters() {
  ic_lui   = 0;
  ic_addi  = 0;
  ic_add   = 0;
  ic_sub   = 0;
  ic_mul   = 0;
  ic_divu  = 0;
  ic_remu  = 0;
  ic_sltu  = 0;
  ic_load  = 0;
  ic_store = 0;
  ic_beq   = 0;
  ic_jal   = 0;
  ic_jalr  = 0;
  ic_ecall = 0;
}

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
// ----------------------------- CACHE -----------------------------
// -----------------------------------------------------------------

// cache
// +---+------------------+
// | 0 | cache memory     | pointer to actual cache consisting of pointers to cache blocks
// | 1 | cache size       | cache size in bytes
// | 2 | associativity    | cache associativity
// | 3 | cache-block size | cache-block size in bytes
// | 4 | cache hits       | counter for cache hits
// | 5 | cache misses     | counter for cache misses
// | 6 | cache timer      | counter for LRU replacement strategy
// +---+------------------+

uint64_t* allocate_cache() {
  return smalloc(1 * SIZEOFUINT64STAR + 6 * SIZEOFUINT64);
}

uint64_t* get_cache_memory(uint64_t* cache)     { return (uint64_t*) *cache; }
uint64_t  get_cache_size(uint64_t* cache)       { return             *(cache + 1); }
uint64_t  get_associativity(uint64_t* cache)    { return             *(cache + 2); }
uint64_t  get_cache_block_size(uint64_t* cache) { return             *(cache + 3); }
uint64_t  get_cache_hits(uint64_t* cache)       { return             *(cache + 4); }
uint64_t  get_cache_misses(uint64_t* cache)     { return             *(cache + 5); }
uint64_t  get_cache_timer(uint64_t* cache)      { return             *(cache + 6); }

void set_cache_memory(uint64_t* cache, uint64_t* cache_memory)        { *cache       = (uint64_t) cache_memory; }
void set_cache_size(uint64_t* cache, uint64_t cache_size)             { *(cache + 1) = cache_size; }
void set_associativity(uint64_t* cache, uint64_t associativity)       { *(cache + 2) = associativity; }
void set_cache_block_size(uint64_t* cache, uint64_t cache_block_size) { *(cache + 3) = cache_block_size; }
void set_cache_hits(uint64_t* cache, uint64_t cache_hits)             { *(cache + 4) = cache_hits; }
void set_cache_misses(uint64_t* cache, uint64_t cache_misses)         { *(cache + 5) = cache_misses; }
void set_cache_timer(uint64_t* cache, uint64_t cache_timer)           { *(cache + 6) = cache_timer; }

// cache block
// +---+------------+
// | 0 | valid flag | valid block or not
// | 1 | tag        | unique identifier within a set
// | 2 | memory     | pointer to cache-block memory
// | 3 | timestamp  | timestamp for replacement strategy
// +---+------------+

uint64_t* allocate_cache_block() {
  return zmalloc(1 * SIZEOFUINT64STAR + 3 * SIZEOFUINT64);
}

uint64_t  get_valid_flag(uint64_t* cache_block)   { return             *cache_block; }
uint64_t  get_tag(uint64_t* cache_block)          { return             *(cache_block + 1); }
uint64_t* get_block_memory(uint64_t* cache_block) { return (uint64_t*) *(cache_block + 2); }
uint64_t  get_timestamp(uint64_t* cache_block)    { return             *(cache_block + 3); }

void set_valid_flag(uint64_t* cache_block, uint64_t valid)     { *cache_block       = valid; }
void set_tag(uint64_t* cache_block, uint64_t tag)              { *(cache_block + 1) = tag; }
void set_block_memory(uint64_t* cache_block, uint64_t* memory) { *(cache_block + 2) = (uint64_t) memory; }
void set_timestamp(uint64_t* cache_block, uint64_t timestamp)  { *(cache_block + 3) = timestamp; }

void reset_cache_counters(uint64_t* cache);
void reset_all_cache_counters();

void init_cache_memory(uint64_t* cache);
void init_cache(uint64_t* cache, uint64_t cache_size, uint64_t associativity, uint64_t cache_block_size);
void init_all_caches();

void flush_cache(uint64_t* cache);
void flush_all_caches();

uint64_t cache_set_size(uint64_t* cache);

uint64_t cache_tag(uint64_t* cache, uint64_t address);
uint64_t cache_index(uint64_t* cache, uint64_t address);
uint64_t cache_block_address(uint64_t* cache, uint64_t address);
uint64_t cache_byte_offset(uint64_t* cache, uint64_t address);

uint64_t* cache_set(uint64_t* cache, uint64_t vaddr);

uint64_t  get_new_timestamp(uint64_t* cache);
uint64_t* cache_lookup(uint64_t* cache, uint64_t vaddr, uint64_t paddr, uint64_t is_access);

void      fill_cache_block(uint64_t* cache, uint64_t* cache_block, uint64_t paddr);
uint64_t* handle_cache_miss(uint64_t* cache, uint64_t* cache_block, uint64_t paddr, uint64_t is_access);
uint64_t* retrieve_cache_block(uint64_t* cache, uint64_t vaddr, uint64_t paddr, uint64_t is_access);

void     flush_cache_block(uint64_t* cache, uint64_t* cache_block, uint64_t paddr);
uint64_t load_from_cache(uint64_t* cache, uint64_t vaddr, uint64_t paddr);
void     store_in_cache(uint64_t* cache, uint64_t vaddr, uint64_t paddr, uint64_t data);

uint64_t load_instruction_from_cache(uint64_t vaddr, uint64_t paddr);
uint64_t load_data_from_cache(uint64_t vaddr, uint64_t paddr);
void     store_data_in_cache(uint64_t vaddr, uint64_t paddr, uint64_t data);

void print_cache_profile(uint64_t hits, uint64_t misses, char* cache_name);

// ------------------------ GLOBAL CONSTANTS -----------------------

// indicates whether the machine has a cache or not
uint64_t L1_CACHE_ENABLED = 0;

// machine-enforced coherency for self-modifying code (selfie also
// works if this is turned off since there is no code modification
// during runtime and stores in the code segment are illegal)
uint64_t L1_CACHE_COHERENCY = 0;

// example configurations:
// +-------------------+---------------+-----------------------------+------------+
// |              name |    cache size |               associativity | block size |
// +===================+===============+=============================+============+
// |       CORE-V CVA6 | dcache: 32 KB |                   dcache: 8 |       16 B |
// |                   | icache: 16 KB |                   icache: 4 |            |
// +-------------------+---------------+-----------------------------+------------+
// |     direct-mapped |         2^x B |                           1 |      2^y B |
// +-------------------+---------------+-----------------------------+------------+
// | fully associative |         2^x B | (cache size) / (block size) |      2^y B |
// +-------------------+---------------+-----------------------------+------------+

// L1-cache size in byte
// assert: cache sizes are powers of 2
uint64_t L1_DCACHE_SIZE = 32768; // 32 KB data cache
uint64_t L1_ICACHE_SIZE = 16384; // 16 KB instruction cache

// L1-cache associativity
// assert: associativities are powers of 2
// assert: L1_xCACHE_SIZE / L1_xCACHE_ASSOCIATIVITY <= PAGESIZE
// (this is necessary in order to prevent aliasing problems)
uint64_t L1_DCACHE_ASSOCIATIVITY = 8;
uint64_t L1_ICACHE_ASSOCIATIVITY = 4;

// L1 cache-block size
// assert: cache-block sizes are powers of 2
// assert: L1_xCACHE_BLOCK_SIZE >= WORDSIZE
// assert: L1_xCACHE_SIZE / L1_xCACHE_ASSOCIATIVITY >= L1_xCACHE_BLOCK_SIZE
uint64_t L1_DCACHE_BLOCK_SIZE = 16; // in bytes
uint64_t L1_ICACHE_BLOCK_SIZE = 16; // in bytes

// pointers to VIPT n-way set-associative write-through L1-caches
uint64_t* L1_ICACHE;
uint64_t* L1_DCACHE;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t L1_icache_coherency_invalidations = 0;

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

uint64_t get_page_of_virtual_address(uint64_t vaddr);
uint64_t get_virtual_address_of_page_start(uint64_t page);

uint64_t is_virtual_address_valid(uint64_t vaddr, uint64_t alignment);
uint64_t is_virtual_address_mapped(uint64_t* table, uint64_t vaddr);

uint64_t* tlb(uint64_t* table, uint64_t vaddr);

uint64_t load_virtual_memory(uint64_t* table, uint64_t vaddr);
void     store_virtual_memory(uint64_t* table, uint64_t vaddr, uint64_t data);

uint64_t load_cached_virtual_memory(uint64_t* table, uint64_t vaddr);
void     store_cached_virtual_memory(uint64_t* table, uint64_t vaddr, uint64_t data);

uint64_t load_cached_instruction_word(uint64_t* table, uint64_t vaddr);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t debug_tlb = 0;

uint64_t KILOBYTE = 1024;       // 1KB (KiB: 2^10B)
uint64_t MEGABYTE = 1048576;    // 1MB (MiB: 2^20B)
uint64_t GIGABYTE = 1073741824; // 1GB (GiB: 2^30B)

uint64_t VIRTUALMEMORYSIZE = 4; // 4GB of virtual memory (avoiding 32-bit overflow)

uint64_t PAGESIZE = 4096; // 4KB virtual pages

uint64_t NUMBEROFPAGES = 1048576; // VIRTUALMEMORYSIZE * GIGABYTE / PAGESIZE

uint64_t PAGETABLETREE = 1; // two-level page table is default

uint64_t PHYSICALMEMORYSIZE   = 0; // total amount of physical memory available for frames
uint64_t PHYSICALMEMORYEXCESS = 2; // tolerate more allocation than physically available

// target-dependent, see init_target()
uint64_t HIGHESTVIRTUALADDRESS = 4294967288; // VIRTUALMEMORYSIZE * GIGABYTE - WORDSIZE

// host-dependent, see init_memory()
uint64_t NUMBEROFLEAFPTES = 512; // number of leaf page table entries == PAGESIZE / SIZEOFUINT64STAR

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t mc_brk = 0; // memory counter for brk syscall

uint64_t mc_mapped_heap = 0; // memory counter for mapped heap

// ------------------------- INITIALIZATION ------------------------

void init_memory(uint64_t megabytes) {
  if (megabytes < 1)
    megabytes = 1;
  else if (megabytes > 4096)
    megabytes = 4096;

  PHYSICALMEMORYSIZE = megabytes * MEGABYTE;

  // host-dependent: reinitialize in case SIZEOFUINT64STAR is not 8
  NUMBEROFLEAFPTES = PAGESIZE / SIZEOFUINT64STAR;
}

void reset_memory_counters() {
  mc_brk = 0;
  sc_brk = 0;

  mc_mapped_heap = 0;
}

// -----------------------------------------------------------------
// ---------------------- GARBAGE COLLECTOR ------------------------
// -----------------------------------------------------------------

void reset_gc_counters();

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

// gc metadata entry
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

uint64_t  get_stack_seg_start_gc(uint64_t* context);
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

void gc_init_selfie(uint64_t* context);

// interface to initialize an external garbage collector (e.g. tools/boehm-gc.c)
void gc_init(uint64_t* context);

// this function performs first-fit retrieval of free memory in O(n) where n is memory size
// improvement: push O(n) down to O(1), e.g. using Boehm's chunk allocator, or even compact-fit
// see https://github.com/cksystemsgroup/compact-fit
uint64_t* retrieve_from_free_list(uint64_t* context, uint64_t size);

uint64_t gc_load_memory(uint64_t* context, uint64_t address);
void     gc_store_memory(uint64_t* context, uint64_t address, uint64_t value);

void zero_object(uint64_t* context, uint64_t* metadata);

uint64_t* allocate_new_memory(uint64_t* context, uint64_t size);
uint64_t* reuse_memory(uint64_t* context, uint64_t size);
uint64_t* allocate_memory_selfie(uint64_t* context, uint64_t size);
uint64_t* gc_malloc_implementation(uint64_t* context, uint64_t size);

// interface to allocate an object using an external collector (e.g. tools/boehm-gc.c)
uint64_t* allocate_memory(uint64_t* context, uint64_t size);

// this function performs an O(n) list search where n is memory size
// improvement: push O(n) down to O(1), e.g. using Boehm's chunk allocator
uint64_t* get_metadata_if_address_is_valid(uint64_t* context, uint64_t address);

// interface to marking an object using an external collector (e.g. tools/boehm-gc.c)
void mark_object(uint64_t* context, uint64_t address);

void mark_object_selfie(uint64_t* context, uint64_t gc_address);
void mark_segment(uint64_t* context, uint64_t segment_start, uint64_t segment_end);

// this function scans the heap from two roots (data segment and stack) in O(n^2)
// where n is memory size; checking if a value is a pointer takes O(n), see above
// improvement: push O(n^2) down to O(n)
void mark(uint64_t* context);

void free_object(uint64_t* context, uint64_t* metadata, uint64_t* prev_metadata);

// interface to sweep marked objects using an external collector (e.g. tools/boehm-gc.c)
void sweep(uint64_t* context);

void sweep_selfie(uint64_t* context);

void gc_collect(uint64_t* context);

void print_gc_profile(uint64_t* context);

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

uint64_t GC_WORDSIZE = 8; // SIZEOFUINT64 for library variant, otherwise WORDSIZE

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

uint64_t print_code_line_number_for_instruction(uint64_t address, uint64_t offset);
uint64_t print_code_context_for_instruction(uint64_t address);

uint64_t print_lui();
void     print_lui_before();
void     print_lui_after();
void     record_lui_addi_add_sub_mul_divu_remu_sltu_jal_jalr();
void     do_lui();
void     undo_lui_addi_add_sub_mul_divu_remu_sltu_load_jal_jalr();

uint64_t print_addi();
void     print_addi_before();
void     print_addi_add_sub_mul_divu_remu_sltu_after();
void     do_addi();

uint64_t print_add_sub_mul_divu_remu_sltu();
void     print_add_sub_mul_divu_remu_sltu_before();

void do_add();
void do_sub();
void do_mul();
void do_divu();
void do_remu();

void do_sltu();

uint64_t print_load();
void     print_load_before();
void     print_load_after(uint64_t vaddr);
void     record_load();
uint64_t do_load();

uint64_t print_store();
void     print_store_before();
void     print_store_after(uint64_t vaddr);
void     record_store();
uint64_t do_store();
void     undo_store();

uint64_t print_beq();
void     print_beq_before();
void     print_beq_after();
void     record_beq();
void     do_beq();

uint64_t print_jal();
void     print_jal_before();
void     print_jal_jalr_after();
void     do_jal();

uint64_t print_jalr();
void     print_jalr_before();
void     do_jalr();

uint64_t print_ecall();
void     record_ecall();
void     do_ecall();
void     undo_ecall();

uint64_t print_data_line_number();
uint64_t print_data_context();
uint64_t print_data();

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
uint64_t LOAD  = 9;
uint64_t STORE = 10;
uint64_t BEQ   = 11;
uint64_t JAL   = 12;
uint64_t JALR  = 13;
uint64_t ECALL = 14;

uint64_t* MNEMONICS; // assembly mnemonics of instructions

// -----------------------------------------------------------------
// -------------------------- DISASSEMBLER -------------------------
// -----------------------------------------------------------------

void init_disassembler();
void reset_disassembler();

char* get_mnemonic(uint64_t ins);

uint64_t print_instruction();

void selfie_disassemble(uint64_t verbose);

// ------------------------ GLOBAL VARIABLES -----------------------

char*    assembly_name = (char*) 0; // name of assembly file
uint64_t assembly_fd   = 0;         // file descriptor of open assembly file

// ------------------------- INITIALIZATION ------------------------

void init_disassembler() {
  MNEMONICS = smalloc((ECALL + 1) * SIZEOFUINT64STAR);

  *(MNEMONICS + LUI)   = (uint64_t) "lui";
  *(MNEMONICS + ADDI)  = (uint64_t) "addi";
  *(MNEMONICS + ADD)   = (uint64_t) "add";
  *(MNEMONICS + SUB)   = (uint64_t) "sub";
  *(MNEMONICS + MUL)   = (uint64_t) "mul";
  *(MNEMONICS + DIVU)  = (uint64_t) "divu";
  *(MNEMONICS + REMU)  = (uint64_t) "remu";
  *(MNEMONICS + SLTU)  = (uint64_t) "sltu";

  reset_disassembler();

  *(MNEMONICS + BEQ)   = (uint64_t) "beq";
  *(MNEMONICS + JAL)   = (uint64_t) "jal";
  *(MNEMONICS + JALR)  = (uint64_t) "jalr";
  *(MNEMONICS + ECALL) = (uint64_t) "ecall";
}

void reset_disassembler() {
  if (IS64BITTARGET) {
    *(MNEMONICS + LOAD)  = (uint64_t) "ld";
    *(MNEMONICS + STORE) = (uint64_t) "sd";
  } else {
    *(MNEMONICS + LOAD)  = (uint64_t) "lw";
    *(MNEMONICS + STORE) = (uint64_t) "sw";
  }
}

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

void reset_source_profile();
void reset_registers_profile();
void reset_segments_profile();

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

void print_host_os();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t INSTRUCTIONSIZE       = 4;  // in bytes
uint64_t INSTRUCTIONSIZEINBITS = 32; // INSTRUCTIONSIZE * 8

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
uint64_t EXCEPTION_INTEGEROVERFLOW       = 9;

uint64_t* EXCEPTIONS; // textual representation of exceptions

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

uint64_t nopc_lui   = 0;
uint64_t nopc_addi  = 0;
uint64_t nopc_add   = 0;
uint64_t nopc_sub   = 0;
uint64_t nopc_mul   = 0;
uint64_t nopc_divu  = 0;
uint64_t nopc_remu  = 0;
uint64_t nopc_sltu  = 0;
uint64_t nopc_load  = 0;
uint64_t nopc_store = 0;
uint64_t nopc_beq   = 0;
uint64_t nopc_jal   = 0;
uint64_t nopc_jalr  = 0;

// source profile

uint64_t  calls               = 0;             // total number of executed procedure calls
uint64_t* calls_per_procedure = (uint64_t*) 0; // number of executed calls of each procedure

uint64_t  iterations          = 0;             // total number of executed loop iterations
uint64_t* iterations_per_loop = (uint64_t*) 0; // number of executed iterations of each loop

uint64_t* loads_per_instruction  = (uint64_t*) 0; // number of executed loads per load instruction
uint64_t* stores_per_instruction = (uint64_t*) 0; // number of executed stores per store instruction

// registers profile

uint64_t* reads_per_register  = (uint64_t*) 0;
uint64_t* writes_per_register = (uint64_t*) 0;

uint64_t stack_peak = 0;

uint64_t stack_register_reads  = 0;
uint64_t stack_register_writes = 0;

uint64_t argument_register_reads  = 0;
uint64_t argument_register_writes = 0;

uint64_t temporary_register_reads  = 0;
uint64_t temporary_register_writes = 0;

// segments profile

uint64_t data_reads  = 0;
uint64_t data_writes = 0;

uint64_t stack_reads  = 0;
uint64_t stack_writes = 0;

uint64_t heap_reads  = 0;
uint64_t heap_writes = 0;

// ------------------------- INITIALIZATION ------------------------

void init_interpreter() {
  EXCEPTIONS = smalloc((EXCEPTION_INTEGEROVERFLOW + 1) * SIZEOFUINT64STAR);

  *(EXCEPTIONS + EXCEPTION_NOEXCEPTION)           = (uint64_t) "no exception";
  *(EXCEPTIONS + EXCEPTION_PAGEFAULT)             = (uint64_t) "page fault";
  *(EXCEPTIONS + EXCEPTION_SEGMENTATIONFAULT)     = (uint64_t) "segmentation fault";
  *(EXCEPTIONS + EXCEPTION_SYSCALL)               = (uint64_t) "syscall";
  *(EXCEPTIONS + EXCEPTION_TIMER)                 = (uint64_t) "timer interrupt";
  *(EXCEPTIONS + EXCEPTION_DIVISIONBYZERO)        = (uint64_t) "division by zero";
  *(EXCEPTIONS + EXCEPTION_INVALIDADDRESS)        = (uint64_t) "invalid address";
  *(EXCEPTIONS + EXCEPTION_UNKNOWNINSTRUCTION)    = (uint64_t) "unknown instruction";
  *(EXCEPTIONS + EXCEPTION_UNINITIALIZEDREGISTER) = (uint64_t) "uninitialized register";
  *(EXCEPTIONS + EXCEPTION_INTEGEROVERFLOW)       = (uint64_t) "integer overflow";
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
  nopc_lui   = 0;
  nopc_addi  = 0;
  nopc_add   = 0;
  nopc_sub   = 0;
  nopc_mul   = 0;
  nopc_divu  = 0;
  nopc_remu  = 0;
  nopc_sltu  = 0;
  nopc_load  = 0;
  nopc_store = 0;
  nopc_beq   = 0;
  nopc_jal   = 0;
  nopc_jalr  = 0;
}

void reset_source_profile() {
  calls               = 0;
  calls_per_procedure = zmalloc(code_size / INSTRUCTIONSIZE * SIZEOFUINT64);

  iterations          = 0;
  iterations_per_loop = zmalloc(code_size / INSTRUCTIONSIZE * SIZEOFUINT64);

  loads_per_instruction  = zmalloc(code_size / INSTRUCTIONSIZE * SIZEOFUINT64);
  stores_per_instruction = zmalloc(code_size / INSTRUCTIONSIZE * SIZEOFUINT64);
}

void reset_registers_profile() {
  reads_per_register  = zmalloc(NUMBEROFREGISTERS * SIZEOFUINT64);
  writes_per_register = zmalloc(NUMBEROFREGISTERS * SIZEOFUINT64);

  // zero register is initialized by definition
  *(writes_per_register + REG_ZR) = 1;

  // stack and frame pointer registers are initialized by boot loader
  *(writes_per_register + REG_SP) = 1;
  *(writes_per_register + REG_S0) = 1;

  // a6 register is written to by the kernel
  *(writes_per_register + REG_A6) = 1;

  stack_peak = HIGHESTVIRTUALADDRESS;

  stack_register_reads      = 0;
  stack_register_writes     = 0;
  argument_register_reads   = 0;
  argument_register_writes  = 0;
  temporary_register_reads  = 0;
  temporary_register_writes = 0;
}

void reset_segments_profile() {
  data_reads   = 0;
  data_writes  = 0;
  stack_reads  = 0;
  stack_writes = 0;
  heap_reads   = 0;
  heap_writes  = 0;
}

void reset_profiler() {
  reset_instruction_counters();
  reset_memory_counters();
  reset_nop_counters();
  reset_source_profile();
  reset_registers_profile();
  reset_segments_profile();
  reset_all_cache_counters();
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------ MACHINE CONTEXTS -----------------------
// -----------------------------------------------------------------

uint64_t* new_context();

void init_context(uint64_t* context, uint64_t* parent, uint64_t* vctxt);

uint64_t* find_context(uint64_t* parent, uint64_t* vctxt);

void      free_context(uint64_t* context);
uint64_t* delete_context(uint64_t* context, uint64_t* from);

// machine context
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
// |  9 | code start      | start of code segment
// | 10 | code size       | size of code segment
// | 11 | data start      | start of data segment
// | 12 | data size       | size of data segment
// | 13 | heap start      | start of heap segment
// | 14 | program break   | current program break
// | 15 | exception       | exception ID
// | 16 | faulting page   | faulting page
// | 17 | exit code       | exit code
// | 18 | parent          | context that created this context
// | 19 | virtual context | virtual context address
// | 20 | name            | binary name loaded into context
// +----+-----------------+
// | 21 | used-list head  | pointer to head of used list
// | 22 | free-list head  | pointer to head of free list
// | 23 | gcs counter     | number of gc runs in gc period
// | 24 | gc enabled      | flag indicating whether to use gc or not
// +----+-----------------+

// number of entries of a machine context: 9 uint64_t plus 16 uint64_t* entries
// extended in the symbolic execution engine and the Boehm garbage collector
uint64_t CONTEXTENTRIES = 25;

uint64_t* allocate_context(); // declaration avoids warning in the Boehm garbage collector

uint64_t* allocate_context() {
  // SIZEOFUINT64 == SIZEOFUINT64STAR (always, so no need to differentiate although it would be nicer)
  return smalloc(CONTEXTENTRIES * SIZEOFUINT64);
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
uint64_t code_seg_size(uint64_t* context)   { return (uint64_t) (context + 10); }
uint64_t data_seg_start(uint64_t* context)  { return (uint64_t) (context + 11); }
uint64_t data_seg_size(uint64_t* context)   { return (uint64_t) (context + 12); }
uint64_t heap_seg_start(uint64_t* context)  { return (uint64_t) (context + 13); }
uint64_t program_break(uint64_t* context)   { return (uint64_t) (context + 14); }
uint64_t exception(uint64_t* context)       { return (uint64_t) (context + 15); }
uint64_t fault(uint64_t* context)           { return (uint64_t) (context + 16); }
uint64_t exit_code(uint64_t* context)       { return (uint64_t) (context + 17); }
uint64_t parent(uint64_t* context)          { return (uint64_t) (context + 18); }
uint64_t virtual_context(uint64_t* context) { return (uint64_t) (context + 19); }
uint64_t name(uint64_t* context)            { return (uint64_t) (context + 20); }

uint64_t used_list_head(uint64_t* context)   { return (uint64_t) (context + 21); }
uint64_t free_list_head(uint64_t* context)   { return (uint64_t) (context + 22); }
uint64_t gcs_in_period(uint64_t* context)    { return (uint64_t) (context + 23); }
uint64_t use_gc_kernel(uint64_t* context)    { return (uint64_t) (context + 24); }

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
uint64_t  get_code_seg_size(uint64_t* context)   { return             *(context + 10); }
uint64_t  get_data_seg_start(uint64_t* context)  { return             *(context + 11); }
uint64_t  get_data_seg_size(uint64_t* context)   { return             *(context + 12); }
uint64_t  get_heap_seg_start(uint64_t* context)  { return             *(context + 13); }
uint64_t  get_program_break(uint64_t* context)   { return             *(context + 14); }
uint64_t  get_exception(uint64_t* context)       { return             *(context + 15); }
uint64_t  get_fault(uint64_t* context)           { return             *(context + 16); }
uint64_t  get_exit_code(uint64_t* context)       { return             *(context + 17); }
uint64_t* get_parent(uint64_t* context)          { return (uint64_t*) *(context + 18); }
uint64_t* get_virtual_context(uint64_t* context) { return (uint64_t*) *(context + 19); }
char*     get_name(uint64_t* context)            { return (char*)     *(context + 20); }

uint64_t* get_used_list_head(uint64_t* context)   { return (uint64_t*) *(context + 21); }
uint64_t* get_free_list_head(uint64_t* context)   { return (uint64_t*) *(context + 22); }
uint64_t  get_gcs_in_period(uint64_t* context)    { return             *(context + 23); }
uint64_t  get_use_gc_kernel(uint64_t* context)    { return             *(context + 24); }

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
void set_code_seg_size(uint64_t* context, uint64_t size)      { *(context + 10) = size; }
void set_data_seg_start(uint64_t* context, uint64_t start)    { *(context + 11) = start; }
void set_data_seg_size(uint64_t* context, uint64_t size)      { *(context + 12) = size; }
void set_heap_seg_start(uint64_t* context, uint64_t start)    { *(context + 13) = start; }
void set_program_break(uint64_t* context, uint64_t brk)       { *(context + 14) = brk; }
void set_exception(uint64_t* context, uint64_t exception)     { *(context + 15) = exception; }
void set_fault(uint64_t* context, uint64_t page)              { *(context + 16) = page; }
void set_exit_code(uint64_t* context, uint64_t code)          { *(context + 17) = code; }
void set_parent(uint64_t* context, uint64_t* parent)          { *(context + 18) = (uint64_t) parent; }
void set_virtual_context(uint64_t* context, uint64_t* vctxt)  { *(context + 19) = (uint64_t) vctxt; }
void set_name(uint64_t* context, char* name)                  { *(context + 20) = (uint64_t) name; }

void set_used_list_head(uint64_t* context, uint64_t* used_list_head) { *(context + 21) = (uint64_t) used_list_head; }
void set_free_list_head(uint64_t* context, uint64_t* free_list_head) { *(context + 22) = (uint64_t) free_list_head; }
void set_gcs_in_period(uint64_t* context, uint64_t gcs)              { *(context + 23) = gcs; }
void set_use_gc_kernel(uint64_t* context, uint64_t use)              { *(context + 24) = use; }

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

uint64_t is_code_address(uint64_t* context, uint64_t vaddr);
uint64_t is_data_address(uint64_t* context, uint64_t vaddr);
uint64_t is_stack_address(uint64_t* context, uint64_t vaddr);
uint64_t is_heap_address(uint64_t* context, uint64_t vaddr);

uint64_t is_address_between_stack_and_heap(uint64_t* context, uint64_t vaddr);
uint64_t is_data_stack_heap_address(uint64_t* context, uint64_t vaddr);

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
uint64_t EXIT      = 1; // extended in symbolic execution engine

uint64_t EXITCODE_NOERROR                = 0;
uint64_t EXITCODE_NOARGUMENTS            = 11; // leaving 1-10 for apps
uint64_t EXITCODE_BADARGUMENTS           = 12;
uint64_t EXITCODE_MOREARGUMENTS          = 13;
uint64_t EXITCODE_SYSTEMERROR            = 14;
uint64_t EXITCODE_IOERROR                = 15;
uint64_t EXITCODE_SCANNERERROR           = 16;
uint64_t EXITCODE_PARSERERROR            = 17;
uint64_t EXITCODE_COMPILERERROR          = 18;
uint64_t EXITCODE_SYNTAXERROR            = 19;
uint64_t EXITCODE_OUTOFVIRTUALMEMORY     = 20;
uint64_t EXITCODE_OUTOFPHYSICALMEMORY    = 21;
uint64_t EXITCODE_DIVISIONBYZERO         = 22;
uint64_t EXITCODE_UNKNOWNINSTRUCTION     = 23;
uint64_t EXITCODE_UNKNOWNSYSCALL         = 24;
uint64_t EXITCODE_UNSUPPORTEDSYSCALL     = 25;
uint64_t EXITCODE_MULTIPLEEXCEPTIONERROR = 26;
uint64_t EXITCODE_UNCAUGHTEXCEPTION      = 27;

uint64_t SYSCALL_BITWIDTH = 32; // integer bit width for system calls

uint64_t MIPSTER = 1;
uint64_t DIPSTER = 2;
uint64_t RIPSTER = 3;

uint64_t HYPSTER = 4;

uint64_t MINSTER = 5;
uint64_t MOBSTER = 6;

uint64_t CAPSTER = 7;

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
void init_target();

void turn_on_gc_library(uint64_t period, char* name);

void experimental_features();

// ------------------------ GLOBAL CONSTANTS -----------------------

char* selfie_name = (char*) 0; // name of running selfie executable

// IDs for host operating systems

uint64_t SELFIE    = 0;
uint64_t LINUX     = 1;
uint64_t MACOS     = 2;
uint64_t WINDOWS   = 3;
uint64_t BAREMETAL = 4;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t OS = 0; // default host operating system is selfie

// ------------------------- INITIALIZATION ------------------------

void init_selfie(uint64_t argc, uint64_t* argv) {
  selfie_argc = argc;
  selfie_argv = argv;

  selfie_name = get_argument();
}

void init_system() {
  uint64_t selfie_fd;

  if (SIZEOFUINT64 != SIZEOFUINT64STAR)
    // selfie requires an LP64 or ILP32 data model
    // uint64_t and uint64_t* must be the same size
    exit(EXITCODE_SYSTEMERROR);

  if (SIZEOFUINT64INBITS != 64) {
    if (SIZEOFUINT64INBITS == 32) {
      IS64BITSYSTEM = 0;
      IS64BITTARGET = 0;
    } else
      // selfie only supports 32-bit and 64-bit systems
      exit(EXITCODE_SYSTEMERROR);
  }

  if (is_boot_level_zero()) {
    // try opening executable
    selfie_fd = open_read_only(selfie_name);

    if (signed_less_than(selfie_fd, 0))
      // failure likely indicates Windows
      OS = WINDOWS;
    else {
      // read first byte of magic number
      read(selfie_fd, binary_buffer, 1);

      if (*binary_buffer == EI_MAG0)
        OS = LINUX;
      else if (*binary_buffer == MACHO_MAG0)
        OS = MACOS;
      else
        OS = WINDOWS;
    }
  } else
    OS = SELFIE;

  if (OS == MACOS)
    O_CREAT_TRUNC_WRONLY = MAC_O_CREAT_TRUNC_WRONLY;
  else if (OS == WINDOWS)
    O_CREAT_TRUNC_WRONLY = WINDOWS_O_BINARY_CREAT_TRUNC_WRONLY;
  else
    // Linux file opening flags are the default for Linux, selfie, and bare-metal hosts
    O_CREAT_TRUNC_WRONLY = LINUX_O_CREAT_TRUNC_WRONLY;
}

void init_target() {
  if (IS64BITTARGET) {
    if (IS64BITSYSTEM) {
      SIZEOFUINT = SIZEOFUINT64;
      UINT_MAX   = UINT64_MAX;

      WORDSIZE       = SIZEOFUINT64;
      WORDSIZEINBITS = WORDSIZE * 8;

      MAX_INTEGER_LENGTH = 20; // 2^64-1 requires 20 decimal digits

      // configuring ELF64 file header

      EI_CLASS = ELFCLASS64; // file class is 2 (ELFCLASS64)

      e_phoff = 64; // program header offset 0x40 (ELFCLASS64)

      e_ehsize    = 64; // elf header size 64 bytes (ELFCLASS64)
      e_phentsize = 56; // size of program header entry 56 bytes (ELFCLASS64)
    } else
      // selfie does not support 64-bit targets on 32-bit systems
      exit(EXITCODE_SYSTEMERROR);
  } else {
    if (IS64BITSYSTEM) {
      SIZEOFUINT = SINGLEWORDSIZE;
      UINT_MAX   = two_to_the_power_of(SINGLEWORDSIZEINBITS) - 1;

      WORDSIZE = SINGLEWORDSIZE;
    } else {
      SIZEOFUINT = SIZEOFUINT64;
      UINT_MAX   = UINT64_MAX;

      WORDSIZE = SIZEOFUINT64;
    }

    WORDSIZEINBITS = WORDSIZE * 8;

    MAX_INTEGER_LENGTH = 10; // 2^32-1 requires 10 decimal digits

    // configuring ELF32 file header

    EI_CLASS = ELFCLASS32; // file class is 1 (ELFCLASS32)

    e_phoff = 52; // program header offset 0x34 (ELFCLASS32)

    e_ehsize    = 52; // elf header size 52 bytes (ELFCLASS32)
    e_phentsize = 32; // size of program header entry 32 bytes (ELFCLASS32)
  }

  HIGHESTVIRTUALADDRESS = VIRTUALMEMORYSIZE * GIGABYTE - WORDSIZE;
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
  // assert: 0 <= p < SIZEOFUINT64INBITS
  return *(power_of_two_table + p);
}

uint64_t log_two(uint64_t n) {
  // use recursion for simplicity and educational value
  // for n < 0x10000 performance is not relevant
  if (n < 2)
    return 0;
  else
    return log_two(n / 2) + 1;
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
  // assert: 0 <= b < SIZEOFUINT64INBITS
  return n * two_to_the_power_of(b);
}

uint64_t right_shift(uint64_t n, uint64_t b) {
  // assert: 0 <= b < SIZEOFUINT64INBITS
  return n / two_to_the_power_of(b);
}

uint64_t get_bits(uint64_t n, uint64_t i, uint64_t b) {
  // assert: 0 <= i + b <= SIZEOFUINT64INBITS
  // assert: 0 < b
  if (b < SIZEOFUINT64INBITS)
    return right_shift(n, i) % two_to_the_power_of(b);
  else
    return right_shift(n, i);
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
  // assert: 0 < b <= SIZEOFUINT64INBITS
  if (n < two_to_the_power_of(b - 1))
    return 1;
  else if (n >= -two_to_the_power_of(b - 1))
    return 1;
  else
    return 0;
}

uint64_t sign_extend(uint64_t n, uint64_t b) {
  // assert: -2^(b - 1) <= n < 2^(b - 1)
  // assert: 0 < b <= SIZEOFUINT64INBITS
  if (n < two_to_the_power_of(b - 1))
    return n;
  else if (b < SIZEOFUINT64INBITS)
    return n - two_to_the_power_of(b);
  else
    return n;
}

uint64_t sign_shrink(uint64_t n, uint64_t b) {
  // assert: 0 < b <= SIZEOFUINT64INBITS
  return get_bits(n, 0, b);
}

char load_character(char* s, uint64_t i) {
  // assert: i >= 0
  uint64_t a;

  // a is the index of the word where the
  // to-be-loaded i-th character in s is
  a = i / SIZEOFUINT64;

  // CAUTION: at boot levels higher than 0, s is only accessible
  // in C* at word granularity, not individual characters

  // return i-th 8-bit character in s
  return get_bits(*((uint64_t*) s + a), (i % SIZEOFUINT64) * 8, 8);
}

char* store_character(char* s, uint64_t i, char c) {
  // assert: i >= 0, 0 <= c < 2^8 (all characters are 8-bit)
  uint64_t a;

  // a is the index of the word where the with c
  // to-be-overwritten i-th character in s is
  a = i / SIZEOFUINT64;

  // CAUTION: at boot levels higher than 0, s is only accessible
  // in C* at word granularity, not individual characters

  // subtract the to-be-overwritten character to reset its bits in s
  // then add c to set its bits at the i-th position in s
  *((uint64_t*) s + a) = (*((uint64_t*) s + a) - left_shift(load_character(s, i), (i % SIZEOFUINT64) * 8)) + left_shift(c, (i % SIZEOFUINT64) * 8);

  return s;
}

uint64_t is_letter(char c) {
  // ASCII codes for lower- and uppercase letters are in contiguous intervals
  if (c >= 'a')
    if (c <= 'z')
      return 1;
    else
      return 0;
  else if (c >= 'A')
    if (c <= 'Z')
      return 1;
    else
      return 0;
  else
    return 0;
}

uint64_t is_digit(char c) {
  // ASCII codes for digits are in a contiguous interval
  if (c >= '0')
    if (c <= '9')
      return 1;
    else
      return 0;
  else
    return 0;
}

char* string_alloc(uint64_t l) {
  // allocates zeroed memory for a string of l characters
  // plus a null terminator aligned to word size
  return (char*) zmalloc(l + 1);
}

uint64_t string_length(char* s) {
  uint64_t i;

  i = 0;

  while (load_character(s, i) != 0)
    i = i + 1;

  return i;
}

char* string_shrink(char* s) {
  uint64_t l;
  uint64_t i;
  char* t;

  l = string_length(s);

  i = 0;

  while (i < l)
    if (load_character(s, i) == ' ')
      // discard any characters to the right of a space
      l = i;
    else
      i = i + 1;

  t = string_alloc(l);

  i = 0;

  while (i < l) {
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
  // bit shifting since memory access can only be done at word granularity
  c = load_character(s, i);

  // loop until s is terminated
  while (c != 0) {
    // the numerical value of ASCII-encoded decimal digits
    // is offset by the ASCII code of '0' (which is 48)
    c = c - '0';

    if (c > 9) {
      printf("%s: cannot convert non-decimal number %s\n", selfie_name, s);

      exit(EXITCODE_SCANNERERROR);
    }

    // assert: s contains a decimal number

    // use base 10 but detect wrap around
    if (n < UINT_MAX / 10)
      n = n * 10 + c;
    else if (n == UINT_MAX / 10)
      if (c <= UINT_MAX % 10)
        n = n * 10 + c;
      else {
        // s contains a decimal number larger than UINT_MAX
        printf("%s: cannot convert out-of-bound number %s\n", selfie_name, s);

        exit(EXITCODE_SCANNERERROR);
      }
    else {
      // s contains a decimal number larger than UINT_MAX
      printf("%s: cannot convert out-of-bound number %s\n", selfie_name, s);

      exit(EXITCODE_SCANNERERROR);
    }

    // go to the next digit
    i = i + 1;

    // load character (one byte) at index i in s from memory requires
    // bit shifting since memory access can only be done at word granularity
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

  }

  store_character(s, i, 0); // null-terminated string

  // our numeral system is positional hindu-arabic, that is,
  // the weight of digits increases right to left, which means
  // that we need to reverse the string we computed above
  string_reverse(s);

  return s;
}

uint64_t fixed_point_ratio(uint64_t a, uint64_t b, uint64_t f) {
  // compute fixed-point ratio with f fractional digits
  return a / b * ten_to_the_power_of(f) + a % b * ten_to_the_power_of(f) / b;
}

uint64_t fixed_point_percentage(uint64_t r, uint64_t f) {
  if (r != 0)
    // 10^4 (for 100.00%) * 10^f (for f fractional digits of r)
    return ten_to_the_power_of(4 + f) / r;
  else
    return 0;
}

uint64_t fixed_point_integral(uint64_t a, uint64_t f) {
  return a / ten_to_the_power_of(f);
}

uint64_t fixed_point_fractional(uint64_t a, uint64_t f) {
 return a % ten_to_the_power_of(f);
}

uint64_t ratio_format_integral_2(uint64_t a, uint64_t b) {
  return fixed_point_integral(fixed_point_ratio(a, b, 2), 2);
}

uint64_t ratio_format_fractional_2(uint64_t a, uint64_t b) {
  return fixed_point_fractional(fixed_point_ratio(a, b, 2), 2);
}

uint64_t percentage_format_integral_2(uint64_t a, uint64_t b) {
  if (b != 0)
    return fixed_point_integral(fixed_point_percentage(fixed_point_ratio(a, b, 4), 4), 2);
  else
    return 0;
}

uint64_t percentage_format_fractional_2(uint64_t a, uint64_t b) {
  if (b != 0)
    return fixed_point_fractional(fixed_point_percentage(fixed_point_ratio(a, b, 4), 4), 2);
  else
    return 0;
}

void put_character(char c) {
  uint64_t written_bytes;

  if (output_buffer) {
    // buffering character instead of outputting
    store_character(output_buffer, output_cursor, c);

    output_cursor = output_cursor + 1;
  } else if (character_buffer) {
    *character_buffer = c;

    // assert: character_buffer is mapped

    if (output_fd == 1) {
      if (OS != SELFIE)
        // on bootlevel zero use printf to print on console
        // to keep output synchronized with other printf output
        written_bytes = printf("%c", c);
      else
        // on non-zero bootlevel use write to print on console
        // to avoid infinite loop back to printf
        written_bytes = write(output_fd, (uint64_t*) character_buffer, 1);
    } else
      // try to write 1 character from character_buffer
      // into file with output_fd file descriptor
      written_bytes = write(output_fd, (uint64_t*) character_buffer, 1);

    if (written_bytes != 1) {
      // output failed
      if (output_fd != 1) {
        // failed output was not to console which has file descriptor 1
        // to report the error we may thus still write to the console
        output_fd = 1;

        printf("%s: could not write character into output file %s\n", selfie_name, output_name);
      }

      exit(EXITCODE_IOERROR);
    }
  } else
    // character_buffer has not been successfully allocated yet
    exit(EXITCODE_IOERROR);

  number_of_put_characters = number_of_put_characters + 1;
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
  // not used in printf implementation
  printf("\n");
}

void print_character(char c) {
  // not used in printf implementation
  if (c == CHAR_EOF)
    printf("'end of file'");
  else if (c == CHAR_TAB)
    printf("'tabulator'");
  else if (c == CHAR_LF)
    printf("'line feed'");
  else if (c == CHAR_CR)
    printf("'carriage return'");
  else
    printf("'%c'", c);
}

void print_string(char* s) {
  // not used in printf implementation
  printf("\"%s\"", s);
}

void print_unsigned_integer(uint64_t n) {
  // use print, not printf to avoid recursion
  print(itoa(n, integer_buffer, 10, 0, 0));
}

void print_integer(uint64_t n) {
  // use print, not printf to avoid recursion
  print(itoa(n, integer_buffer, 10, 1, 0));
}

void print_fractional(uint64_t n, uint64_t p) {
  uint64_t d;

  // number of digits of n
  d = log_ten(n) + 1;

  while (p > d) {
    put_character('0');

    p = p - 1;
  }

  // use print, not printf to avoid recursion
  print(itoa(n, integer_buffer, 10, 0, 0));
}

void unprint_integer(uint64_t n) {
  n = string_length(itoa(n, integer_buffer, 10, 1, 0));

  while (n > 0) {
    put_character(CHAR_BACKSPACE);

    n = n - 1;
  }
}

void print_hexadecimal_no_prefix(uint64_t n, uint64_t a) {
  // use print, not printf to avoid recursion
  print(itoa(n, integer_buffer, 16, 0, a));
}

void print_hexadecimal(uint64_t n, uint64_t a) {
  printf("0x");print_hexadecimal_no_prefix(n, a);
}

void print_octal_no_prefix(uint64_t n, uint64_t a) {
  // use print, not printf to avoid recursion
  print(itoa(n, integer_buffer, 8, 0, a));
}

void print_octal(uint64_t n, uint64_t a) {
  printf("0o");print_octal_no_prefix(n, a);
}

void print_binary_no_prefix(uint64_t n, uint64_t a) {
  // use print, not printf to avoid recursion
  print(itoa(n, integer_buffer, 2, 0, a));
}

void print_binary(uint64_t n, uint64_t a) {
  printf("0b");print_binary_no_prefix(n, a);
}

uint64_t print_format(char* s, uint64_t i, char* a) {
  // print argument a according to the encountered % formatting code
  // that starts at position i in string s

  uint64_t p;

  if (load_character(s, i) == 's') {
    print(a);

    return i + 1;
  } else if (load_character(s, i) == 'c') {
    put_character((uint64_t) a);

    return i + 1;
  } else if (load_character(s, i) == 'l') {
    if (load_character(s, i + 1) == 'u') {
      print_unsigned_integer((uint64_t) a);

      return i + 2;
    } else if (load_character(s, i + 1) == 'd') {
      print_integer((uint64_t) a);

      return i + 2;
    } else if (load_character(s, i + 1) == 'X') {
      print_hexadecimal_no_prefix((uint64_t) a, 0);

      return i + 2;
    } else if (load_character(s, i + 1) == 'o') {
      print_octal_no_prefix((uint64_t) a, 0);

      return i + 2;
    }
  } else if (load_character(s, i) == 'b') {
    print_binary_no_prefix((uint64_t) a, 0);

    return i + 1;
  } else if (load_character(s, i) == '.') {
    // for integer specifiers, precision specifies
    // the minimum number of digits to be written;
    // we only support single-digit precision
    p = load_character(s, i + 1);

    if (is_digit(p))
      if (load_character(s, i + 2) == 'l')
        if (load_character(s, i + 3) == 'u') {
          // precision support only for %lu
          print_fractional((uint64_t) a, p - '0');

          return i + 4;
        }
  } else if (load_character(s, i) == '0') {
    // we only support padding with 0s and single-digit width
    p = load_character(s, i + 1);

    if (is_digit(p))
      if (load_character(s, i + 2) == 'l')
        if (load_character(s, i + 3) == 'X') {
          // padding support only for %lX
          print_hexadecimal_no_prefix((uint64_t) a, p - '0');

          return i + 4;
        }
  }

  return i;
}

uint64_t vdsprintf(uint64_t fd, char* buffer, char* s, uint64_t* args) {
  uint64_t save_fd;
  uint64_t i;

  save_fd = output_fd;

  if (buffer) {
    output_buffer = buffer;
    output_cursor = 0;
  } else
    output_fd = fd;

  number_of_put_characters = 0;

  i = 0;

  if (s != (char*) 0) {
    while (load_character(s, i) != 0) {
      if (load_character(s, i) == '%') {
        i = i + 1;

        if (load_character(s, i) != 0) {
          if (load_character(s, i) != '%')
            i = print_format(s, i, var_arg(args));
          else {
            // for %% print just one %
            put_character('%');

            i = i + 1;
          }
        }
      } else {
        put_character(load_character(s, i));

        i = i + 1;
      }
    }

    // sprintf always null-terminates the buffer
    if (buffer)
      store_character(buffer, output_cursor, 0);
  }

  if (buffer) {
    output_buffer = (char*) 0;
    output_cursor = 0;
  }

  output_fd = save_fd;

  return number_of_put_characters;
}

uint64_t selfie_printf(char* format, ...) {
  uint64_t* args;
  uint64_t written_bytes;

  args = (uint64_t*) 0;

  var_start(args);
  written_bytes = vdsprintf(1, (char*) 0, format, args);
  var_end(args);

  return written_bytes;
}

uint64_t selfie_sprintf(char* buffer, char* format, ...) {
  uint64_t* args;
  uint64_t written_bytes;

  args = (uint64_t*) 0;

  var_start(args);
  written_bytes = vdsprintf(0, buffer, format, args);
  var_end(args);

  return written_bytes;
}

uint64_t selfie_dprintf(uint64_t fd, char* format, ...) {
  uint64_t* args;
  uint64_t written_bytes;

  args = (uint64_t*) 0;

  var_start(args);
  written_bytes = vdsprintf(fd, (char*) 0, format, args);
  var_end(args);

  return written_bytes;
}

char* remove_prefix_from_printf_procedures(char* procedure) {
  // for bootstrapping remove prefix from selfie *printf procedures
  if (string_compare(procedure, "selfie_printf"))
    // length of string literal must be multiple of SIZEOFUINT64;
    // trailing spaces are removed by string_shrink resulting
    // in unique hash for global symbol table
    return string_shrink("printf ");
  else if (string_compare(procedure, "selfie_sprintf"))
    // "sprintf" is 7 characters plus null termination
    return "sprintf";
  else if (string_compare(procedure, "selfie_dprintf"))
    // "dprintf" is 7 characters plus null termination
    return "dprintf";
  else
    return procedure;
}

uint64_t round_up(uint64_t n, uint64_t m) {
  if (n % m == 0)
    return n;
  else
    return n - n % m + m;
}

uint64_t* smalloc(uint64_t size) {
  // use this procedure, instead of malloc, for heap allocation
  // to ensure a defined program exit if no memory can be allocated
  uint64_t* memory;

  if (USE_GC_LIBRARY)
    memory = gc_malloc(size);
  else
    memory = malloc(size);

  if (size == 0)
    // any address including 0
    return memory;
  else if (memory != (uint64_t*) 0)
    return memory;
  else {
    if (character_buffer)
      // can only print error message if character_buffer has been successfully allocated
      printf("%s: malloc out of memory\n", selfie_name);

    exit(EXITCODE_OUTOFVIRTUALMEMORY);
  }
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

uint64_t* zalloc(uint64_t size) {
  // internal use only!

  // this procedure is only executed at boot level 0;
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
  // use this procedure, instead of smalloc,
  // if allocated memory needs to be zeroed
  if (USE_GC_LIBRARY)
    // assert: on boot level 1 or above mallocated memory is zeroed
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
  if (symbol == SYM_EOF)
    print_string("end of file");
  else
    print_string((char*) *(SYMBOLS + symbol));
}

void print_line_number(char* message, uint64_t line) {
  printf("%s: %s in %s in line %lu: ", selfie_name, message, source_name, line);
}

void syntax_error_message(char* message) {
  print_line_number("syntax error", line_number);
  printf("%s\n", message);

  number_of_syntax_errors = number_of_syntax_errors + 1;
}

void syntax_error_expected_character(char expected) {
  print_line_number("syntax error", line_number);
  print_character(expected);
  printf(" expected but ");
  print_character(character);
  printf(" found\n");

  number_of_syntax_errors = number_of_syntax_errors + 1;
}

void get_character() {
  uint64_t number_of_read_bytes;

  // assert: character_buffer is mapped

  // try to read 1 character into character_buffer
  // from file with source_fd file descriptor
  number_of_read_bytes = read(source_fd, (uint64_t*) character_buffer, 1);

  if (number_of_read_bytes == 1) {
    // store the read character in the global variable called character
    character = *character_buffer;

    number_of_read_characters = number_of_read_characters + 1;
  } else if (number_of_read_bytes == 0)
    // reached end of file
    character = CHAR_EOF;
  else {
    printf("%s: could not read character from input file %s\n", selfie_name, source_name);

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

char find_next_character() {
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

uint64_t is_character_letter_or_digit_or_underscore() {
  if (is_letter(character))
    return 1;
  else if (is_digit(character))
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
  else if (identifier_string_match(SYM_CONST))
    // selfie bootstraps const to uint64_t!
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

      // start state of finite state machine
      // for recognizing C* symbols is here
      if (is_letter(character)) {
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
      } else if (is_digit(character)) {
        if (character == '0') {
          // 0 is 0, not 00, 000, etc.
          get_character();

          literal = 0;
        } else {
          // accommodate integer and null for termination
          integer = string_alloc(MAX_INTEGER_LENGTH);

          i = 0;

          while (is_digit(character)) {
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
          syntax_error_expected_character(CHAR_SINGLEQUOTE);

          exit(EXITCODE_SCANNERERROR);
        } else
          syntax_error_expected_character(CHAR_SINGLEQUOTE);

        symbol = SYM_CHARACTER;
      } else if (character == CHAR_DOUBLEQUOTE) {
        get_character();

        // accommodate string and null for termination,
        // allocate zeroed memory since strings are emitted
        // in words but may end non-word-aligned
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
          syntax_error_expected_character(CHAR_DOUBLEQUOTE);

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
          syntax_error_expected_character(CHAR_EQUAL);

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
      } else if (character == CHAR_DOT) {
        get_character();

        if (character == CHAR_DOT) {
          get_character();

          if (character == CHAR_DOT)
            get_character();
          else
            syntax_error_expected_character(CHAR_DOT);
        } else
          syntax_error_expected_character(CHAR_DOT);

        symbol = SYM_ELLIPSIS;
      } else {
        print_line_number("syntax error", line_number);
        printf("found unknown character ");
        print_character(character);
        println();

        number_of_syntax_errors = number_of_syntax_errors + 1;

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

uint64_t* create_symbol_table_entry(uint64_t table, char* string,
  uint64_t line, uint64_t class, uint64_t type, uint64_t value, uint64_t address) {
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
  if (table == GLOBAL_TABLE) {
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
  } else if (table == LOCAL_TABLE) {
    set_scope(new_entry, REG_S0);
    set_next_entry(new_entry, local_symbol_table);
    local_symbol_table = new_entry;
  } else {
    set_scope(new_entry, REG_GP);
    set_next_entry(new_entry, library_symbol_table);
    library_symbol_table = new_entry;
  }

  return new_entry;
}

uint64_t* search_symbol_table(uint64_t* entry, char* string, uint64_t class) {
  number_of_searches = number_of_searches + 1;

  while (entry != (uint64_t*) 0) {
    total_search_time = total_search_time + 1;

    if (class == get_class(entry))
      if (string_compare(string, get_string(entry)))
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
  if (get_class(entry) != PROCEDURE)
    return 0;

  if (get_address(entry) == 0)
    // procedure declared but not defined
    return 1;
  else if (get_opcode(load_instruction(get_address(entry))) == OP_JAL)
    // procedure called but not defined
    return 1;
  else
    return 0;
}

uint64_t is_library_procedure(char* name) {
  return search_symbol_table(library_symbol_table, name, PROCEDURE) != (uint64_t*) 0;
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
      if (is_library_procedure(get_string(entry)) == 0)
        if (is_undefined_procedure(entry)) {
          undefined = 1;

          print_line_number("syntax error", get_line_number(entry));
          printf("procedure %s undefined\n", get_string(entry));

          number_of_syntax_errors = number_of_syntax_errors + 1;
      }

      // keep looking
      entry = get_next_entry(entry);
    }

    i = i + 1;
  }

  return undefined;
}

// -----------------------------------------------------------------
// ---------------------- REGISTER ALLOCATOR -----------------------
// -----------------------------------------------------------------

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

// -----------------------------------------------------------------
// ---------------------------- PARSER -----------------------------
// -----------------------------------------------------------------

uint64_t is_type() {
  return symbol == SYM_UINT64;
}

uint64_t is_value() {
  if (symbol == SYM_INTEGER)
    return 1;
  else if (symbol == SYM_CHARACTER)
    return 1;
  else
    return 0;
}

uint64_t is_expression() {
  return is_factor();
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

uint64_t is_plus_or_minus() {
  if (symbol == SYM_PLUS)
    return 1;
  else if (symbol == SYM_MINUS)
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

uint64_t is_factor() {
  if (symbol == SYM_LPARENTHESIS)
    return 1;
  else if (symbol == SYM_MINUS)
    return 1;
  else if (symbol == SYM_ASTERISK)
    return 1;
  else if (is_literal())
    return 1;
  else if (symbol == SYM_IDENTIFIER)
    return 1;
  else
    return 0;
}

uint64_t is_literal() {
  if (is_value())
    return 1;
  else if (symbol == SYM_STRING)
    return 1;
  else
    return 0;
}

uint64_t is_neither_rbrace_nor_eof() {
  if (symbol == SYM_RBRACE)
    return 0;
  else if (symbol == SYM_EOF)
    return 0;
  else
    return 1;
}

uint64_t is_possibly_parameter(uint64_t is_already_variadic) {
  if (symbol == SYM_COMMA)
    if (is_already_variadic == 0)
      return 1;

  return 0;
}

uint64_t is_neither_type_nor_void() {
  if (is_type())
    return 0;
  else if (symbol == SYM_VOID)
    return 0;
  else if (symbol == SYM_EOF)
    return 0;
  else
    return 1;
}

uint64_t is_not_statement() {
  if (symbol == SYM_ASTERISK)
    return 0;
  else if (symbol == SYM_IDENTIFIER)
    return 0;
  else if (symbol == SYM_IF)
    return 0;
  else if (symbol == SYM_WHILE)
    return 0;
  else if (symbol == SYM_RETURN)
    return 0;
  else if (symbol == SYM_EOF)
    return 0;
  else
    return 1;
}

uint64_t is_not_factor() {
  if (is_factor())
    return 0;
  else if (symbol == SYM_EOF)
    return 0;
  else
    return 1;
}

void syntax_error_expected_symbol(uint64_t expected) {
  print_line_number("syntax error", line_number);
  print_symbol(expected);
  printf(" expected but ");
  print_symbol(symbol);
  printf(" found\n");

  number_of_syntax_errors = number_of_syntax_errors + 1;
}

void syntax_error_unexpected_symbol() {
  print_line_number("syntax error", line_number);
  printf("unexpected symbol ");
  print_symbol(symbol);
  printf(" found\n");

  number_of_syntax_errors = number_of_syntax_errors + 1;
}

uint64_t get_expected_symbol(uint64_t expected_symbol) {
  if (symbol == expected_symbol) {
    get_symbol();

    return 1;
  }

  syntax_error_expected_symbol(expected_symbol);

  return 0;
}

void get_required_symbol(uint64_t required_symbol) {
  if (get_expected_symbol(required_symbol) == 0)
    exit(EXITCODE_PARSERERROR);
}

void syntax_error_undeclared_identifier(char* name) {
  print_line_number("syntax error", line_number);
  printf("%s undeclared\n", name);

  number_of_syntax_errors = number_of_syntax_errors + 1;
}

void syntax_error_unexpected_identifier(char* expected) {
  print_line_number("syntax error", line_number);
  printf("%s expected but %s found\n", expected, identifier);

  number_of_syntax_errors = number_of_syntax_errors + 1;
}

void print_type(uint64_t type) {
  if (type == UINT64_T)
    printf("uint64_t");
  else if (type == UINT64STAR_T)
    printf("uint64_t*");
  else if (type == VOID_T)
    printf("void");
  else if (type == UNDECLARED_T)
    printf("undeclared");
  else
    printf("unknown");
}

void type_warning(uint64_t expected, uint64_t found) {
  print_line_number("warning", line_number);
  printf("type mismatch, ");
  print_type(expected);
  printf(" expected but ");
  print_type(found);
  printf(" found\n");
}

void compile_cstar() {
  uint64_t type;
  char* variable_or_procedure;
  uint64_t* entry;

  while (symbol != SYM_EOF) {
    while (is_neither_type_nor_void()) {
      syntax_error_unexpected_symbol();

      if (symbol == SYM_EOF)
        exit(EXITCODE_PARSERERROR);
      else
        get_symbol();
    }

    if (is_type()) {
      type = compile_type();

      if (symbol == SYM_IDENTIFIER) {
        variable_or_procedure = identifier;

        get_symbol();

        if (symbol != SYM_LPARENTHESIS) {
          // type identifier [ initialize ] ";"
          // global variable declaration or definition
          entry = compile_variable(variable_or_procedure, type, 0);

          set_value(entry, compile_initialize(type));

          get_expected_symbol(SYM_SEMICOLON);
        } else
          // type identifier "(" ...
          // procedure declaration or definition
          compile_procedure(variable_or_procedure, type);
      } else
        syntax_error_expected_symbol(SYM_IDENTIFIER);
    } else if (symbol == SYM_VOID) {
      // not a type, must be void, followed by procedure
      get_symbol();

      if (symbol == SYM_ASTERISK) {
        // we tolerate void* return types for bootstrapping
        get_symbol();

        type = UINT64STAR_T;
      } else
        type = VOID_T;

      if (symbol == SYM_IDENTIFIER) {
        // void identifier "(" ...
        // procedure declaration or definition
        variable_or_procedure = identifier;

        get_symbol();

        compile_procedure(variable_or_procedure, type);
      } else
        syntax_error_expected_symbol(SYM_IDENTIFIER);
    } else
      syntax_error_unexpected_symbol();
  }
}

uint64_t* compile_variable(char* variable, uint64_t type, uint64_t offset) {
  uint64_t* entry;

  if (variable != (char*) 0) {
    // global variable
    entry = search_global_symbol_table(variable, VARIABLE);

    if (entry == (uint64_t*) 0) {
      // allocate memory for global variable in data segment
      data_size = data_size + WORDSIZE;

      entry = create_symbol_table_entry(GLOBAL_TABLE, variable,
        line_number, VARIABLE, type, 0, -data_size);
    } else {
      // global variable already declared or defined
      print_line_number("warning", line_number);
      printf("redefinition of global variable %s ignored\n", variable);
    }
  } else {
    // local variable or formal parameter
    if (symbol == SYM_IDENTIFIER) {
      // TODO: check if identifier has already been declared
      entry = create_symbol_table_entry(LOCAL_TABLE, identifier,
        line_number, VARIABLE, type, 0, offset);

      get_symbol();
    } else {
      syntax_error_expected_symbol(SYM_IDENTIFIER);

      entry = create_symbol_table_entry(LOCAL_TABLE, "no_name",
        line_number, VARIABLE, type, 0, offset);
    }
  }

  return entry;
}

uint64_t compile_type() {
  uint64_t type;

  type = UINT64_T;

  if (is_type()) {
    get_symbol();

    while (is_type())
      // we tolerate multiple uint64_t aliases for bootstrapping
      get_symbol();

    while (symbol == SYM_ASTERISK) {
      // we tolerate pointer to pointers for bootstrapping
      type = UINT64STAR_T;

      get_symbol();
    }
  } else
    syntax_error_expected_symbol(SYM_UINT64);

  // type is grammar attribute
  return type;
}

uint64_t compile_initialize(uint64_t type) {
  uint64_t cast;
  uint64_t initial_value;

  if (symbol == SYM_ASSIGN) {
    // "=" [ cast ] [ "-" ] value
    // global variable definition
    get_symbol();

    // optional: [ cast ]
    if (symbol == SYM_LPARENTHESIS) {
      get_symbol();

      cast = compile_type();

      if (type != cast)
        type_warning(type, cast);

      get_expected_symbol(SYM_RPARENTHESIS);
    } else if (type != UINT64_T)
      type_warning(type, UINT64_T);

    // optional: [ "-" ]
    if (symbol == SYM_MINUS) {
      integer_is_signed = 1;

      get_symbol();
    }

    // value
    initial_value = compile_value();

    if (integer_is_signed) {
      integer_is_signed = 0;

      return -initial_value;
    } else
      return initial_value;
  } else
    // uninitialized global variables are initialized to 0
    return 0;

  // initial value is grammar attribute
}

uint64_t compile_value() {
  if (is_value())
    get_symbol();
  else {
    syntax_error_unexpected_symbol();

    return 0;
  }

  return literal;
}

void compile_statement() {
  char* variable_or_procedure;

  // assert: allocated_temporaries == 0

  while (is_not_statement()) {
    syntax_error_unexpected_symbol();

    if (symbol == SYM_EOF)
      exit(EXITCODE_PARSERERROR);
    else
      get_symbol();
  }

  if (symbol == SYM_ASTERISK) {
    // assignment: "*" ...
    compile_assignment((char*) 0);

    get_expected_symbol(SYM_SEMICOLON);
  } else if (symbol == SYM_IDENTIFIER) {
    variable_or_procedure = identifier;

    get_symbol();

    if (symbol != SYM_LPARENTHESIS)
      // assignment: identifier ...
      compile_assignment(variable_or_procedure);
    else {
      // procedure call: identifier "(" ... ")"
      get_symbol();

      compile_call(variable_or_procedure);

      // reset return register to initial return value
      // for missing return expressions
      emit_addi(REG_A0, REG_ZR, 0);
    }

    get_expected_symbol(SYM_SEMICOLON);
  } else if (symbol == SYM_IF)
    compile_if();
  else if (symbol == SYM_WHILE)
    compile_while();
  else if (symbol == SYM_RETURN) {
    compile_return();

    get_expected_symbol(SYM_SEMICOLON);
  }

  // assert: allocated_temporaries == 0
}

uint64_t load_upper_value(uint64_t reg, uint64_t value) {
  uint64_t lower;
  uint64_t upper;

  // assert: -2^31 <= value < 2^31

  lower = get_bits(value,  0, 12);
  upper = get_bits(value, 12, 20);

  if (lower >= two_to_the_power_of(11)) {
    // add 1 which is effectively 2^12 to cancel sign extension of lower
    upper = upper + 1;

    // assert: 0 < upper <= 2^(32-12)
    emit_lui(reg, sign_extend(upper, 20));

    if (upper == two_to_the_power_of(19))
      // for example, value == 2147481600, in binary:

      // ..00 0111 1111 1111 1111 1111 1000 0000 0000
      //      ======================== --------------
      //               upper               lower

      // ..00 1000 0000 0000 0000 0000 1000 0000 0000
      //      ======================== --------------
      //             upper + 1             lower

      // ..11 1000 0000 0000 0000 0000 0000 0000 0000 = (upper + 1) sign-extended << 12
      // ..11 1111 1111 1111 1111 1111 1000 0000 0000 = lower sign-extended
      // ++++++++++++++++++++++++++++++++++++++++++++
      // ..11 0111 1111 1111 1111 1111 1000 0000 0000 = incorrect with 64 bits

      // upper overflowed, cancel sign extension (redundant for 32-bit systems)
      emit_sub(reg, REG_ZR, reg);

      // ..11 1000 0000 0000 0000 0000 0000 0000 0000 = (upper + 1) sign-extended << 12
      // --------------------------------------------
      // ..00 0111 1111 1111 1111 1111 1111 1111 1111 = one'complement
      // ..00 0000 0000 0000 0000 0000 0000 0000 0001 = 1
      // ++++++++++++++++++++++++++++++++++++++++++++
      // ..00 1000 0000 0000 0000 0000 0000 0000 0000 = 0 - ((upper + 1) sign-extended << 12)
      // ..11 1111 1111 1111 1111 1111 1000 0000 0000 = lower sign-extended
      // ++++++++++++++++++++++++++++++++++++++++++++
      // ..00 0111 1111 1111 1111 1111 1000 0000 0000 = correct with 32-bit and 64-bit systems
  } else
    // assert: 0 < upper < 2^(32-12)
    emit_lui(reg, sign_extend(upper, 20));

  return sign_extend(lower, 12);
}

uint64_t load_upper_address(uint64_t* entry) {
  uint64_t offset;

  offset = get_address(entry);

  if (is_signed_integer(offset, 12) == 0) {
    // offset does not fit 12-bit immediate value
    talloc();

    offset = load_upper_value(current_temporary(), offset);

    // calculate new base
    emit_add(current_temporary(), get_scope(entry), current_temporary());
  }

  // base changed to current temporary if offset != get_address(entry)
  return offset;
}

uint64_t load_value(uint64_t* entry) {
  uint64_t offset;

  // assert: n = allocated_temporaries

  offset = load_upper_address(entry);

  if (offset == get_address(entry)) {
    // offset fits 12-bit immediate value
    talloc();

    emit_load(current_temporary(), get_scope(entry), offset);
  } else
    // assert: current temporary is scope register + 20-MSB part of original offset
    // assert: offset is remaining 12-LSB part of original offset
    emit_load(current_temporary(), current_temporary(), offset);

  // assert: allocated_temporaries == n + 1

  return get_type(entry);
}

uint64_t* get_variable_entry(char* variable) {
  uint64_t* entry;

  entry = get_scoped_symbol_table_entry(variable, VARIABLE);

  if (entry == (uint64_t*) 0) {
    syntax_error_undeclared_identifier(variable);

    // TODO: declare global variables to continue parsing

    exit(EXITCODE_PARSERERROR);
  }

  return entry;
}

uint64_t load_variable(char* variable) {
  return load_value(get_variable_entry(variable));
}

void compile_assignment(char* variable) {
  uint64_t dereference;
  uint64_t* entry;
  uint64_t base;
  uint64_t offset;
  uint64_t ltype;
  uint64_t rtype;

  // assert: identifier has already been parsed if variable != (char*) 0

  // assert: allocated_temporaries == 0

  if (variable != (char*) 0) {
    // variable is identifier
    dereference = 0;

    entry = get_variable_entry(variable);

    base = get_scope(entry);

    // load variable upper address, if needed
    offset = load_upper_address(entry);

    if (offset != get_address(entry))
      // assert: allocated_temporaries == 1
      base = current_temporary();

    ltype = get_type(entry);
  } else {
    // "*" identifier | "*" "(" expression ")"
    get_required_symbol(SYM_ASTERISK);

    dereference = 1;

    if (symbol == SYM_IDENTIFIER) {
      variable = identifier;

      get_symbol();

      // load variable value (as address)
      ltype = load_variable(variable);
    } else if (symbol == SYM_LPARENTHESIS) {
      get_symbol();

      // load expression value (as address)
      ltype = compile_expression();

      get_expected_symbol(SYM_RPARENTHESIS);
    } else {
      syntax_error_unexpected_symbol();

      // we need allocated_temporaries == 1
      // to keep running the compiler
      talloc();

      // loading 0 to trigger store at address 0
      emit_addi(current_temporary(), REG_ZR, 0);

      // but no further warning below
      ltype = UINT64STAR_T;
    }

    // assert: allocated_temporaries == 1
    base   = current_temporary();
    offset = 0;
  }

  // assert: base + offset is address where to store

  if (symbol == SYM_ASSIGN) {
    get_symbol();

    if (dereference) {
      if (ltype != UINT64STAR_T)
        type_warning(UINT64STAR_T, ltype);
      else
        ltype = UINT64_T;
    }

    rtype = compile_expression();

    if (ltype != rtype)
      type_warning(ltype, rtype);

    // assign value of RHS in current temporary to LHS at base + offset
    emit_store(base, offset, current_temporary());

    tfree(1);

    number_of_assignments = number_of_assignments + 1;
  } else
    syntax_error_expected_symbol(SYM_ASSIGN);

  if (dereference)
    // assert: allocated_temporaries == 1
    tfree(1);
  else if (offset != get_address(entry))
    // assert: allocated_temporaries == 1
    tfree(1);

  // assert: allocated_temporaries == 0
}

uint64_t compile_expression() {
  uint64_t ltype;
  uint64_t operator_symbol;
  uint64_t rtype;

  // assert: n = allocated_temporaries

  ltype = compile_arithmetic();

  // assert: allocated_temporaries == n + 1

  //optional: ==, !=, <, >, <=, >= simple_expression
  if (is_comparison()) {
    operator_symbol = symbol;

    get_symbol();

    rtype = compile_arithmetic();

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

  // type of expression is grammar attribute
  return ltype;
}

uint64_t compile_arithmetic() {
  uint64_t ltype;
  uint64_t operator_symbol;
  uint64_t rtype;

  // assert: n = allocated_temporaries

  ltype = compile_term();

  // assert: allocated_temporaries == n + 1

  while (is_plus_or_minus()) {
    operator_symbol = symbol;

    get_symbol();

    rtype = compile_term();

    // assert: allocated_temporaries == n + 2

    if (operator_symbol == SYM_PLUS) {
      if (ltype == UINT64STAR_T) {
        if (rtype == UINT64_T)
          // UINT64STAR_T + UINT64_T
          // pointer arithmetic: left_term + right_term * SIZEOFUINT
          emit_multiply_by(current_temporary(), SIZEOFUINT);
        else
          // UINT64STAR_T + UINT64STAR_T
          syntax_error_message("(uint64_t*) + (uint64_t*) is undefined");
      } else if (rtype == UINT64STAR_T) {
        // UINT64_T + UINT64STAR_T
        // pointer arithmetic: left_term * SIZEOFUINT + right_term
        emit_multiply_by(previous_temporary(), SIZEOFUINT);

        ltype = UINT64STAR_T;
      }

      emit_add(previous_temporary(), previous_temporary(), current_temporary());

    } else if (operator_symbol == SYM_MINUS) {
      if (ltype == UINT64STAR_T) {
        if (rtype == UINT64_T) {
          // UINT64STAR_T - UINT64_T
          // pointer arithmetic: left_term - right_term * SIZEOFUINT
          emit_multiply_by(current_temporary(), SIZEOFUINT);
          emit_sub(previous_temporary(), previous_temporary(), current_temporary());
        } else {
          // UINT64STAR_T - UINT64STAR_T
          // pointer arithmetic: (left_term - right_term) / SIZEOFUINT
          emit_sub(previous_temporary(), previous_temporary(), current_temporary());
          emit_addi(current_temporary(), REG_ZR, SIZEOFUINT);
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

  // type of simple expression is grammar attribute
  return ltype;
}

uint64_t compile_term() {
  uint64_t ltype;
  uint64_t operator_symbol;
  uint64_t rtype;

  // assert: n = allocated_temporaries

  ltype = compile_factor();

  // assert: allocated_temporaries == n + 1

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

  // type of term is grammar attribute
  return ltype;
}

uint64_t compile_factor() {
  uint64_t has_cast;
  uint64_t cast;
  uint64_t type;
  uint64_t negative;
  uint64_t dereference;
  char* variable_or_procedure;

  // assert: n = allocated_temporaries

  while (is_not_factor()) {
    syntax_error_unexpected_symbol();

    if (symbol == SYM_EOF)
      exit(EXITCODE_PARSERERROR);
    else
      get_symbol();
  }
  // optional: cast
  if (symbol == SYM_LPARENTHESIS) {
    // possibly a cast
    has_cast = 1;

    get_symbol();

    if (is_type()) {
      // cast: "(" "uint64_t" [ "*" ] ")"
      cast = compile_type();

      get_expected_symbol(SYM_RPARENTHESIS);
    } else {
      // not a cast but: "(" expression ")"
      type = compile_expression();

      get_expected_symbol(SYM_RPARENTHESIS);

      // assert: allocated_temporaries == n + 1

      return type;
    }
  } else
    has_cast = 0;
  // optional: "-"
  if (symbol == SYM_MINUS) {
    negative = 1;

    integer_is_signed = 1;

    get_symbol();

    integer_is_signed = 0;
  } else
    negative = 0;
  // optional: "*"
  if (symbol == SYM_ASTERISK) {
    dereference = 1;

    get_symbol();
  } else
    dereference = 0;

  if (is_literal())
    // integer, character, or string literal
    type = compile_literal();
  else if (symbol == SYM_IDENTIFIER) {
    variable_or_procedure = identifier;

    get_symbol();

    if (symbol != SYM_LPARENTHESIS)
      // variable access: identifier ...
      type = load_variable(variable_or_procedure);
    else {
      // procedure call: identifier "(" ... ")"
      get_symbol();

      type = compile_call(variable_or_procedure);

      talloc();

      // retrieve return value
      emit_addi(current_temporary(), REG_A0, 0);

      // reset return register to initial return value
      // for missing return expressions
      emit_addi(REG_A0, REG_ZR, 0);
    }
  } else if (symbol == SYM_LPARENTHESIS) {
    // "(" expression ")"
    get_symbol();

    type = compile_expression();

    get_expected_symbol(SYM_RPARENTHESIS);
  } else {
    syntax_error_unexpected_symbol();

    type = UINT64_T;
  }

  if (dereference) {
    if (type != UINT64STAR_T)
      type_warning(UINT64STAR_T, type);

    // dereference
    emit_load(current_temporary(), current_temporary(), 0);

    type = UINT64_T;
  }
  if (negative) {
    if (type != UINT64_T) {
      type_warning(UINT64_T, type);

      type = UINT64_T;
    }
    // subtract from 0
    emit_sub(current_temporary(), REG_ZR, current_temporary());
  }

  // assert: allocated_temporaries == n + 1

  if (has_cast)
    // cast is grammar attribute
    return cast;
  else
    // type of factor is grammar attribute
    return type;
}

void load_small_and_medium_integer(uint64_t reg, uint64_t value) {
  // assert: -2^31 <= value < 2^31

  if (is_signed_integer(value, 12))
    // integers with -2^11 <= value < 2^11
    // are loaded with one addi into a register
    emit_addi(reg, REG_ZR, value);
  else {
    // integers with -2^31 <= value < -2^11 and 2^11 <= value < 2^31
    // are loaded with one lui and one addi into a register plus
    // an additional sub to cancel sign extension if necessary
    value = load_upper_value(reg, value);

    emit_addi(reg, reg, value);
  }
}

uint64_t load_big_integer(char* big_integer) {
  uint64_t* entry;

  // assert: n = allocated_temporaries

  entry = search_global_symbol_table(big_integer, BIGINT);

  return
    // type of big integer is grammar attribute
    load_value(entry);
    // assert: allocated_temporaries == n + 1
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
      // allocate memory for big integer in data segment
      data_size = data_size + WORDSIZE;

      create_symbol_table_entry(GLOBAL_TABLE, integer,
        line_number, BIGINT, UINT64_T, value, -data_size);
    }

    load_big_integer(integer);
  }

  // assert: allocated_temporaries == n + 1
}

void load_string(char* string) {
  uint64_t length;

  // assert: n = allocated_temporaries

  length = string_length(string) + 1;

  // allocate memory for string in data segment
  data_size = data_size + round_up(length, WORDSIZE);

  create_symbol_table_entry(GLOBAL_TABLE, string,
    line_number, STRING, UINT64STAR_T, 0, -data_size);

  load_integer(-data_size);

  emit_add(current_temporary(), REG_GP, current_temporary());

  // assert: allocated_temporaries == n + 1
}

uint64_t compile_literal() {
  // assert: allocated_temporaries == 0

  if (is_value()) {
    load_integer(compile_value());

    // assert: allocated_temporaries == 1

    return UINT64_T;
  } else if (symbol == SYM_STRING) {
    load_string(string);

    // assert: allocated_temporaries == 1

    get_symbol();

    return UINT64STAR_T;
  } else {
    syntax_error_unexpected_symbol();

    // we must allocate an additional temporary
    load_integer(0);

    // assert: allocated_temporaries == 1

    return UINT64_T;
  }
}

void compile_if() {
  uint64_t branch_forward_to_else_or_end;
  uint64_t jump_forward_to_end;

  // assert: allocated_temporaries == 0

  if (symbol == SYM_IF) {
    get_symbol();

    if (symbol == SYM_LPARENTHESIS) {
      // "if" "(" expression ")"
      get_symbol();

      compile_expression();

      // if the "if" condition is false we skip the true case
      // by branching to "else" (if provided)
      branch_forward_to_else_or_end = code_size;

      // the target address is still unknown, using 0 for now
      emit_beq(current_temporary(), REG_ZR, 0);

      tfree(1);

      if (symbol == SYM_RPARENTHESIS) {
        get_symbol();

        if (symbol == SYM_LBRACE) {
          // zero or more statements: "{" { statement } "}"
          get_symbol();

          while (is_neither_rbrace_nor_eof())
            // assert: allocated_temporaries == 0
            compile_statement();

          get_required_symbol(SYM_RBRACE);
        } else
          // only one statement without {}
          compile_statement();

        if (symbol == SYM_ELSE) {
          // optional: "else"
          get_symbol();

          // if the "if" condition was true we skip "else"
          // by unconditionally jumping to the end
          jump_forward_to_end = code_size;

          // the target address is still unknown, using 0 for now
          emit_jal(REG_ZR, 0);

          // if the "if" condition was false we branch here
          fixup_relative_BFormat(branch_forward_to_else_or_end);

          if (symbol == SYM_LBRACE) {
            // zero or more statements: "{" { statement } "}"
            get_symbol();

            while (is_neither_rbrace_nor_eof())
              // assert: allocated_temporaries == 0
              compile_statement();

            get_required_symbol(SYM_RBRACE);
          } else
            // only one statement without "{" "}"
            compile_statement();

          // if the "if" condition was true we unconditionally jump here
          fixup_relative_JFormat(jump_forward_to_end, code_size);
        } else
          // if the "if" condition was false we branch here
          fixup_relative_BFormat(branch_forward_to_else_or_end);
      } else
        syntax_error_expected_symbol(SYM_RPARENTHESIS);
    } else
      syntax_error_expected_symbol(SYM_LPARENTHESIS);
  } else
    syntax_error_expected_symbol(SYM_IF);

  // assert: allocated_temporaries == 0

  number_of_if = number_of_if + 1;
}

void compile_while() {
  uint64_t jump_back_to_while;
  uint64_t branch_forward_to_end;

  // assert: allocated_temporaries == 0

  jump_back_to_while = code_size;

  branch_forward_to_end = 0;

  if (symbol == SYM_WHILE) {
    // "while" "(" expression ")"
    get_symbol();

    if (symbol == SYM_LPARENTHESIS) {
      get_symbol();

      compile_expression();

      // if the "while" condition is false
      // we skip the "while" body by branching to the end
      branch_forward_to_end = code_size;

      // the target address is still unknown, using 0 for now
      emit_beq(current_temporary(), REG_ZR, 0);

      tfree(1);

      if (symbol == SYM_RPARENTHESIS) {
        get_symbol();

        if (symbol == SYM_LBRACE) {
          // zero or more statements: "{" { statement } "}"
          get_symbol();

          while (is_neither_rbrace_nor_eof())
            // assert: allocated_temporaries == 0
            compile_statement();

          get_required_symbol(SYM_RBRACE);
        } else
          // only one statement without "{" "}"
          compile_statement();
      } else
        syntax_error_expected_symbol(SYM_RPARENTHESIS);
    } else
      syntax_error_expected_symbol(SYM_LPARENTHESIS);
  } else
    syntax_error_expected_symbol(SYM_WHILE);

  // we use JAL for the unconditional jump back to the loop condition because:
  // 1. the RISC-V doc recommends to do so to not disturb branch prediction
  // 2. GCC also uses JAL for the unconditional back jump of a while loop
  emit_jal(REG_ZR, jump_back_to_while - code_size);

  if (branch_forward_to_end != 0)
    // first instruction after loop body will be generated here
    // now we have the address for the conditional branch from above
    fixup_relative_BFormat(branch_forward_to_end);

  // assert: allocated_temporaries == 0

  number_of_while = number_of_while + 1;
}

void procedure_prologue(uint64_t number_of_local_variable_bytes) {
  // allocate memory for return address
  emit_addi(REG_SP, REG_SP, -WORDSIZE);

  // save return address
  emit_store(REG_SP, 0, REG_RA);

  // allocate memory for caller's frame pointer
  emit_addi(REG_SP, REG_SP, -WORDSIZE);

  // save caller's frame pointer
  emit_store(REG_SP, 0, REG_S0);

  // set callee's frame pointer
  emit_addi(REG_S0, REG_SP, 0);

  // allocate memory for callee's local variables
  if (number_of_local_variable_bytes > 0) {
    if (is_signed_integer(-number_of_local_variable_bytes, 12))
      emit_addi(REG_SP, REG_SP, -number_of_local_variable_bytes);
    else {
      syntax_error_message("too many local variables");

      exit(EXITCODE_COMPILERERROR);
    }
  }
}

void procedure_epilogue(uint64_t number_of_parameter_bytes) {
  // deallocate memory for callee's frame pointer and local variables
  emit_addi(REG_SP, REG_S0, 0);

  // restore caller's frame pointer
  emit_load(REG_S0, REG_SP, 0);

  // deallocate memory for caller's frame pointer
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  // restore return address
  emit_load(REG_RA, REG_SP, 0);

  if (is_signed_integer(WORDSIZE + number_of_parameter_bytes, 12))
    // deallocate memory for return address and (non-variadic) actual parameters
    emit_addi(REG_SP, REG_SP, WORDSIZE + number_of_parameter_bytes);
  else {
    syntax_error_message("too many formal parameters");

    exit(EXITCODE_COMPILERERROR);
  }

  // return
  emit_jalr(REG_ZR, REG_RA, 0);
}

void compile_procedure(char* procedure, uint64_t type) {
  uint64_t is_variadic;
  uint64_t number_of_formal_parameters;
  uint64_t* entry;
  uint64_t number_of_local_variable_bytes;

  // assert: identifier has already been parsed

  local_symbol_table = (uint64_t*) 0;

  // assuming procedure is not variadic
  is_variadic = 0;

  number_of_formal_parameters = 0;

  // try parsing formal parameters

  if (symbol == SYM_LPARENTHESIS) {
    get_symbol();

    if (symbol != SYM_RPARENTHESIS) {
      // try parsing first formal parameter
      if (is_type()) {
        entry = compile_variable((char*) 0, compile_type(), 0);

        number_of_formal_parameters = 1;

        // 2 * WORDSIZE offset to skip frame pointer and link
        // additional offset (number_of_formal_parameters - 1) * WORDSIZE
        // since actual parameters are pushed onto stack in reverse
        set_address(entry, 2 * WORDSIZE + (number_of_formal_parameters - 1) * WORDSIZE);

        while (is_possibly_parameter(is_variadic)) {
          // try parsing next formal parameter
          get_symbol();

          if (symbol == SYM_ELLIPSIS) {
            get_symbol();

            is_variadic = 1;
          } else if (is_type()) {
            entry = compile_variable((char*) 0, compile_type(), 0);

            number_of_formal_parameters = number_of_formal_parameters + 1;

            set_address(entry, 2 * WORDSIZE + (number_of_formal_parameters - 1) * WORDSIZE);
          } else
            syntax_error_expected_symbol(SYM_UINT64);
        }

        get_expected_symbol(SYM_RPARENTHESIS);
      } else
        syntax_error_expected_symbol(SYM_UINT64);
    } else
      get_symbol();
  } else
    syntax_error_expected_symbol(SYM_LPARENTHESIS);

  if (is_variadic)
    // negative number of formal parameters indicates procedure is variadic
    number_of_formal_parameters = -number_of_formal_parameters;

  // try parsing rest of procedure declaration or definition

  // bootstrap selfie implementation of *printf procedures
  procedure = remove_prefix_from_printf_procedures(procedure);

  // look up procedure to see if it has been called, declared, or even defined
  entry = search_global_symbol_table(procedure, PROCEDURE);

  if (entry == (uint64_t*) 0)
    // procedure never called nor declared nor defined
    entry = create_symbol_table_entry(GLOBAL_TABLE, procedure,
      line_number, PROCEDURE, type, number_of_formal_parameters, 0);
  else if (get_type(entry) == UNDECLARED_T)
    // procedure already called but neither declared nor defined
    set_type(entry, type);

  if (symbol == SYM_SEMICOLON) {
    // this is a procedure declaration

    if (get_type(entry) != type)
      // procedure already declared or even defined before;
      // warn about mismatching return type but otherwise ignore
      type_warning(get_type(entry), type);

    get_symbol();
  } else if (symbol == SYM_LBRACE) {
    // this is a procedure definition

    if (is_undefined_procedure(entry)) {
      set_line_number(entry, line_number);

      if (get_type(entry) != type) {
        // procedure already declared but with different return type
        type_warning(get_type(entry), type);

        // return type of definition counts
        set_type(entry, type);
      }

      if (get_address(entry) != 0)
        // procedure already called but not defined
        fixlink_relative(get_address(entry), code_size);

      set_address(entry, code_size);

      if (string_compare(procedure, main_name)) {
        // first source containing main procedure provides binary name
        binary_name = source_name;

        // account for initial call to main procedure
        number_of_calls = number_of_calls + 1;
      }
    } else {
      // procedure already defined
      print_line_number("warning", line_number);
      printf("redefinition of procedure %s ignored\n", procedure);
    }

    get_symbol();

    // try parsing local variable declarations

    number_of_local_variable_bytes = 0;

    while (is_type()) {
      // try parsing next local variable declaration
      number_of_local_variable_bytes = number_of_local_variable_bytes + WORDSIZE;

      // offset of local variables relative to frame pointer is negative
      compile_variable((char*) 0, compile_type(), -number_of_local_variable_bytes);

      get_expected_symbol(SYM_SEMICOLON);
    }

    // try parsing statements in procedure body

    procedure_prologue(number_of_local_variable_bytes);

    // macros require access to current procedure
    current_procedure = entry;

    // create a fixup chain for return statements
    return_jumps = 0;

    return_type = type;

    while (is_neither_rbrace_nor_eof())
      // assert: allocated_temporaries == 0
      compile_statement();

    return_type = 0;

    if (symbol == SYM_RBRACE) {
      // all return statements jump here
      fixlink_relative(return_jumps, code_size);

      return_jumps = 0;

      if (is_variadic)
        procedure_epilogue(-number_of_formal_parameters * WORDSIZE);
      else
        procedure_epilogue(number_of_formal_parameters * WORDSIZE);

      get_symbol();
    } else {
      syntax_error_expected_symbol(SYM_RBRACE);

      exit(EXITCODE_PARSERERROR);
    }
  } else
    syntax_error_unexpected_symbol();

  current_procedure = (uint64_t*) 0;

  local_symbol_table = (uint64_t*) 0;

  // assert: allocated_temporaries == 0
}

uint64_t save_temporaries() {
  uint64_t number_of_temporaries;

  number_of_temporaries = allocated_temporaries;

  while (allocated_temporaries > 0) {
    // push temporary onto stack
    emit_addi(REG_SP, REG_SP, -WORDSIZE);
    emit_store(REG_SP, 0, current_temporary());

    tfree(1);
  }

  return number_of_temporaries;
}

void restore_temporaries(uint64_t number_of_temporaries) {
  while (allocated_temporaries < number_of_temporaries) {
    talloc();

    // restore temporary from stack
    emit_load(current_temporary(), REG_SP, 0);
    emit_addi(REG_SP, REG_SP, WORDSIZE);
  }
}

uint64_t macro_expand(uint64_t* entry) {
  char* name;

  name = get_string(entry);

  if (string_compare(name, "var_start"))
    macro_var_start();
  else if (string_compare(name, "var_arg"))
    macro_var_arg();
  else if (string_compare(name, "var_end"))
    macro_var_end();

  // return type is grammar attribute
  return get_type(entry);
}

uint64_t procedure_call(uint64_t* entry, char* procedure, uint64_t number_of_actual_parameters) {
  uint64_t type;

  if (entry == (uint64_t*) 0) {
    // procedure never called nor declared nor defined
    syntax_error_undeclared_identifier(procedure);

    // return type will be determined by procedure declaration or definition
    type = UNDECLARED_T;

    create_symbol_table_entry(GLOBAL_TABLE, procedure,
      line_number, PROCEDURE, type, number_of_actual_parameters, code_size);

    emit_jal(REG_RA, 0);

  } else {
    type = get_type(entry);

    if (get_address(entry) == 0) {
      // procedure declared but never called nor defined
      set_address(entry, code_size);

      emit_jal(REG_RA, 0);
    } else if (get_opcode(load_instruction(get_address(entry))) == OP_JAL) {
      // procedure called and possibly declared but not defined

      // create fixup chain using absolute address
      emit_jal(REG_RA, get_address(entry));
      set_address(entry, code_size - INSTRUCTIONSIZE);
    } else
      // procedure defined, use relative address
      emit_jal(REG_RA, get_address(entry) - code_size);
  }

  // return type is grammar attribute
  return type;
}

uint64_t compile_call(char* procedure) {
  uint64_t* entry;
  uint64_t number_of_temporaries;
  uint64_t allocate_memory_on_stack;
  uint64_t number_of_actual_parameters;
  uint64_t number_of_formal_parameters;
  uint64_t type;

  // assert: identifier "(" has already been parsed

  entry = search_symbol_table(library_symbol_table, procedure, MACRO);

  if (entry != (uint64_t*) 0)
    // actually expanding a macro, not calling a procedure
    return macro_expand(entry);

  // assert: n = allocated_temporaries

  number_of_temporaries = save_temporaries();

  // assert: allocated_temporaries == 0

  if (is_expression()) {
    // try parsing first actual parameter
    compile_expression();

    // TODO: check if types of actual and formal parameters match

    // remember where to allocate memory on stack for actual parameters
    allocate_memory_on_stack = code_size;

    // we do not yet know how many bytes are needed, fixup later
    emit_addi(REG_SP, REG_SP, 0);

    // push first actual parameter onto top (!) of stack
    emit_store(REG_SP, 0, current_temporary());

    tfree(1);

    number_of_actual_parameters = 1;

    while (symbol == SYM_COMMA) {
      // try parsing next actual parameter
      get_symbol();

      compile_expression();

      // push next actual parameter onto stack in reverse (!) order
      emit_store(REG_SP, number_of_actual_parameters * WORDSIZE, current_temporary());

      tfree(1);

      number_of_actual_parameters = number_of_actual_parameters + 1;
    }

    // now we know the number of actual parameters
    fixup_IFormat(allocate_memory_on_stack, -(number_of_actual_parameters * WORDSIZE));
  } else
    number_of_actual_parameters = 0;

  if (symbol == SYM_RPARENTHESIS) {
    // ready to call procedure
    get_symbol();

    entry = get_scoped_symbol_table_entry(procedure, PROCEDURE);

    type = procedure_call(entry, procedure, number_of_actual_parameters);

    if (entry != (uint64_t*) 0) {
      // procedure declared or defined before this call
      number_of_formal_parameters = get_value(entry);

      if (signed_less_than(number_of_formal_parameters, 0)) {
        // variadic procedure
        number_of_formal_parameters = -number_of_formal_parameters;

        if (number_of_actual_parameters > number_of_formal_parameters)
          // deallocate variadic actual parameters
          emit_addi(REG_SP, REG_SP,
            (number_of_actual_parameters - number_of_formal_parameters) * WORDSIZE);
        else if (number_of_actual_parameters < number_of_formal_parameters)
          syntax_error_message("fewer actual than formal parameters");
      } else if (number_of_actual_parameters != number_of_formal_parameters)
        syntax_error_message("different number of actual and formal parameters");
    }
  } else {
    syntax_error_expected_symbol(SYM_RPARENTHESIS);

    type = UINT64_T;
  }

  // assert: allocated_temporaries == 0

  restore_temporaries(number_of_temporaries);

  // assert: allocated_temporaries == n

  number_of_calls = number_of_calls + 1;

  // return type is grammar attribute
  return type;
}

void compile_return() {
  uint64_t type;

  // assert: allocated_temporaries == 0

  get_expected_symbol(SYM_RETURN);

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
  emit_jal(REG_ZR, return_jumps);

  // new head of fixup chain
  return_jumps = code_size - INSTRUCTIONSIZE;

  // assert: allocated_temporaries == 0

  number_of_return = number_of_return + 1;
}

// -----------------------------------------------------------------
// ---------------------------- MACROS -----------------------------
// -----------------------------------------------------------------

void macro_var_start() {
  uint64_t* var_list_variable;
  uint64_t s0_offset;

  var_list_variable = (uint64_t*) 0;
  s0_offset         = 0;

  if (signed_less_than(get_value(current_procedure), 0) == 0)
    syntax_error_message("'var_start' used in procedure with non-variadic parameters");

  if (symbol == SYM_IDENTIFIER) {
    var_list_variable = search_symbol_table(local_symbol_table, identifier, VARIABLE);

    if (var_list_variable != (uint64_t*) 0) {
      get_symbol();

      if (symbol == SYM_RPARENTHESIS) {
        get_symbol();

        // skip the return address, frame pointer and non-variadic parameters
        s0_offset = 2 * WORDSIZE - get_value(current_procedure) * WORDSIZE;

        load_integer(s0_offset);

        // address of first variadic parameter is:
        // S0 + 2 * WORDSIZE + #non-variadic parameters * WORDSIZE
        emit_add(current_temporary(), current_temporary(), REG_S0);

        // store address in variable passed as macro argument
        emit_store(REG_S0, get_address(var_list_variable), current_temporary());

        tfree(1);
      }
    } else {
      syntax_error_undeclared_identifier(identifier);

      get_symbol();
    }
  } else
    syntax_error_expected_symbol(SYM_IDENTIFIER);
}

void macro_var_arg() {
  uint64_t* var_list_variable;
  uint64_t  var_list_address;

  var_list_variable = (uint64_t*) 0;
  var_list_address  = 0;

  if (symbol == SYM_IDENTIFIER) {
    var_list_variable = search_symbol_table(local_symbol_table, identifier, VARIABLE);

    if (var_list_variable != (uint64_t*) 0) {
      get_symbol();

      if (symbol == SYM_RPARENTHESIS) {
        get_symbol();

        var_list_address = get_address(var_list_variable);

        talloc();

        // load variadic parameter from memory address pointed to
        // by variable passed as macro argument (var_list_variable)
        emit_load(current_temporary(), REG_S0, var_list_address);

        // store variadic parameter as return value of macro
        emit_load(REG_A0, current_temporary(), 0);

        // increment var_list_variable pointer by one parameter size (WORDSIZE)
        emit_addi(current_temporary(), current_temporary(), WORDSIZE);

        // store incremented address in variable passed as macro argument
        emit_store(REG_S0, var_list_address, current_temporary());

        tfree(1);
      } else
        syntax_error_expected_symbol(SYM_RPARENTHESIS);
    } else {
      syntax_error_undeclared_identifier(identifier);

      get_symbol();
    }
  } else
    syntax_error_expected_symbol(SYM_IDENTIFIER);
}

// implementation of va_start, va_arg, and va_end is platform-specific;
// RISC-V va_end does nothing and is only implemented for parity with standard C
void macro_var_end() {
  if (signed_less_than(get_value(current_procedure), 0) == 0)
    syntax_error_message("'var_end' used in procedure with non-variadic parameters");

  if (symbol == SYM_IDENTIFIER) {
    get_symbol();

    get_expected_symbol(SYM_RPARENTHESIS);
  } else
    syntax_error_expected_symbol(SYM_IDENTIFIER);
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

void emit_multiply_by(uint64_t reg, uint64_t m) {
  // assert: there is a 0 <= b < 11 such that m == 2^b

  // load multiplier less than 2^11 to avoid sign extension
  emit_addi(next_temporary(), REG_ZR, m);
  emit_mul(reg, reg, next_temporary());
}

void emit_program_entry() {
  uint64_t i;

  i = 0;

  // allocate memory for machine initialization code

  // emit exactly 22 NOPs with source code line 1
  while (i < 22) {
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
  uint64_t gp_value;
  uint64_t saved_code_size;
  uint64_t* entry;

  // code segment starts at PK_CODE_START
  code_start = PK_CODE_START;

  // code size must be memory-word-aligned
  if (code_size % WORDSIZE != 0)
    emit_nop();

  // start of data segment must be page-aligned for ELF program header
  data_start = round_up(code_start + code_size, p_align);

  // calculate global pointer value
  gp_value = data_start + data_size;

  // further allocations in the data segment are not allowed at this point,
  // because it would increase data_size and therefore lead to a false gp_value

  // set code emission to program entry
  saved_code_size = code_size;
  code_size       = 0;

  // assert: emitting no more than 22 instructions, see emit_program_entry

  if (report_undefined_procedures()) {
    // if there are undefined procedures just exit
    // by loading exit code 0 into return register
    emit_addi(REG_A0, REG_ZR, 0);
  } else {
    // avoid sign extension that would result in an additional sub instruction
    if (gp_value < two_to_the_power_of(31) - two_to_the_power_of(11))
      // assert: generates no more than two instructions and
      // no data segment allocations in load_integer for gp_value
      load_integer(gp_value);
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

    // memory-word-align current program break
    emit_round_up(REG_A0, WORDSIZE);

    // set program break to word-aligned program break
    emit_addi(REG_A7, REG_ZR, SYSCALL_BRK);
    emit_ecall();

    // look up global variable _bump for storing malloc's bump pointer
    // use bump_name string to obtain unique hash
    entry = search_global_symbol_table(bump_name, VARIABLE);

    // store word-aligned program break in _bump
    emit_store(get_scope(entry), get_address(entry), REG_A0);

    // reset return register to initial return value
    emit_addi(REG_A0, REG_ZR, 0);

    // assert: stack is set up with argv pointer still missing

    //   sp
    //    |
    //    V
    // | argc | argv[0] | argv[1] | ... | argv[n]

    // first push argc again (!) onto stack

    talloc();

    emit_load(current_temporary(), REG_SP, 0);
    emit_addi(REG_SP, REG_SP, -WORDSIZE);
    emit_store(REG_SP, 0, current_temporary());

    //   sp  sp+TRGTWRDSZ sp+2*WORDSIZE
    //    |      |        |
    //    V      V        V
    // | argc | argc | argv[0] | argv[1] | ... | argv[n]

    // then overwrite below-top argc with &argv

    emit_addi(current_temporary(), REG_SP, 2 * WORDSIZE);
    emit_store(REG_SP, WORDSIZE, current_temporary());

    tfree(1);

    //   sp
    //    |        _______
    //    V       |       V
    // | argc | &argv | argv[0] | argv[1] | ... | argv[n]

    // assert: global, _bump, and stack pointers are set up
    //         with all other non-temporary registers zeroed

    // use main_name string to obtain unique hash
    entry = search_global_symbol_table(main_name, PROCEDURE);

    procedure_call(entry, main_name, get_value(entry));
  }

  // we exit with exit code in return register pushed onto the stack
  emit_addi(REG_SP, REG_SP, -WORDSIZE);
  emit_store(REG_SP, 0, REG_A0);

  // discount NOPs in profile that were generated for program entry
  ic_addi = ic_addi - code_size / INSTRUCTIONSIZE;

  // wrapper code for exit must follow here

  // restore original code size
  code_size = saved_code_size;
}

// -----------------------------------------------------------------
// --------------------------- COMPILER ----------------------------
// -----------------------------------------------------------------

uint64_t open_read_only(char* name) {
  return sign_extend(open(name, O_RDONLY, 0), SYSCALL_BITWIDTH);
}

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

  reset_binary();

  // allocate zeroed memory for storing binary
  code_binary = zmalloc(MAX_CODE_SIZE);
  data_binary = zmalloc(MAX_DATA_SIZE);

  // allocate zeroed memory for storing source code line numbers
  code_line_number = zmalloc(MAX_CODE_SIZE / INSTRUCTIONSIZE * SIZEOFUINT64);
  data_line_number = zmalloc(MAX_DATA_SIZE / WORDSIZE * SIZEOFUINT64);

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
    fetch_dss_code_location = code_size;

    emit_fetch_data_segment_size_interface();
  }

  // declare macros in library symbol table to override entries in global symbol table
  create_symbol_table_entry(LIBRARY_TABLE, "var_start", 0, MACRO, VOID_T, 1, 0);
  create_symbol_table_entry(LIBRARY_TABLE, "var_arg", 0, MACRO, UINT64_T, 1, 0);
  create_symbol_table_entry(LIBRARY_TABLE, "var_end", 0, MACRO, VOID_T, 1, 0);

  // declare main procedure in global symbol table
  // use main_name string to obtain unique hash
  create_symbol_table_entry(GLOBAL_TABLE, main_name, 0, PROCEDURE, UINT64_T, 0, 0);

  while (link) {
    if (number_of_remaining_arguments() == 0)
      link = 0;
    else if (load_character(peek_argument(0), 0) == '-')
      link = 0;
    else {
      source_name = get_argument();

      number_of_source_files = number_of_source_files + 1;

      printf("%s: selfie compiling %s to %lu-bit RISC-U with %lu-bit starc\n", selfie_name,
        source_name, WORDSIZEINBITS, SIZEOFUINT64INBITS);

      // assert: source_name is mapped and not longer than MAX_FILENAME_LENGTH

      source_fd = open_read_only(source_name);

      if (signed_less_than(source_fd, 0)) {
        printf("%s: could not open input file %s\n", selfie_name, source_name);

        exit(EXITCODE_IOERROR);
      }

      reset_scanner();
      reset_parser();

      compile_cstar();

      printf("%s: %lu characters read in %lu lines and %lu comments\n", selfie_name,
        number_of_read_characters,
        line_number,
        number_of_comments);

      printf("%s: with %lu(%lu.%.2lu%%) characters in %lu actual symbols\n", selfie_name,
        number_of_read_characters - number_of_ignored_characters,
        percentage_format_integral_2(number_of_read_characters, number_of_read_characters - number_of_ignored_characters),
        percentage_format_fractional_2(number_of_read_characters, number_of_read_characters - number_of_ignored_characters),
        number_of_scanned_symbols);

      printf("%s: %lu global variables, %lu procedures, %lu string literals\n", selfie_name,
        number_of_global_variables,
        number_of_procedures,
        number_of_strings);

      printf("%s: %lu calls, %lu assignments, %lu while, %lu if, %lu return\n", selfie_name,
        number_of_calls,
        number_of_assignments,
        number_of_while,
        number_of_if,
        number_of_return);

      if (number_of_syntax_errors != 0) {
        printf("%s: encountered %lu syntax errors while compiling %s - omitting output\n",
          selfie_name,
          number_of_syntax_errors,
          source_name);
        exit(EXITCODE_SYNTAXERROR);
      }
    }
  }

  if (number_of_source_files == 0)
    printf("%s: nothing to compile, only library generated\n", selfie_name);

  emit_bootstrapping();

  if (GC_ON)
    emit_fetch_data_segment_size_implementation(fetch_dss_code_location);

  emit_data_segment();

  ELF_header = encode_elf_header();

  printf("%s: symbol table search time was %lu iterations on average and %lu in total\n", selfie_name,
    total_search_time / number_of_searches,
    total_search_time);

  printf("%s: %lu bytes generated with %lu instructions and %lu bytes of data\n", selfie_name,
    code_size + data_size,
    code_size / INSTRUCTIONSIZE,
    data_size);

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
  printf("%s", get_register_name(reg));
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

void read_register_wrap(uint64_t reg, uint64_t wrap) {
  if (*(writes_per_register + reg) > 0) {
    // register has been written to before
    if (*(reads_per_register + reg) < UINT64_MAX)
      *(reads_per_register + reg) = *(reads_per_register + reg) + 1;

    // tolerate unwrapped values in register-to-register transfers
    if (wrap)
      if (*(registers + reg) > UINT_MAX) {
        print_instruction();
        printf(": reading unwrapped value from register ");
        print_register_name(reg);
        println();

        throw_exception(EXCEPTION_INTEGEROVERFLOW, reg);
      }
  } else {
    print_instruction();
    printf(": reading from uninitialized register ");
    print_register_name(reg);
    println();

    throw_exception(EXCEPTION_UNINITIALIZEDREGISTER, reg);
  }
}

void read_register(uint64_t reg) {
  read_register_wrap(reg, 1);
}

void write_register_wrap(uint64_t reg, uint64_t wrap) {
  if (wrap)
    *(registers + reg) = sign_shrink(*(registers + reg), WORDSIZEINBITS);

  if (reg == REG_SP)
    if (*(registers + REG_SP) < stack_peak)
      stack_peak = *(registers + REG_SP);

  if (*(writes_per_register + reg) < UINT64_MAX)
    *(writes_per_register + reg) = *(writes_per_register + reg) + 1;
}

void write_register(uint64_t reg) {
  write_register_wrap(reg, 1);
}

// -----------------------------------------------------------------
// ------------------------ ENCODER/DECODER ------------------------
// -----------------------------------------------------------------

void check_immediate_range(uint64_t immediate, uint64_t bits) {
  if (is_signed_integer(immediate, bits) == 0) {
    print_line_number("encoding error", line_number);
    printf("%ld expected between %ld and %ld\n",
      immediate,
      -two_to_the_power_of(bits - 1),
      two_to_the_power_of(bits - 1) - 1);

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

uint64_t get_total_number_of_instructions() {
  return ic_lui + ic_addi + ic_add + ic_sub + ic_mul + ic_divu + ic_remu + ic_sltu + ic_load + ic_store + ic_beq + ic_jal + ic_jalr + ic_ecall;
}

uint64_t get_total_number_of_nops() {
  return nopc_lui + nopc_addi + nopc_add + nopc_sub + nopc_mul + nopc_divu + nopc_remu + nopc_sltu + nopc_load + nopc_store + nopc_beq + nopc_jal + nopc_jalr;
}

void print_instruction_counter(uint64_t counter, uint64_t ins) {
  printf("%s: %lu(%lu.%.2lu%%)",
    get_mnemonic(ins),
    counter,
    percentage_format_integral_2(get_total_number_of_instructions(), counter),
    percentage_format_fractional_2(get_total_number_of_instructions(), counter));
}

void print_instruction_counter_with_nops(uint64_t counter, uint64_t nops, uint64_t ins) {
  print_instruction_counter(counter, ins);

  if (run)
    printf("[%lu.%.2lu%%]",
      percentage_format_integral_2(counter, nops),
      percentage_format_fractional_2(counter, nops));
}

void print_instruction_counters() {
  printf("%s: init:    ", selfie_name);
  print_instruction_counter_with_nops(ic_lui, nopc_lui, LUI);
  printf(", ");
  print_instruction_counter_with_nops(ic_addi, nopc_addi, ADDI);
  println();

  printf("%s: memory:  ", selfie_name);
  print_instruction_counter_with_nops(ic_load, nopc_load, LOAD);
  printf(", ");
  print_instruction_counter_with_nops(ic_store, nopc_store, STORE);
  println();

  printf("%s: compute: ", selfie_name);
  print_instruction_counter_with_nops(ic_add, nopc_add, ADD);
  printf(", ");
  print_instruction_counter_with_nops(ic_sub, nopc_sub, SUB);
  printf(", ");
  print_instruction_counter_with_nops(ic_mul, nopc_mul, MUL);
  println();

  printf("%s: compute: ", selfie_name);
  print_instruction_counter_with_nops(ic_divu, nopc_divu, DIVU);
  printf(", ");
  print_instruction_counter_with_nops(ic_remu, nopc_remu, REMU);
  println();

  printf("%s: compare: ", selfie_name);
  print_instruction_counter_with_nops(ic_sltu, nopc_sltu, SLTU);
  println();

  printf("%s: control: ", selfie_name);
  print_instruction_counter_with_nops(ic_beq, nopc_beq, BEQ);
  printf(", ");
  print_instruction_counter_with_nops(ic_jal, nopc_jal, JAL);
  printf(", ");
  print_instruction_counter_with_nops(ic_jalr, nopc_jalr, JALR);
  println();

  printf("%s: system:  ", selfie_name);
  print_instruction_counter(ic_ecall, ECALL);
  println();
}

uint64_t get_low_word(uint64_t word) {
  return get_bits(word, 0, SINGLEWORDSIZEINBITS);
}

uint64_t get_high_word(uint64_t word) {
  return get_bits(word, SINGLEWORDSIZEINBITS, SINGLEWORDSIZEINBITS);
}

uint64_t load_word(uint64_t* memory, uint64_t waddr, uint64_t is_double_word) {
  if (IS64BITSYSTEM) {
    if (IS64BITTARGET)
      if (is_double_word)
        return *(memory + waddr / SIZEOFUINT64);

    if (waddr % SIZEOFUINT64 == 0)
      return get_low_word(*(memory + waddr / SIZEOFUINT64));
    else
      return get_high_word(*(memory + waddr / SIZEOFUINT64));
  } else
    return *(memory + waddr / SIZEOFUINT64);
}

void store_word(uint64_t* memory, uint64_t waddr, uint64_t is_double_word, uint64_t word) {
  if (IS64BITSYSTEM) {
    if (IS64BITTARGET)
      if (is_double_word) {
        *(memory + waddr / SIZEOFUINT64) = word;

        return;
      }

    if (waddr % SIZEOFUINT64 == 0)
      // replace low word
      *(memory + waddr / SIZEOFUINT64) =
        left_shift(load_word(memory, waddr + SINGLEWORDSIZE, is_double_word), SINGLEWORDSIZEINBITS) + word;
    else
      // replace high word
      *(memory + waddr / SIZEOFUINT64) =
        left_shift(word, SINGLEWORDSIZEINBITS) + load_word(memory, waddr - SINGLEWORDSIZE, is_double_word);
  } else
    *(memory + waddr / SIZEOFUINT64) = word;
}

uint64_t load_instruction(uint64_t caddr) {
  return load_word(code_binary, caddr, 0);
}

void store_instruction(uint64_t caddr, uint64_t instruction) {
  if (caddr >= MAX_CODE_SIZE) {
    syntax_error_message("maximum code size exceeded");

    exit(EXITCODE_COMPILERERROR);
  }

  store_word(code_binary, caddr, 0, instruction);
}

uint64_t load_code(uint64_t caddr) {
  return load_word(code_binary, caddr, 1);
}

uint64_t load_data(uint64_t daddr) {
  return load_word(data_binary, daddr, 1);
}

void store_data(uint64_t daddr, uint64_t data) {
  if (daddr >= MAX_DATA_SIZE) {
    syntax_error_message("maximum data size exceeded");

    exit(EXITCODE_COMPILERERROR);
  }

  store_word(data_binary, daddr, 1, data);
}

void emit_instruction(uint64_t instruction) {
  store_instruction(code_size, instruction);

  if (code_line_number != (uint64_t*) 0)
    if (*(code_line_number + code_size / INSTRUCTIONSIZE) == 0)
      *(code_line_number + code_size / INSTRUCTIONSIZE) = line_number;

  code_size = code_size + INSTRUCTIONSIZE;
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

void emit_load(uint64_t rd, uint64_t rs1, uint64_t immediate) {
  if (IS64BITTARGET)
    emit_instruction(encode_i_format(immediate, rs1, F3_LD, rd, OP_LOAD));
  else
    emit_instruction(encode_i_format(immediate, rs1, F3_LW, rd, OP_LOAD));

  ic_load = ic_load + 1;
}

void emit_store(uint64_t rs1, uint64_t immediate, uint64_t rs2) {
  if (IS64BITTARGET)
    emit_instruction(encode_s_format(immediate, rs2, rs1, F3_SD, OP_STORE));
  else
    emit_instruction(encode_s_format(immediate, rs2, rs1, F3_SW, OP_STORE));

  ic_store = ic_store + 1;
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
    encode_b_format(code_size - from_address,
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

void fixup_IFormat(uint64_t from_address, uint64_t immediate) {
  uint64_t instruction;

  instruction = load_instruction(from_address);

  store_instruction(from_address,
    encode_i_format(immediate,
      get_rs1(instruction),
    get_funct3(instruction),
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

  store_data(data_size + offset, data);

  if (data_line_number != (uint64_t*) 0)
    *(data_line_number + (data_size + offset) / WORDSIZE) = source_line_number;
}

void emit_string_data(uint64_t* entry) {
  char* s;
  uint64_t i;
  uint64_t l;

  s = get_string(entry);

  i = 0;

  l = round_up(string_length(s) + 1, WORDSIZE);

  while (i < l) {
    emit_data_word(load_word((uint64_t*) s, i, 1), get_address(entry) + i, get_line_number(entry));

    i = i + WORDSIZE;
  }
}

void emit_data_segment() {
  uint64_t i;
  uint64_t* entry;

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
}

uint64_t* allocate_elf_header() {
  // allocate and map (on all boot levels) zeroed memory for ELF header preparing
  // read calls (memory must be mapped) and write calls (memory must be mapped and zeroed)
  return touch(zmalloc(ELF_HEADER_SIZE), ELF_HEADER_SIZE);
}

uint64_t* encode_elf_header() {
  uint64_t* header;

  header = allocate_elf_header();

  // store all data necessary for creating a minimal and valid file and program header

  store_word(header, 0, 0, EI_MAG0
              + left_shift(EI_MAG1, 8)
              + left_shift(EI_MAG2, 16)
              + left_shift(EI_MAG3, 24));
  store_word(header, 4, 0, EI_CLASS
              + left_shift(EI_DATA, 8)
              + left_shift(EI_VERSION, 16)
              + left_shift(EI_OSABI, 24));
  store_word(header, 8, 0, EI_ABIVERSION); // ignoring 24 LSBs of EI_PAD
  store_word(header, 12, 0, EI_PAD);       // ignoring 24 MSBs of EI_PAD
  store_word(header, 16, 0, e_type + left_shift(e_machine, 16));
  store_word(header, 20, 0, e_version);

  if (EI_CLASS == ELFCLASS64) {
    // RISC-U ELF64 file header
    store_word(header, 24, 1, e_entry);
    store_word(header, 32, 1, e_phoff);
    store_word(header, 40, 1, e_shoff);
    store_word(header, 48, 1, e_flags
                + left_shift(e_ehsize, 32)
                + left_shift(e_phentsize, 48));
    store_word(header, 56, 1, e_phnum
                + left_shift(e_shentsize, 16)
                + left_shift(e_shnum, 32)
                + left_shift(e_shstrndx, 48));
  } else {
    // RISC-U ELF32 file header
    store_word(header, 24, 0, e_entry);
    store_word(header, 28, 0, e_phoff);
    store_word(header, 32, 0, e_shoff);
    store_word(header, 36, 0, e_flags);
    store_word(header, 40, 0, e_ehsize + left_shift(e_phentsize, 16));
    store_word(header, 44, 0, e_phnum + left_shift(e_shentsize, 16));
    store_word(header, 48, 0, e_shnum + left_shift(e_shstrndx, 16));
  }

  // start of segments have to be aligned in the binary file

  // assert: ELF_HEADER_SIZE % p_align == 0

  p_flags  = 5; // code segment attributes are RE
  p_offset = ELF_HEADER_SIZE; // must match binary format
  p_vaddr  = code_start;
  p_filesz = code_size;
  p_memsz  = code_size;

  encode_elf_program_header(header, 0);

  p_flags  = 6; // data segment attributes are RW
  p_offset = ELF_HEADER_SIZE + round_up(code_size, p_align); // must match binary format
  p_vaddr  = data_start;
  p_filesz = data_size;
  p_memsz  = data_size;

  encode_elf_program_header(header, 1);

  return header;
}

void decode_elf_header(uint64_t* header) {
  EI_CLASS = get_bits(load_word(header, 4, 0), 0, 8);

  if (EI_CLASS == ELFCLASS64)
    IS64BITTARGET = 1;
  else
    IS64BITTARGET = 0;
}

uint64_t get_elf_program_header_offset(uint64_t ph_index) {
  return e_ehsize + e_phentsize * ph_index;
}

void encode_elf_program_header(uint64_t* header, uint64_t ph_index) {
  uint64_t ph_offset;

  ph_offset = get_elf_program_header_offset(ph_index);

  if (EI_CLASS == ELFCLASS64) {
    // RISC-U ELF64 program header
    store_word(header, ph_offset + 0, 1, p_type + left_shift(p_flags, 32));
    store_word(header, ph_offset + 8, 1, p_offset);
    store_word(header, ph_offset + 16, 1, p_vaddr);
    store_word(header, ph_offset + 24, 1, p_paddr);
    store_word(header, ph_offset + 32, 1, p_filesz);
    store_word(header, ph_offset + 40, 1, p_memsz);
    store_word(header, ph_offset + 48, 1, p_align);
  } else {
    // RISC-U ELF32 program header
    store_word(header, ph_offset + 0, 0, p_type);
    store_word(header, ph_offset + 4, 0, p_offset);
    store_word(header, ph_offset + 8, 0, p_vaddr);
    store_word(header, ph_offset + 12, 0, p_paddr);
    store_word(header, ph_offset + 16, 0, p_filesz);
    store_word(header, ph_offset + 20, 0, p_memsz);
    store_word(header, ph_offset + 24, 0, p_flags);
    store_word(header, ph_offset + 28, 0, p_align);
  }
}

void decode_elf_program_header(uint64_t* header, uint64_t ph_index) {
  if (EI_CLASS == ELFCLASS64)
    p_filesz = load_word(header, get_elf_program_header_offset(ph_index) + 32, 1);
  else
    p_filesz = load_word(header, get_elf_program_header_offset(ph_index) + 16, 0);
}

uint64_t validate_elf_header(uint64_t* header) {
  uint64_t* valid_header;
  uint64_t i;

  decode_elf_header(header);

  // must match binary bootstrapping
  code_start = PK_CODE_START;

  decode_elf_program_header(header, 0);

  code_size = p_filesz;

  decode_elf_program_header(header, 1);

  data_size = p_filesz;

  // must match binary bootstrapping
  data_start = round_up(code_start + code_size, p_align);

  if (code_size > MAX_CODE_SIZE)
    return 0;

  if (data_size > MAX_DATA_SIZE)
    return 0;

  valid_header = encode_elf_header();

  i = 0;

  while (i < ELF_HEADER_SIZE / SIZEOFUINT64) {
    if (*(header + i) != *(valid_header + i))
      return 0;

    i = i + 1;
  }

  return 1;
}

uint64_t open_write_only(char* name, uint64_t mode) {
  return sign_extend(open(name, O_CREAT_TRUNC_WRONLY, mode), SYSCALL_BITWIDTH);
}

void selfie_output(char* filename) {
  uint64_t fd;
  uint64_t code_size_with_padding;

  binary_name = filename;

  if (code_size + data_size == 0) {
    printf("%s: nothing to emit to output file %s\n", selfie_name, binary_name);

    return;
  }

  // assert: binary_name is mapped and not longer than MAX_FILENAME_LENGTH

  fd = open_write_only(binary_name, S_IRUSR_IWUSR_IXUSR_IRGRP_IXGRP_IROTH_IXOTH);

  if (signed_less_than(fd, 0)) {
    printf("%s: could not create binary output file %s\n", selfie_name, binary_name);

    exit(EXITCODE_IOERROR);
  }

  // assert: ELF_header is mapped

  // first write ELF header
  if (write(fd, ELF_header, ELF_HEADER_SIZE) != ELF_HEADER_SIZE) {
    printf("%s: could not write ELF header of binary output file %s\n", selfie_name, binary_name);

    exit(EXITCODE_IOERROR);
  }

  code_size_with_padding = round_up(code_size, p_align);

  touch(code_binary, code_size_with_padding);

  // assert: code_binary is mapped

  // then write code with padding bytes
  if (write(fd, code_binary, code_size_with_padding) != code_size_with_padding) {
    printf("%s: could not write code into binary output file %s\n", selfie_name, binary_name);

    exit(EXITCODE_IOERROR);
  }

  // assert: data_binary is mapped

  // finally write data
  if (write(fd, data_binary, data_size) != data_size) {
    printf("%s: could not write data into binary output file %s\n", selfie_name, binary_name);

    exit(EXITCODE_IOERROR);
  }

  printf("%s: %lu bytes with %lu %lu-bit RISC-U instructions and %lu bytes of data written into %s\n", selfie_name,
    ELF_HEADER_SIZE + code_size + data_size,
    code_size / INSTRUCTIONSIZE,
    WORDSIZEINBITS,
    data_size,
    binary_name);
}

uint64_t* touch(uint64_t* memory, uint64_t bytes) {
  uint64_t* m;
  uint64_t n;

  m = memory;

  if (bytes > 0)
    // touch memory at beginning
    n = *m;

  while (bytes > PAGESIZE) {
    bytes = bytes - PAGESIZE;

    m = m + PAGESIZE / SIZEOFUINT64;

    // touch every following page
    n = *m;
  }

  if (bytes > 0) {
    m = m + (bytes - 1) / SIZEOFUINT64;

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
  uint64_t code_size_with_padding;

  binary_name = get_argument();

  // assert: binary_name is mapped and not longer than MAX_FILENAME_LENGTH

  fd = open_read_only(binary_name);

  if (signed_less_than(fd, 0)) {
    printf("%s: could not open input file %s\n", selfie_name, binary_name);

    exit(EXITCODE_IOERROR);
  }

  // no source line numbers in binaries
  reset_binary();

  // this call makes sure ELF_header is mapped for reading into it
  ELF_header = allocate_elf_header();

  // make sure code and data binaries are also mapped for reading into them
  code_binary = touch(smalloc(MAX_CODE_SIZE), MAX_CODE_SIZE);
  data_binary = touch(smalloc(MAX_DATA_SIZE), MAX_DATA_SIZE);

  number_of_read_bytes = read(fd, ELF_header, ELF_HEADER_SIZE);

  if (number_of_read_bytes == ELF_HEADER_SIZE) {
    if (validate_elf_header(ELF_header)) {
      init_target();

      reset_disassembler();

      code_size_with_padding = round_up(code_size, p_align);

      number_of_read_bytes = sign_extend(read(fd, code_binary, code_size_with_padding), SYSCALL_BITWIDTH);

      if (number_of_read_bytes == code_size_with_padding) {
        number_of_read_bytes = sign_extend(read(fd, data_binary, data_size), SYSCALL_BITWIDTH);

        if (number_of_read_bytes == data_size) {
          // check if we are really at EOF
          if (read(fd, binary_buffer, SIZEOFUINT64) == 0) {
            printf("%s: %lu bytes with %lu %lu-bit RISC-U instructions and %lu bytes of data loaded from %s\n",
              selfie_name,
              ELF_HEADER_SIZE + code_size + data_size,
              code_size / INSTRUCTIONSIZE,
              WORDSIZEINBITS,
              data_size,
              binary_name);

            return;
          }
        }
      }
    }
  }

  printf("%s: failed to load binary from input file %s\n", selfie_name, binary_name);

  exit(EXITCODE_IOERROR);
}

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emit_exit() {
  create_symbol_table_entry(LIBRARY_TABLE, "exit", 0, PROCEDURE, VOID_T, 1, code_size);

  // load signed 32-bit integer exit code
  emit_load(REG_A0, REG_SP, 0);

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
    printf("(exit): ");
    print_register_hexadecimal(REG_A0);
    printf(" |- ->\n");
  }

  signed_int_exit_code = *(get_regs(context) + REG_A0);

  set_exit_code(context, sign_shrink(signed_int_exit_code, SYSCALL_BITWIDTH));

  printf("%s: <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<\n", selfie_name);
  printf("%s: %s exiting with exit code %ld\n", selfie_name,
    get_name(context),
    sign_extend(get_exit_code(context), SYSCALL_BITWIDTH));
}

void emit_read() {
  create_symbol_table_entry(LIBRARY_TABLE, "read", 0, PROCEDURE, UINT64_T, 3, code_size);

  emit_load(REG_A0, REG_SP, 0); // fd
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  emit_load(REG_A1, REG_SP, 0); // *buffer
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  emit_load(REG_A2, REG_SP, 0); // size
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
    printf("(read): ");
    print_register_value(REG_A0);
    printf(",");
    print_register_hexadecimal(REG_A1);
    printf(",");
    print_register_value(REG_A2);
    printf(" |- ");
    print_register_value(REG_A0);
  }

  fd      = *(get_regs(context) + REG_A0);
  vbuffer = *(get_regs(context) + REG_A1);
  size    = *(get_regs(context) + REG_A2);

  if (debug_read)
    printf("%s: trying to read %lu bytes from file with descriptor %lu into buffer at virtual address 0x%08lX\n", selfie_name,
      size,
      fd,
      (uint64_t) vbuffer);

  read_total = 0;

  bytes_to_read = WORDSIZE;

  failed = 0;

  while (size > 0) {
    if (size < bytes_to_read)
      bytes_to_read = size;

    if (is_virtual_address_valid(vbuffer, WORDSIZE))
      if (is_data_stack_heap_address(context, vbuffer))
        if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
          buffer = tlb(get_pt(context), vbuffer);

          actually_read = sign_extend(read(fd, buffer, bytes_to_read), SYSCALL_BITWIDTH);

          if (actually_read == bytes_to_read) {
            read_total = read_total + actually_read;

            size = size - actually_read;

            if (size > 0)
              vbuffer = vbuffer + WORDSIZE;
          } else {
            if (signed_less_than(0, actually_read))
              read_total = read_total + actually_read;

            size = 0;
          }
        } else {
          failed = 1;

          size = 0;

          printf("%s: reading into virtual address 0x%08lX failed because the address is unmapped\n", selfie_name, (uint64_t) vbuffer);
        }
      else {
        failed = 1;

        size = 0;

        printf("%s: reading into virtual address 0x%08lX failed because the address is in an invalid segment\n", selfie_name, (uint64_t) vbuffer);
      }
    else {
      failed = 1;

      size = 0;

      printf("%s: reading into virtual address 0x%08lX failed because the address is invalid\n", selfie_name, (uint64_t) vbuffer);
    }
  }

  if (failed)
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);
  else
    *(get_regs(context) + REG_A0) = read_total;

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);

  if (debug_read)
    printf("%s: actually read %lu bytes from file with descriptor %lu\n", selfie_name, read_total, fd);

  if (debug_syscalls) {
    printf(" -> ");
    print_register_value(REG_A0);
    println();
  }
}

void emit_write() {
  create_symbol_table_entry(LIBRARY_TABLE, "write", 0, PROCEDURE, UINT64_T, 3, code_size);

  emit_load(REG_A0, REG_SP, 0); // fd
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  emit_load(REG_A1, REG_SP, 0); // *buffer
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  emit_load(REG_A2, REG_SP, 0); // size
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
    printf("(write): ");
    print_register_value(REG_A0);
    printf(",");
    print_register_hexadecimal(REG_A1);
    printf(",");
    print_register_value(REG_A2);
    printf(" |- ");
    print_register_value(REG_A0);
  }

  fd      = *(get_regs(context) + REG_A0);
  vbuffer = *(get_regs(context) + REG_A1);
  size    = *(get_regs(context) + REG_A2);

  if (debug_write)
    printf("%s: trying to write %lu bytes from buffer at virtual address 0x%08lX into file with descriptor %lu\n", selfie_name,
      size,
      (uint64_t) vbuffer,
      fd);

  written_total = 0;

  bytes_to_write = WORDSIZE;

  failed = 0;

  while (size > 0) {
    if (size < bytes_to_write)
      bytes_to_write = size;

    if (is_virtual_address_valid(vbuffer, WORDSIZE))
      if (is_data_stack_heap_address(context, vbuffer))
        if (is_virtual_address_mapped(get_pt(context), vbuffer)) {
          buffer = tlb(get_pt(context), vbuffer);

          actually_written = sign_extend(write(fd, buffer, bytes_to_write), SYSCALL_BITWIDTH);

          if (actually_written == bytes_to_write) {
            written_total = written_total + actually_written;

            size = size - actually_written;

            if (size > 0)
              vbuffer = vbuffer + WORDSIZE;
          } else {
            if (signed_less_than(0, actually_written))
              written_total = written_total + actually_written;

            size = 0;
          }
        } else {
          failed = 1;

          size = 0;

          printf("%s: writing from virtual address 0x%08lX failed because the address is unmapped\n", selfie_name, (uint64_t) vbuffer);
        }
      else {
        failed = 1;

        size = 0;

        printf("%s: writing from virtual address 0x%08lX failed because the address is in an invalid segment\n", selfie_name, (uint64_t) vbuffer);
      }
    else {
      failed = 1;

      size = 0;

      printf("%s: writing from virtual address 0x%08lX failed because the address is invalid\n", selfie_name, (uint64_t) vbuffer);
    }
  }

  if (failed)
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);
  else
    *(get_regs(context) + REG_A0) = written_total;

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);

  if (debug_write)
    printf("%s: actually wrote %lu bytes into file with descriptor %lu\n", selfie_name, written_total, fd);

  if (debug_syscalls) {
    printf(" -> ");
    print_register_value(REG_A0);
    println();
  }
}

void emit_open() {
  create_symbol_table_entry(LIBRARY_TABLE, "open", 0, PROCEDURE, UINT64_T, 3, code_size);

  emit_load(REG_A1, REG_SP, 0); // filename
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  emit_load(REG_A2, REG_SP, 0); // flags
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  emit_load(REG_A3, REG_SP, 0); // mode
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

  while (i < MAX_FILENAME_LENGTH) {
    if (is_virtual_address_valid(vaddr, WORDSIZE))
      if (is_data_stack_heap_address(context, vaddr)) {
        if (is_virtual_address_mapped(get_pt(context), vaddr))
          store_word((uint64_t*) s, i, 1, load_virtual_memory(get_pt(context), vaddr));
        else {
          printf("%s: opening file failed because the file name address 0x%08lX is unmapped\n", selfie_name, (uint64_t) vaddr);

          return 0;
        }

        // WORDSIZE may be less than SIZEOFUINT64
        j = i % SIZEOFUINT64;

        // check if string ends in the current word
        while (j - i % SIZEOFUINT64 < WORDSIZE) {
          if (load_character((char*) ((uint64_t*) s + i / SIZEOFUINT64), j) == 0)
            return 1;

          j = j + 1;
        }

        // advance to the next word in virtual memory
        vaddr = vaddr + WORDSIZE;

        // advance to the corresponding word in our memory
        i = i + WORDSIZE;
      } else {
        printf("%s: opening file failed because the file name address 0x%08lX is in an invalid segment\n", selfie_name, (uint64_t) vaddr);

        return 0;
      }
    else {
      printf("%s: opening file failed because the file name address 0x%08lX is invalid\n", selfie_name, (uint64_t) vaddr);

      return 0;
    }
  }

  printf("%s: opening file failed because the file name is too long at address 0x%08lX\n", selfie_name, (uint64_t) vaddr);

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
    printf("(openat): ");
    print_register_hexadecimal(REG_A0);
    printf(",");
    print_register_hexadecimal(REG_A1);
    printf(",");
    print_register_hexadecimal(REG_A2);
    printf(",");
    print_register_octal(REG_A3);
    printf(" |- ");
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
    if (flags == LINUX_O_CREAT_TRUNC_WRONLY)
      // use correct flags for host operating system
      flags = O_CREAT_TRUNC_WRONLY;

    fd = sign_extend(open(filename_buffer, flags, mode), SYSCALL_BITWIDTH);

    *(get_regs(context) + REG_A0) = fd;

    if (debug_open)
      printf("%s: opened file %s with flags 0x%lX and mode 0o%lo returning file descriptor %lu\n", selfie_name,
        filename_buffer,
        flags,
        mode,
        fd);
  } else
    *(get_regs(context) + REG_A0) = sign_shrink(-1, SYSCALL_BITWIDTH);

  set_pc(context, get_pc(context) + INSTRUCTIONSIZE);

  if (debug_syscalls) {
    printf(" -> ");
    print_register_value(REG_A0);
    println();
  }
}

void emit_malloc() {
  uint64_t* entry;

  create_symbol_table_entry(LIBRARY_TABLE, "malloc",
    0, PROCEDURE, UINT64STAR_T, 1, code_size);

  // on boot levels higher than 0, zalloc falls back to malloc
  // assuming that page frames are zeroed on boot level zero
  create_symbol_table_entry(LIBRARY_TABLE, "zalloc",
    0, PROCEDURE, UINT64STAR_T, 1, code_size);

  // allocate memory in data segment for recording state of
  // malloc (bump pointer) in compiler-declared global variable
  data_size = data_size + WORDSIZE;

  // define global variable _bump for storing malloc's bump pointer
  // use bump_name string to obtain unique hash
  entry = create_symbol_table_entry(GLOBAL_TABLE, bump_name,
    1, VARIABLE, UINT64_T, 0, -data_size);

  // do not account for _bump as global variable
  number_of_global_variables = number_of_global_variables - 1;

  // allocate register for size parameter
  talloc();

  emit_load(current_temporary(), REG_SP, 0); // size
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  // round up to target-dependent memory word size
  emit_round_up(current_temporary(), WORDSIZE);

  // allocate register to compute new bump pointer
  talloc();

  // assert: current temporary is $t1 register to enable propagation of
  // lower and upper bounds on addresses in model generation of brk syscall

  // get current _bump which will be returned upon success
  emit_load(current_temporary(), get_scope(entry), get_address(entry));

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
  emit_store(get_scope(entry), get_address(entry), REG_A0);
  emit_addi(REG_A0, current_temporary(), 0);

  // gc_brk syscall skips up to this point, see implement_gc_brk

  tfree(2);

  emit_jalr(REG_ZR, REG_RA, 0);
}

uint64_t try_brk(uint64_t* context, uint64_t new_program_break) {
  uint64_t current_program_break;

  current_program_break = get_program_break(context);

  if (is_virtual_address_valid(new_program_break, WORDSIZE))
    if (is_address_between_stack_and_heap(context, new_program_break)) {
      if (debug_brk)
        printf("%s: setting program break to 0x%08lX\n", selfie_name, (uint64_t) new_program_break);

      set_program_break(context, new_program_break);

      // account for memory allocated by brk
      mc_brk = mc_brk + (new_program_break - current_program_break);

      return new_program_break;
    }

  // setting new program break failed, return current program break

  if (debug_brk)
    printf("%s: retrieving current program break 0x%08lX\n", selfie_name, (uint64_t) current_program_break);

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
    printf("(brk): ");
    print_register_hexadecimal(REG_A0);
    printf(" |- ");
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
    printf(" -> ");
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

  first_malloc  = (uint64_t) malloc(0);
  second_malloc = (uint64_t) malloc(0);

  if (first_malloc == 0)
    return 1;
  if (first_malloc != second_malloc)
    return 1;

  // selfie's malloc, cannot be boot level zero!
  return 0;
}

// -----------------------------------------------------------------
// ----------------------- HYPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emit_switch() {
  create_symbol_table_entry(LIBRARY_TABLE, "hypster_switch", 0,
    PROCEDURE, UINT64STAR_T, 2, code_size);

  emit_load(REG_A0, REG_SP, 0); // context to which we switch
  emit_addi(REG_SP, REG_SP, WORDSIZE);

  emit_load(REG_A1, REG_SP, 0); // number of instructions to execute
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

  write_register(REG_A6);

  timer = timeout;

  if (debug_switch) {
    printf("%s: switched from context 0x%08lX to context 0x%08lX", selfie_name,
      (uint64_t) from_context,
      (uint64_t) to_context);
    if (timer != TIMEROFF)
      printf(" to execute %lu instructions", timer);
    println();
  }

  return to_context;
}

void implement_switch() {
  // parameters
  uint64_t* to_context;
  uint64_t timeout;

  if (debug_syscalls) {
    printf("(switch): ");
    print_register_hexadecimal(REG_A0);
    printf(",");
    print_register_value(REG_A1);
    printf(" |- ");
    print_register_value(REG_A6);
  }

  read_register(REG_A0);
  read_register(REG_A1);

  to_context = (uint64_t*) *(registers + REG_A0);
  timeout    =             *(registers + REG_A1);

  save_context(current_context);

  // cache context on my boot level before switching
  to_context = cache_context(to_context);

  current_context = do_switch(current_context, to_context, timeout);

  if (debug_syscalls) {
    printf(" -> ");
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
// ----------------------------- CACHE -----------------------------
// -----------------------------------------------------------------

void reset_cache_counters(uint64_t* cache) {
  set_cache_hits(cache, 0);
  set_cache_misses(cache, 0);
}

void reset_all_cache_counters() {
  if (L1_CACHE_ENABLED) {
    reset_cache_counters(L1_DCACHE);
    reset_cache_counters(L1_ICACHE);
  }
}

void init_cache_memory(uint64_t* cache) {
  uint64_t number_of_cache_blocks;
  uint64_t* cache_memory;
  uint64_t i;
  uint64_t* cache_block;

  number_of_cache_blocks = get_cache_size(cache) / get_cache_block_size(cache);

  cache_memory = smalloc(number_of_cache_blocks * SIZEOFUINT64STAR);

  set_cache_memory(cache, cache_memory);

  i = 0;

  while (i < number_of_cache_blocks) {
    cache_block = allocate_cache_block();

    // valid bit and timestamp are already initialized to 0

    *(cache_memory + i) = (uint64_t) cache_block;

    set_block_memory(cache_block, smalloc(get_cache_block_size(cache)));

    i = i + 1;
  }
}

void init_cache(uint64_t* cache, uint64_t cache_size, uint64_t associativity, uint64_t cache_block_size) {
  set_cache_size(cache, cache_size);
  set_associativity(cache, associativity);
  set_cache_block_size(cache, cache_block_size);

  init_cache_memory(cache);

  reset_cache_counters(cache);
}

void init_all_caches() {
  L1_DCACHE = allocate_cache();

  init_cache(L1_DCACHE, L1_DCACHE_SIZE, L1_DCACHE_ASSOCIATIVITY, L1_DCACHE_BLOCK_SIZE);

  L1_ICACHE = allocate_cache();

  init_cache(L1_ICACHE, L1_ICACHE_SIZE, L1_ICACHE_ASSOCIATIVITY, L1_ICACHE_BLOCK_SIZE);
}

void flush_cache(uint64_t* cache) {
  uint64_t number_of_cache_blocks;
  uint64_t* cache_memory;
  uint64_t i;
  uint64_t* cache_block;

  number_of_cache_blocks = get_cache_size(cache) / get_cache_block_size(cache);

  cache_memory = get_cache_memory(cache);

  i = 0;

  while (i < number_of_cache_blocks) {
    cache_block = (uint64_t*) *(cache_memory + i);

    set_valid_flag(cache_block, 0);
    set_timestamp(cache_block, 0);

    i = i + 1;
  }

  set_cache_timer(cache, 0);
}

void flush_all_caches() {
  if (L1_CACHE_ENABLED) {
    flush_cache(L1_DCACHE);
    flush_cache(L1_ICACHE);
  }
}

uint64_t cache_set_size(uint64_t* cache) {
  return get_cache_size(cache) / get_associativity(cache);
}

// cache addressing:
//
// vaddr
// +-----+-------+-------------+
// |     | index | byte offset |
// +-----+-------+-------------+
// 31    ^       ^             0
//       |       |
//       |  log(cache_block_size)
//       |
// log(cache_size / associativity)
//       |
// paddr v
// +-----+---------------------+
// | tag |                     |
// +-----+---------------------+

uint64_t cache_tag(uint64_t* cache, uint64_t address) {
  return address / cache_set_size(cache);
}

uint64_t cache_index(uint64_t* cache, uint64_t address) {
  return (address - cache_tag(cache, address) * cache_set_size(cache)) / get_cache_block_size(cache);
}

uint64_t cache_block_address(uint64_t* cache, uint64_t address) {
  return address / get_cache_block_size(cache) * get_cache_block_size(cache);
}

uint64_t cache_byte_offset(uint64_t* cache, uint64_t address) {
  return address - cache_block_address(cache, address);
}

uint64_t* cache_set(uint64_t* cache, uint64_t vaddr) {
  return get_cache_memory(cache) + cache_index(cache, vaddr) * get_associativity(cache);
}

uint64_t get_new_timestamp(uint64_t* cache) {
  uint64_t timestamp;

  timestamp = get_cache_timer(cache);

  set_cache_timer(cache, timestamp + 1);

  return timestamp;
}

uint64_t* cache_lookup(uint64_t* cache, uint64_t vaddr, uint64_t paddr, uint64_t is_access) {
  uint64_t tag;
  uint64_t* set;
  uint64_t i;
  uint64_t* lru_block;
  uint64_t* cache_block;

  tag = cache_tag(cache, paddr);
  set = cache_set(cache, vaddr);

  i = 0;

  lru_block = (uint64_t*) *set;

  while (i < get_associativity(cache)) {
    cache_block = (uint64_t*) *(set + i);

    if (get_timestamp(cache_block) < get_timestamp(lru_block))
      lru_block = cache_block;

    if (get_valid_flag(cache_block))
      if (get_tag(cache_block) == tag) {
        // cache hit

        if (is_access) {
          set_cache_hits(cache, get_cache_hits(cache) + 1);

          set_timestamp(cache_block, get_new_timestamp(cache));
        }

        return cache_block;
      }

    i = i + 1;
  }

  // cache miss

  set_valid_flag(lru_block, 0);

  return lru_block;
}

void fill_cache_block(uint64_t* cache, uint64_t* cache_block, uint64_t paddr) {
  uint64_t number_of_words_in_cache_block;
  uint64_t* block_memory;
  uint64_t i;

  // cache block size / SIZEOFUINT64 (not WORDSIZE)
  number_of_words_in_cache_block = get_cache_block_size(cache) / SIZEOFUINT64;

  block_memory = get_block_memory(cache_block);

  // align paddr to cache block
  paddr = cache_block_address(cache, paddr);

  i = 0;

  while (i < number_of_words_in_cache_block) {
    *(block_memory + i) = load_physical_memory((uint64_t*) paddr + i);

    i = i + 1;
  }
}

uint64_t* handle_cache_miss(uint64_t* cache, uint64_t* cache_block, uint64_t paddr, uint64_t is_access) {
  if (is_access) {
    set_cache_misses(cache, get_cache_misses(cache) + 1);

    // make sure the entire cache block contains valid data
    fill_cache_block(cache, cache_block, paddr);

    set_tag(cache_block, cache_tag(cache, paddr));

    set_timestamp(cache_block, get_new_timestamp(cache));

    set_valid_flag(cache_block, 1);

    return cache_block;
  } else
    return (uint64_t*) 0;
}

uint64_t* retrieve_cache_block(uint64_t* cache, uint64_t vaddr, uint64_t paddr, uint64_t is_access) {
  uint64_t* cache_block;

  cache_block = cache_lookup(cache, vaddr, paddr, is_access);

  if (get_valid_flag(cache_block))
    // cache hit
    return cache_block;
  else
    return handle_cache_miss(cache, cache_block, paddr, is_access);
}

void flush_cache_block(uint64_t* cache, uint64_t* cache_block, uint64_t paddr) {
  uint64_t number_of_words_in_cache_block;
  uint64_t* block_memory;
  uint64_t i;

  // cache block size / SIZEOFUINT64 (not WORDSIZE)
  number_of_words_in_cache_block = get_cache_block_size(cache) / SIZEOFUINT64;

  block_memory = get_block_memory(cache_block);

  // align paddr to cache block
  paddr = cache_block_address(cache, paddr);

  i = 0;

  while (i < number_of_words_in_cache_block) {
    store_physical_memory((uint64_t*) paddr + i, *(block_memory + i));

    i = i + 1;
  }
}

uint64_t load_from_cache(uint64_t* cache, uint64_t vaddr, uint64_t paddr) {
  uint64_t* cache_block;
  uint64_t* block_memory;

  cache_block = retrieve_cache_block(cache, vaddr, paddr, 1);

  block_memory = get_block_memory(cache_block);

  return *(block_memory + cache_byte_offset(cache, vaddr) / SIZEOFUINT64);
}

void store_in_cache(uint64_t* cache, uint64_t vaddr, uint64_t paddr, uint64_t data) {
  uint64_t* cache_block;
  uint64_t* block_memory;

  cache_block = retrieve_cache_block(cache, vaddr, paddr, 1);

  block_memory = get_block_memory(cache_block);

  *(block_memory + cache_byte_offset(cache, vaddr) / SIZEOFUINT64) = data;

  flush_cache_block(cache, cache_block, paddr);
}

uint64_t load_instruction_from_cache(uint64_t vaddr, uint64_t paddr) {
  // assert: is_valid_virtual_address(vaddr) == 1

  return load_from_cache(L1_ICACHE, vaddr, paddr);
}

uint64_t load_data_from_cache(uint64_t vaddr, uint64_t paddr) {
  // assert: is_valid_virtual_address(vaddr) == 1

  return load_from_cache(L1_DCACHE, vaddr, paddr);
}

void store_data_in_cache(uint64_t vaddr, uint64_t paddr, uint64_t data) {
  uint64_t* cache_block;

  // assert: is_valid_virtual_address(vaddr) == 1

  store_in_cache(L1_DCACHE, vaddr, paddr, data);

  if (L1_CACHE_COHERENCY) {
    cache_block = retrieve_cache_block(L1_ICACHE, vaddr, paddr, 0);

    // mimicking x86 behavior (see Intel 64 and IA-32 Architectures Software Developer's
    // Manual Volume 3, Chapter 11.6 Self-Modifying Code: "A write to a memory location in
    // a code segment that is currently cached in the processor causes the associated
    // cache line (or lines) to be invalidated")
    if (cache_block != (uint64_t*) 0) {
      set_valid_flag(cache_block, 0);
      set_timestamp(cache_block, 0);

      L1_icache_coherency_invalidations = L1_icache_coherency_invalidations + 1;
    }
  }
}

void print_cache_profile(uint64_t hits, uint64_t misses, char* cache_name) {
  uint64_t accesses;

  accesses = hits + misses;

  printf("%s: %s%lu,", selfie_name, cache_name, accesses);
  printf("%lu(%lu.%.2lu%%),%lu(%lu.%.2lu%%)",
    hits,
    percentage_format_integral_2(accesses, hits),
    percentage_format_fractional_2(accesses, hits),
    misses,
    percentage_format_integral_2(accesses, misses),
    percentage_format_fractional_2(accesses, misses));
}

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

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

uint64_t get_page_of_virtual_address(uint64_t vaddr) {
  return vaddr / PAGESIZE;
}

uint64_t get_virtual_address_of_page_start(uint64_t page) {
  return page * PAGESIZE;
}

uint64_t is_virtual_address_valid(uint64_t vaddr, uint64_t alignment) {
  // is address virtual?
  if (vaddr <= HIGHESTVIRTUALADDRESS + (WORDSIZE - alignment))
    // is address aligned?
    if (vaddr % alignment == 0)
      return 1;

  return 0;
}

uint64_t is_virtual_address_mapped(uint64_t* table, uint64_t vaddr) {
  // assert: is_virtual_address_valid(vaddr, WORDSIZE) == 1

  return is_page_mapped(table, get_page_of_virtual_address(vaddr));
}

uint64_t* tlb(uint64_t* table, uint64_t vaddr) {
  uint64_t page;
  uint64_t frame;
  uint64_t paddr;

  // assert: is_virtual_address_valid(vaddr, WORDSIZE) == 1
  // assert: is_virtual_address_mapped(table, vaddr) == 1

  page = get_page_of_virtual_address(vaddr);

  frame = get_frame_for_page(table, page);

  // map virtual address to physical address
  // (single word on 32-bit target occupies double word on 64-bit system)
  paddr = (vaddr - page * PAGESIZE) * (SIZEOFUINT64 / WORDSIZE) + frame;

  if (debug_tlb)
    printf("%s: tlb access:\n vaddr: 0x%08lX\n page: 0x%04lX\n frame: 0x%08lX\n paddr: 0x%08lX\n", selfie_name,
      vaddr,
      page,
      frame,
      paddr);

  return (uint64_t*) paddr;
}

uint64_t load_virtual_memory(uint64_t* table, uint64_t vaddr) {
  // assert: is_virtual_address_valid(vaddr, WORDSIZE) == 1
  // assert: is_virtual_address_mapped(table, vaddr) == 1

  return load_physical_memory(tlb(table, vaddr));
}

void store_virtual_memory(uint64_t* table, uint64_t vaddr, uint64_t data) {
  // assert: is_virtual_address_valid(vaddr, WORDSIZE) == 1
  // assert: is_virtual_address_mapped(table, vaddr) == 1

  store_physical_memory(tlb(table, vaddr), data);
}

uint64_t load_cached_virtual_memory(uint64_t* table, uint64_t vaddr) {
  if (L1_CACHE_ENABLED)
    // assert: is_virtual_address_valid(vaddr, WORDSIZE) == 1
    // assert: is_virtual_address_mapped(table, vaddr) == 1
    return load_data_from_cache(vaddr, (uint64_t) tlb(table, vaddr));
  else
    return load_virtual_memory(table, vaddr);
}

void store_cached_virtual_memory(uint64_t* table, uint64_t vaddr, uint64_t data) {
  if (L1_CACHE_ENABLED)
    // assert: is_virtual_address_valid(vaddr, WORDSIZE) == 1
    // assert: is_virtual_address_mapped(table, vaddr) == 1
    store_data_in_cache(vaddr, (uint64_t) tlb(table, vaddr), data);
  else
    store_virtual_memory(table, vaddr, data);
}

uint64_t load_cached_instruction_word(uint64_t* table, uint64_t vaddr) {
  if (L1_CACHE_ENABLED)
    // assert: is_virtual_address_valid(vaddr, WORDSIZE) == 1
    // assert: is_virtual_address_mapped(table, vaddr) == 1
    return load_instruction_from_cache(vaddr, (uint64_t) tlb(table, vaddr));
  else
    return load_virtual_memory(table, vaddr);
}

// -----------------------------------------------------------------
// ---------------------- GARBAGE COLLECTOR ------------------------
// -----------------------------------------------------------------

void emit_fetch_stack_pointer() {
  create_symbol_table_entry(LIBRARY_TABLE, "fetch_stack_pointer",
    0, PROCEDURE, UINT64_T, 0, code_size);

  emit_add(REG_A0, REG_ZR, REG_SP);

  emit_jalr(REG_ZR, REG_RA, 0);
}

void emit_fetch_global_pointer() {
  create_symbol_table_entry(LIBRARY_TABLE, "fetch_global_pointer",
    0, PROCEDURE, UINT64_T, 0, code_size);

  emit_add(REG_A0, REG_ZR, REG_GP);

  emit_jalr(REG_ZR, REG_RA, 0);
}

void emit_fetch_data_segment_size_interface() {
  create_symbol_table_entry(LIBRARY_TABLE, "fetch_data_segment_size",
    0, PROCEDURE, UINT64_T, 0, code_size);

  // up to three instructions needed to load data segment size but is not yet known

  emit_nop();
  emit_nop();
  emit_nop();

  emit_jalr(REG_ZR, REG_RA, 0);
}

void emit_fetch_data_segment_size_implementation(uint64_t fetch_dss_code_location) {
  uint64_t saved_code_size;

  // set code emission to fetch_data_segment_size
  saved_code_size = code_size;
  code_size       = fetch_dss_code_location;

  // assert: emitting no more than 3 instructions

  // load data segment size into A0 (size is independent of entry point)
  load_small_and_medium_integer(REG_A0, data_size);

  // discount NOPs in profile that were generated for fetch_data_segment_size
  ic_addi = ic_addi - (code_size - fetch_dss_code_location) / INSTRUCTIONSIZE;

  // restore original code size
  code_size = saved_code_size;
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
      printf("(gc_brk): ");
      print_register_hexadecimal(REG_A0);
    }

    // calculate size by subtracting the current from the new program break
    size = program_break - get_program_break(context);

    if (debug_syscalls) {
      printf(" |- ");
      print_register_hexadecimal(REG_A0);
    }

    // yields the pointer to the newly/reused memory (or 0 if failed)
    *(get_regs(context) + REG_A0) = (uint64_t) gc_malloc_implementation(context, size);

    if (debug_syscalls) {
      printf(" -> ");
      print_register_hexadecimal(REG_A0);
      println();
    }

    // assert: _bump pointer is last entry in data segment

    // updating the _bump pointer of the program (for consistency)
    store_virtual_memory(get_pt(context), get_data_seg_end_gc(context) - WORDSIZE, get_program_break(context));

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
    return allocate_new_memory(context, GC_METADATA_SIZE);
  else
    return smalloc(GC_METADATA_SIZE);
}

uint64_t get_stack_seg_start_gc(uint64_t* context) {
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
    return get_data_seg_start(context) + get_data_seg_size(context);
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
  gc_init_selfie(context);
}

void gc_init_selfie(uint64_t* context) {
  reset_memory_counters();
  reset_gc_counters();

  // calculate metadata size using actual width of integers/pointers
  GC_METADATA_SIZE = SIZEOFUINT64 * 2 + SIZEOFUINT64STAR * 2;

  if (is_gc_library(context))
    GC_WORDSIZE = SIZEOFUINT64;
  else
    GC_WORDSIZE = WORDSIZE;

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
    // assert: is_virtual_address_valid(address, WORDSIZE) == 1
    if (is_virtual_address_mapped(get_pt(context), address))
      return load_virtual_memory(get_pt(context), address);
    else
      return 0;
}

void gc_store_memory(uint64_t* context, uint64_t address, uint64_t value) {
  if (is_gc_library(context))
    *((uint64_t*) address) = value;
  else
    // assert: is_virtual_address_valid(address, WORDSIZE) == 1
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

    object_start = object_start + GC_WORDSIZE;
  }
}

uint64_t* allocate_new_memory(uint64_t* context, uint64_t size) {
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

uint64_t* allocate_memory(uint64_t* context, uint64_t size) {
  return allocate_memory_selfie(context, size);
}

uint64_t* allocate_memory_selfie(uint64_t* context, uint64_t size) {
  uint64_t* object;
  uint64_t* metadata;

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
  object = allocate_new_memory(context, size);

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

uint64_t* gc_malloc_implementation(uint64_t* context, uint64_t size) {
  // first, garbage collect
  if (get_gcs_in_period_gc(context) >= GC_PERIOD) {
    gc_collect(context);

    set_gcs_in_period_gc(context, 0);
  } else
    set_gcs_in_period_gc(context, get_gcs_in_period_gc(context) + 1);

  // then, allocate memory

  size = round_up(size, GC_WORDSIZE);

  return allocate_memory(context, size);
}

uint64_t* get_metadata_if_address_is_valid(uint64_t* context, uint64_t address) {
  uint64_t* node;
  uint64_t  object;

  // pointer below gced heap
  if (address < get_heap_seg_start_gc(context))
    return (uint64_t*) 0;

  // pointer above gced heap
  if (address >= get_heap_seg_end_gc(context))
    return (uint64_t*) 0;

  node = get_used_list_head_gc(context);

  while (node != (uint64_t*) 0) {
    if (is_gc_library(context))
      if (address >= (uint64_t) node)
        if (address < ((uint64_t) node + GC_METADATA_SIZE))
          // address points to metadata (redundant check but possibly faster)
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
  uint64_t gc_address;

  gc_address = gc_load_memory(context, address);

  mark_object_selfie(context, gc_address);
}

void mark_object_selfie(uint64_t* context, uint64_t gc_address) {
  uint64_t* metadata;
  uint64_t object_start;
  uint64_t object_end;

  if (is_gc_library(context) == 0)
    if (is_virtual_address_valid(gc_address, WORDSIZE) == 0)
      return;

  metadata = get_metadata_if_address_is_valid(context, gc_address);

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

    object_start = object_start + GC_WORDSIZE;
  }
}

void mark_segment(uint64_t* context, uint64_t segment_start, uint64_t segment_end) {
  // assert: segment is not heap

  // prevent (32-bit) overflow by subtracting GC_WORDSIZE from index
  segment_start = segment_start - GC_WORDSIZE;

  while (segment_start < segment_end - GC_WORDSIZE) {
    // undo GC_WORDSIZE index offset before marking address
    mark_object(context, segment_start + GC_WORDSIZE);

    segment_start = segment_start + GC_WORDSIZE;
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
  mark_segment(context, get_stack_seg_start_gc(context), VIRTUALMEMORYSIZE * GIGABYTE);

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
  sweep_selfie(context);
}

void sweep_selfie(uint64_t* context) {
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
  printf("%s: gc:      %lu.%.2luMB requested in %lu mallocs (%lu gced, %lu reuses)\n", selfie_name,
    ratio_format_integral_2(gc_mem_mallocated, MEGABYTE),
    ratio_format_fractional_2(gc_mem_mallocated, MEGABYTE),
    gc_num_mallocated,
    gc_num_gced_mallocs,
    gc_num_reused_mallocs);
  printf("%s: gc:      %lu.%.2luMB(%lu.%.2lu%%) reused in %lu reused mallocs\n", selfie_name,
    ratio_format_integral_2(gc_mem_reused, MEGABYTE),
    ratio_format_fractional_2(gc_mem_reused, MEGABYTE),
    percentage_format_integral_2(gc_mem_mallocated, gc_mem_reused),
    percentage_format_fractional_2(gc_mem_mallocated, gc_mem_reused),
    gc_num_reused_mallocs);
  printf("%s: gc:      %lu.%.2luMB collected in %lu gc runs\n", selfie_name,
    ratio_format_integral_2(gc_mem_collected, MEGABYTE),
    ratio_format_fractional_2(gc_mem_collected, MEGABYTE),
    gc_num_collects);
  printf("%s: gc:      %lu.%.2luMB(%lu.%.2lu%%) allocated in %lu mallocs (%lu gced, %lu ungced)\n", selfie_name,
    ratio_format_integral_2(gc_mem_objects + gc_mem_metadata, MEGABYTE),
    ratio_format_fractional_2(gc_mem_objects + gc_mem_metadata, MEGABYTE),
    percentage_format_integral_2(gc_mem_mallocated, gc_mem_objects + gc_mem_metadata),
    percentage_format_fractional_2(gc_mem_mallocated, gc_mem_objects + gc_mem_metadata),
    gc_num_gced_mallocs + gc_num_ungced_mallocs,
    gc_num_gced_mallocs,
    gc_num_ungced_mallocs);
  printf("%s: gc:      %lu.%.2luMB(%lu.%.2lu%%) allocated in %lu gced mallocs\n", selfie_name,
    ratio_format_integral_2(gc_mem_objects, MEGABYTE),
    ratio_format_fractional_2(gc_mem_objects, MEGABYTE),
    percentage_format_integral_2(gc_mem_mallocated, gc_mem_objects),
    percentage_format_fractional_2(gc_mem_mallocated, gc_mem_objects),
    gc_num_gced_mallocs);
  printf("%s: gc:      %lu.%.2luMB(%lu.%.2lu%%) allocated in %lu ungced mallocs", selfie_name,
    ratio_format_integral_2(gc_mem_metadata, MEGABYTE),
    ratio_format_fractional_2(gc_mem_metadata, MEGABYTE),
    percentage_format_integral_2(gc_mem_mallocated, gc_mem_metadata),
    percentage_format_fractional_2(gc_mem_mallocated, gc_mem_metadata),
    gc_num_ungced_mallocs);
  if (is_gc_library(context) == 0)
    printf(" (external)");
  println();
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

uint64_t print_code_line_number_for_instruction(uint64_t address, uint64_t offset) {
  if (code_line_number != (uint64_t*) 0)
    return dprintf(output_fd, "(~%lu)", *(code_line_number + (address - offset) / INSTRUCTIONSIZE));
  else
    return 0;
}

uint64_t print_code_context_for_instruction(uint64_t address) {
  uint64_t w;

  if (run) {
    w = dprintf(output_fd, "%s: pc==0x%lX", binary_name, address)
      + print_code_line_number_for_instruction(address, code_start);
    if (symbolic)
      // skip further output
      return w;
    else
      return w + dprintf(output_fd, ": ");
  } else if (model)
    return dprintf(output_fd, "0x%lX", address)
      + print_code_line_number_for_instruction(address, code_start)
      + dprintf(output_fd, ": ");
  else if (disassemble_verbose)
    return dprintf(output_fd, "0x%lX", address)
      + print_code_line_number_for_instruction(address, 0)
      + dprintf(output_fd, ": 0x%08lX: ", (uint64_t) ir);
  else
    return 0;
}

uint64_t print_lui() {
  return print_code_context_for_instruction(pc) +
    dprintf(output_fd, "%s %s,0x%lX", get_mnemonic(is), get_register_name(rd), sign_shrink(imm, 20));
}

void print_lui_before() {
  printf(": |- ");
  print_register_hexadecimal(rd);
}

void print_lui_after() {
  printf(" -> ");
  print_register_hexadecimal(rd);
}

void record_lui_addi_add_sub_mul_divu_remu_sltu_jal_jalr() {
  record_state(*(registers + rd));
}

void do_lui() {
  // load upper immediate

  uint64_t next_rd_value;

  if (rd != REG_ZR) {
    // semantics of lui
    next_rd_value = left_shift(imm, 12);

    if (*(registers + rd) != next_rd_value)
      *(registers + rd) = next_rd_value;
    else
      nopc_lui = nopc_lui + 1;
  } else
    nopc_lui = nopc_lui + 1;

  write_register(rd);

  pc = pc + INSTRUCTIONSIZE;

  ic_lui = ic_lui + 1;
}

void undo_lui_addi_add_sub_mul_divu_remu_sltu_load_jal_jalr() {
  *(registers + rd) = *(values + (tc % MAX_REPLAY_LENGTH));
}

uint64_t print_addi() {
  uint64_t w;

  w = print_code_context_for_instruction(pc);

  if (rd == REG_ZR)
    if (rs1 == REG_ZR)
      if (imm == 0)
        return w + dprintf(output_fd, "nop");

  return w + dprintf(output_fd, "%s %s,%s,%ld", get_mnemonic(is), get_register_name(rd), get_register_name(rs1), imm);
}

void print_addi_before() {
  printf(": ");
  print_register_value(rs1);
  printf(" |- ");
  print_register_value(rd);
}

void print_addi_add_sub_mul_divu_remu_sltu_after() {
  printf(" -> ");
  print_register_value(rd);
}

void do_addi() {
  // add immediate

  uint64_t next_rd_value;

  read_register_wrap(rs1, imm);

  if (rd != REG_ZR) {
    // semantics of addi
    next_rd_value = *(registers + rs1) + imm;

    if (*(registers + rd) != next_rd_value)
      *(registers + rd) = next_rd_value;
    else
      nopc_addi = nopc_addi + 1;
  } else
    nopc_addi = nopc_addi + 1;

  write_register(rd);

  pc = pc + INSTRUCTIONSIZE;

  ic_addi = ic_addi + 1;
}

uint64_t print_add_sub_mul_divu_remu_sltu() {
  return print_code_context_for_instruction(pc)
    + dprintf(output_fd, "%s %s,%s,%s", get_mnemonic(is), get_register_name(rd), get_register_name(rs1), get_register_name(rs2));
}

void print_add_sub_mul_divu_remu_sltu_before() {
  printf(": ");
  print_register_value(rs1);
  printf(",");
  print_register_value(rs2);
  printf(" |- ");
  print_register_value(rd);
}

void do_add() {
  uint64_t next_rd_value;

  read_register(rs1);
  read_register(rs2);

  if (rd != REG_ZR) {
    // semantics of add
    next_rd_value = *(registers + rs1) + *(registers + rs2);

    if (*(registers + rd) != next_rd_value)
      *(registers + rd) = next_rd_value;
    else
      nopc_add = nopc_add + 1;
  } else
    nopc_add = nopc_add + 1;

  write_register(rd);

  pc = pc + INSTRUCTIONSIZE;

  ic_add = ic_add + 1;
}

void do_sub() {
  uint64_t next_rd_value;

  read_register(rs1);
  read_register(rs2);

  if (rd != REG_ZR) {
    // semantics of sub
    next_rd_value = *(registers + rs1) - *(registers + rs2);

    if (*(registers + rd) != next_rd_value)
      *(registers + rd) = next_rd_value;
    else
      nopc_sub = nopc_sub + 1;
  } else
    nopc_sub = nopc_sub + 1;

  write_register(rd);

  pc = pc + INSTRUCTIONSIZE;

  ic_sub = ic_sub + 1;
}

void do_mul() {
  uint64_t next_rd_value;

  read_register(rs1);
  read_register(rs2);

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

  write_register(rd);

  pc = pc + INSTRUCTIONSIZE;

  ic_mul = ic_mul + 1;
}

void do_divu() {
  // division unsigned

  uint64_t next_rd_value;

  if (*(registers + rs2) != 0) {
    read_register(rs1);
    read_register(rs2);

    if (rd != REG_ZR) {
      // semantics of divu
      next_rd_value = *(registers + rs1) / *(registers + rs2);

      if (*(registers + rd) != next_rd_value)
        *(registers + rd) = next_rd_value;
      else
        nopc_divu = nopc_divu + 1;
    } else
      nopc_divu = nopc_divu + 1;

    write_register(rd);

    pc = pc + INSTRUCTIONSIZE;

    ic_divu = ic_divu + 1;
  } else
    throw_exception(EXCEPTION_DIVISIONBYZERO, pc);
}

void do_remu() {
  // remainder unsigned

  uint64_t next_rd_value;

  if (*(registers + rs2) != 0) {
    read_register(rs1);
    read_register(rs2);

    if (rd != REG_ZR) {
      // semantics of remu
      next_rd_value = *(registers + rs1) % *(registers + rs2);

      if (*(registers + rd) != next_rd_value)
        *(registers + rd) = next_rd_value;
      else
        nopc_remu = nopc_remu + 1;
    } else
      nopc_remu = nopc_remu + 1;

    write_register(rd);

    pc = pc + INSTRUCTIONSIZE;

    ic_remu = ic_remu + 1;
  } else
    throw_exception(EXCEPTION_DIVISIONBYZERO, pc);
}

void do_sltu() {
  // set on less than unsigned

  uint64_t next_rd_value;

  read_register(rs1);
  read_register(rs2);

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

  write_register(rd);

  pc = pc + INSTRUCTIONSIZE;

  ic_sltu = ic_sltu + 1;
}

uint64_t print_load() {
  return print_code_context_for_instruction(pc)
    + dprintf(output_fd, "%s %s,%ld(%s)", get_mnemonic(is), get_register_name(rd), imm, get_register_name(rs1));
}

void print_load_before() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  printf(": ");
  print_register_hexadecimal(rs1);

  if (is_virtual_address_valid(vaddr, WORDSIZE))
    if (is_virtual_address_mapped(pt, vaddr)) {
      if (is_system_register(rd))
        printf(",mem[0x%lX]==0x%lX |- ", vaddr, load_virtual_memory(pt, vaddr));
      else
        printf(",mem[0x%lX]==%ld |- ", vaddr, load_virtual_memory(pt, vaddr));
      print_register_value(rd);

      return;
    }

  printf(" |-");
}

void print_load_after(uint64_t vaddr) {
  if (is_virtual_address_valid(vaddr, WORDSIZE))
    if (is_virtual_address_mapped(pt, vaddr)) {
      printf(" -> ");
      print_register_value(rd);
      printf("==mem[0x%lX]", vaddr);
    }
}

void record_load() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  if (is_virtual_address_valid(vaddr, WORDSIZE))
    if (is_virtual_address_mapped(pt, vaddr))
      record_state(*(registers + rd));
}

uint64_t do_load() {
  uint64_t vaddr;
  uint64_t next_rd_value;
  uint64_t a;

  // load (double) word

  read_register(rs1);

  vaddr = *(registers + rs1) + imm;

  if (is_virtual_address_valid(vaddr, WORDSIZE)) {
    if (is_valid_segment_read(vaddr)) {
      if (is_virtual_address_mapped(pt, vaddr)) {
        if (rd != REG_ZR) {
          // semantics of load (double) word
          next_rd_value = load_cached_virtual_memory(pt, vaddr);

          if (*(registers + rd) != next_rd_value)
            *(registers + rd) = next_rd_value;
          else
            nopc_load = nopc_load + 1;
        } else
          nopc_load = nopc_load + 1;

        write_register_wrap(rd, 0);

        // keep track of instruction address for profiling loads
        a = (pc - code_start) / INSTRUCTIONSIZE;

        pc = pc + INSTRUCTIONSIZE;

        // keep track of number of loads in total
        ic_load = ic_load + 1;

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

uint64_t print_store() {
  return print_code_context_for_instruction(pc)
    + dprintf(output_fd, "%s %s,%ld(%s)", get_mnemonic(is), get_register_name(rs2), imm, get_register_name(rs1));
}

void print_store_before() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  printf(": ");
  print_register_hexadecimal(rs1);

  if (is_virtual_address_valid(vaddr, WORDSIZE))
    if (is_virtual_address_mapped(pt, vaddr)) {
      printf(",");
      print_register_value(rs2);
      if (is_system_register(rd))
        printf(" |- mem[0x%lX]==0x%lX", vaddr, load_virtual_memory(pt, vaddr));
      else
        printf(" |- mem[0x%lX]==%ld", vaddr, load_virtual_memory(pt, vaddr));

      return;
    }

  printf(" |-");
}

void print_store_after(uint64_t vaddr) {
  if (is_virtual_address_valid(vaddr, WORDSIZE))
    if (is_virtual_address_mapped(pt, vaddr)) {
      printf(" -> mem[0x%lX]==", vaddr);
      print_register_value(rs2);
    }
}

void record_store() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  if (is_virtual_address_valid(vaddr, WORDSIZE))
    if (is_virtual_address_mapped(pt, vaddr))
      record_state(load_virtual_memory(pt, vaddr));
}

uint64_t do_store() {
  uint64_t vaddr;
  uint64_t a;

  // store (double) word

  read_register(rs1);

  vaddr = *(registers + rs1) + imm;

  if (is_virtual_address_valid(vaddr, WORDSIZE)) {
    if (is_valid_segment_write(vaddr)) {
      if (is_virtual_address_mapped(pt, vaddr)) {
        read_register_wrap(rs2, 0);

        // semantics of store (double) word
        if (load_virtual_memory(pt, vaddr) != *(registers + rs2))
          store_cached_virtual_memory(pt, vaddr, *(registers + rs2));
        else {
          nopc_store = nopc_store + 1;

          if (L1_CACHE_ENABLED)
            // effective nop still changes the cache state
            store_cached_virtual_memory(pt, vaddr, *(registers + rs2));
        }

        // keep track of instruction address for profiling stores
        a = (pc - code_start) / INSTRUCTIONSIZE;

        pc = pc + INSTRUCTIONSIZE;

        // keep track of number of stores in total
        ic_store = ic_store + 1;

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

void undo_store() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  store_virtual_memory(pt, vaddr, *(values + (tc % MAX_REPLAY_LENGTH)));
}

uint64_t print_beq() {
  uint64_t w;

  w = print_code_context_for_instruction(pc)
    + dprintf(output_fd, "%s %s,%s,%ld", get_mnemonic(is), get_register_name(rs1), get_register_name(rs2), signed_division(imm, INSTRUCTIONSIZE));
  if (disassemble_verbose)
    return w + dprintf(output_fd, "[0x%lX]", pc + imm);
  else
    return w;
}

void print_beq_before() {
  printf(": ");
  print_register_value(rs1);
  printf(",");
  print_register_value(rs2);
  printf(" |- pc==0x%lX", pc);
}

void print_beq_after() {
  printf(" -> pc==0x%lX", pc);
}

void record_beq() {
  record_state(0);
}

void do_beq() {
  // branch on equal

  read_register(rs1);
  read_register(rs2);

  // semantics of beq
  if (*(registers + rs1) == *(registers + rs2))
    pc = pc + imm;
  else {
    pc = pc + INSTRUCTIONSIZE;

    nopc_beq = nopc_beq + 1;
  }

  ic_beq = ic_beq + 1;
}

uint64_t print_jal() {
  uint64_t w;

  w = print_code_context_for_instruction(pc)
    + dprintf(output_fd, "%s %s,%ld", get_mnemonic(is), get_register_name(rd), signed_division(imm, INSTRUCTIONSIZE));
  if (disassemble_verbose)
    return w + dprintf(output_fd, "[0x%lX]", pc + imm);
  else
    return w;
}

void print_jal_before() {
  printf(": |- ");
  if (rd != REG_ZR) {
    print_register_hexadecimal(rd);
    printf(",");
  }
  printf("pc==0x%lX", pc);
}

void print_jal_jalr_after() {
  print_beq_after();
  if (rd != REG_ZR) {
    printf(",");
    print_register_hexadecimal(rd);
  }
}

void do_jal() {
  uint64_t a;

  // jump and link

  if (rd != REG_ZR) {
    // first link
    *(registers + rd) = pc + INSTRUCTIONSIZE;

    // then jump (for procedure call)
    pc = pc + imm;

    // prologue address for profiling procedure calls
    a = (pc - code_start) / INSTRUCTIONSIZE;

    // keep track of number of procedure calls in total
    calls = calls + 1;

    // and individually
    *(calls_per_procedure + a) = *(calls_per_procedure + a) + 1;
  } else if (signed_less_than(imm, 0)) {
    // just jump backward (to check loop condition again)
    pc = pc + imm;

    // first loop instruction address for profiling loop iterations
    a = (pc - code_start) / INSTRUCTIONSIZE;

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

  write_register(rd);

  ic_jal = ic_jal + 1;
}

uint64_t print_jalr() {
  return print_code_context_for_instruction(pc)
    + dprintf(output_fd, "%s %s,%ld(%s)", get_mnemonic(is), get_register_name(rd), signed_division(imm, INSTRUCTIONSIZE), get_register_name(rs1));
}

void print_jalr_before() {
  printf(": ");
  print_register_hexadecimal(rs1);
  printf(" |- ");
  if (rd != REG_ZR) {
    print_register_hexadecimal(rd);
    printf(",");
  }
  printf("pc==0x%lX", pc);
}

void do_jalr() {
  uint64_t next_pc;

  // jump and link register

  read_register(rs1);

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

  write_register(rd);

  ic_jalr = ic_jalr + 1;
}

uint64_t print_ecall() {
  return print_code_context_for_instruction(pc)
    + dprintf(output_fd, "%s", get_mnemonic(is));
}

void record_ecall() {
  // TODO: record all side effects
  record_state(*(registers + REG_A0));
}

void do_ecall() {
  read_register(REG_A7);

  ic_ecall = ic_ecall + 1;

  if (redo) {
    // TODO: redo all side effects
    *(registers + REG_A0) = *(values + (tc % MAX_REPLAY_LENGTH));

    // TODO: print ecall details
    println();

    pc = pc + INSTRUCTIONSIZE;
  } else if (*(registers + REG_A7) == SYSCALL_SWITCH)
    if (record) {
      printf("%s: context switching during recording is unsupported\n", selfie_name);

      exit(EXITCODE_UNSUPPORTEDSYSCALL);
    } else if (symbolic) {
      printf("%s: context switching during symbolic execution is unsupported\n", selfie_name);

      exit(EXITCODE_UNSUPPORTEDSYSCALL);
    } else {
      pc = pc + INSTRUCTIONSIZE;

      implement_switch();
    }
  else {
    read_register(REG_A0);

    if (*(registers + REG_A7) != SYSCALL_EXIT) {
      if (*(registers + REG_A7) != SYSCALL_BRK) {
        read_register(REG_A1);
        read_register(REG_A2);

        if (*(registers + REG_A7) == SYSCALL_OPENAT)
          read_register(REG_A3);
      }

      write_register(REG_A0);
    }

    // all system calls other than switch are handled by exception
    throw_exception(EXCEPTION_SYSCALL, *(registers + REG_A7));
  }
}

void undo_ecall() {
  uint64_t a0;

  a0 = *(registers + REG_A0);

  // TODO: undo all side effects
  *(registers + REG_A0) = *(values + (tc % MAX_REPLAY_LENGTH));

  // save register a0 for redoing system call
  *(values + (tc % MAX_REPLAY_LENGTH)) = a0;
}

uint64_t print_data_line_number() {
  if (data_line_number != (uint64_t*) 0)
    return dprintf(output_fd, "(~%lu)", *(data_line_number + (pc - code_size) / WORDSIZE));
  else
    return 0;
}

uint64_t print_data_context() {
  return dprintf(output_fd, "0x%lX", pc)
    + print_data_line_number()
    + dprintf(output_fd, ": ");
}

uint64_t print_data() {
  uint64_t w;

  if (disassemble_verbose)
    w = print_data_context();
  else
    w = 0;
  if (IS64BITTARGET)
    w = w + dprintf(output_fd, ".8byte ");
  else
    w = w + dprintf(output_fd, ".4byte ");

  return w + dprintf(output_fd, "0x%lX", load_data(pc - code_size));
}

// -----------------------------------------------------------------
// -------------------------- DISASSEMBLER -------------------------
// -----------------------------------------------------------------

char* get_mnemonic(uint64_t ins) {
  return (char*) *(MNEMONICS + ins);
}

uint64_t print_instruction() {
  // assert: 1 <= is <= number of RISC-U instructions
  if (is == ADDI)
    return print_addi();
  else if (is == LOAD)
    return print_load();
  else if (is == STORE)
    return print_store();
  else if (is == ADD)
    return print_add_sub_mul_divu_remu_sltu();
  else if (is == SUB)
    return print_add_sub_mul_divu_remu_sltu();
  else if (is == MUL)
    return print_add_sub_mul_divu_remu_sltu();
  else if (is == DIVU)
    return print_add_sub_mul_divu_remu_sltu();
  else if (is == REMU)
    return print_add_sub_mul_divu_remu_sltu();
  else if (is == SLTU)
    return print_add_sub_mul_divu_remu_sltu();
  else if (is == BEQ)
    return print_beq();
  else if (is == JAL)
    return print_jal();
  else if (is == JALR)
    return print_jalr();
  else if (is == LUI)
    return print_lui();
  else if (is == ECALL)
    return print_ecall();
  else
    return 0;
}

void selfie_disassemble(uint64_t verbose) {
  uint64_t number_of_written_characters;

  assembly_name = get_argument();

  if (code_size + data_size == 0) {
    printf("%s: nothing to disassemble to output file %s\n", selfie_name, assembly_name);

    return;
  }

  // assert: assembly_name is mapped and not longer than MAX_FILENAME_LENGTH

  assembly_fd = open_write_only(assembly_name, S_IRUSR_IWUSR_IRGRP_IROTH);

  if (signed_less_than(assembly_fd, 0)) {
    printf("%s: could not create assembly output file %s\n", selfie_name, assembly_name);

    exit(EXITCODE_IOERROR);
  }

  output_name = assembly_name;
  output_fd   = assembly_fd;

  reset_library();
  reset_interpreter();

  run = 0;

  disassemble_verbose = verbose;

  number_of_written_characters = 0;

  while (pc < code_size) {
    ir = load_instruction(pc);

    decode();

    number_of_written_characters = number_of_written_characters
      + print_instruction()
      + dprintf(output_fd, "\n");

    pc = pc + INSTRUCTIONSIZE;
  }

  while (pc - code_size < data_size) {
    number_of_written_characters = number_of_written_characters
      + print_data()
      + dprintf(output_fd, "\n");

    pc = pc + WORDSIZE;
  }

  disassemble_verbose = 0;

  output_name = (char*) 0;
  output_fd   = 1;

  printf("%s: %lu characters of assembly with %lu %lu-bit RISC-U instructions and %lu bytes of data written into %s\n", selfie_name,
    number_of_written_characters,
    code_size / INSTRUCTIONSIZE,
    WORDSIZEINBITS,
    data_size,
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
  printf("%s==0x%lX", get_register_name(reg), *(registers + reg));
}

void print_register_octal(uint64_t reg) {
  printf("%s==0o%lo", get_register_name(reg), *(registers + reg));
}

void print_register_value(uint64_t reg) {
  if (is_system_register(reg))
    print_register_hexadecimal(reg);
  else
    printf("%s==%ld(0x%lX)", get_register_name(reg), *(registers + reg), *(registers + reg));
}

void print_exception(uint64_t exception, uint64_t fault) {
  printf("%s", (char*) *(EXCEPTIONS + exception));

  if (exception == EXCEPTION_PAGEFAULT)
    printf(" at page 0x%04lX", (uint64_t) fault);
  else if (exception == EXCEPTION_SEGMENTATIONFAULT)
    printf(" at address 0x%08lX", (uint64_t) fault);
  else if (exception == EXCEPTION_SYSCALL)
    printf(" ID %lu", fault);
  else if (exception == EXCEPTION_DIVISIONBYZERO)
    printf(" at address 0x%08lX", (uint64_t) fault);
  else if (exception == EXCEPTION_INVALIDADDRESS)
    printf(" 0x%08lX", (uint64_t) fault);
  else if (exception == EXCEPTION_UNKNOWNINSTRUCTION)
    printf(" at address 0x%08lX", (uint64_t) fault);
  else if (exception == EXCEPTION_UNINITIALIZEDREGISTER) {
    printf(" ");print_register_name(fault);
  }
}

void throw_exception(uint64_t exception, uint64_t fault) {
  if (get_exception(current_context) != EXCEPTION_NOEXCEPTION)
    if (get_exception(current_context) != exception) {
      printf("%s: context 0x%08lX throws exception: ", selfie_name, (uint64_t) current_context);
      print_exception(exception, fault);
      printf(" in presence of existing exception: ");
      print_exception(get_exception(current_context), get_fault(current_context));
      println();

      exit(EXITCODE_MULTIPLEEXCEPTIONERROR);
    }

  set_exception(current_context, exception);
  set_fault(current_context, fault);

  trap = 1;

  if (debug_exception) {
    printf("%s: context 0x%08lX throws exception: ", selfie_name, (uint64_t) current_context);
    print_exception(exception, fault);
    println();
  }
}

void fetch() {
  if (is_virtual_address_valid(pc, INSTRUCTIONSIZE)) {
    if (is_code_address(current_context, pc)) {
      // assert: is_virtual_address_mapped(pt, pc) == 1

      if (pc % WORDSIZE == 0)
        ir = get_low_word(load_cached_instruction_word(pt, pc));
      else
        ir = get_high_word(load_cached_instruction_word(pt, pc - INSTRUCTIONSIZE));

      return;
    } else
      throw_exception(EXCEPTION_SEGMENTATIONFAULT, pc);
  } else
    throw_exception(EXCEPTION_INVALIDADDRESS, pc);

  // reset instruction register
  ir = encode_nop();
}

void decode() {
  opcode = get_opcode(ir);

  is = 0;

  if (opcode == OP_IMM) {
    decode_i_format();

    if (funct3 == F3_ADDI)
      is = ADDI;
  } else if (opcode == OP_LOAD) {
    decode_i_format();

    if (IS64BITTARGET) {
      if (funct3 == F3_LD)
        is = LOAD;
    } else if (funct3 == F3_LW)
      is = LOAD;
  } else if (opcode == OP_STORE) {
    decode_s_format();

    if (IS64BITTARGET) {
      if (funct3 == F3_SD)
        is = STORE;
    } else if (funct3 == F3_SW)
      is = STORE;
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

      printf("%s: at address 0x%08lX unknown instruction 0x%lX with opcode 0x%lX detected\n", selfie_name,
        pc,
        ir,
        opcode);

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
  else if (is == LOAD)
    do_load();
  else if (is == STORE)
    do_store();
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
  } else if (is == LOAD) {
    record_load();
    do_load();
  } else if (is == STORE) {
    record_store();
    do_store();
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
  if (is == STORE)
    undo_store();
  else if (is == BEQ)
    // beq does not require any undo
    return;
  else if (is == ECALL)
    undo_ecall();
  else
    undo_lui_addi_add_sub_mul_divu_remu_sltu_load_jal_jalr();
}

void execute_debug() {
  print_instruction();

  // assert: 1 <= is <= number of RISC-U instructions
  if (is == ADDI) {
    print_addi_before();
    do_addi();
    print_addi_add_sub_mul_divu_remu_sltu_after();
  } else if (is == LOAD) {
    print_load_before();
    print_load_after(do_load());
  } else if (is == STORE) {
    print_store_before();
    print_store_after(do_store());
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

  while (i < code_size / INSTRUCTIONSIZE) {
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

    printf(",%lu(%lu.%.2lu%%)@0x%lX", c,
      percentage_format_integral_2(total, c),
      percentage_format_fractional_2(total, c), a);
    if (code_line_number != (uint64_t*) 0)
      printf("(~%lu)", *(code_line_number + a / INSTRUCTIONSIZE));

    return c;
  } else {
    printf(",0(0.00%%)");

    return 0;
  }
}

void print_per_instruction_profile(char* message, uint64_t total, uint64_t* counters) {
  printf("%s: %s%lu", selfie_name, message, total);
  print_per_instruction_counter(total, counters, print_per_instruction_counter(total, counters, print_per_instruction_counter(total, counters, UINT64_MAX)));
  println();
}

void print_access_profile(char* message, char* padding, uint64_t reads, uint64_t writes) {
  if (reads + writes > 0) {
    if (writes == 0)
      // may happen in read-only memory segments
      writes = 1;

    printf("%s: %s%s%lu,%lu,%lu[%lu.%.2lu]\n", selfie_name, message, padding,
      reads + writes, reads, writes,
      ratio_format_integral_2(reads, writes),
      ratio_format_fractional_2(reads, writes));
  }
}

void print_per_register_profile(uint64_t reg) {
  print_access_profile(get_register_name(reg), " register:   ", *(reads_per_register + reg), *(writes_per_register + reg));
}

void print_register_memory_profile() {
  uint64_t reg;

  printf("%s: CPU+memory:    reads+writes,reads,writes[reads/writes]\n", selfie_name);

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
  printf("%s: --------------------------------------------------------------------------------\n", selfie_name);
  printf("%s: summary: %lu executed instructions [%lu.%.2lu%% nops]\n", selfie_name,
    get_total_number_of_instructions(),
    percentage_format_integral_2(get_total_number_of_instructions(), get_total_number_of_nops()),
    percentage_format_fractional_2(get_total_number_of_instructions(), get_total_number_of_nops()));
  printf("%s:          %lu.%.2luKB peak stack size\n", selfie_name,
    ratio_format_integral_2(VIRTUALMEMORYSIZE * GIGABYTE - stack_peak, KILOBYTE),
    ratio_format_fractional_2(VIRTUALMEMORYSIZE * GIGABYTE - stack_peak, KILOBYTE));
  printf("%s:          %lu.%.2luMB allocated in %lu mallocs\n", selfie_name,
    ratio_format_integral_2(mc_brk, MEGABYTE),
    ratio_format_fractional_2(mc_brk, MEGABYTE),
    sc_brk);
  printf("%s:          %lu.%.2luMB(%lu.%.2lu%% of %lu.%.2luMB) actually accessed\n", selfie_name,
    ratio_format_integral_2(mc_mapped_heap, MEGABYTE),
    ratio_format_fractional_2(mc_mapped_heap, MEGABYTE),
    percentage_format_integral_2(round_up(mc_brk, PAGESIZE), mc_mapped_heap),
    percentage_format_fractional_2(round_up(mc_brk, PAGESIZE), mc_mapped_heap),
    ratio_format_integral_2(mc_brk, MEGABYTE),
    ratio_format_fractional_2(mc_brk, MEGABYTE));
  printf("%s:          %lu.%.2luMB(%lu.%.2lu%% of %luMB) mapped memory\n", selfie_name,
    ratio_format_integral_2(pused(), MEGABYTE),
    ratio_format_fractional_2(pused(), MEGABYTE),
    percentage_format_integral_2(PHYSICALMEMORYSIZE, pused()),
    percentage_format_fractional_2(PHYSICALMEMORYSIZE, pused()),
    PHYSICALMEMORYSIZE / MEGABYTE);

  if (GC_ON) {
    printf("%s: --------------------------------------------------------------------------------\n", selfie_name);
    print_gc_profile(context);
  }

  if (get_total_number_of_instructions() > 0) {
    printf("%s: --------------------------------------------------------------------------------\n", selfie_name);
    print_instruction_counters();

    if (code_line_number != (uint64_t*) 0)
      printf("%s: profile: total,max(ratio%%)@address(line#),2ndmax,3rdmax\n", selfie_name);
    else
      printf("%s: profile: total,max(ratio%%)@address,2ndmax,3rdmax\n", selfie_name);

    print_per_instruction_profile("calls:   ", calls, calls_per_procedure);
    print_per_instruction_profile("loops:   ", iterations, iterations_per_loop);
    print_per_instruction_profile("loads:   ", ic_load, loads_per_instruction);
    print_per_instruction_profile("stores:  ", ic_store, stores_per_instruction);

    print_register_memory_profile();
  }

  if (L1_CACHE_ENABLED) {
    printf("%s: L1 caches:     accesses,hits,misses\n", selfie_name);

    print_cache_profile(get_cache_hits(L1_DCACHE), get_cache_misses(L1_DCACHE), "data:          ");
    println();

    print_cache_profile(get_cache_hits(L1_ICACHE), get_cache_misses(L1_ICACHE), "instruction:   ");
    if (L1_CACHE_COHERENCY)
      printf(" (coherency invalidations: %lu)", L1_icache_coherency_invalidations);
    println();
  }

  printf("%s: --------------------------------------------------------------------------------\n", selfie_name);
}

void print_host_os() {
  if (OS == SELFIE)
    printf("selfie");
  else if (OS == LINUX)
    printf("Linux");
  else if (OS == MACOS)
    printf("macOS");
  else if (OS == WINDOWS)
    printf("Windows");
  else if (OS == BAREMETAL)
    printf("bare metal");
  else
    printf("unknown");
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------ MACHINE CONTEXTS -----------------------
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

  // allocate zeroed memory for general-purpose registers
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
  set_lowest_hi_page(context, get_page_of_virtual_address(HIGHESTVIRTUALADDRESS));
  set_highest_hi_page(context, get_lowest_hi_page(context));

  if (parent != MY_CONTEXT) {
    set_code_seg_start(context, load_virtual_memory(get_pt(parent), code_seg_start(vctxt)));
    set_code_seg_size(context, load_virtual_memory(get_pt(parent), code_seg_size(vctxt)));
    set_data_seg_start(context, load_virtual_memory(get_pt(parent), data_seg_start(vctxt)));
    set_data_seg_size(context, load_virtual_memory(get_pt(parent), data_seg_size(vctxt)));
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
    printf("%s: parent context 0x%08lX created child context 0x%08lX\n", selfie_name,
      (uint64_t) parent,
      (uint64_t) used_contexts);

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

  if (debug_map)
    printf("%s: page 0x%04lX mapped to frame 0x%08lX in context 0x%08lX\n", selfie_name,
      page, (uint64_t) frame, (uint64_t) context);
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

  flush_all_caches();
}

uint64_t is_code_address(uint64_t* context, uint64_t vaddr) {
  // is address in code segment?
  if (vaddr >= get_code_seg_start(context))
    if (vaddr < get_code_seg_start(context) + get_code_seg_size(context))
      return 1;

  return 0;
}

uint64_t is_data_address(uint64_t* context, uint64_t vaddr) {
  // is address in data segment?
  if (vaddr >= get_data_seg_start(context))
    if (vaddr < get_data_seg_start(context) + get_data_seg_size(context))
      return 1;

  return 0;
}

uint64_t is_stack_address(uint64_t* context, uint64_t vaddr) {
  // is address in stack segment?
  if (vaddr >= *(get_regs(context) + REG_SP))
    if (vaddr <= HIGHESTVIRTUALADDRESS)
      return 1;

  return 0;
}

uint64_t is_heap_address(uint64_t* context, uint64_t vaddr) {
  // is address in heap segment?
  if (vaddr >= get_heap_seg_start(context))
    if (vaddr < get_program_break(context))
      return 1;

  return 0;
}

uint64_t is_address_between_stack_and_heap(uint64_t* context, uint64_t vaddr) {
  // is address between heap and stack segments?
  if (vaddr >= get_program_break(context))
    if (vaddr < *(get_regs(context) + REG_SP))
      return 1;

  return 0;
}

uint64_t is_data_stack_heap_address(uint64_t* context, uint64_t vaddr) {
  if (is_data_address(context, vaddr))
    return 1;
  else if (is_stack_address(context, vaddr))
    return 1;
  else if (is_heap_address(context, vaddr))
    return 1;
  else
    return 0;
}

uint64_t is_valid_segment_read(uint64_t vaddr) {
  if (is_data_address(current_context, vaddr)) {
    data_reads = data_reads + 1;

    return 1;
  } else if (is_stack_address(current_context, vaddr)) {
    stack_reads = stack_reads + 1;

    return 1;
  } else if (is_heap_address(current_context, vaddr)) {
    heap_reads = heap_reads + 1;

    return 1;
  } else
    return 0;
}

uint64_t is_valid_segment_write(uint64_t vaddr) {
  if (is_data_address(current_context, vaddr)) {
    data_writes = data_writes + 1;

    return 1;
  } else if (is_stack_address(current_context, vaddr)) {
    stack_writes = stack_writes + 1;

    return 1;
  } else if (is_heap_address(current_context, vaddr)) {
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
  else if (allocated_page_frame_memory + MEGABYTE <=
            PHYSICALMEMORYEXCESS * PHYSICALMEMORYSIZE * SIZEOFUINT64 / WORDSIZE)
    // single word on 32-bit target occupies double word on 64-bit system
    return 1;
  else
    return 0;
}

uint64_t pused() {
  return allocated_page_frame_memory - free_page_frame_memory;
}

uint64_t* palloc() {
  uint64_t double_for_single_word;
  uint64_t block;
  uint64_t frame;

  // single word on 32-bit target occupies double word on 64-bit system
  double_for_single_word = SIZEOFUINT64 / WORDSIZE;

  // assert: PHYSICALMEMORYSIZE is equal to or a multiple of MEGABYTE
  // assert: PAGESIZE is a factor of MEGABYTE strictly less than MEGABYTE

  if (free_page_frame_memory == 0) {
    if (pavailable()) {
      free_page_frame_memory = MEGABYTE * double_for_single_word;

      // on boot level zero allocate zeroed memory
      block = (uint64_t) zmalloc(free_page_frame_memory);

      allocated_page_frame_memory = allocated_page_frame_memory + free_page_frame_memory;

      // page frames must be page-aligned to work as page table index
      next_page_frame = round_up(block, PAGESIZE * double_for_single_word);

      if (next_page_frame > block)
        // losing one page frame to fragmentation
        free_page_frame_memory = free_page_frame_memory - PAGESIZE * double_for_single_word;
    } else {
      printf("%s: palloc out of physical memory\n", selfie_name);

      exit(EXITCODE_OUTOFPHYSICALMEMORY);
    }
  }

  frame = next_page_frame;

  next_page_frame = next_page_frame + PAGESIZE * double_for_single_word;

  free_page_frame_memory = free_page_frame_memory - PAGESIZE * double_for_single_word;

  // strictly, touching is only necessary on boot levels higher than 0
  return touch((uint64_t*) frame, PAGESIZE * double_for_single_word);
}

void pfree(uint64_t* frame) {
  // TODO: implement free list of page frames
  frame = frame + 1;
}

void map_and_store(uint64_t* context, uint64_t vaddr, uint64_t data) {
  // assert: is_virtual_address_valid(vaddr, WORDSIZE) == 1

  if (is_virtual_address_mapped(get_pt(context), vaddr) == 0)
    map_page(context, get_page_of_virtual_address(vaddr), (uint64_t) palloc());

  store_virtual_memory(get_pt(context), vaddr, data);
}

void up_load_binary(uint64_t* context) {
  uint64_t baddr;

  // assert: e_entry is multiple of PAGESIZE and INSTRUCTIONSIZE

  set_pc(context, e_entry);

  // setting up page table cache

  set_lowest_lo_page(context, get_page_of_virtual_address(code_start));
  set_highest_lo_page(context, get_lowest_lo_page(context));

  // setting up memory segments

  set_code_seg_start(context, code_start);
  set_code_seg_size(context, code_size);
  set_data_seg_start(context, data_start);
  set_data_seg_size(context, data_size);
  set_heap_seg_start(context, round_up(data_start + data_size, p_align));
  set_program_break(context, get_heap_seg_start(context));

  baddr = 0;

  while (baddr < code_size) {
    map_and_store(context, get_code_seg_start(context) + baddr, load_code(baddr));

    baddr = baddr + WORDSIZE;
  }

  baddr = 0;

  while (baddr < data_size) {
    map_and_store(context, get_data_seg_start(context) + baddr, load_data(baddr));

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
    map_and_store(context, SP + i, load_word((uint64_t*) s, i, 1));

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
  SP = VIRTUALMEMORYSIZE * GIGABYTE;

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
    printf("%s: unknown system call %lu\n", selfie_name, a7);

    set_exit_code(context, EXITCODE_UNKNOWNSYSCALL);

    return EXIT;
  }

  return DONOTEXIT;
}

uint64_t handle_page_fault(uint64_t* context) {
  uint64_t page;

  page = get_fault(context);

  if (pavailable()) {
    set_exception(context, EXCEPTION_NOEXCEPTION);

    // TODO: reuse frames
    map_page(context, page, (uint64_t) palloc());

    if (is_heap_address(context, get_virtual_address_of_page_start(page)))
      mc_mapped_heap = mc_mapped_heap + PAGESIZE;

    return DONOTEXIT;
  } else {
    printf("%s: page fault at 0x%lX out of physical memory\n", selfie_name, page);

    set_exit_code(context, EXITCODE_OUTOFPHYSICALMEMORY);

    return EXIT;
  }
}

uint64_t handle_division_by_zero(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  if (record) {
    printf("%s: division by zero, replaying...\n", selfie_name);

    replay_trace();

    set_exit_code(context, EXITCODE_NOERROR);
  } else {
    printf("%s: division by zero\n", selfie_name);

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
    printf("%s: context %s threw uncaught exception: ", selfie_name, get_name(context));
    print_exception(exception, get_fault(context));
    println();

    set_exit_code(context, EXITCODE_UNCAUGHTEXCEPTION);

    return EXIT;
  }
}

uint64_t mipster(uint64_t* to_context) {
  uint64_t timeout;
  uint64_t* from_context;

  printf("mipster\n");
  printf("%s: >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n", selfie_name);

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

  printf("hypster\n");
  printf("%s: >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n", selfie_name);

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

  printf("mixter (%lu%% mipster/%lu%% hypster)\n", mix, 100 - mix);
  printf("%s: >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n", selfie_name);

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
        printf("%s: context %s threw uncaught exception: ", selfie_name, get_name(from_context));
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

  // allowing more palloc for caching tree page tables
  PHYSICALMEMORYEXCESS = PHYSICALMEMORYEXCESS + 1;
}

uint64_t minster(uint64_t* to_context) {
  printf("minster\n");
  printf("%s: >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n", selfie_name);

  // virtual is like physical memory in initial context up to memory size
  // by mapping unmapped pages (for the heap) to all available page frames
  // CAUTION: consumes memory even when not accessed
  map_unmapped_pages(to_context);

  // does not handle page faults, works only until running out of mapped pages
  return minmob(to_context);
}

uint64_t mobster(uint64_t* to_context) {
  printf("mobster\n");
  printf("%s: >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n", selfie_name);

  // does not handle page faults, relies on fancy hypsters to do that
  return minmob(to_context);
}

char* replace_extension(char* filename, char* extension) {
  char* s;
  uint64_t i;
  uint64_t c;
  char* filename_without_extension;

  // assert: string_length(filename) + 1 + string_length(extension) < MAX_FILENAME_LENGTH

  s = string_alloc(string_length(filename) + 1 + string_length(extension));

  // start reading at end of filename
  i = string_length(filename);

  c = 0;

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

  if (i == 0)
    // filename has no extension
    filename_without_extension = filename;
  else {
    filename_without_extension = string_alloc(i);

    // assert: filename_without_extension is zeroed and thus null-terminated

    // copy filename without extension and null-terminator into filename_without_extension
    while (i > 0) {
      i = i - 1;

      store_character(filename_without_extension, i, load_character(filename, i));
    }
  }

  // writing filename_without_extension plus extension into s
  sprintf(s, "%s.%s", filename_without_extension, extension);

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

  if (code_size == 0) {
    printf("%s: nothing to run, debug, or host\n", selfie_name);

    return EXITCODE_BADARGUMENTS;
  } else if (machine == HYPSTER) {
    if (OS != SELFIE) {
      printf("%s: hypster only runs on mipster\n", selfie_name);

      return EXITCODE_BADARGUMENTS;
    }
  }

  if (machine == CAPSTER) {
    init_all_caches();

    L1_CACHE_ENABLED = 1;

    machine = MIPSTER;
  }

  reset_interpreter();
  reset_profiler();
  reset_microkernel();

  init_memory(atoi(peek_argument(0)));

  current_context = create_context(MY_CONTEXT, 0);

  // assert: number_of_remaining_arguments() > 0

  boot_loader(current_context);

  // current_context is ready to run

  run = 1;

  printf("%s: selfie executing %lu-bit RISC-U binary %s with %luMB physical memory", selfie_name,
    WORDSIZEINBITS,
    binary_name,
    PHYSICALMEMORYSIZE / MEGABYTE);

  if (GC_ON) {
    gc_init(current_context);

    printf(", gcing every %lu mallocs, ", GC_PERIOD);
    if (GC_REUSE) printf("reusing memory"); else printf("not reusing memory");
  }

  if (machine == DIPSTER) {
    debug          = 1;
    debug_syscalls = 1;
    printf(", debugger");
    machine = MIPSTER;
  } else if (machine == RIPSTER) {
    debug  = 1;
    record = 1;
    init_replay_engine();
    printf(", replay");
    machine = MIPSTER;
  }

  printf(" on %lu-bit ", SIZEOFUINT64INBITS);

  if (machine == MIPSTER)
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

  record = 0;

  debug_syscalls = 0;
  debug          = 0;

  printf("%s: selfie terminating %lu-bit RISC-U binary %s with exit code %ld\n", selfie_name,
    WORDSIZEINBITS,
    get_name(current_context),
    sign_extend(exit_code, SYSCALL_BITWIDTH));

  if (machine != HYPSTER)
    print_profile(current_context);
  else if (GC_ON) {
    printf("%s: --------------------------------------------------------------------------------\n", selfie_name);
    print_gc_profile(current_context);
  }

  run = 0;

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
  printf("synopsis: %s { -c { source } | -o binary | ( -s | -S ) assembly | -l binary }%s\n", selfie_name, extras);
}

// -----------------------------------------------------------------
// ----------------------------- SELFIE ----------------------------
// -----------------------------------------------------------------

uint64_t selfie(uint64_t extras) {
  if (number_of_remaining_arguments() == 0)
    return EXITCODE_NOARGUMENTS;
  else {
    printf("%s: this is the selfie system from %s with\n", selfie_name, SELFIE_URL);
    printf("%s: %lu-bit unsigned integers and %lu-bit pointers hosted on ", selfie_name,
      SIZEOFUINT64INBITS,
      SIZEOFUINT64STARINBITS);
    print_host_os();
    println();

    init_scanner();
    init_bootstrapping();

    init_register();
    init_interpreter();

    init_disassembler();

    while (number_of_remaining_arguments() > 0) {
      get_argument();

      experimental_features();

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
        else if (string_compare(argument, "-L1"))
          return selfie_run(CAPSTER);
        else
          return EXITCODE_BADARGUMENTS;
      } else
        return EXITCODE_MOREARGUMENTS;
    }

    return EXITCODE_NOERROR;
  }
}

void experimental_features() {
  if (string_compare(argument, "-m32")) {
    IS64BITTARGET = 0;

    init_target();
    reset_disassembler();
    reset_binary();

    get_argument();
  } else if (string_compare(argument, "-m64")) {
    IS64BITTARGET = 1;

    init_target();
    reset_disassembler();
    reset_binary();

    get_argument();
  } else if (string_compare(argument, "-gc")) {
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
  init_target();

  exit_code = selfie(0);

  return exit_selfie(exit_code, " [ ( -m | -d | -r | -y ) 0-4096 ... ]");
}