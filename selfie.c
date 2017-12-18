// Copyright (c) 2015-2017, the Selfie Project authors. All rights reserved.
// Please see the AUTHORS file for details. Use of this source code is
// governed by a BSD license that can be found in the LICENSE file.
//
// Selfie is a project of the Computational Systems Group at the
// Department of Computer Sciences of the University of Salzburg
// in Austria. For further information and code please refer to:
//
// http://selfie.cs.uni-salzburg.at
//
// The Selfie Project provides an educational platform for teaching
// undergraduate and graduate students the design and implementation
// of programming languages and runtime systems. The focus is on the
// construction of compilers, libraries, operating systems, and even
// virtual machine monitors. The common theme is to identify and
// resolve self-reference in systems code which is seen as the key
// challenge when teaching systems engineering, hence the name.
//
// Selfie is a fully self-referential 7k-line C implementation of:
//
// 1. a self-compiling compiler called starc that compiles
//    a tiny but powerful subset of C called C Star (C*) to
//    a tiny but powerful subset of MIPS64 called MIPSter,
// 2. a self-executing emulator called mipster that executes
//    MIPSter code including itself when compiled with starc,
// 3. a self-hosting hypervisor called hypster which is based on
//    a tiny microkernel implemented in mipster and provides
//    MIPSter virtual machines that can host all of selfie,
//    that is, starc, mipster, and hypster itself, and
// 4. a tiny C* library called libcstar utilized by selfie.
//
// Selfie is kept minimal for simplicity and implemented in a single file.
// There is a simple linker, disassembler, profiler, and debugger as well as
// minimal operating system support in the form of MIPS64 o64 system calls
// built into the emulator.
//
// C* is a tiny Turing-complete subset of C that includes dereferencing
// (the * operator) but excludes composite data types, bitwise and Boolean
// operators, and many other features. There are only unsigned 64-bit
// integers and 64-bit pointers as well as character and string literals.
// This choice turns out to be helpful for students to understand the
// true role of composite data types such as arrays and records.
// Bitwise operations are implemented in libcstar using unsigned integer
// arithmetics helping students better understand arithmetic operators.
// C* is supposed to be close to the minimum necessary for implementing
// a self-compiling, single-pass, recursive-descent compiler. C* can be
// taught in around two weeks of classes depending on student background.
//
// The compiler can readily be extended to compile features missing in C*
// and to improve performance of the generated code. The compiler generates
// MIPSter executables that can directly be executed by the emulator or
// written to a file in a simple, custom-defined format. Support of standard
// MIPS64 ELF binaries should be easy but remains future work.
//
// MIPSter is a tiny Turing-complete subset of the MIPS64 instruction set.
// It only features arithmetic, memory, and control-flow instructions but
// neither bitwise nor byte-level instructions. MIPSter can be properly
// explained in a single week of classes.
//
// The emulator implements minimal operating system support that is meant
// to be extended by students, first as part of the emulator, and then
// ported to run on top of it, similar to an actual operating system or
// virtual machine monitor. The fact that the emulator can execute itself
// helps exposing the self-referential nature of that challenge. In fact,
// selfie goes one step further by implementing microkernel functionality
// as part of the emulator and a hypervisor that can run as part of the
// emulator as well as on top of it, all with the same code.
//
// Selfie is the result of many years of teaching systems engineering.
// The design of the compiler is inspired by the Oberon compiler of
// Professor Niklaus Wirth from ETH Zurich. The design of the selfie
// microkernel is inspired by microkernels of Professor Jochen Liedtke
// from University of Karlsruhe.

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     L I B R A R Y     ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------- BUILTIN PROCEDURES ----------------------
// -----------------------------------------------------------------

void      exit(uint64_t code);
uint64_t  read(uint64_t fd, uint64_t* buffer, uint64_t bytesToRead);
uint64_t  write(uint64_t fd, uint64_t* buffer, uint64_t bytesToWrite);
uint64_t  open(uint64_t* filename, uint64_t flags, uint64_t mode);
uint64_t* malloc(uint64_t size);

// -----------------------------------------------------------------
// ----------------------- LIBRARY PROCEDURES ----------------------
// -----------------------------------------------------------------

void initLibrary();
void resetLibrary();

uint64_t twoToThePowerOf(uint64_t p);
uint64_t leftShift(uint64_t n, uint64_t b);
uint64_t rightShift(uint64_t n, uint64_t b);
uint64_t signedLessThan(uint64_t lhs, uint64_t rhs);
uint64_t signedGreaterThan(uint64_t lhs, uint64_t rhs);

uint64_t signShrink(uint64_t immediate, uint64_t bits);

uint64_t getHighWord(uint64_t doubleWord);
uint64_t getLowWord(uint64_t doubleWord);

uint64_t  loadCharacter(uint64_t* s, uint64_t i);
uint64_t* storeCharacter(uint64_t* s, uint64_t i, uint64_t c);

uint64_t stringLength(uint64_t* s);
void     stringReverse(uint64_t* s);
uint64_t stringCompare(uint64_t* s, uint64_t* t);

uint64_t  atoi(uint64_t* s);
uint64_t* itoa(uint64_t n, uint64_t* s, uint64_t b, uint64_t a, uint64_t p);

uint64_t fixedPointRatio(uint64_t a, uint64_t b);

void putCharacter(uint64_t c);

void print(uint64_t* s);
void println();

void printCharacter(uint64_t c);
void printString(uint64_t* s);
void printInteger(uint64_t n);
void printFixedPointPercentage(uint64_t a, uint64_t b);
void printFixedPointRatio(uint64_t a, uint64_t b);
void printHexadecimal(uint64_t n, uint64_t a);
void printOctal(uint64_t n, uint64_t a);
void printBinary(uint64_t n, uint64_t a);

uint64_t roundUp(uint64_t n, uint64_t m);

uint64_t* smalloc(uint64_t size);
uint64_t* zalloc(uint64_t size);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t CHAR_EOF          =  -1; // end of file
uint64_t CHAR_TAB          =   9; // ASCII code 9  = tabulator
uint64_t CHAR_LF           =  10; // ASCII code 10 = line feed
uint64_t CHAR_CR           =  13; // ASCII code 13 = carriage return
uint64_t CHAR_SPACE        = ' ';
uint64_t CHAR_SEMICOLON    = ';';
uint64_t CHAR_PLUS         = '+';
uint64_t CHAR_DASH         = '-';
uint64_t CHAR_ASTERISK     = '*';
uint64_t CHAR_SLASH        = '/';
uint64_t CHAR_UNDERSCORE   = '_';
uint64_t CHAR_EQUAL        = '=';
uint64_t CHAR_LPARENTHESIS = '(';
uint64_t CHAR_RPARENTHESIS = ')';
uint64_t CHAR_LBRACE       = '{';
uint64_t CHAR_RBRACE       = '}';
uint64_t CHAR_COMMA        = ',';
uint64_t CHAR_LT           = '<';
uint64_t CHAR_GT           = '>';
uint64_t CHAR_EXCLAMATION  = '!';
uint64_t CHAR_PERCENTAGE   = '%';
uint64_t CHAR_SINGLEQUOTE  =  39; // ASCII code 39 = '
uint64_t CHAR_DOUBLEQUOTE  = '"';

uint64_t CPUBITWIDTH = 64;

uint64_t SIZEOFUINT64     = 8; // must be the same as REGISTERSIZE
uint64_t SIZEOFUINT64STAR = 8; // must be the same as REGISTERSIZE

uint64_t* power_of_two_table;

uint64_t INT64_MAX; // maximum numerical value of a signed 64-bit integer
uint64_t INT64_MIN; // minimum numerical value of a signed 64-bit integer

uint64_t INT_BITWIDTH = 32; // int bit width used for system call compatibility

uint64_t maxFilenameLength = 128;

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

uint64_t numberOfWrittenCharacters = 0;

uint64_t* outputName = (uint64_t*) 0;
uint64_t  outputFD   = 1;

// ------------------------- INITIALIZATION ------------------------

void initLibrary() {
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

  // compute two's complement boundaries
  INT64_MAX = twoToThePowerOf(CPUBITWIDTH - 1) - 1;
  INT64_MIN = INT64_MAX + 1;

  // allocate and touch to make sure memory is mapped for read calls
  character_buffer  = smalloc(SIZEOFUINT64);
  *character_buffer = 0;

  // accommodate at least CPUBITWIDTH numbers for itoa, no mapping needed
  integer_buffer = smalloc(CPUBITWIDTH + 1);

  // does not need to be mapped
  filename_buffer = smalloc(maxFilenameLength);

  // allocate and touch to make sure memory is mapped for read calls
  binary_buffer  = smalloc(SIZEOFUINT64);
  *binary_buffer = 0;
}

void resetLibrary() {
  numberOfWrittenCharacters = 0;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------    C O M P I L E R    ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- SCANNER ----------------------------
// -----------------------------------------------------------------

void initScanner();
void resetScanner();

void printSymbol(uint64_t symbol);
void printLineNumber(uint64_t* message, uint64_t line);

void syntaxErrorMessage(uint64_t* message);
void syntaxErrorCharacter(uint64_t character);
void syntaxErrorIdentifier(uint64_t* expected);

void getCharacter();

uint64_t isCharacterNewLine();
uint64_t isCharacterWhitespace();

uint64_t findNextCharacter();

uint64_t isCharacterLetter();
uint64_t isCharacterDigit();
uint64_t isCharacterLetterOrDigitOrUnderscore();
uint64_t isCharacterNotDoubleQuoteOrNewLineOrEOF();

uint64_t identifierStringMatch(uint64_t stringIndex);
uint64_t identifierOrKeyword();

void getSymbol();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t SYM_EOF          = -1; // end of file
uint64_t SYM_IDENTIFIER   = 0;  // identifier
uint64_t SYM_INTEGER      = 1;  // integer
uint64_t SYM_VOID         = 2;  // void
uint64_t SYM_UINT64       = 3;  // uint64_t
uint64_t SYM_SEMICOLON    = 4;  // ;
uint64_t SYM_IF           = 5;  // if
uint64_t SYM_ELSE         = 6;  // else
uint64_t SYM_PLUS         = 7;  // +
uint64_t SYM_MINUS        = 8;  // -
uint64_t SYM_ASTERISK     = 9;  // *
uint64_t SYM_DIV          = 10; // /
uint64_t SYM_EQUALITY     = 11; // ==
uint64_t SYM_ASSIGN       = 12; // =
uint64_t SYM_LPARENTHESIS = 13; // (
uint64_t SYM_RPARENTHESIS = 14; // )
uint64_t SYM_LBRACE       = 15; // {
uint64_t SYM_RBRACE       = 16; // }
uint64_t SYM_WHILE        = 17; // while
uint64_t SYM_RETURN       = 18; // return
uint64_t SYM_COMMA        = 19; // ,
uint64_t SYM_LT           = 20; // <
uint64_t SYM_LEQ          = 21; // <=
uint64_t SYM_GT           = 22; // >
uint64_t SYM_GEQ          = 23; // >=
uint64_t SYM_NOTEQ        = 24; // !=
uint64_t SYM_MOD          = 25; // %
uint64_t SYM_CHARACTER    = 26; // character
uint64_t SYM_STRING       = 27; // string

uint64_t* SYMBOLS; // strings representing symbols

uint64_t maxIdentifierLength = 64;  // maximum number of characters in an identifier
uint64_t maxIntegerLength    = 19;  // maximum number of characters in an integer
uint64_t maxStringLength     = 128; // maximum number of characters in a string

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t lineNumber = 1; // current line number for error reporting

uint64_t* identifier = (uint64_t*) 0; // stores scanned identifier as string
uint64_t* integer    = (uint64_t*) 0; // stores scanned integer as string
uint64_t* string     = (uint64_t*) 0; // stores scanned string

uint64_t literal = 0; // stores numerical value of scanned integer or character

uint64_t mayBeINTMIN = 0; // allow INT64_MIN if '-' was scanned before

uint64_t character; // most recently read character

uint64_t numberOfReadCharacters = 0;

uint64_t symbol; // most recently recognized symbol

uint64_t numberOfIgnoredCharacters = 0;
uint64_t numberOfComments          = 0;
uint64_t numberOfScannedSymbols    = 0;

uint64_t* sourceName = (uint64_t*) 0; // name of source file
uint64_t  sourceFD   = 0;             // file descriptor of open source file

// ------------------------- INITIALIZATION ------------------------

void initScanner () {
  SYMBOLS = smalloc((SYM_STRING + 1) * SIZEOFUINT64STAR);

  *(SYMBOLS + SYM_IDENTIFIER)   = (uint64_t) "identifier";
  *(SYMBOLS + SYM_INTEGER)      = (uint64_t) "integer";
  *(SYMBOLS + SYM_VOID)         = (uint64_t) "void";
  *(SYMBOLS + SYM_UINT64)       = (uint64_t) "uint64_t";
  *(SYMBOLS + SYM_SEMICOLON)    = (uint64_t) ";";
  *(SYMBOLS + SYM_IF)           = (uint64_t) "if";
  *(SYMBOLS + SYM_ELSE)         = (uint64_t) "else";
  *(SYMBOLS + SYM_PLUS)         = (uint64_t) "+";
  *(SYMBOLS + SYM_MINUS)        = (uint64_t) "-";
  *(SYMBOLS + SYM_ASTERISK)     = (uint64_t) "*";
  *(SYMBOLS + SYM_DIV)          = (uint64_t) "/";
  *(SYMBOLS + SYM_EQUALITY)     = (uint64_t) "==";
  *(SYMBOLS + SYM_ASSIGN)       = (uint64_t) "=";
  *(SYMBOLS + SYM_LPARENTHESIS) = (uint64_t) "(";
  *(SYMBOLS + SYM_RPARENTHESIS) = (uint64_t) ")";
  *(SYMBOLS + SYM_LBRACE)       = (uint64_t) "{";
  *(SYMBOLS + SYM_RBRACE)       = (uint64_t) "}";
  *(SYMBOLS + SYM_WHILE)        = (uint64_t) "while";
  *(SYMBOLS + SYM_RETURN)       = (uint64_t) "return";
  *(SYMBOLS + SYM_COMMA)        = (uint64_t) ",";
  *(SYMBOLS + SYM_LT)           = (uint64_t) "<";
  *(SYMBOLS + SYM_LEQ)          = (uint64_t) "<=";
  *(SYMBOLS + SYM_GT)           = (uint64_t) ">";
  *(SYMBOLS + SYM_GEQ)          = (uint64_t) ">=";
  *(SYMBOLS + SYM_NOTEQ)        = (uint64_t) "!=";
  *(SYMBOLS + SYM_MOD)          = (uint64_t) "%";
  *(SYMBOLS + SYM_CHARACTER)    = (uint64_t) "character";
  *(SYMBOLS + SYM_STRING)       = (uint64_t) "string";

  character = CHAR_EOF;
  symbol    = SYM_EOF;
}

void resetScanner() {
  lineNumber = 1;

  numberOfReadCharacters = 0;

  getCharacter();

  numberOfIgnoredCharacters = 0;
  numberOfComments          = 0;
  numberOfScannedSymbols    = 0;
}

// -----------------------------------------------------------------
// ------------------------- SYMBOL TABLE --------------------------
// -----------------------------------------------------------------

void resetSymbolTables();

void createSymbolTableEntry(uint64_t which, uint64_t* string, uint64_t line, uint64_t class, uint64_t type, uint64_t value, uint64_t address);

uint64_t* searchSymbolTable(uint64_t* entry, uint64_t* string, uint64_t class);
uint64_t* getScopedSymbolTableEntry(uint64_t* string, uint64_t class);

uint64_t isUndefinedProcedure(uint64_t* entry);
uint64_t reportUndefinedProcedures();

// symbol table entry:
// +----+---------+
// |  0 | next    | pointer to next entry
// |  1 | string  | identifier string, string literal
// |  2 | line#   | source line number
// |  3 | class   | VARIABLE, PROCEDURE, STRING
// |  4 | type    | UINT64_T, UINT64STAR_T, VOID_T
// |  5 | value   | VARIABLE: initial value
// |  6 | address | VARIABLE: offset, PROCEDURE: address, STRING: offset
// |  7 | scope   | REG_GP, REG_FP
// +----+---------+

uint64_t* getNextEntry(uint64_t* entry)  { return (uint64_t*) *entry; }
uint64_t* getString(uint64_t* entry)     { return (uint64_t*) *(entry + 1); }
uint64_t  getLineNumber(uint64_t* entry) { return        *(entry + 2); }
uint64_t  getClass(uint64_t* entry)      { return        *(entry + 3); }
uint64_t  getType(uint64_t* entry)       { return        *(entry + 4); }
uint64_t  getValue(uint64_t* entry)      { return        *(entry + 5); }
uint64_t  getAddress(uint64_t* entry)    { return        *(entry + 6); }
uint64_t  getScope(uint64_t* entry)      { return        *(entry + 7); }

void setNextEntry(uint64_t* entry, uint64_t* next)    { *entry       = (uint64_t) next; }
void setString(uint64_t* entry, uint64_t* identifier) { *(entry + 1) = (uint64_t) identifier; }
void setLineNumber(uint64_t* entry, uint64_t line)    { *(entry + 2) = line; }
void setClass(uint64_t* entry, uint64_t class)        { *(entry + 3) = class; }
void setType(uint64_t* entry, uint64_t type)          { *(entry + 4) = type; }
void setValue(uint64_t* entry, uint64_t value)        { *(entry + 5) = value; }
void setAddress(uint64_t* entry, uint64_t address)    { *(entry + 6) = address; }
void setScope(uint64_t* entry, uint64_t scope)        { *(entry + 7) = scope; }

// ------------------------ GLOBAL CONSTANTS -----------------------

// classes
uint64_t VARIABLE  = 1;
uint64_t PROCEDURE = 2;
uint64_t STRING    = 3;

// types
uint64_t UINT64_T     = 1;
uint64_t UINT64STAR_T = 2;
uint64_t VOID_T       = 3;

// symbol tables
uint64_t GLOBAL_TABLE  = 1;
uint64_t LOCAL_TABLE   = 2;
uint64_t LIBRARY_TABLE = 3;

// ------------------------ GLOBAL VARIABLES -----------------------

// table pointers
uint64_t* global_symbol_table  = (uint64_t*) 0;
uint64_t* local_symbol_table   = (uint64_t*) 0;
uint64_t* library_symbol_table = (uint64_t*) 0;

uint64_t numberOfGlobalVariables = 0;
uint64_t numberOfProcedures      = 0;
uint64_t numberOfStrings         = 0;

// ------------------------- INITIALIZATION ------------------------

void resetSymbolTables() {
  global_symbol_table  = (uint64_t*) 0;
  local_symbol_table   = (uint64_t*) 0;
  library_symbol_table = (uint64_t*) 0;

  numberOfGlobalVariables = 0;
  numberOfProcedures      = 0;
  numberOfStrings         = 0;
}

// -----------------------------------------------------------------
// ---------------------------- PARSER -----------------------------
// -----------------------------------------------------------------

void resetParser();

uint64_t isNotRbraceOrEOF();
uint64_t isExpression();
uint64_t isLiteral();
uint64_t isStarOrDivOrModulo();
uint64_t isPlusOrMinus();
uint64_t isComparison();

uint64_t lookForFactor();
uint64_t lookForStatement();
uint64_t lookForType();

void save_temporaries();
void restore_temporaries(uint64_t numberOfTemporaries);

void syntaxErrorSymbol(uint64_t expected);
void syntaxErrorUnexpected();
void printType(uint64_t type);
void typeWarning(uint64_t expected, uint64_t found);

uint64_t* getVariable(uint64_t* variable);
uint64_t  load_variable(uint64_t* variable);
void      load_integer(uint64_t value);
void      load_string(uint64_t* string);

uint64_t help_call_codegen(uint64_t* entry, uint64_t* procedure);
void     help_procedure_prologue(uint64_t localVariables);
void     help_procedure_epilogue(uint64_t parameters);

uint64_t gr_call(uint64_t* procedure);
uint64_t gr_factor();
uint64_t gr_term();
uint64_t gr_simpleExpression();
uint64_t gr_expression();
void     gr_while();
void     gr_if();
void     gr_return();
void     gr_statement();
uint64_t gr_type();
void     gr_variable(uint64_t offset);
uint64_t gr_initialization(uint64_t type);
void     gr_procedure(uint64_t* procedure, uint64_t type);
void     gr_cstar();

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t allocatedTemporaries = 0; // number of allocated temporaries

uint64_t allocatedMemory = 0; // number of bytes for global variables and strings

uint64_t returnBranches = 0; // fixup chain for return statements

uint64_t returnType = 0; // return type of currently parsed procedure

uint64_t mainJump = 0; // address where JAL instruction to main procedure is

uint64_t numberOfCalls       = 0;
uint64_t numberOfAssignments = 0;
uint64_t numberOfWhile       = 0;
uint64_t numberOfIf          = 0;
uint64_t numberOfReturn      = 0;

// ------------------------- INITIALIZATION ------------------------

void resetParser() {
  numberOfCalls       = 0;
  numberOfAssignments = 0;
  numberOfWhile       = 0;
  numberOfIf          = 0;
  numberOfReturn      = 0;

  getSymbol();
}

// -----------------------------------------------------------------
// ---------------------- MACHINE CODE LIBRARY ---------------------
// -----------------------------------------------------------------

void emitLeftShiftBy(uint64_t reg, uint64_t b);
void emitMainEntry();
void bootstrapCode();

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

void initRegister();

void printRegister(uint64_t reg);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t NUMBEROFREGISTERS = 32;

uint64_t REG_ZR = 0;
uint64_t REG_AT = 1;
uint64_t REG_V0 = 2;
uint64_t REG_V1 = 3;
uint64_t REG_A0 = 4;
uint64_t REG_A1 = 5;
uint64_t REG_A2 = 6;
uint64_t REG_A3 = 7;
uint64_t REG_T0 = 8;
uint64_t REG_T1 = 9;
uint64_t REG_T2 = 10;
uint64_t REG_T3 = 11;
uint64_t REG_T4 = 12;
uint64_t REG_T5 = 13;
uint64_t REG_T6 = 14;
uint64_t REG_T7 = 15;
uint64_t REG_S0 = 16;
uint64_t REG_S1 = 17;
uint64_t REG_S2 = 18;
uint64_t REG_S3 = 19;
uint64_t REG_S4 = 20;
uint64_t REG_S5 = 21;
uint64_t REG_S6 = 22;
uint64_t REG_S7 = 23;
uint64_t REG_T8 = 24;
uint64_t REG_T9 = 25;
uint64_t REG_K0 = 26;
uint64_t REG_K1 = 27;
uint64_t REG_GP = 28;
uint64_t REG_SP = 29;
uint64_t REG_FP = 30;
uint64_t REG_RA = 31;

uint64_t* REGISTERS; // strings representing registers

// ------------------------- INITIALIZATION ------------------------

void initRegister() {
  REGISTERS = smalloc(NUMBEROFREGISTERS * SIZEOFUINT64STAR);

  *(REGISTERS + REG_ZR) = (uint64_t) "$zero";
  *(REGISTERS + REG_AT) = (uint64_t) "$at";
  *(REGISTERS + REG_V0) = (uint64_t) "$v0";
  *(REGISTERS + REG_V1) = (uint64_t) "$v1";
  *(REGISTERS + REG_A0) = (uint64_t) "$a0";
  *(REGISTERS + REG_A1) = (uint64_t) "$a1";
  *(REGISTERS + REG_A2) = (uint64_t) "$a2";
  *(REGISTERS + REG_A3) = (uint64_t) "$a3";
  *(REGISTERS + REG_T0) = (uint64_t) "$t0";
  *(REGISTERS + REG_T1) = (uint64_t) "$t1";
  *(REGISTERS + REG_T2) = (uint64_t) "$t2";
  *(REGISTERS + REG_T3) = (uint64_t) "$t3";
  *(REGISTERS + REG_T4) = (uint64_t) "$t4";
  *(REGISTERS + REG_T5) = (uint64_t) "$t5";
  *(REGISTERS + REG_T6) = (uint64_t) "$t6";
  *(REGISTERS + REG_T7) = (uint64_t) "$t7";
  *(REGISTERS + REG_S0) = (uint64_t) "$s0";
  *(REGISTERS + REG_S1) = (uint64_t) "$s1";
  *(REGISTERS + REG_S2) = (uint64_t) "$s2";
  *(REGISTERS + REG_S3) = (uint64_t) "$s3";
  *(REGISTERS + REG_S4) = (uint64_t) "$s4";
  *(REGISTERS + REG_S5) = (uint64_t) "$s5";
  *(REGISTERS + REG_S6) = (uint64_t) "$s6";
  *(REGISTERS + REG_S7) = (uint64_t) "$s7";
  *(REGISTERS + REG_T8) = (uint64_t) "$t8";
  *(REGISTERS + REG_T9) = (uint64_t) "$t9";
  *(REGISTERS + REG_K0) = (uint64_t) "$k0";
  *(REGISTERS + REG_K1) = (uint64_t) "$k1";
  *(REGISTERS + REG_GP) = (uint64_t) "$gp";
  *(REGISTERS + REG_SP) = (uint64_t) "$sp";
  *(REGISTERS + REG_FP) = (uint64_t) "$fp";
  *(REGISTERS + REG_RA) = (uint64_t) "$ra";
}

// -----------------------------------------------------------------
// ---------------------------- ENCODER ----------------------------
// -----------------------------------------------------------------

uint64_t encodeRFormat(uint64_t opcode, uint64_t rs, uint64_t rt, uint64_t rd, uint64_t function);
uint64_t encodeIFormat(uint64_t opcode, uint64_t rs, uint64_t rt, uint64_t immediate);
uint64_t encodeJFormat(uint64_t opcode, uint64_t instr_index);

// -----------------------------------------------------------------
// ---------------------------- DECODER ----------------------------
// -----------------------------------------------------------------

void initDecoder();

uint64_t getOpcode(uint64_t instruction);
uint64_t getRS(uint64_t instruction);
uint64_t getRT(uint64_t instruction);
uint64_t getRD(uint64_t instruction);
uint64_t getFunction(uint64_t instruction);
uint64_t getImmediate(uint64_t instruction);
uint64_t getInstrIndex(uint64_t instruction);
uint64_t signExtend(uint64_t immediate, uint64_t bits);

void decodeRFormat();
void decodeIFormat();
void decodeJFormat();

void decode();

void printOpcode(uint64_t opcode);
void printFunction(uint64_t function);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t OP_SPECIAL = 0;
uint64_t OP_J       = 2;
uint64_t OP_JAL     = 3;
uint64_t OP_BEQ     = 4;
uint64_t OP_DADDIU  = 25;
uint64_t OP_LD      = 55;
uint64_t OP_SD      = 63;

uint64_t* OPCODES; // strings representing MIPS opcodes

uint64_t FCT_NOP     = 0;
uint64_t FCT_JR      = 8;
uint64_t FCT_SYSCALL = 12;
uint64_t FCT_MFHI    = 16;
uint64_t FCT_MFLO    = 18;
uint64_t FCT_DMULTU  = 29;
uint64_t FCT_DDIVU   = 31;
uint64_t FCT_SLTU    = 43;
uint64_t FCT_DADDU   = 45;
uint64_t FCT_DSUBU   = 47;

uint64_t* FUNCTIONS; // strings representing MIPS functions

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t opcode      = 0;
uint64_t rs          = 0;
uint64_t rt          = 0;
uint64_t rd          = 0;
uint64_t immediate   = 0;
uint64_t function    = 0;
uint64_t instr_index = 0;

// ------------------------- INITIALIZATION ------------------------

void initDecoder() {
  OPCODES = smalloc((OP_SD + 1) * SIZEOFUINT64STAR);

  *(OPCODES + OP_SPECIAL) = (uint64_t) "nop";
  *(OPCODES + OP_J)       = (uint64_t) "j";
  *(OPCODES + OP_JAL)     = (uint64_t) "jal";
  *(OPCODES + OP_BEQ)     = (uint64_t) "beq";
  *(OPCODES + OP_DADDIU)  = (uint64_t) "daddiu";
  *(OPCODES + OP_LD)      = (uint64_t) "ld";
  *(OPCODES + OP_SD)      = (uint64_t) "sd";

  FUNCTIONS = smalloc((FCT_DSUBU + 1) * SIZEOFUINT64STAR);

  *(FUNCTIONS + FCT_NOP)     = (uint64_t) "nop";
  *(FUNCTIONS + FCT_JR)      = (uint64_t) "jr";
  *(FUNCTIONS + FCT_SYSCALL) = (uint64_t) "syscall";
  *(FUNCTIONS + FCT_MFHI)    = (uint64_t) "mfhi";
  *(FUNCTIONS + FCT_MFLO)    = (uint64_t) "mflo";
  *(FUNCTIONS + FCT_DMULTU)  = (uint64_t) "dmultu";
  *(FUNCTIONS + FCT_DDIVU)   = (uint64_t) "ddivu";
  *(FUNCTIONS + FCT_SLTU)    = (uint64_t) "sltu";
  *(FUNCTIONS + FCT_DADDU)   = (uint64_t) "daddu";
  *(FUNCTIONS + FCT_DSUBU)   = (uint64_t) "dsubu";
}

// -----------------------------------------------------------------
// ----------------------------- CODE ------------------------------
// -----------------------------------------------------------------

uint64_t loadInstruction(uint64_t baddr);
void storeInstruction(uint64_t baddr, uint64_t instruction);

uint64_t loadData(uint64_t baddr);
void storeData(uint64_t baddr, uint64_t data);

void emitInstruction(uint64_t instruction);
void emitRFormat(uint64_t opcode, uint64_t rs, uint64_t rt, uint64_t rd, uint64_t function);
void emitIFormat(uint64_t opcode, uint64_t rs, uint64_t rt, uint64_t immediate);
void emitJFormat(uint64_t opcode, uint64_t instr_index);

void fixup_relative(uint64_t fromAddress);
void fixup_absolute(uint64_t fromAddress, uint64_t toAddress);
void fixlink_absolute(uint64_t fromAddress, uint64_t toAddress);

uint64_t copyStringToBinary(uint64_t* s, uint64_t a);

void emitGlobalsStrings();

uint64_t openWriteOnly(uint64_t* name);

void selfie_output();

uint64_t* touch(uint64_t* memory, uint64_t length);

void selfie_load();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t maxBinaryLength = 262144; // 256KB

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* binary = (uint64_t*) 0; // binary of emitted instructions

uint64_t binaryLength = 0; // length of binary in bytes incl. globals & strings

uint64_t codeLength = 0; // length of code portion of binary in bytes

uint64_t* binaryName = (uint64_t*) 0; // file name of binary

uint64_t* sourceLineNumber = (uint64_t*) 0; // source line number per emitted instruction

uint64_t* assemblyName = (uint64_t*) 0; // name of assembly file
uint64_t  assemblyFD   = 0;        // file descriptor of open assembly file

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emitExit();
void implementExit(uint64_t* context);

void emitRead();
void implementRead(uint64_t* context);

void emitWrite();
void implementWrite(uint64_t* context);

void     emitOpen();
uint64_t down_loadString(uint64_t* table, uint64_t vaddr, uint64_t* s);
void     implementOpen(uint64_t* context);

void     emitMalloc();
uint64_t implementMalloc(uint64_t* context);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t debug_read   = 0;
uint64_t debug_write  = 0;
uint64_t debug_open   = 0;

uint64_t debug_malloc = 0;

uint64_t SYSCALL_EXIT   = 4001;
uint64_t SYSCALL_READ   = 4003;
uint64_t SYSCALL_WRITE  = 4004;
uint64_t SYSCALL_OPEN   = 4005;

uint64_t SYSCALL_MALLOC = 4045;

// -----------------------------------------------------------------
// ----------------------- HYPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void      emitSwitch();
void      doSwitch(uint64_t* toContext, uint64_t timeout);
void      implementSwitch();
uint64_t* mipster_switch(uint64_t* toContext, uint64_t timeout);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t SYSCALL_SWITCH = 4901;

uint64_t debug_switch = 0;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void initMemory(uint64_t megabytes);

uint64_t loadPhysicalMemory(uint64_t* paddr);
void     storePhysicalMemory(uint64_t* paddr, uint64_t data);

uint64_t FrameForPage(uint64_t* table, uint64_t page);
uint64_t getFrameForPage(uint64_t* table, uint64_t page);
uint64_t isPageMapped(uint64_t* table, uint64_t page);

uint64_t isValidVirtualAddress(uint64_t vaddr);
uint64_t getPageOfVirtualAddress(uint64_t vaddr);
uint64_t isVirtualAddressMapped(uint64_t* table, uint64_t vaddr);

uint64_t* tlb(uint64_t* table, uint64_t vaddr);

uint64_t loadVirtualMemory(uint64_t* table, uint64_t vaddr);
void     storeVirtualMemory(uint64_t* table, uint64_t vaddr, uint64_t data);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t debug_tlb = 0;

uint64_t MEGABYTE = 1048576;

uint64_t VIRTUALMEMORYSIZE = 4294967296; // 4GB of virtual memory

uint64_t WORDSIZE = 4;
uint64_t DOUBLEWORDSIZE = 8;

uint64_t INSTRUCTIONSIZE = 4; // must be the same as WORDSIZE
uint64_t REGISTERSIZE = 8;    // must be the same as DOUBLEWORDSIZE

uint64_t PAGESIZE = 4096;  // we use standard 4KB pages (=> 12 pagebits: 2^12 == 4096)

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t pageFrameMemory = 0; // size of memory for frames

// ------------------------- INITIALIZATION ------------------------

void initMemory(uint64_t megabytes) {
  if (megabytes > 4096)
    megabytes = 4096;

  pageFrameMemory = megabytes * MEGABYTE;
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

void fct_nop();
void fct_daddu();
void fct_dsubu();
void fct_dmultu();
void fct_ddivu();
void fct_mfhi();
void fct_mflo();
void fct_sltu();
void fct_jr();
void fct_syscall();

void op_daddiu();
void op_ld();
void op_sd();
void op_beq();
void op_jal();
void op_j();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t debug_divisionByZero = 1;

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void initInterpreter();
void resetInterpreter();

void printException(uint64_t exception, uint64_t faultingPage);
void throwException(uint64_t exception, uint64_t faultingPage);

void fetch();
void execute();
void interrupt();

uint64_t* runUntilException();

uint64_t addressWithMaxCounter(uint64_t* counters, uint64_t max);

uint64_t printCounters(uint64_t total, uint64_t* counters, uint64_t max);
void     printProfile(uint64_t* message, uint64_t total, uint64_t* counters);

void selfie_disassemble();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t EXCEPTION_NOEXCEPTION        = 0;
uint64_t EXCEPTION_PAGEFAULT          = 1;
uint64_t EXCEPTION_SYSCALL            = 2;
uint64_t EXCEPTION_TIMER              = 3;
uint64_t EXCEPTION_INVALIDADDRESS     = 4;
uint64_t EXCEPTION_UNKNOWNINSTRUCTION = 5;

uint64_t* EXCEPTIONS; // strings representing exceptions

uint64_t debug_exception = 0;

// number of instructions from context switch to timer interrupt
// CAUTION: avoid interrupting any kernel activities, keep TIMESLICE large
// TODO: implement proper interrupt controller to turn interrupts on and off
uint64_t TIMESLICE = 10000000;

uint64_t TIMEROFF = -1;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t interpret = 0; // flag for executing or disassembling code

uint64_t debug = 0; // flag for logging code execution

// hardware thread state

uint64_t pc = 0; // program counter
uint64_t ir = 0; // instruction register

uint64_t* registers = (uint64_t*) 0; // general-purpose registers

uint64_t loReg = 0; // lo register for multiplication/division
uint64_t hiReg = 0; // hi register for multiplication/division

uint64_t* pt = (uint64_t*) 0; // page table

// core state

uint64_t timer = -1; // counter for timer interrupt

uint64_t trap = 0; // flag for creating a trap

uint64_t  calls           = 0;              // total number of executed procedure calls
uint64_t* callsPerAddress = (uint64_t*) 0;  // number of executed calls of each procedure

uint64_t  loops           = 0;              // total number of executed loop iterations
uint64_t* loopsPerAddress = (uint64_t*) 0;  // number of executed iterations of each loop

uint64_t  loads           = 0;              // total number of executed memory loads
uint64_t* loadsPerAddress = (uint64_t*) 0;  // number of executed loads per load operation

uint64_t  stores           = 0;             // total number of executed memory stores
uint64_t* storesPerAddress = (uint64_t*) 0; // number of executed stores per store operation

// ------------------------- INITIALIZATION ------------------------

void initInterpreter() {
  EXCEPTIONS = smalloc((EXCEPTION_UNKNOWNINSTRUCTION + 1) * SIZEOFUINT64STAR);

  *(EXCEPTIONS + EXCEPTION_NOEXCEPTION)        = (uint64_t) "no exception";
  *(EXCEPTIONS + EXCEPTION_PAGEFAULT)          = (uint64_t) "page fault";
  *(EXCEPTIONS + EXCEPTION_SYSCALL)            = (uint64_t) "syscall";
  *(EXCEPTIONS + EXCEPTION_TIMER)              = (uint64_t) "timer interrupt";
  *(EXCEPTIONS + EXCEPTION_INVALIDADDRESS)     = (uint64_t) "invalid address";
  *(EXCEPTIONS + EXCEPTION_UNKNOWNINSTRUCTION) = (uint64_t) "unknown instruction";
}

void resetInterpreter() {
  pc = 0;
  ir = 0;

  registers = (uint64_t*) 0;

  loReg = 0;
  hiReg = 0;

  pt = (uint64_t*) 0;

  trap = 0;

  timer = TIMEROFF;

  if (interpret) {
    calls           = 0;
    callsPerAddress = zalloc(maxBinaryLength / INSTRUCTIONSIZE * SIZEOFUINT64);

    loops           = 0;
    loopsPerAddress = zalloc(maxBinaryLength / INSTRUCTIONSIZE * SIZEOFUINT64);

    loads           = 0;
    loadsPerAddress = zalloc(maxBinaryLength / INSTRUCTIONSIZE * SIZEOFUINT64);

    stores           = 0;
    storesPerAddress = zalloc(maxBinaryLength / INSTRUCTIONSIZE * SIZEOFUINT64);
  }
}

// -----------------------------------------------------------------
// ---------------------------- CONTEXTS ---------------------------
// -----------------------------------------------------------------

uint64_t* allocateContext(uint64_t* parent, uint64_t* vctxt, uint64_t* in);

uint64_t* findContext(uint64_t* parent, uint64_t* vctxt, uint64_t* in);

void      freeContext(uint64_t* context);
uint64_t* deleteContext(uint64_t* context, uint64_t* from);

// context struct:
// +----+----------------+
// |  0 | nextContext    | pointer to next context
// |  1 | prevContext    | pointer to previous context
// |  2 | pc             | program counter
// |  3 | regs           | pointer to general purpose registers
// |  4 | loReg          | lo register
// |  5 | hiReg          | hi register
// |  6 | pt             | pointer to page table
// |  7 | loPage         | lowest low unmapped page
// |  8 | mePage         | highest low unmapped page
// |  9 | hiPage         | highest high unmapped page
// | 10 | brk            | break between code, data, and heap
// | 11 | exception      | exception ID
// | 12 | faultingPage   | faulting page
// | 13 | exitCode       | exit code
// | 14 | parent         | context that created this context
// | 15 | virtualContext | virtual context address
// | 16 | name           | binary name loaded into context
// +----+----------------+

uint64_t nextContext(uint64_t* context)    { return (uint64_t) context; }
uint64_t prevContext(uint64_t* context)    { return (uint64_t) (context + 1); }
uint64_t PC(uint64_t* context)             { return (uint64_t) (context + 2); }
uint64_t Regs(uint64_t* context)           { return (uint64_t) (context + 3); }
uint64_t LoReg(uint64_t* context)          { return (uint64_t) (context + 4); }
uint64_t HiReg(uint64_t* context)          { return (uint64_t) (context + 5); }
uint64_t PT(uint64_t* context)             { return (uint64_t) (context + 6); }
uint64_t LoPage(uint64_t* context)         { return (uint64_t) (context + 7); }
uint64_t MePage(uint64_t* context)         { return (uint64_t) (context + 8); }
uint64_t HiPage(uint64_t* context)         { return (uint64_t) (context + 9); }
uint64_t ProgramBreak(uint64_t* context)   { return (uint64_t) (context + 10); }
uint64_t Exception(uint64_t* context)      { return (uint64_t) (context + 11); }
uint64_t FaultingPage(uint64_t* context)   { return (uint64_t) (context + 12); }
uint64_t ExitCode(uint64_t* context)       { return (uint64_t) (context + 13); }
uint64_t Parent(uint64_t* context)         { return (uint64_t) (context + 14); }
uint64_t VirtualContext(uint64_t* context) { return (uint64_t) (context + 15); }
uint64_t Name(uint64_t* context)           { return (uint64_t) (context + 16); }

uint64_t* getNextContext(uint64_t* context)    { return (uint64_t*) *context; }
uint64_t* getPrevContext(uint64_t* context)    { return (uint64_t*) *(context + 1); }
uint64_t  getPC(uint64_t* context)             { return             *(context + 2); }
uint64_t* getRegs(uint64_t* context)           { return (uint64_t*) *(context + 3); }
uint64_t  getLoReg(uint64_t* context)          { return             *(context + 4); }
uint64_t  getHiReg(uint64_t* context)          { return             *(context + 5); }
uint64_t* getPT(uint64_t* context)             { return (uint64_t*) *(context + 6); }
uint64_t  getLoPage(uint64_t* context)         { return             *(context + 7); }
uint64_t  getMePage(uint64_t* context)         { return             *(context + 8); }
uint64_t  getHiPage(uint64_t* context)         { return             *(context + 9); }
uint64_t  getProgramBreak(uint64_t* context)   { return             *(context + 10); }
uint64_t  getException(uint64_t* context)      { return             *(context + 11); }
uint64_t  getFaultingPage(uint64_t* context)   { return             *(context + 12); }
uint64_t  getExitCode(uint64_t* context)       { return             *(context + 13); }
uint64_t* getParent(uint64_t* context)         { return (uint64_t*) *(context + 14); }
uint64_t* getVirtualContext(uint64_t* context) { return (uint64_t*) *(context + 15); }
uint64_t* getName(uint64_t* context)           { return (uint64_t*) *(context + 16); }

void setNextContext(uint64_t* context, uint64_t* next)     { *context        = (uint64_t) next; }
void setPrevContext(uint64_t* context, uint64_t* prev)     { *(context + 1)  = (uint64_t) prev; }
void setPC(uint64_t* context, uint64_t pc)                 { *(context + 2)  = pc; }
void setRegs(uint64_t* context, uint64_t* regs)            { *(context + 3)  = (uint64_t) regs; }
void setLoReg(uint64_t* context, uint64_t loReg)           { *(context + 4)  = loReg; }
void setHiReg(uint64_t* context, uint64_t hiReg)           { *(context + 5)  = hiReg; }
void setPT(uint64_t* context, uint64_t* pt)                { *(context + 6)  = (uint64_t) pt; }
void setLoPage(uint64_t* context, uint64_t loPage)         { *(context + 7)  = loPage; }
void setMePage(uint64_t* context, uint64_t mePage)         { *(context + 8)  = mePage; }
void setHiPage(uint64_t* context, uint64_t hiPage)         { *(context + 9)  = hiPage; }
void setProgramBreak(uint64_t* context, uint64_t brk)      { *(context + 10) = brk; }
void setException(uint64_t* context, uint64_t exception)   { *(context + 11) = exception; }
void setFaultingPage(uint64_t* context, uint64_t page)     { *(context + 12) = page; }
void setExitCode(uint64_t* context, uint64_t code)         { *(context + 13) = code; }
void setParent(uint64_t* context, uint64_t* parent)        { *(context + 14) = (uint64_t) parent; }
void setVirtualContext(uint64_t* context, uint64_t* vctxt) { *(context + 15) = (uint64_t) vctxt; }
void setName(uint64_t* context, uint64_t* name)            { *(context + 16) = (uint64_t) name; }

// -----------------------------------------------------------------
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

void resetMicrokernel();

uint64_t* createContext(uint64_t* parent, uint64_t* vctxt);

uint64_t* cacheContext(uint64_t* vctxt);

void saveContext(uint64_t* context);

void mapPage(uint64_t* context, uint64_t page, uint64_t frame);

void restoreContext(uint64_t* context);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t debug_create = 0;
uint64_t debug_map    = 0;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* currentContext = (uint64_t*) 0; // context currently running

uint64_t* usedContexts = (uint64_t*) 0; // doubly-linked list of used contexts
uint64_t* freeContexts = (uint64_t*) 0; // singly-linked list of free contexts

// ------------------------- INITIALIZATION ------------------------

void resetMicrokernel() {
  currentContext = (uint64_t*) 0;

  while (usedContexts != (uint64_t*) 0)
    usedContexts = deleteContext(usedContexts, usedContexts);
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

void initKernel();

uint64_t pavailable();
uint64_t pused();

uint64_t* palloc();
void      pfree(uint64_t* frame);

void mapAndStore(uint64_t* context, uint64_t vaddr, uint64_t data);

void up_loadBinary(uint64_t* context);

uint64_t up_loadString(uint64_t* context, uint64_t* s, uint64_t SP);
void     up_loadArguments(uint64_t* context, uint64_t argc, uint64_t* argv);

void mapUnmappedPages(uint64_t* context);

uint64_t isBootLevelZero();

uint64_t handleSystemCalls(uint64_t* context);

uint64_t mipster(uint64_t* toContext);
uint64_t minster(uint64_t* toContext);
uint64_t mobster(uint64_t* toContext);
uint64_t hypster(uint64_t* toContext);
uint64_t mixter(uint64_t* toContext, uint64_t mix);

uint64_t selfie_run(uint64_t machine);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t* MY_CONTEXT = (uint64_t*) 0;

uint64_t DONOTEXIT = 0;
uint64_t EXIT = 1;

// signed 32-bit exit codes [int]
uint64_t EXITCODE_NOERROR = 0;
uint64_t EXITCODE_IOERROR;
uint64_t EXITCODE_SCANNERERROR;
uint64_t EXITCODE_PARSERERROR;
uint64_t EXITCODE_COMPILERERROR;
uint64_t EXITCODE_OUTOFVIRTUALMEMORY;
uint64_t EXITCODE_OUTOFPHYSICALMEMORY;
uint64_t EXITCODE_UNKNOWNSYSCALL;
uint64_t EXITCODE_UNCAUGHTEXCEPTION;

uint64_t MINSTER = 1;
uint64_t MIPSTER = 2;
uint64_t MOBSTER = 3;

uint64_t HYPSTER = 4;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t nextPageFrame = 0;

uint64_t usedPageFrameMemory = 0;
uint64_t freePageFrameMemory = 0;

// ------------------------- INITIALIZATION ------------------------

void initKernel() {
  EXITCODE_IOERROR = signShrink(-1, INT_BITWIDTH);
  EXITCODE_SCANNERERROR = signShrink(-2, INT_BITWIDTH);
  EXITCODE_PARSERERROR = signShrink(-3, INT_BITWIDTH);
  EXITCODE_COMPILERERROR = signShrink(-4, INT_BITWIDTH);
  EXITCODE_OUTOFVIRTUALMEMORY = signShrink(-5, INT_BITWIDTH);
  EXITCODE_OUTOFPHYSICALMEMORY = signShrink(-6, INT_BITWIDTH);
  EXITCODE_UNKNOWNSYSCALL = signShrink(-7, INT_BITWIDTH);
  EXITCODE_UNCAUGHTEXCEPTION = signShrink(-8, INT_BITWIDTH);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------   T H E O R E M  P R O V E R    ----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// -------------------------- SAT Solver ---------------------------
// -----------------------------------------------------------------

uint64_t FALSE = 0;
uint64_t TRUE  = 1;

uint64_t UNSAT = 0;
uint64_t SAT   = 1;

uint64_t* dimacsName = (uint64_t*) 0;

uint64_t numberOfSATVariables = 0;

 // numberOfSATVariables
uint64_t* SATAssignment = (uint64_t*) 0;

uint64_t numberOfSATClauses = 0;

// numberOfSATClauses * 2 * numberOfSATVariables
uint64_t* SATInstance = (uint64_t*) 0;

uint64_t clauseMayBeTrue(uint64_t* clauseAddress, uint64_t depth);
uint64_t instanceMayBeTrue(uint64_t depth);

uint64_t babysat(uint64_t depth);

// -----------------------------------------------------------------
// ----------------------- DIMACS CNF PARSER -----------------------
// -----------------------------------------------------------------

void selfie_printDimacs();

void     dimacs_findNextCharacter(uint64_t newLine);
void     dimacs_getSymbol();
void     dimacs_word(uint64_t* word);
uint64_t dimacs_number();
void     dimacs_getClause(uint64_t clause);
void     dimacs_getInstance();

void selfie_loadDimacs();

void selfie_sat();

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

void initSelfie(uint64_t argc, uint64_t* argv);

uint64_t  numberOfRemainingArguments();
uint64_t* remainingArguments();

uint64_t* peekArgument();
uint64_t* getArgument();
void      setArgument(uint64_t* argv);

void printUsage();

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t  selfie_argc = 0;
uint64_t* selfie_argv = (uint64_t*) 0;

uint64_t* selfieName = (uint64_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void initSelfie(uint64_t argc, uint64_t* argv) {
  selfie_argc = argc;
  selfie_argv = argv;

  selfieName = getArgument();
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     L I B R A R Y     ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------- LIBRARY PROCEDURES ----------------------
// -----------------------------------------------------------------

uint64_t twoToThePowerOf(uint64_t p) {
  // assert: 0 <= p < CPUBITWIDTH
  return *(power_of_two_table + p);
}

uint64_t leftShift(uint64_t n, uint64_t b) {
  // assert: 0 <= b < CPUBITWIDTH
  return n * twoToThePowerOf(b);
}

uint64_t rightShift(uint64_t n, uint64_t b) {
  // assert: 0 <= b < CPUBITWIDTH
  return n / twoToThePowerOf(b);
}

uint64_t signedLessThan(uint64_t lhs, uint64_t rhs) {
  // signed "<" operator: compare lhs and rhs in two's complement
  return lhs + INT64_MIN < rhs + INT64_MIN;
}

uint64_t signedGreaterThan(uint64_t lhs, uint64_t rhs) {
  // signed ">" operator: compare lhs and rhs in two's complement
  return lhs + INT64_MIN > rhs + INT64_MIN;
}

uint64_t signShrink(uint64_t immediate, uint64_t bits) {
  // assert: 0 < bits <= CPUBITWIDTH
  return rightShift(leftShift(immediate, CPUBITWIDTH - bits), CPUBITWIDTH - bits);
}

uint64_t getHighWord(uint64_t doubleWord) {
  return rightShift(doubleWord, 32);
}

uint64_t getLowWord(uint64_t doubleWord) {
  return rightShift(leftShift(doubleWord, 32), 32);
}

uint64_t loadCharacter(uint64_t* s, uint64_t i) {
  // assert: i >= 0
  uint64_t a;

  // a is the index of the word where the to-be-loaded i-th character in s is
  a = i / SIZEOFUINT64;

  // shift to-be-loaded character to the left resetting all bits to the left
  // then shift to-be-loaded character all the way to the right and return
  return rightShift(leftShift(*(s + a), ((SIZEOFUINT64 - 1) - (i % SIZEOFUINT64)) * 8), (SIZEOFUINT64 - 1) * 8);
}

uint64_t* storeCharacter(uint64_t* s, uint64_t i, uint64_t c) {
  // assert: i >= 0, all characters are 7-bit
  uint64_t a;

  // a is the index of the word where the with c
  // to-be-overwritten i-th character in s is
  a = i / SIZEOFUINT64;

  // subtract the to-be-overwritten character resetting its bits in s
  // then add c setting its bits at the i-th position in s
  *(s + a) = (*(s + a) - leftShift(loadCharacter(s, i), (i % SIZEOFUINT64) * 8)) + leftShift(c, (i % SIZEOFUINT64) * 8);

  return s;
}

uint64_t stringLength(uint64_t* s) {
  uint64_t i;

  i = 0;

  while (loadCharacter(s, i) != 0)
    i = i + 1;

  return i;
}

void stringReverse(uint64_t* s) {
  uint64_t i;
  uint64_t j;
  uint64_t tmp;

  i = 0;
  j = stringLength(s) - 1;

  while (i < j) {
    tmp = loadCharacter(s, i);

    storeCharacter(s, i, loadCharacter(s, j));
    storeCharacter(s, j, tmp);

    i = i + 1;
    j = j - 1;
  }
}

uint64_t stringCompare(uint64_t* s, uint64_t* t) {
  uint64_t i;

  i = 0;

  while (1)
    if (loadCharacter(s, i) == 0)
      if (loadCharacter(t, i) == 0)
        return 1;
      else
        return 0;
    else if (loadCharacter(s, i) == loadCharacter(t, i))
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

  // load character (one byte) at index i in s from memory
  // requires bit shifting since memory access is in words
  c = loadCharacter(s, i);

  // loop until s is terminated
  while (c != 0) {
    // the numerical value of ASCII-encoded decimal digits
    // is offset by the ASCII code of '0' (which is 48)
    c = c - '0';

    if (c > 9)
      // c was not a decimal digit
      return -1;

    // assert: s contains a decimal number

    // use base 10 but avoid integer overflow
    if (n < INT64_MAX / 10)
      n = n * 10 + c;
    else if (n == INT64_MAX / 10) {
      if (c <= INT64_MAX % 10)
        n = n * 10 + c;
      else if (c == (INT64_MAX % 10) + 1)
        // s must be terminated next, check below
        n = INT64_MIN;
      else
        // s contains a decimal number larger than INT64_MAX
        return -1;
    } else
      // s contains a decimal number larger than INT64_MAX
      return -1;

    // go to the next digit
    i = i + 1;

    // load character (one byte) at index i in s from memory
    // requires bit shifting since memory access is in words
    c = loadCharacter(s, i);

    if (n == INT64_MIN)
      if (c != 0)
        // n == INT64_MIN but s is not terminated yet
        return -1;
  }

  return n;
}

uint64_t* itoa(uint64_t n, uint64_t* s, uint64_t b, uint64_t a, uint64_t p) {
  // assert: b in {2,4,8,10,16}

  uint64_t i;
  uint64_t sign;

  // the conversion of the integer n to an ASCII string in s
  // with base b, alignment a, and fixed point p
  // begins with the leftmost digit in s
  i = 0;

  // for now assuming n is positive
  sign = 0;

  if (n == 0) {
    storeCharacter(s, 0, '0');

    i = 1;
  } else if (signedLessThan(n, 0)) {
    if (b == 10) {
      // n is represented as two's complement
      // convert n to a positive number but remember the sign
      n = -n;

      sign = 1;
    }
  }

  while (n != 0) {
    if (p > 0)
      if (i == p) {
        storeCharacter(s, i, '.'); // set point of fixed point number

        // go to the next digit
        i = i + 1;

        // we are done with the fixed point
        p = 0;
      }

    if (n % b > 9)
      // the ASCII code of hexadecimal digits larger than 9
      // is offset by the ASCII code of 'A' (which is 65)
      storeCharacter(s, i, n % b - 10 + 'A');
    else
      // the ASCII code of digits less than or equal to 9
      // is offset by the ASCII code of '0' (which is 48)
      storeCharacter(s, i, n % b + '0');

    // convert n by dividing n with base b
    n = n / b;

    i = i + 1;
  }

  if (p > 0) {
    while (i < p) {
      storeCharacter(s, i, '0'); // no point yet, fill with 0s

      i = i + 1;
    }

    storeCharacter(s, i, '.'); // set point
    storeCharacter(s, i + 1, '0'); // leading 0

    // go to the second next digit
    i = i + 2;

    // we are done with the fixed point
    p = 0;
  }

  if (b == 10) {
    if (sign) {
      storeCharacter(s, i, '-'); // negative decimal numbers start with -

      i = i + 1;
    }

    while (i < a) {
      storeCharacter(s, i, ' '); // align with spaces

      i = i + 1;
    }
  } else {
    while (i < a) {
      storeCharacter(s, i, '0'); // align with 0s

      i = i + 1;
    }

    if (b == 8) {
      storeCharacter(s, i, '0');   // octal numbers start with 00
      storeCharacter(s, i + 1, '0');

      i = i + 2;
    } else if (b == 16) {
      storeCharacter(s, i, 'x');   // hexadecimal numbers start with 0x
      storeCharacter(s, i + 1, '0');

      i = i + 2;
    }
  }

  storeCharacter(s, i, 0); // null-terminated string

  // our numeral system is positional hindu-arabic, that is,
  // the weight of digits increases right to left, which means
  // that we need to reverse the string we computed above
  stringReverse(s);

  return s;
}

uint64_t fixedPointRatio(uint64_t a, uint64_t b) {
  // compute fixed point ratio with 2 fractional digits

  // multiply a/b with 100 but avoid overflow

  if (a <= INT64_MAX / 100) {
    if (b != 0)
      return a * 100 / b;
  } else if (a <= INT64_MAX / 10) {
    if (b / 10 != 0)
      return a * 10 / (b / 10);
  } else {
    if (b / 100 != 0)
      return a / (b / 100);
  }

  return 0;
}

uint64_t fixedPointPercentage(uint64_t r) {
  if (r != 0)
    // 1000000 = 10000 (for 100.00%) * 100 (for 2 fractional digits of r)
    return 1000000 / r;
  else
    return 0;
}

void putCharacter(uint64_t c) {
  *character_buffer = c;

  // assert: character_buffer is mapped

  // try to write 1 character from character_buffer
  // into file with outputFD file descriptor
  if (write(outputFD, character_buffer, 1) == 1) {
    if (outputFD != 1)
      // count number of characters written to a file,
      // not the console which has file descriptor 1
      numberOfWrittenCharacters = numberOfWrittenCharacters + 1;
  } else {
    // write failed
    if (outputFD != 1) {
      // failed write was not to the console which has file descriptor 1
      // to report the error we may thus still write to the console via print
      outputFD = 1;

      print(selfieName);
      print((uint64_t*) ": could not write character to output file ");
      print(outputName);
      println();
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

    while (loadCharacter(s, i) != 0) {
      putCharacter(loadCharacter(s, i));

      i = i + 1;
    }
  }
}

void println() {
  putCharacter(CHAR_LF);
}

void printCharacter(uint64_t c) {
  putCharacter(CHAR_SINGLEQUOTE);

  if (c == CHAR_EOF)
    print((uint64_t*) "end of file");
  else if (c == CHAR_TAB)
    print((uint64_t*) "tabulator");
  else if (c == CHAR_LF)
    print((uint64_t*) "line feed");
  else if (c == CHAR_CR)
    print((uint64_t*) "carriage return");
  else
    putCharacter(c);

  putCharacter(CHAR_SINGLEQUOTE);
}

void printString(uint64_t* s) {
  putCharacter(CHAR_DOUBLEQUOTE);

  print(s);

  putCharacter(CHAR_DOUBLEQUOTE);
}

void printInteger(uint64_t n) {
  print(itoa(n, integer_buffer, 10, 0, 0));
}

void printFixedPointPercentage(uint64_t a, uint64_t b) {
  print(itoa(fixedPointPercentage(fixedPointRatio(a, b)), integer_buffer, 10, 0, 2));
}

void printFixedPointRatio(uint64_t a, uint64_t b) {
  print(itoa(fixedPointRatio(a, b), integer_buffer, 10, 0, 2));
}

void printHexadecimal(uint64_t n, uint64_t a) {
  print(itoa(n, integer_buffer, 16, a, 0));
}

void printOctal(uint64_t n, uint64_t a) {
  print(itoa(n, integer_buffer, 8, a, 0));
}

void printBinary(uint64_t n, uint64_t a) {
  print(itoa(n, integer_buffer, 2, a, 0));
}

uint64_t roundUp(uint64_t n, uint64_t m) {
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
    print(selfieName);
    print((uint64_t*) ": malloc out of memory");
    println();

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

  size = roundUp(size, SIZEOFUINT64);

  memory = smalloc(size);

  size = size / SIZEOFUINT64;

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

void printSymbol(uint64_t symbol) {
  putCharacter(CHAR_DOUBLEQUOTE);

  if (symbol == SYM_EOF)
    print((uint64_t*) "end of file");
  else
    print((uint64_t*) *(SYMBOLS + symbol));

  putCharacter(CHAR_DOUBLEQUOTE);
}

void printLineNumber(uint64_t* message, uint64_t line) {
  print(selfieName);
  print((uint64_t*) ": ");
  print(message);
  print((uint64_t*) " in ");
  print(sourceName);
  print((uint64_t*) " in line ");
  printInteger(line);
  print((uint64_t*) ": ");
}

void syntaxErrorMessage(uint64_t* message) {
  printLineNumber((uint64_t*) "error", lineNumber);

  print(message);

  println();
}

void syntaxErrorCharacter(uint64_t expected) {
  printLineNumber((uint64_t*) "error", lineNumber);

  printCharacter(expected);
  print((uint64_t*) " expected but ");

  printCharacter(character);
  print((uint64_t*) " found");

  println();
}

void syntaxErrorIdentifier(uint64_t* expected) {
  printLineNumber((uint64_t*) "error", lineNumber);

  print(expected);
  print((uint64_t*) " expected but ");

  print(identifier);
  print((uint64_t*) " found");

  println();
}

void getCharacter() {
  uint64_t numberOfReadBytes;

  // assert: character_buffer is mapped

  // try to read 1 character into character_buffer
  // from file with sourceFD file descriptor
  numberOfReadBytes = read(sourceFD, character_buffer, 1);

  if (numberOfReadBytes == 1) {
    // store the read character in the global variable called character
    character = *character_buffer;

    numberOfReadCharacters = numberOfReadCharacters + 1;
  } else if (numberOfReadBytes == 0)
    // reached end of file
    character = CHAR_EOF;
  else {
    print(selfieName);
    print((uint64_t*) ": could not read character from input file ");
    print(sourceName);
    println();

    exit(EXITCODE_IOERROR);
  }
}

uint64_t isCharacterNewLine() {
  if (character == CHAR_LF)
    return 1;
  else if (character == CHAR_CR)
    return 1;
  else
    return 0;
}

uint64_t isCharacterWhitespace() {
  if (character == CHAR_SPACE)
    return 1;
  else if (character == CHAR_TAB)
    return 1;
  else
    return isCharacterNewLine();
}

uint64_t findNextCharacter() {
  uint64_t inComment;

  // assuming we are not in a comment
  inComment = 0;

  // read and discard all whitespace and comments until a character is found
  // that is not whitespace and does not occur in a comment, or the file ends
  while (1) {
    if (inComment) {
      getCharacter();

      if (isCharacterNewLine())
        // comments end with new line
        inComment = 0;
      else if (character == CHAR_EOF)
        return character;
      else
        // count the characters in comments as ignored characters
        // line feed and carriage return are counted below
        numberOfIgnoredCharacters = numberOfIgnoredCharacters + 1;

    } else if (isCharacterWhitespace()) {
      // keep track of line numbers for error reporting and code annotation
      if (character == CHAR_LF)
        lineNumber = lineNumber + 1;

      // count line feed and carriage return as ignored characters
      numberOfIgnoredCharacters = numberOfIgnoredCharacters + 1;

      getCharacter();

    } else if (character == CHAR_SLASH) {
      getCharacter();

      if (character == CHAR_SLASH) {
        // "//" begins a comment
        inComment = 1;

        // count both slashes as ignored characters as well
        numberOfIgnoredCharacters = numberOfIgnoredCharacters + 2;

        // count the number of comments
        numberOfComments = numberOfComments + 1;
      } else {
        // while looking for "//" we actually found '/'
        symbol = SYM_DIV;

        return character;
      }

    } else
      // character found that is not whitespace and not occurring in a comment
      return character;
  }
}

uint64_t isCharacterLetter() {
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

uint64_t isCharacterDigit() {
  // ASCII codes for digits are in a contiguous interval
  if (character >= '0')
    if (character <= '9')
      return 1;
    else
      return 0;
  else
    return 0;
}

uint64_t isCharacterLetterOrDigitOrUnderscore() {
  if (isCharacterLetter())
    return 1;
  else if (isCharacterDigit())
    return 1;
  else if (character == CHAR_UNDERSCORE)
    return 1;
  else
    return 0;
}

uint64_t isCharacterNotDoubleQuoteOrNewLineOrEOF() {
  if (character == CHAR_DOUBLEQUOTE)
    return 0;
  else if (isCharacterNewLine())
    return 0;
  else if (character == CHAR_EOF)
    return 0;
  else
    return 1;
}

uint64_t identifierStringMatch(uint64_t keyword) {
  return stringCompare(identifier, (uint64_t*) *(SYMBOLS + keyword));
}

uint64_t identifierOrKeyword() {
  if (identifierStringMatch(SYM_WHILE))
    return SYM_WHILE;
  if (identifierStringMatch(SYM_IF))
    return SYM_IF;
  if (identifierStringMatch(SYM_UINT64))
    return SYM_UINT64;
  if (identifierStringMatch(SYM_ELSE))
    return SYM_ELSE;
  if (identifierStringMatch(SYM_RETURN))
    return SYM_RETURN;
  if (identifierStringMatch(SYM_VOID))
    return SYM_VOID;
  else
    return SYM_IDENTIFIER;
}

void getSymbol() {
  uint64_t i;

  // reset previously scanned symbol
  symbol = SYM_EOF;

  if (findNextCharacter() != CHAR_EOF) {
    if (symbol != SYM_DIV) {
      // '/' may have already been recognized
      // while looking for whitespace and "//"
      if (isCharacterLetter()) {
        // accommodate identifier and null for termination
        identifier = smalloc(maxIdentifierLength + 1);

        i = 0;

        while (isCharacterLetterOrDigitOrUnderscore()) {
          if (i >= maxIdentifierLength) {
            syntaxErrorMessage((uint64_t*) "identifier too long");

            exit(EXITCODE_SCANNERERROR);
          }

          storeCharacter(identifier, i, character);

          i = i + 1;

          getCharacter();
        }

        storeCharacter(identifier, i, 0); // null-terminated string

        symbol = identifierOrKeyword();

      } else if (isCharacterDigit()) {
        // accommodate integer and null for termination
        integer = smalloc(maxIntegerLength + 1);

        i = 0;

        while (isCharacterDigit()) {
          if (i >= maxIntegerLength) {
            syntaxErrorMessage((uint64_t*) "integer out of bound");

            exit(EXITCODE_SCANNERERROR);
          }

          storeCharacter(integer, i, character);

          i = i + 1;

          getCharacter();
        }

        storeCharacter(integer, i, 0); // null-terminated string

        literal = atoi(integer);

        if (signedLessThan(literal, 0)) {
          if (literal == INT64_MIN) {
            if (mayBeINTMIN == 0) {
              syntaxErrorMessage((uint64_t*) "integer out of bound");

              exit(EXITCODE_SCANNERERROR);
            }
          } else {
            syntaxErrorMessage((uint64_t*) "integer out of bound");

            exit(EXITCODE_SCANNERERROR);
          }
        }

        symbol = SYM_INTEGER;

      } else if (character == CHAR_SINGLEQUOTE) {
        getCharacter();

        literal = 0;

        if (character == CHAR_EOF) {
          syntaxErrorMessage((uint64_t*) "reached end of file looking for a character literal");

          exit(EXITCODE_SCANNERERROR);
        } else
          literal = character;

        getCharacter();

        if (character == CHAR_SINGLEQUOTE)
          getCharacter();
        else if (character == CHAR_EOF) {
          syntaxErrorCharacter(CHAR_SINGLEQUOTE);

          exit(EXITCODE_SCANNERERROR);
        } else
          syntaxErrorCharacter(CHAR_SINGLEQUOTE);

        symbol = SYM_CHARACTER;

      } else if (character == CHAR_DOUBLEQUOTE) {
        getCharacter();

        // accommodate string and null for termination
        // allocate zeroed memory since strings are emitted
        // in whole words but may end non-word-aligned
        string = zalloc(maxStringLength + 1);

        i = 0;

        while (isCharacterNotDoubleQuoteOrNewLineOrEOF()) {
          if (i >= maxStringLength) {
            syntaxErrorMessage((uint64_t*) "string too long");

            exit(EXITCODE_SCANNERERROR);
          }

          storeCharacter(string, i, character);

          i = i + 1;

          getCharacter();
        }

        if (character == CHAR_DOUBLEQUOTE)
          getCharacter();
        else {
          syntaxErrorCharacter(CHAR_DOUBLEQUOTE);

          exit(EXITCODE_SCANNERERROR);
        }

        storeCharacter(string, i, 0); // null-terminated string

        symbol = SYM_STRING;

      } else if (character == CHAR_SEMICOLON) {
        getCharacter();

        symbol = SYM_SEMICOLON;

      } else if (character == CHAR_PLUS) {
        getCharacter();

        symbol = SYM_PLUS;

      } else if (character == CHAR_DASH) {
        getCharacter();

        symbol = SYM_MINUS;

      } else if (character == CHAR_ASTERISK) {
        getCharacter();

        symbol = SYM_ASTERISK;

      } else if (character == CHAR_EQUAL) {
        getCharacter();

        if (character == CHAR_EQUAL) {
          getCharacter();

          symbol = SYM_EQUALITY;
        } else
          symbol = SYM_ASSIGN;

      } else if (character == CHAR_LPARENTHESIS) {
        getCharacter();

        symbol = SYM_LPARENTHESIS;

      } else if (character == CHAR_RPARENTHESIS) {
        getCharacter();

        symbol = SYM_RPARENTHESIS;

      } else if (character == CHAR_LBRACE) {
        getCharacter();

        symbol = SYM_LBRACE;

      } else if (character == CHAR_RBRACE) {
        getCharacter();

        symbol = SYM_RBRACE;

      } else if (character == CHAR_COMMA) {
        getCharacter();

        symbol = SYM_COMMA;

      } else if (character == CHAR_LT) {
        getCharacter();

        if (character == CHAR_EQUAL) {
          getCharacter();

          symbol = SYM_LEQ;
        } else
          symbol = SYM_LT;

      } else if (character == CHAR_GT) {
        getCharacter();

        if (character == CHAR_EQUAL) {
          getCharacter();

          symbol = SYM_GEQ;
        } else
          symbol = SYM_GT;

      } else if (character == CHAR_EXCLAMATION) {
        getCharacter();

        if (character == CHAR_EQUAL)
          getCharacter();
        else
          syntaxErrorCharacter(CHAR_EQUAL);

        symbol = SYM_NOTEQ;

      } else if (character == CHAR_PERCENTAGE) {
        getCharacter();

        symbol = SYM_MOD;

      } else {
        printLineNumber((uint64_t*) "error", lineNumber);
        print((uint64_t*) "found unknown character ");
        printCharacter(character);

        println();

        exit(EXITCODE_SCANNERERROR);
      }
    }

    numberOfScannedSymbols = numberOfScannedSymbols + 1;
  }
}

// -----------------------------------------------------------------
// ------------------------- SYMBOL TABLE --------------------------
// -----------------------------------------------------------------

void createSymbolTableEntry(uint64_t whichTable, uint64_t* string, uint64_t line, uint64_t class, uint64_t type, uint64_t value, uint64_t address) {
  uint64_t* newEntry;

  newEntry = smalloc(2 * SIZEOFUINT64STAR + 6 * SIZEOFUINT64);

  setString(newEntry, string);
  setLineNumber(newEntry, line);
  setClass(newEntry, class);
  setType(newEntry, type);
  setValue(newEntry, value);
  setAddress(newEntry, address);

  // create entry at head of symbol table
  if (whichTable == GLOBAL_TABLE) {
    setScope(newEntry, REG_GP);
    setNextEntry(newEntry, global_symbol_table);
    global_symbol_table = newEntry;

    if (class == VARIABLE)
      numberOfGlobalVariables = numberOfGlobalVariables + 1;
    else if (class == PROCEDURE)
      numberOfProcedures = numberOfProcedures + 1;
    else if (class == STRING)
      numberOfStrings = numberOfStrings + 1;
  } else if (whichTable == LOCAL_TABLE) {
    setScope(newEntry, REG_FP);
    setNextEntry(newEntry, local_symbol_table);
    local_symbol_table = newEntry;
  } else {
    // library procedures
    setScope(newEntry, REG_GP);
    setNextEntry(newEntry, library_symbol_table);
    library_symbol_table = newEntry;
  }
}

uint64_t* searchSymbolTable(uint64_t* entry, uint64_t* string, uint64_t class) {
  while (entry != (uint64_t*) 0) {
    if (stringCompare(string, getString(entry)))
      if (class == getClass(entry))
        return entry;

    // keep looking
    entry = getNextEntry(entry);
  }

  return (uint64_t*) 0;
}

uint64_t* getScopedSymbolTableEntry(uint64_t* string, uint64_t class) {
  uint64_t* entry;

  if (class == VARIABLE)
    // local variables override global variables
    entry = searchSymbolTable(local_symbol_table, string, VARIABLE);
  else if (class == PROCEDURE)
    // library procedures override declared or defined procedures
    entry = searchSymbolTable(library_symbol_table, string, PROCEDURE);
  else
    entry = (uint64_t*) 0;

  if (entry == (uint64_t*) 0)
    return searchSymbolTable(global_symbol_table, string, class);
  else
    return entry;
}

uint64_t isUndefinedProcedure(uint64_t* entry) {
  uint64_t* libraryEntry;

  if (getClass(entry) == PROCEDURE) {
    // library procedures override declared or defined procedures
    libraryEntry = searchSymbolTable(library_symbol_table, getString(entry), PROCEDURE);

    if (libraryEntry != (uint64_t*) 0)
      // procedure is library procedure
      return 0;
    else if (getAddress(entry) == 0)
      // procedure declared but not defined
      return 1;
    else if (getOpcode(loadInstruction(getAddress(entry))) == OP_JAL)
      // procedure called but not defined
      return 1;
  }

  return 0;
}

uint64_t reportUndefinedProcedures() {
  uint64_t undefined;
  uint64_t* entry;

  undefined = 0;

  entry = global_symbol_table;

  while (entry != (uint64_t*) 0) {
    if (isUndefinedProcedure(entry)) {
      undefined = 1;

      printLineNumber((uint64_t*) "error", getLineNumber(entry));
      print((uint64_t*) "procedure ");
      print(getString(entry));
      print((uint64_t*) " undefined");
      println();
    }

    // keep looking
    entry = getNextEntry(entry);
  }

  return undefined;
}

// -----------------------------------------------------------------
// ---------------------------- PARSER -----------------------------
// -----------------------------------------------------------------

uint64_t isNotRbraceOrEOF() {
  if (symbol == SYM_RBRACE)
    return 0;
  else if (symbol == SYM_EOF)
    return 0;
  else
    return 1;
}

uint64_t isExpression() {
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

uint64_t isLiteral() {
  if (symbol == SYM_INTEGER)
    return 1;
  else if (symbol == SYM_CHARACTER)
    return 1;
  else
    return 0;
}

uint64_t isStarOrDivOrModulo() {
  if (symbol == SYM_ASTERISK)
    return 1;
  else if (symbol == SYM_DIV)
    return 1;
  else if (symbol == SYM_MOD)
    return 1;
  else
    return 0;
}

uint64_t isPlusOrMinus() {
  if (symbol == SYM_MINUS)
    return 1;
  else if (symbol == SYM_PLUS)
    return 1;
  else
    return 0;
}

uint64_t isComparison() {
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

uint64_t lookForFactor() {
  if (symbol == SYM_LPARENTHESIS)
    return 0;
  else if (symbol == SYM_ASTERISK)
    return 0;
  else if (symbol == SYM_IDENTIFIER)
    return 0;
  else if (symbol == SYM_INTEGER)
    return 0;
  else if (symbol == SYM_CHARACTER)
    return 0;
  else if (symbol == SYM_STRING)
    return 0;
  else if (symbol == SYM_EOF)
    return 0;
  else
    return 1;
}

uint64_t lookForStatement() {
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

uint64_t lookForType() {
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
  // we use registers REG_T0-REG_T7 for temporaries
  if (allocatedTemporaries < REG_T7 - REG_A3)
    allocatedTemporaries = allocatedTemporaries + 1;
  else {
    syntaxErrorMessage((uint64_t*) "out of registers");

    exit(EXITCODE_COMPILERERROR);
  }
}

uint64_t currentTemporary() {
  if (allocatedTemporaries > 0)
    return allocatedTemporaries + REG_A3;
  else {
    syntaxErrorMessage((uint64_t*) "illegal register access");

    exit(EXITCODE_COMPILERERROR);
  }
}

uint64_t previousTemporary() {
  if (allocatedTemporaries > 1)
    return currentTemporary() - 1;
  else {
    syntaxErrorMessage((uint64_t*) "illegal register access");

    exit(EXITCODE_COMPILERERROR);
  }
}

uint64_t nextTemporary() {
  if (allocatedTemporaries < REG_T7 - REG_A3)
    return currentTemporary() + 1;
  else {
    syntaxErrorMessage((uint64_t*) "out of registers");

    exit(EXITCODE_COMPILERERROR);
  }
}

void tfree(uint64_t numberOfTemporaries) {
  if (allocatedTemporaries >= numberOfTemporaries)
    allocatedTemporaries = allocatedTemporaries - numberOfTemporaries;
  else {
    syntaxErrorMessage((uint64_t*) "illegal register deallocation");

    exit(EXITCODE_COMPILERERROR);
  }
}

void save_temporaries() {
  while (allocatedTemporaries > 0) {
    // push temporary onto stack
    emitIFormat(OP_DADDIU, REG_SP, REG_SP, -REGISTERSIZE);
    emitIFormat(OP_SD, REG_SP, currentTemporary(), 0);

    tfree(1);
  }
}

void restore_temporaries(uint64_t numberOfTemporaries) {
  while (allocatedTemporaries < numberOfTemporaries) {
    talloc();

    // restore temporary from stack
    emitIFormat(OP_LD, REG_SP, currentTemporary(), 0);
    emitIFormat(OP_DADDIU, REG_SP, REG_SP, REGISTERSIZE);
  }
}

void syntaxErrorSymbol(uint64_t expected) {
  printLineNumber((uint64_t*) "error", lineNumber);

  printSymbol(expected);
  print((uint64_t*) " expected but ");

  printSymbol(symbol);
  print((uint64_t*) " found");

  println();
}

void syntaxErrorUnexpected() {
  printLineNumber((uint64_t*) "error", lineNumber);

  print((uint64_t*) "unexpected symbol ");
  printSymbol(symbol);
  print((uint64_t*) " found");

  println();
}

void printType(uint64_t type) {
  if (type == UINT64_T)
    print((uint64_t*) "uint64_t");
  else if (type == UINT64STAR_T)
    print((uint64_t*) "uint64_t*");
  else if (type == VOID_T)
    print((uint64_t*) "void");
  else
    print((uint64_t*) "unknown");
}

void typeWarning(uint64_t expected, uint64_t found) {
  printLineNumber((uint64_t*) "warning", lineNumber);

  print((uint64_t*) "type mismatch, ");

  printType(expected);

  print((uint64_t*) " expected but ");

  printType(found);

  print((uint64_t*) " found");

  println();
}

uint64_t* getVariable(uint64_t* variable) {
  uint64_t* entry;

  entry = getScopedSymbolTableEntry(variable, VARIABLE);

  if (entry == (uint64_t*) 0) {
    printLineNumber((uint64_t*) "error", lineNumber);
    print(variable);
    print((uint64_t*) " undeclared");
    println();

    exit(EXITCODE_PARSERERROR);
  }

  return entry;
}

uint64_t load_variable(uint64_t* variable) {
  uint64_t* entry;

  entry = getVariable(variable);

  talloc();

  emitIFormat(OP_LD, getScope(entry), currentTemporary(), getAddress(entry));

  return getType(entry);
}

void load_integer(uint64_t value) {
  uint64_t reg;
  uint64_t shifted;
  uint64_t toShift;
  uint64_t i;

  talloc();

  reg = REG_ZR;
  shifted = 0;

  toShift = CPUBITWIDTH % 14;

  i = CPUBITWIDTH - toShift;

  while (i >= 14) {
    if (value >= twoToThePowerOf(i)) {
      emitIFormat(OP_DADDIU, reg, currentTemporary(), rightShift(leftShift(value, shifted), shifted + i));

      reg = currentTemporary();

      emitLeftShiftBy(reg, 14);
    }

    shifted = shifted + toShift;

    toShift = 14;

    i = i - toShift;
  }

  emitIFormat(OP_DADDIU, reg, currentTemporary(), rightShift(leftShift(value, shifted), shifted));
}

void load_string(uint64_t* string) {
  uint64_t length;

  length = stringLength(string) + 1;

  allocatedMemory = allocatedMemory + roundUp(length, REGISTERSIZE);

  createSymbolTableEntry(GLOBAL_TABLE, string, lineNumber, STRING, UINT64STAR_T, 0, -allocatedMemory);

  talloc();

  emitIFormat(OP_DADDIU, REG_GP, currentTemporary(), -allocatedMemory);
}

uint64_t help_call_codegen(uint64_t* entry, uint64_t* procedure) {
  uint64_t type;

  if (entry == (uint64_t*) 0) {
    // procedure never called nor declared nor defined

    // default return type is "int"
    type = UINT64_T;

    createSymbolTableEntry(GLOBAL_TABLE, procedure, lineNumber, PROCEDURE, type, 0, binaryLength);

    emitJFormat(OP_JAL, 0);

  } else {
    type = getType(entry);

    if (getAddress(entry) == 0) {
      // procedure declared but never called nor defined
      setAddress(entry, binaryLength);

      emitJFormat(OP_JAL, 0);
    } else if (getOpcode(loadInstruction(getAddress(entry))) == OP_JAL) {
      // procedure called and possibly declared but not defined

      // create fixup chain
      emitJFormat(OP_JAL, getAddress(entry) / INSTRUCTIONSIZE);
      setAddress(entry, binaryLength - 2 * INSTRUCTIONSIZE);
    } else
      // procedure defined, use address
      emitJFormat(OP_JAL, getAddress(entry) / INSTRUCTIONSIZE);
  }

  return type;
}

void help_procedure_prologue(uint64_t localVariables) {
  // allocate memory for return address
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, -REGISTERSIZE);

  // save return address
  emitIFormat(OP_SD, REG_SP, REG_RA, 0);

  // allocate memory for caller's frame pointer
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, -REGISTERSIZE);

  // save caller's frame pointer
  emitIFormat(OP_SD, REG_SP, REG_FP, 0);

  // set callee's frame pointer
  emitIFormat(OP_DADDIU, REG_SP, REG_FP, 0);

  // allocate memory for callee's local variables
  if (localVariables != 0)
    emitIFormat(OP_DADDIU, REG_SP, REG_SP, -localVariables * REGISTERSIZE);
}

void help_procedure_epilogue(uint64_t parameters) {
  // deallocate memory for callee's frame pointer and local variables
  emitIFormat(OP_DADDIU, REG_FP, REG_SP, 0);

  // restore caller's frame pointer
  emitIFormat(OP_LD, REG_SP, REG_FP, 0);

  // deallocate memory for caller's frame pointer
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, REGISTERSIZE);

  // restore return address
  emitIFormat(OP_LD, REG_SP, REG_RA, 0);

  // deallocate memory for return address and parameters
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, (parameters + 1) * REGISTERSIZE);

  // return
  emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

uint64_t gr_call(uint64_t* procedure) {
  uint64_t* entry;
  uint64_t numberOfTemporaries;
  uint64_t type;

  // assert: n = allocatedTemporaries

  entry = getScopedSymbolTableEntry(procedure, PROCEDURE);

  numberOfTemporaries = allocatedTemporaries;

  save_temporaries();

  // assert: allocatedTemporaries == 0

  if (isExpression()) {
    gr_expression();

    // TODO: check if types/number of parameters is correct

    // push first parameter onto stack
    emitIFormat(OP_DADDIU, REG_SP, REG_SP, -REGISTERSIZE);
    emitIFormat(OP_SD, REG_SP, currentTemporary(), 0);

    tfree(1);

    while (symbol == SYM_COMMA) {
      getSymbol();

      gr_expression();

      // push more parameters onto stack
      emitIFormat(OP_DADDIU, REG_SP, REG_SP, -REGISTERSIZE);
      emitIFormat(OP_SD, REG_SP, currentTemporary(), 0);

      tfree(1);
    }

    if (symbol == SYM_RPARENTHESIS) {
      getSymbol();

      type = help_call_codegen(entry, procedure);
    } else {
      syntaxErrorSymbol(SYM_RPARENTHESIS);

      type = UINT64_T;
    }
  } else if (symbol == SYM_RPARENTHESIS) {
    getSymbol();

    type = help_call_codegen(entry, procedure);
  } else {
    syntaxErrorSymbol(SYM_RPARENTHESIS);

    type = UINT64_T;
  }

  // assert: allocatedTemporaries == 0

  restore_temporaries(numberOfTemporaries);

  numberOfCalls = numberOfCalls + 1;

  // assert: allocatedTemporaries == n

  return type;
}

uint64_t gr_factor() {
  uint64_t hasCast;
  uint64_t cast;
  uint64_t type;

  uint64_t* variableOrProcedureName;

  // assert: n = allocatedTemporaries

  hasCast = 0;

  type = UINT64_T;

  while (lookForFactor()) {
    syntaxErrorUnexpected();

    if (symbol == SYM_EOF)
      exit(EXITCODE_PARSERERROR);
    else
      getSymbol();
  }

  // optional cast: [ cast ]
  if (symbol == SYM_LPARENTHESIS) {
    getSymbol();

    // cast: "(" "uint64_t" [ "*" ] ")"
    if (symbol == SYM_UINT64) {
      hasCast = 1;

      cast = gr_type();

      if (symbol == SYM_RPARENTHESIS)
        getSymbol();
      else
        syntaxErrorSymbol(SYM_RPARENTHESIS);

    // not a cast: "(" expression ")"
    } else {
      type = gr_expression();

      if (symbol == SYM_RPARENTHESIS)
        getSymbol();
      else
        syntaxErrorSymbol(SYM_RPARENTHESIS);

      // assert: allocatedTemporaries == n + 1

      return type;
    }
  }

  // dereference?
  if (symbol == SYM_ASTERISK) {
    getSymbol();

    // ["*"] identifier
    if (symbol == SYM_IDENTIFIER) {
      type = load_variable(identifier);

      getSymbol();

    // * "(" expression ")"
    } else if (symbol == SYM_LPARENTHESIS) {
      getSymbol();

      type = gr_expression();

      if (symbol == SYM_RPARENTHESIS)
        getSymbol();
      else
        syntaxErrorSymbol(SYM_RPARENTHESIS);
    } else
      syntaxErrorUnexpected();

    if (type != UINT64STAR_T)
      typeWarning(UINT64STAR_T, type);

    // dereference
    emitIFormat(OP_LD, currentTemporary(), currentTemporary(), 0);

    type = UINT64_T;

  // identifier?
  } else if (symbol == SYM_IDENTIFIER) {
    variableOrProcedureName = identifier;

    getSymbol();

    if (symbol == SYM_LPARENTHESIS) {
      getSymbol();

      // procedure call: identifier "(" ... ")"
      type = gr_call(variableOrProcedureName);

      talloc();

      // retrieve return value
      emitIFormat(OP_DADDIU, REG_V0, currentTemporary(), 0);

      // reset return register to initial return value
      // for missing return expressions
      emitIFormat(OP_DADDIU, REG_ZR, REG_V0, 0);
    } else
      // variable access: identifier
      type = load_variable(variableOrProcedureName);

  // integer?
  } else if (symbol == SYM_INTEGER) {
    load_integer(literal);

    getSymbol();

    type = UINT64_T;

  // character?
  } else if (symbol == SYM_CHARACTER) {
    talloc();

    emitIFormat(OP_DADDIU, REG_ZR, currentTemporary(), literal);

    getSymbol();

    type = UINT64_T;

  // string?
  } else if (symbol == SYM_STRING) {
    load_string(string);

    getSymbol();

    type = UINT64STAR_T;

  //  "(" expression ")"
  } else if (symbol == SYM_LPARENTHESIS) {
    getSymbol();

    type = gr_expression();

    if (symbol == SYM_RPARENTHESIS)
      getSymbol();
    else
      syntaxErrorSymbol(SYM_RPARENTHESIS);
  } else
    syntaxErrorUnexpected();

  // assert: allocatedTemporaries == n + 1

  if (hasCast)
    return cast;
  else
    return type;
}

uint64_t gr_term() {
  uint64_t ltype;
  uint64_t operatorSymbol;
  uint64_t rtype;

  // assert: n = allocatedTemporaries

  ltype = gr_factor();

  // assert: allocatedTemporaries == n + 1

  // * / or % ?
  while (isStarOrDivOrModulo()) {
    operatorSymbol = symbol;

    getSymbol();

    rtype = gr_factor();

    // assert: allocatedTemporaries == n + 2

    if (ltype != rtype)
      typeWarning(ltype, rtype);

    if (operatorSymbol == SYM_ASTERISK) {
      emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), 0, FCT_DMULTU);
      emitRFormat(OP_SPECIAL, 0, 0, previousTemporary(), FCT_MFLO);

    } else if (operatorSymbol == SYM_DIV) {
      emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), 0, FCT_DDIVU);
      emitRFormat(OP_SPECIAL, 0, 0, previousTemporary(), FCT_MFLO);

    } else if (operatorSymbol == SYM_MOD) {
      emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), 0, FCT_DDIVU);
      emitRFormat(OP_SPECIAL, 0, 0, previousTemporary(), FCT_MFHI);
    }

    tfree(1);
  }

  // assert: allocatedTemporaries == n + 1

  return ltype;
}

uint64_t gr_simpleExpression() {
  uint64_t ltype;
  uint64_t operatorSymbol;
  uint64_t rtype;

  // assert: n = allocatedTemporaries

  // optional: -
  if (symbol == SYM_MINUS) {
    mayBeINTMIN = 1;

    getSymbol();

    mayBeINTMIN = 0;

    ltype = gr_term();

    if (ltype != UINT64_T) {
      typeWarning(UINT64_T, ltype);

      ltype = UINT64_T;
    }

    emitRFormat(OP_SPECIAL, REG_ZR, currentTemporary(), currentTemporary(), FCT_DSUBU);
  } else
    ltype = gr_term();

  // assert: allocatedTemporaries == n + 1

  // + or -?
  while (isPlusOrMinus()) {
    operatorSymbol = symbol;

    getSymbol();

    rtype = gr_term();

    // assert: allocatedTemporaries == n + 2

    if (operatorSymbol == SYM_PLUS) {
      if (ltype == UINT64STAR_T) {
        if (rtype == UINT64_T)
          // UINT64STAR_T + UINT64_T
          // pointer arithmetic: factor of 2^3 of integer operand
          emitLeftShiftBy(currentTemporary(), 3);
        else
          // UINT64STAR_T + UINT64STAR_T
          syntaxErrorMessage((uint64_t*) "(uint64_t*) + (uint64_t*) is undefined");
      } else if (rtype == UINT64STAR_T) {
        // UINT64_T + UINT64STAR_T
        // pointer arithmetic: factor of 2^3 of integer operand
        emitLeftShiftBy(previousTemporary(), 3);

        ltype = UINT64STAR_T;
      }

      emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_DADDU);

    } else if (operatorSymbol == SYM_MINUS) {
      if (ltype == UINT64STAR_T) {
        if (rtype == UINT64_T) {
          // UINT64STAR_T - UINT64_T
          // pointer arithmetic: factor of 2^3 of integer operand
          emitLeftShiftBy(currentTemporary(), 3);
          emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_DSUBU);
        } else {
          // UINT64STAR_T - UINT64STAR_T
          // pointer arithmetic: (left_term - right_term) / SIZEOFUINT64
          emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_DSUBU);
          emitIFormat(OP_DADDIU, REG_ZR, currentTemporary(), SIZEOFUINT64);
          emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), 0, FCT_DDIVU);
          emitRFormat(OP_SPECIAL, 0, 0, previousTemporary(), FCT_MFLO);

          ltype = UINT64_T;
        }
      } else if (rtype == UINT64STAR_T)
        // UINT64_T - UINT64STAR_T
        syntaxErrorMessage((uint64_t*) "(uint64_t) - (uint64_t*) is undefined");
      else
        // UINT64_T - UINT64_T
        emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_DSUBU);
    }

    tfree(1);
  }

  // assert: allocatedTemporaries == n + 1

  return ltype;
}

uint64_t gr_expression() {
  uint64_t ltype;
  uint64_t operatorSymbol;
  uint64_t rtype;

  // assert: n = allocatedTemporaries

  ltype = gr_simpleExpression();

  // assert: allocatedTemporaries == n + 1

  //optional: ==, !=, <, >, <=, >= simpleExpression
  if (isComparison()) {
    operatorSymbol = symbol;

    getSymbol();

    rtype = gr_simpleExpression();

    // assert: allocatedTemporaries == n + 2

    if (ltype != rtype)
      typeWarning(ltype, rtype);

    if (operatorSymbol == SYM_EQUALITY) {
      // a == b iff unsigned b - a < 1
      emitRFormat(OP_SPECIAL, currentTemporary(), previousTemporary(), previousTemporary(), FCT_DSUBU);
      emitIFormat(OP_DADDIU, REG_ZR, currentTemporary(), 1);
      emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_SLTU);

      tfree(1);

    } else if (operatorSymbol == SYM_NOTEQ) {
      // a != b iff unsigned 0 < b - a
      emitRFormat(OP_SPECIAL, currentTemporary(), previousTemporary(), previousTemporary(), FCT_DSUBU);

      tfree(1);

      emitRFormat(OP_SPECIAL, REG_ZR, currentTemporary(), currentTemporary(), FCT_SLTU);

    } else if (operatorSymbol == SYM_LT) {
      emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_SLTU);

      tfree(1);

    } else if (operatorSymbol == SYM_GT) {
      // a > b iff b < a
      emitRFormat(OP_SPECIAL, currentTemporary(), previousTemporary(), previousTemporary(), FCT_SLTU);

      tfree(1);

    } else if (operatorSymbol == SYM_LEQ) {
      // a <= b iff 1 - (b < a)
      emitRFormat(OP_SPECIAL, currentTemporary(), previousTemporary(), previousTemporary(), FCT_SLTU);
      emitIFormat(OP_DADDIU, REG_ZR, currentTemporary(), 1);
      emitRFormat(OP_SPECIAL, currentTemporary(), previousTemporary(), previousTemporary(), FCT_DSUBU);

      tfree(1);

    } else if (operatorSymbol == SYM_GEQ) {
      // a >= b iff 1 - (a < b)
      emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_SLTU);
      emitIFormat(OP_DADDIU, REG_ZR, currentTemporary(), 1);
      emitRFormat(OP_SPECIAL, currentTemporary(), previousTemporary(), previousTemporary(), FCT_DSUBU);

      tfree(1);
    }
  }

  // assert: allocatedTemporaries == n + 1

  return ltype;
}

void gr_while() {
  uint64_t brBackToWhile;
  uint64_t brForwardToEnd;

  // assert: allocatedTemporaries == 0

  brBackToWhile = binaryLength;

  brForwardToEnd = 0;

  // while ( expression )
  if (symbol == SYM_WHILE) {
    getSymbol();

    if (symbol == SYM_LPARENTHESIS) {
      getSymbol();

      gr_expression();

      // do not know where to branch, fixup later
      brForwardToEnd = binaryLength;

      emitIFormat(OP_BEQ, REG_ZR, currentTemporary(), 0);

      tfree(1);

      if (symbol == SYM_RPARENTHESIS) {
        getSymbol();

        // zero or more statements: { statement }
        if (symbol == SYM_LBRACE) {
          getSymbol();

          while (isNotRbraceOrEOF())
            gr_statement();

          if (symbol == SYM_RBRACE)
            getSymbol();
          else {
            syntaxErrorSymbol(SYM_RBRACE);

            exit(EXITCODE_PARSERERROR);
          }
        }
        // only one statement without {}
        else
          gr_statement();
      } else
        syntaxErrorSymbol(SYM_RPARENTHESIS);
    } else
      syntaxErrorSymbol(SYM_LPARENTHESIS);
  } else
    syntaxErrorSymbol(SYM_WHILE);

  // unconditional branch to beginning of while
  emitIFormat(OP_BEQ, REG_ZR, REG_ZR, (brBackToWhile - binaryLength - INSTRUCTIONSIZE) / INSTRUCTIONSIZE);

  if (brForwardToEnd != 0)
    // first instruction after loop comes here
    // now we have the address for the conditional branch from above
    fixup_relative(brForwardToEnd);

  // assert: allocatedTemporaries == 0

  numberOfWhile = numberOfWhile + 1;
}

void gr_if() {
  uint64_t brForwardToElseOrEnd;
  uint64_t brForwardToEnd;

  // assert: allocatedTemporaries == 0

  // if ( expression )
  if (symbol == SYM_IF) {
    getSymbol();

    if (symbol == SYM_LPARENTHESIS) {
      getSymbol();

      gr_expression();

      // if the "if" case is not true, we branch to "else" (if provided)
      brForwardToElseOrEnd = binaryLength;

      emitIFormat(OP_BEQ, REG_ZR, currentTemporary(), 0);

      tfree(1);

      if (symbol == SYM_RPARENTHESIS) {
        getSymbol();

        // zero or more statements: { statement }
        if (symbol == SYM_LBRACE) {
          getSymbol();

          while (isNotRbraceOrEOF())
            gr_statement();

          if (symbol == SYM_RBRACE)
            getSymbol();
          else {
            syntaxErrorSymbol(SYM_RBRACE);

            exit(EXITCODE_PARSERERROR);
          }
        }
        // only one statement without {}
        else
          gr_statement();

        //optional: else
        if (symbol == SYM_ELSE) {
          getSymbol();

          // if the "if" case was true, we branch to the end
          brForwardToEnd = binaryLength;
          emitIFormat(OP_BEQ, REG_ZR, REG_ZR, 0);

          // if the "if" case was not true, we branch here
          fixup_relative(brForwardToElseOrEnd);

          // zero or more statements: { statement }
          if (symbol == SYM_LBRACE) {
            getSymbol();

            while (isNotRbraceOrEOF())
              gr_statement();

            if (symbol == SYM_RBRACE)
              getSymbol();
            else {
              syntaxErrorSymbol(SYM_RBRACE);

              exit(EXITCODE_PARSERERROR);
            }

          // only one statement without {}
          } else
            gr_statement();

          // if the "if" case was true, we branch here
          fixup_relative(brForwardToEnd);
        } else
          // if the "if" case was not true, we branch here
          fixup_relative(brForwardToElseOrEnd);
      } else
        syntaxErrorSymbol(SYM_RPARENTHESIS);
    } else
      syntaxErrorSymbol(SYM_LPARENTHESIS);
  } else
    syntaxErrorSymbol(SYM_IF);

  // assert: allocatedTemporaries == 0

  numberOfIf = numberOfIf + 1;
}

void gr_return() {
  uint64_t type;

  // assert: allocatedTemporaries == 0

  if (symbol == SYM_RETURN)
    getSymbol();
  else
    syntaxErrorSymbol(SYM_RETURN);

  // optional: expression
  if (symbol != SYM_SEMICOLON) {
    type = gr_expression();

    if (type != returnType)
      typeWarning(returnType, type);

    // save value of expression in return register
    emitRFormat(OP_SPECIAL, REG_ZR, currentTemporary(), REG_V0, FCT_DADDU);

    tfree(1);
  } else if (returnType != VOID_T)
    typeWarning(returnType, VOID_T);

  // unconditional branch to procedure epilogue
  // maintain fixup chain for later fixup
  emitJFormat(OP_J, returnBranches / INSTRUCTIONSIZE);

  // new head of fixup chain
  // offest is two words rather than one because of delay slot NOP
  returnBranches = binaryLength - 2 * INSTRUCTIONSIZE;

  // assert: allocatedTemporaries == 0

  numberOfReturn = numberOfReturn + 1;
}

void gr_statement() {
  uint64_t ltype;
  uint64_t rtype;
  uint64_t* variableOrProcedureName;
  uint64_t* entry;

  // assert: allocatedTemporaries == 0

  while (lookForStatement()) {
    syntaxErrorUnexpected();

    if (symbol == SYM_EOF)
      exit(EXITCODE_PARSERERROR);
    else
      getSymbol();
  }

  // ["*"]
  if (symbol == SYM_ASTERISK) {
    getSymbol();

    // "*" identifier
    if (symbol == SYM_IDENTIFIER) {
      ltype = load_variable(identifier);

      if (ltype != UINT64STAR_T)
        typeWarning(UINT64STAR_T, ltype);

      getSymbol();

      // "*" identifier "="
      if (symbol == SYM_ASSIGN) {
        getSymbol();

        rtype = gr_expression();

        if (rtype != UINT64_T)
          typeWarning(UINT64_T, rtype);

        emitIFormat(OP_SD, previousTemporary(), currentTemporary(), 0);

        tfree(2);

        numberOfAssignments = numberOfAssignments + 1;
      } else {
        syntaxErrorSymbol(SYM_ASSIGN);

        tfree(1);
      }

      if (symbol == SYM_SEMICOLON)
        getSymbol();
      else
        syntaxErrorSymbol(SYM_SEMICOLON);

    // "*" "(" expression ")"
    } else if (symbol == SYM_LPARENTHESIS) {
      getSymbol();

      ltype = gr_expression();

      if (ltype != UINT64STAR_T)
        typeWarning(UINT64STAR_T, ltype);

      if (symbol == SYM_RPARENTHESIS) {
        getSymbol();

        // "*" "(" expression ")" "="
        if (symbol == SYM_ASSIGN) {
          getSymbol();

          rtype = gr_expression();

          if (rtype != UINT64_T)
            typeWarning(UINT64_T, rtype);

          emitIFormat(OP_SD, previousTemporary(), currentTemporary(), 0);

          tfree(2);

          numberOfAssignments = numberOfAssignments + 1;
        } else {
          syntaxErrorSymbol(SYM_ASSIGN);

          tfree(1);
        }

        if (symbol == SYM_SEMICOLON)
          getSymbol();
        else
          syntaxErrorSymbol(SYM_SEMICOLON);
      } else
        syntaxErrorSymbol(SYM_RPARENTHESIS);
    } else
      syntaxErrorSymbol(SYM_LPARENTHESIS);
  }
  // identifier "=" expression | call
  else if (symbol == SYM_IDENTIFIER) {
    variableOrProcedureName = identifier;

    getSymbol();

    // procedure call
    if (symbol == SYM_LPARENTHESIS) {
      getSymbol();

      gr_call(variableOrProcedureName);

      // reset return register to initial return value
      // for missing return expressions
      emitIFormat(OP_DADDIU, REG_ZR, REG_V0, 0);

      if (symbol == SYM_SEMICOLON)
        getSymbol();
      else
        syntaxErrorSymbol(SYM_SEMICOLON);

    // identifier = expression
    } else if (symbol == SYM_ASSIGN) {
      entry = getVariable(variableOrProcedureName);

      ltype = getType(entry);

      getSymbol();

      rtype = gr_expression();

      if (ltype != rtype)
        typeWarning(ltype, rtype);

      emitIFormat(OP_SD, getScope(entry), currentTemporary(), getAddress(entry));

      tfree(1);

      numberOfAssignments = numberOfAssignments + 1;

      if (symbol == SYM_SEMICOLON)
        getSymbol();
      else
        syntaxErrorSymbol(SYM_SEMICOLON);
    } else
      syntaxErrorUnexpected();
  }
  // while statement?
  else if (symbol == SYM_WHILE) {
    gr_while();
  }
  // if statement?
  else if (symbol == SYM_IF) {
    gr_if();
  }
  // return statement?
  else if (symbol == SYM_RETURN) {
    gr_return();

    if (symbol == SYM_SEMICOLON)
      getSymbol();
    else
      syntaxErrorSymbol(SYM_SEMICOLON);
  }
}

uint64_t gr_type() {
  uint64_t type;

  type = UINT64_T;

  if (symbol == SYM_UINT64) {
    getSymbol();

    if (symbol == SYM_ASTERISK) {
      type = UINT64STAR_T;

      getSymbol();
    }
  } else
    syntaxErrorSymbol(SYM_UINT64);

  return type;
}

void gr_variable(uint64_t offset) {
  uint64_t type;

  type = gr_type();

  if (symbol == SYM_IDENTIFIER) {
    // TODO: check if identifier has already been declared
    createSymbolTableEntry(LOCAL_TABLE, identifier, lineNumber, VARIABLE, type, 0, offset);

    getSymbol();
  } else {
    syntaxErrorSymbol(SYM_IDENTIFIER);

    createSymbolTableEntry(LOCAL_TABLE, (uint64_t*) "missing variable name", lineNumber, VARIABLE, type, 0, offset);
  }
}

uint64_t gr_initialization(uint64_t type) {
  uint64_t initialValue;
  uint64_t hasCast;
  uint64_t cast;

  initialValue = 0;

  hasCast = 0;

  if (symbol == SYM_ASSIGN) {
    getSymbol();

    // optional cast: [ cast ]
    if (symbol == SYM_LPARENTHESIS) {
      hasCast = 1;

      getSymbol();

      cast = gr_type();

      if (symbol == SYM_RPARENTHESIS)
        getSymbol();
      else
        syntaxErrorSymbol(SYM_RPARENTHESIS);
    }

    // optional: -
    if (symbol == SYM_MINUS) {
      mayBeINTMIN = 1;

      getSymbol();

      mayBeINTMIN = 0;

      initialValue = -literal;
    } else
      initialValue = literal;

    if (isLiteral())
      getSymbol();
    else
      syntaxErrorUnexpected();

    if (symbol == SYM_SEMICOLON)
      getSymbol();
    else
      syntaxErrorSymbol(SYM_SEMICOLON);
  } else
    syntaxErrorSymbol(SYM_ASSIGN);

  if (hasCast) {
    if (type != cast)
      typeWarning(type, cast);
  } else if (type != UINT64_T)
    typeWarning(type, UINT64_T);

  return initialValue;
}

void gr_procedure(uint64_t* procedure, uint64_t type) {
  uint64_t isUndefined;
  uint64_t numberOfParameters;
  uint64_t parameters;
  uint64_t localVariables;
  uint64_t* entry;

  // assuming procedure is undefined
  isUndefined = 1;

  numberOfParameters = 0;

  // try parsing formal parameters
  if (symbol == SYM_LPARENTHESIS) {
    getSymbol();

    if (symbol != SYM_RPARENTHESIS) {
      gr_variable(0);

      numberOfParameters = 1;

      while (symbol == SYM_COMMA) {
        getSymbol();

        gr_variable(0);

        numberOfParameters = numberOfParameters + 1;
      }

      entry = local_symbol_table;

      parameters = 0;

      while (parameters < numberOfParameters) {
        // 8 bytes offset to skip frame pointer and link
        setAddress(entry, parameters * REGISTERSIZE + 2 * REGISTERSIZE);

        parameters = parameters + 1;

        entry = getNextEntry(entry);
      }

      if (symbol == SYM_RPARENTHESIS)
        getSymbol();
      else
        syntaxErrorSymbol(SYM_RPARENTHESIS);
    } else
      getSymbol();
  } else
    syntaxErrorSymbol(SYM_LPARENTHESIS);

  entry = searchSymbolTable(global_symbol_table, procedure, PROCEDURE);

  if (symbol == SYM_SEMICOLON) {
    // this is a procedure declaration
    if (entry == (uint64_t*) 0)
      // procedure never called nor declared nor defined
      createSymbolTableEntry(GLOBAL_TABLE, procedure, lineNumber, PROCEDURE, type, 0, 0);
    else if (getType(entry) != type)
      // procedure already called, declared, or even defined
      // check return type but otherwise ignore
      typeWarning(getType(entry), type);

    getSymbol();

  } else if (symbol == SYM_LBRACE) {
    // this is a procedure definition
    if (entry == (uint64_t*) 0)
      // procedure never called nor declared nor defined
      createSymbolTableEntry(GLOBAL_TABLE, procedure, lineNumber, PROCEDURE, type, 0, binaryLength);
    else {
      // procedure already called or declared or defined
      if (getAddress(entry) != 0) {
        // procedure already called or defined
        if (getOpcode(loadInstruction(getAddress(entry))) == OP_JAL) {
          // procedure already called but not defined
          fixlink_absolute(getAddress(entry), binaryLength);

          if (stringCompare(procedure, (uint64_t*) "main"))
            // first source containing main procedure provides binary name
            binaryName = sourceName;
        } else
          // procedure already defined
          isUndefined = 0;
      }

      if (isUndefined) {
        // procedure already called or declared but not defined
        setLineNumber(entry, lineNumber);

        if (getType(entry) != type)
          typeWarning(getType(entry), type);

        setType(entry, type);
        setAddress(entry, binaryLength);
      } else {
        // procedure already defined
        printLineNumber((uint64_t*) "warning", lineNumber);
        print((uint64_t*) "redefinition of procedure ");
        print(procedure);
        print((uint64_t*) " ignored");
        println();
      }
    }

    getSymbol();

    localVariables = 0;

    while (symbol == SYM_UINT64) {
      localVariables = localVariables + 1;

      gr_variable(-localVariables * REGISTERSIZE);

      if (symbol == SYM_SEMICOLON)
        getSymbol();
      else
        syntaxErrorSymbol(SYM_SEMICOLON);
    }

    help_procedure_prologue(localVariables);

    // create a fixup chain for return statements
    returnBranches = 0;

    returnType = type;

    while (isNotRbraceOrEOF())
      gr_statement();

    returnType = 0;

    if (symbol == SYM_RBRACE)
      getSymbol();
    else {
      syntaxErrorSymbol(SYM_RBRACE);

      exit(EXITCODE_PARSERERROR);
    }

    fixlink_absolute(returnBranches, binaryLength);

    returnBranches = 0;

    help_procedure_epilogue(numberOfParameters);

  } else
    syntaxErrorUnexpected();

  local_symbol_table = (uint64_t*) 0;

  // assert: allocatedTemporaries == 0
}

void gr_cstar() {
  uint64_t type;
  uint64_t* variableOrProcedureName;
  uint64_t currentLineNumber;
  uint64_t initialValue;
  uint64_t* entry;

  while (symbol != SYM_EOF) {
    while (lookForType()) {
      syntaxErrorUnexpected();

      if (symbol == SYM_EOF)
        exit(EXITCODE_PARSERERROR);
      else
        getSymbol();
    }

    if (symbol == SYM_VOID) {
      // void identifier ...
      // procedure declaration or definition
      type = VOID_T;

      getSymbol();

      if (symbol == SYM_IDENTIFIER) {
        variableOrProcedureName = identifier;

        getSymbol();

        gr_procedure(variableOrProcedureName, type);
      } else
        syntaxErrorSymbol(SYM_IDENTIFIER);
    } else {
      type = gr_type();

      if (symbol == SYM_IDENTIFIER) {
        variableOrProcedureName = identifier;

        getSymbol();

        if (symbol == SYM_LPARENTHESIS)
          // type identifier "(" ...
          // procedure declaration or definition
          gr_procedure(variableOrProcedureName, type);
        else {
          currentLineNumber = lineNumber;

          if (symbol == SYM_SEMICOLON) {
            // type identifier ";" ...
            // global variable declaration
            getSymbol();

            initialValue = 0;
          } else
            // type identifier "=" ...
            // global variable definition
            initialValue = gr_initialization(type);

          entry = searchSymbolTable(global_symbol_table, variableOrProcedureName, VARIABLE);

          if (entry == (uint64_t*) 0) {
            allocatedMemory = allocatedMemory + REGISTERSIZE;

            createSymbolTableEntry(GLOBAL_TABLE, variableOrProcedureName, currentLineNumber, VARIABLE, type, initialValue, -allocatedMemory);
          } else {
            // global variable already declared or defined
            printLineNumber((uint64_t*) "warning", currentLineNumber);
            print((uint64_t*) "redefinition of global variable ");
            print(variableOrProcedureName);
            print((uint64_t*) " ignored");
            println();
          }
        }
      } else
        syntaxErrorSymbol(SYM_IDENTIFIER);
    }
  }
}

// -----------------------------------------------------------------
// ------------------------ MACHINE CODE LIBRARY -------------------
// -----------------------------------------------------------------

void emitLeftShiftBy(uint64_t reg, uint64_t b) {
  // assert: 0 <= b < 15

  // load multiplication factor less than 2^15 to avoid sign extension
  emitIFormat(OP_DADDIU, REG_ZR, nextTemporary(), twoToThePowerOf(b));
  emitRFormat(OP_SPECIAL, reg, nextTemporary(), 0, FCT_DMULTU);
  emitRFormat(OP_SPECIAL, 0, 0, reg, FCT_MFLO);
}

void emitMainEntry() {
  uint64_t i;

  // the instruction at address zero cannot be fixed up
  // we therefore need at least one not-to-be-fixed-up instruction here

  // we generate NOPs to accommodate GP and SP register
  // initialization code that overwrites the NOPs later
  // when binaryLength is known

  i = 0;

  // 26 NOPs per register is enough for initialization
  // since we load integers 0 <= n < 2^64 which take
  // no more than 26 instructions each, see load_integer
  while (i < 52) {
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_NOP);

    i = i + 1;
  }

  mainJump = binaryLength;

  createSymbolTableEntry(GLOBAL_TABLE, (uint64_t*) "main", 0, PROCEDURE, UINT64_T, 0, mainJump);

  // jump and link to main, will return here only if there is no exit call
  emitJFormat(OP_JAL, 0);

  // we exit with exit code in return register pushed onto the stack
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, -REGISTERSIZE);
  emitIFormat(OP_SD, REG_SP, REG_V0, 0);

  // no need to reset return register here
}

void bootstrapCode() {
  uint64_t savedBinaryLength;

  savedBinaryLength = binaryLength;

  binaryLength = 0;

  // assert: allocatedTemporaries == 0

  load_integer(savedBinaryLength);

  // load binaryLength into GP register
  emitIFormat(OP_DADDIU, currentTemporary(), REG_GP, 0);

  tfree(1);

  // assert: allocatedTemporaries == 0

  // initial stack pointer is stored at highest virtual address
  load_integer(VIRTUALMEMORYSIZE - REGISTERSIZE);

  // load initial stack pointer into SP register
  emitIFormat(OP_LD, currentTemporary(), REG_SP, 0);

  tfree(1);

  // assert: allocatedTemporaries == 0

  binaryLength = savedBinaryLength;

  if (reportUndefinedProcedures())
    // rather than jump and link to the main procedure
    // exit by continuing to the next instruction (with delay slot)
    fixup_absolute(mainJump, mainJump + 2 * INSTRUCTIONSIZE);

  mainJump = 0;
}

// -----------------------------------------------------------------
// --------------------------- COMPILER ----------------------------
// -----------------------------------------------------------------

void selfie_compile() {
  uint64_t link;
  uint64_t numberOfSourceFiles;

  // link until next console option
  link = 1;

  numberOfSourceFiles = 0;

  sourceName = (uint64_t*) "library";

  binaryName = sourceName;

  // allocate memory for storing binary
  binary       = smalloc(maxBinaryLength);
  binaryLength = 0;

  // reset code length
  codeLength = 0;

  // allocate zeroed memory for storing source code line numbers
  sourceLineNumber = zalloc(maxBinaryLength / INSTRUCTIONSIZE * SIZEOFUINT64);

  resetSymbolTables();

  // jump and link to main
  emitMainEntry();

  // library:
  // exit must be first to exit main
  // if exit call in main is missing
  emitExit();
  emitRead();
  emitWrite();
  emitOpen();
  emitMalloc();

  emitSwitch();

  while (link) {
    if (numberOfRemainingArguments() == 0)
      link = 0;
    else if (loadCharacter(peekArgument(), 0) == '-')
      link = 0;
    else {
      sourceName = getArgument();

      numberOfSourceFiles = numberOfSourceFiles + 1;

      print(selfieName);
      print((uint64_t*) ": this is selfie compiling ");
      print(sourceName);
      print((uint64_t*) " with starc");
      println();

      // assert: sourceName is mapped and not longer than maxFilenameLength

      sourceFD = signExtend(open(sourceName, O_RDONLY, 0), INT_BITWIDTH);

      if (signedLessThan(sourceFD, 0)) {
        print(selfieName);
        print((uint64_t*) ": could not open input file ");
        print(sourceName);
        println();

        exit(EXITCODE_IOERROR);
      }

      resetScanner();
      resetParser();

      // compile
      gr_cstar();

      print(selfieName);
      print((uint64_t*) ": ");
      printInteger(numberOfReadCharacters);
      print((uint64_t*) " characters read in ");
      printInteger(lineNumber - 1);
      print((uint64_t*) " lines and ");
      printInteger(numberOfComments);
      print((uint64_t*) " comments");
      println();

      print(selfieName);
      print((uint64_t*) ": with ");
      printInteger(numberOfReadCharacters - numberOfIgnoredCharacters);
      print((uint64_t*) "(");
      printFixedPointPercentage(numberOfReadCharacters, numberOfReadCharacters - numberOfIgnoredCharacters);
      print((uint64_t*) "%) characters in ");
      printInteger(numberOfScannedSymbols);
      print((uint64_t*) " actual symbols");
      println();

      print(selfieName);
      print((uint64_t*) ": ");
      printInteger(numberOfGlobalVariables);
      print((uint64_t*) " global variables, ");
      printInteger(numberOfProcedures);
      print((uint64_t*) " procedures, ");
      printInteger(numberOfStrings);
      print((uint64_t*) " string literals");
      println();

      print(selfieName);
      print((uint64_t*) ": ");
      printInteger(numberOfCalls);
      print((uint64_t*) " calls, ");
      printInteger(numberOfAssignments);
      print((uint64_t*) " assignments, ");
      printInteger(numberOfWhile);
      print((uint64_t*) " while, ");
      printInteger(numberOfIf);
      print((uint64_t*) " if, ");
      printInteger(numberOfReturn);
      print((uint64_t*) " return");
      println();
    }
  }

  if (numberOfSourceFiles == 0) {
    print(selfieName);
    print((uint64_t*) ": nothing to compile, only library generated");
    println();
  }

  emitGlobalsStrings();

  bootstrapCode();

  print(selfieName);
  print((uint64_t*) ": ");
  printInteger(binaryLength + DOUBLEWORDSIZE);
  print((uint64_t*) " bytes generated with ");
  printInteger(codeLength / INSTRUCTIONSIZE);
  print((uint64_t*) " instructions and ");
  printInteger(binaryLength - codeLength + DOUBLEWORDSIZE);
  print((uint64_t*) " bytes of data");
  println();
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- REGISTER ---------------------------
// -----------------------------------------------------------------

void printRegister(uint64_t reg) {
  print((uint64_t*) *(REGISTERS + reg));
}

// -----------------------------------------------------------------
// ---------------------------- ENCODER ----------------------------
// -----------------------------------------------------------------

// -----------------------------------------------------------------
// 32 bit
//
// +------+-----+-----+-----+-----+------+
// |opcode| rs  | rt  | rd  |00000|fction|
// +------+-----+-----+-----+-----+------+
//    6      5     5     5     5     6
uint64_t encodeRFormat(uint64_t opcode, uint64_t rs, uint64_t rt, uint64_t rd, uint64_t function) {
  // assert: 0 <= opcode < 2^6
  // assert: 0 <= rs < 2^5
  // assert: 0 <= rt < 2^5
  // assert: 0 <= rd < 2^5
  // assert: 0 <= function < 2^6
  return leftShift(leftShift(leftShift(leftShift(opcode, 5) + rs, 5) + rt, 5) + rd, 11) + function;
}

// -----------------------------------------------------------------
// 32 bit
//
// +------+-----+-----+----------------+
// |opcode| rs  | rt  |   immediate    |
// +------+-----+-----+----------------+
//    6      5     5          16
uint64_t encodeIFormat(uint64_t opcode, uint64_t rs, uint64_t rt, uint64_t immediate) {
  // assert: 0 <= opcode < 2^6
  // assert: 0 <= rs < 2^5
  // assert: 0 <= rt < 2^5
  // assert: -2^15 <= immediate < 2^15

  // convert from 64-bit to 16-bit two's complement
  immediate = rightShift(leftShift(immediate, 16 + 32), 16 + 32);

  return leftShift(leftShift(leftShift(opcode, 5) + rs, 5) + rt, 16) + immediate;
}

// --------------------------------------------------------------
// 32 bit
//
// +------+--------------------------+
// |opcode|       instr_index        |
// +------+--------------------------+
//    6                26
uint64_t encodeJFormat(uint64_t opcode, uint64_t instr_index) {
  // assert: 0 <= opcode < 2^6
  // assert: 0 <= instr_index < 2^26
  return leftShift(opcode, 26) + instr_index;
}

// -----------------------------------------------------------------
// ---------------------------- DECODER ----------------------------
// -----------------------------------------------------------------

uint64_t getOpcode(uint64_t instruction) {
  return rightShift(leftShift(instruction, 32), 26 + 32);
}

uint64_t getRS(uint64_t instruction) {
  return rightShift(leftShift(instruction, 6 + 32), 27 + 32);
}

uint64_t getRT(uint64_t instruction) {
  return rightShift(leftShift(instruction, 11 + 32), 27 + 32);
}

uint64_t getRD(uint64_t instruction) {
  return rightShift(leftShift(instruction, 16 + 32), 27 + 32);
}

uint64_t getFunction(uint64_t instruction) {
  return rightShift(leftShift(instruction, 26 + 32), 26 + 32);
}

uint64_t getImmediate(uint64_t instruction) {
  return rightShift(leftShift(instruction, 16 + 32), 16 + 32);
}

uint64_t getInstrIndex(uint64_t instruction) {
  return rightShift(leftShift(instruction, 6 + 32), 6 + 32);
}

uint64_t signExtend(uint64_t immediate, uint64_t bits) {
  // sign-extend from n-bits to 64-bit two's complement
  if (immediate < twoToThePowerOf(bits - 1))
    return immediate;
  else
    return immediate - twoToThePowerOf(bits);
}

// --------------------------------------------------------------
// 32 bit
//
// +------+-----+-----+-----+-----+------+
// |opcode| rs  | rt  | rd  |00000|fction|
// +------+-----+-----+-----+-----+------+
//    6      5     5     5     5     6
void decodeRFormat() {
  rs          = getRS(ir);
  rt          = getRT(ir);
  rd          = getRD(ir);
  immediate   = 0;
  function    = getFunction(ir);
  instr_index = 0;
}

// --------------------------------------------------------------
// 32 bit
//
// +------+-----+-----+----------------+
// |opcode| rs  | rt  |   immediate    |
// +------+-----+-----+----------------+
//    6      5     5          16
void decodeIFormat() {
  rs          = getRS(ir);
  rt          = getRT(ir);
  rd          = 0;
  immediate   = getImmediate(ir);
  function    = 0;
  instr_index = 0;
}

// --------------------------------------------------------------
// 32 bit
//
// +------+--------------------------+
// |opcode|       instr_index        |
// +------+--------------------------+
//    6                26
void decodeJFormat() {
  rs          = 0;
  rt          = 0;
  rd          = 0;
  immediate   = 0;
  function    = 0;
  instr_index = getInstrIndex(ir);
}

void decode() {
  opcode = getOpcode(ir);

  if (opcode == 0)
    decodeRFormat();
  else if (opcode == OP_JAL)
    decodeJFormat();
  else if (opcode == OP_J)
    decodeJFormat();
  else
    decodeIFormat();
}

void printOpcode(uint64_t opcode) {
  print((uint64_t*) *(OPCODES + opcode));
}

void printFunction(uint64_t function) {
  print((uint64_t*) *(FUNCTIONS + function));
}

// -----------------------------------------------------------------
// ----------------------------- CODE ------------------------------
// -----------------------------------------------------------------

uint64_t loadInstruction(uint64_t baddr) {
  if (baddr % REGISTERSIZE == 0)
    return getHighWord(*(binary + baddr / SIZEOFUINT64));
  else
    return getLowWord(*(binary + baddr / SIZEOFUINT64));
}

void storeInstruction(uint64_t baddr, uint64_t instruction) {
  uint64_t temp;

  if (baddr >= maxBinaryLength) {
    syntaxErrorMessage((uint64_t*) "maximum binary length exceeded");

    exit(EXITCODE_COMPILERERROR);
  }

  temp = *(binary + baddr / SIZEOFUINT64);

  if (baddr % SIZEOFUINT64 == 0)
    // replace high word
    temp = leftShift(instruction, 32) + rightShift(leftShift(temp, 32), 32);
  else
    // replace low word
    temp = instruction + leftShift(rightShift(temp, 32), 32);

  *(binary + baddr / SIZEOFUINT64) = temp;
}

uint64_t loadData(uint64_t baddr) {
  return *(binary + baddr / SIZEOFUINT64);
}

void storeData(uint64_t baddr, uint64_t data) {
  if (baddr >= maxBinaryLength) {
    syntaxErrorMessage((uint64_t*) "maximum binary length exceeded");

    exit(EXITCODE_COMPILERERROR);
  }

  *(binary + baddr / SIZEOFUINT64) = data;
}

void emitInstruction(uint64_t instruction) {
  storeInstruction(binaryLength, instruction);

  if (*(sourceLineNumber + binaryLength / INSTRUCTIONSIZE) == 0)
    *(sourceLineNumber + binaryLength / INSTRUCTIONSIZE) = lineNumber;

  binaryLength = binaryLength + INSTRUCTIONSIZE;
}

void emitRFormat(uint64_t opcode, uint64_t rs, uint64_t rt, uint64_t rd, uint64_t function) {
  emitInstruction(encodeRFormat(opcode, rs, rt, rd, function));

  if (opcode == OP_SPECIAL) {
    if (function == FCT_JR)
      emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_NOP); // delay slot
    else if (function == FCT_MFLO) {
      // In MIPS I-III two instructions after MFLO/MFHI
      // must not modify the LO/HI registers
      emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_NOP); // pipeline delay
      emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_NOP); // pipeline delay
    } else if (function == FCT_MFHI) {
      emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_NOP); // pipeline delay
      emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_NOP); // pipeline delay
    }
  }
}

void emitIFormat(uint64_t opcode, uint64_t rs, uint64_t rt, uint64_t immediate) {
  emitInstruction(encodeIFormat(opcode, rs, rt, immediate));

  if (opcode == OP_BEQ)
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_NOP); // delay slot
}

void emitJFormat(uint64_t opcode, uint64_t instr_index) {
  emitInstruction(encodeJFormat(opcode, instr_index));

  emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_NOP); // delay slot
}

void fixup_relative(uint64_t fromAddress) {
  uint64_t instruction;

  instruction = loadInstruction(fromAddress);

  storeInstruction(fromAddress,
    encodeIFormat(getOpcode(instruction),
      getRS(instruction),
      getRT(instruction),
      (binaryLength - fromAddress - INSTRUCTIONSIZE) / INSTRUCTIONSIZE));
}

void fixup_absolute(uint64_t fromAddress, uint64_t toAddress) {
  storeInstruction(fromAddress,
    encodeJFormat(getOpcode(loadInstruction(fromAddress)), toAddress / INSTRUCTIONSIZE));
}

void fixlink_absolute(uint64_t fromAddress, uint64_t toAddress) {
  uint64_t previousAddress;

  while (fromAddress != 0) {
    previousAddress = getInstrIndex(loadInstruction(fromAddress)) * INSTRUCTIONSIZE;

    fixup_absolute(fromAddress, toAddress);

    fromAddress = previousAddress;
  }
}

uint64_t copyStringToBinary(uint64_t* s, uint64_t baddr) {
  uint64_t next;

  next = baddr + roundUp(stringLength(s) + 1, SIZEOFUINT64);

  while (baddr < next) {
    storeData(baddr, *s);

    s = s + 1;

    baddr = baddr + SIZEOFUINT64;
  }

  return next;
}

void emitGlobalsStrings() {
  uint64_t* entry;

  // align data section for register access
  if (binaryLength % REGISTERSIZE != 0)
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_NOP);

  codeLength = binaryLength;

  entry = global_symbol_table;

  // assert: n = binaryLength

  // allocate space for global variables and copy strings
  while ((uint64_t) entry != 0) {
    if (getClass(entry) == VARIABLE) {
      storeData(binaryLength, getValue(entry));

      binaryLength = binaryLength + REGISTERSIZE;
    } else if (getClass(entry) == STRING)
      binaryLength = copyStringToBinary(getString(entry), binaryLength);

    entry = getNextEntry(entry);
  }

  // assert: binaryLength == n + allocatedMemory

  allocatedMemory = 0;
}

uint64_t openWriteOnly(uint64_t* name) {
  // we try opening write-only files using platform-specific flags
  // to make selfie platform-independent, this may nevertheless
  // not always work and require intervention
  uint64_t fd;

  // try Mac flags
  fd = signExtend(open(name, MAC_O_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH), INT_BITWIDTH);

  if (signedLessThan(fd, 0)) {
    // try Linux flags
    fd = signExtend(open(name, LINUX_O_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH), INT_BITWIDTH);

    if (signedLessThan(fd, 0))
      // try Windows flags
      fd = signExtend(open(name, WINDOWS_O_BINARY_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH), INT_BITWIDTH);
  }

  return fd;
}

void selfie_output() {
  uint64_t fd;

  binaryName = getArgument();

  if (binaryLength == 0) {
    print(selfieName);
    print((uint64_t*) ": nothing to emit to output file ");
    print(binaryName);
    println();

    return;
  }

  // assert: binaryName is mapped and not longer than maxFilenameLength

  fd = openWriteOnly(binaryName);

  if (signedLessThan(fd, 0)) {
    print(selfieName);
    print((uint64_t*) ": could not create binary output file ");
    print(binaryName);
    println();

    exit(EXITCODE_IOERROR);
  }

  *binary_buffer = codeLength;

  // assert: binary_buffer is mapped

  // first write code length
  write(fd, binary_buffer, SIZEOFUINT64);

  // assert: binary is mapped

  // then write binary
  write(fd, binary, binaryLength);

  print(selfieName);
  print((uint64_t*) ": ");
  printInteger(binaryLength + DOUBLEWORDSIZE);
  print((uint64_t*) " bytes with ");
  printInteger(codeLength / INSTRUCTIONSIZE);
  print((uint64_t*) " instructions and ");
  printInteger(binaryLength - codeLength + DOUBLEWORDSIZE);
  print((uint64_t*) " bytes of data written into ");
  print(binaryName);
  println();
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
  uint64_t numberOfReadBytes;

  binaryName = getArgument();

  // assert: binaryName is mapped and not longer than maxFilenameLength

  fd = signExtend(open(binaryName, O_RDONLY, 0), INT_BITWIDTH);

  if (signedLessThan(fd, 0)) {
    print(selfieName);
    print((uint64_t*) ": could not open input file ");
    print(binaryName);
    println();

    exit(EXITCODE_IOERROR);
  }

  // make sure binary is mapped
  binary = touch(smalloc(maxBinaryLength), maxBinaryLength);

  binaryLength = 0;
  codeLength   = 0;

  // no source line numbers in binaries
  sourceLineNumber = (uint64_t*) 0;

  // assert: binary_buffer is mapped

  // read code length first
  numberOfReadBytes = read(fd, binary_buffer, SIZEOFUINT64);

  if (numberOfReadBytes == SIZEOFUINT64) {
    codeLength = *binary_buffer;

    if (codeLength <= maxBinaryLength) {
      // assert: binary is mapped

      // now read binary including global variables and strings
      numberOfReadBytes = signExtend(read(fd, binary, maxBinaryLength), INT_BITWIDTH);

      if (signedGreaterThan(numberOfReadBytes, 0)) {
        binaryLength = numberOfReadBytes;

        // check if we are really at EOF
        if (read(fd, binary_buffer, SIZEOFUINT64) == 0) {
          print(selfieName);
          print((uint64_t*) ": ");
          printInteger(binaryLength + DOUBLEWORDSIZE);
          print((uint64_t*) " bytes with ");
          printInteger(codeLength / INSTRUCTIONSIZE);
          print((uint64_t*) " instructions and ");
          printInteger(binaryLength - codeLength + DOUBLEWORDSIZE);
          print((uint64_t*) " bytes of data loaded from ");
          print(binaryName);
          println();

          return;
        }
      }
    }
  }

  print(selfieName);
  print((uint64_t*) ": failed to load code from input file ");
  print(binaryName);
  println();

  exit(EXITCODE_IOERROR);
}

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emitExit() {
  createSymbolTableEntry(LIBRARY_TABLE, (uint64_t*) "exit", 0, PROCEDURE, VOID_T, 0, binaryLength);

  // load argument for exit
  emitIFormat(OP_LD, REG_SP, REG_A0, 0); // exit code

  // remove the argument from the stack
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, REGISTERSIZE);

  // load the correct syscall number and invoke syscall
  emitIFormat(OP_DADDIU, REG_ZR, REG_V0, SYSCALL_EXIT);
  emitRFormat(0, 0, 0, 0, FCT_SYSCALL);

  // never returns here
}

void implementExit(uint64_t* context) {
  setExitCode(context, signShrink(*(getRegs(context)+REG_A0), INT_BITWIDTH));

  print(selfieName);
  print((uint64_t*) ": ");
  print(getName(context));
  print((uint64_t*) " exiting with exit code ");
  printInteger(signExtend(getExitCode(context), INT_BITWIDTH));
  print((uint64_t*) " and ");
  printFixedPointRatio(getProgramBreak(context) - maxBinaryLength, MEGABYTE);
  print((uint64_t*) "MB of mallocated memory");
  println();
}

void emitRead() {
  createSymbolTableEntry(LIBRARY_TABLE, (uint64_t*) "read", 0, PROCEDURE, UINT64_T, 0, binaryLength);

  emitIFormat(OP_LD, REG_SP, REG_A2, 0); // size
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, REGISTERSIZE);

  emitIFormat(OP_LD, REG_SP, REG_A1, 0); // *buffer
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, REGISTERSIZE);

  emitIFormat(OP_LD, REG_SP, REG_A0, 0); // fd
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, REGISTERSIZE);

  emitIFormat(OP_DADDIU, REG_ZR, REG_V0, SYSCALL_READ);
  emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

  // jump back to caller, return value is in REG_V0
  emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

void implementRead(uint64_t* context) {
  uint64_t size;
  uint64_t vaddr;
  uint64_t fd;
  uint64_t readTotal;
  uint64_t bytesToRead;
  uint64_t* buffer;
  uint64_t actuallyRead;
  uint64_t failed;

  // assert: read buffer is mapped

  size  = *(getRegs(context)+REG_A2);
  vaddr = *(getRegs(context)+REG_A1);
  fd    = *(getRegs(context)+REG_A0);

  if (debug_read) {
    print(selfieName);
    print((uint64_t*) ": trying to read ");
    printInteger(size);
    print((uint64_t*) " bytes from file with descriptor ");
    printInteger(fd);
    print((uint64_t*) " into buffer at virtual address ");
    printHexadecimal(vaddr, 8);
    println();
  }

  readTotal   = 0;
  bytesToRead = SIZEOFUINT64;

  failed = 0;

  while (size > 0) {
    if (isValidVirtualAddress(vaddr)) {
      if (isVirtualAddressMapped(getPT(context), vaddr)) {
        buffer = tlb(getPT(context), vaddr);

        if (size < bytesToRead)
          bytesToRead = size;

        actuallyRead = signExtend(read(fd, buffer, bytesToRead), INT_BITWIDTH);

        if (actuallyRead == bytesToRead) {
          readTotal = readTotal + actuallyRead;

          size = size - actuallyRead;

          if (size > 0)
            vaddr = vaddr + SIZEOFUINT64;
        } else {
          if (signedGreaterThan(actuallyRead, 0))
            readTotal = readTotal + actuallyRead;

          size = 0;
        }
      } else {
        failed = 1;

        size = 0;

        if (debug_read) {
          print(selfieName);
          print((uint64_t*) ": reading into virtual address ");
          printHexadecimal(vaddr, 8);
          print((uint64_t*) " failed because the address is unmapped");
          println();
        }
      }
    } else {
      failed = 1;

      size = 0;

      if (debug_read) {
        print(selfieName);
        print((uint64_t*) ": reading into virtual address ");
        printHexadecimal(vaddr, 8);
        print((uint64_t*) " failed because the address is invalid");
        println();
      }
    }
  }

  if (failed == 0)
    *(getRegs(context)+REG_V0) = readTotal;
  else
    *(getRegs(context)+REG_V0) = signShrink(-1, INT_BITWIDTH);

  if (debug_read) {
    print(selfieName);
    print((uint64_t*) ": actually read ");
    printInteger(readTotal);
    print((uint64_t*) " bytes from file with descriptor ");
    printInteger(fd);
    println();
  }
}

void emitWrite() {
  createSymbolTableEntry(LIBRARY_TABLE, (uint64_t*) "write", 0, PROCEDURE, UINT64_T, 0, binaryLength);

  emitIFormat(OP_LD, REG_SP, REG_A2, 0); // size
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, REGISTERSIZE);

  emitIFormat(OP_LD, REG_SP, REG_A1, 0); // *buffer
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, REGISTERSIZE);

  emitIFormat(OP_LD, REG_SP, REG_A0, 0); // fd
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, REGISTERSIZE);

  emitIFormat(OP_DADDIU, REG_ZR, REG_V0, SYSCALL_WRITE);
  emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

  emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

void implementWrite(uint64_t* context) {
  uint64_t size;
  uint64_t vaddr;
  uint64_t fd;
  uint64_t writtenTotal;
  uint64_t bytesToWrite;
  uint64_t* buffer;
  uint64_t actuallyWritten;
  uint64_t failed;

  // assert: write buffer is mapped

  size  = *(getRegs(context)+REG_A2);
  vaddr = *(getRegs(context)+REG_A1);
  fd    = *(getRegs(context)+REG_A0);

  if (debug_write) {
    print(selfieName);
    print((uint64_t*) ": trying to write ");
    printInteger(size);
    print((uint64_t*) " bytes from buffer at virtual address ");
    printHexadecimal(vaddr, 8);
    print((uint64_t*) " into file with descriptor ");
    printInteger(fd);
    println();
  }

  writtenTotal = 0;
  bytesToWrite = SIZEOFUINT64;

  failed = 0;

  while (size > 0) {
    if (isValidVirtualAddress(vaddr)) {
      if (isVirtualAddressMapped(getPT(context), vaddr)) {
        buffer = tlb(getPT(context), vaddr);

        if (size < bytesToWrite)
          bytesToWrite = size;

        actuallyWritten = signExtend(write(fd, buffer, bytesToWrite), INT_BITWIDTH);

        if (actuallyWritten == bytesToWrite) {
          writtenTotal = writtenTotal + actuallyWritten;

          size = size - actuallyWritten;

          if (size > 0)
            vaddr = vaddr + SIZEOFUINT64;
        } else {
          if (signedGreaterThan(actuallyWritten, 0))
            writtenTotal = writtenTotal + actuallyWritten;

          size = 0;
        }
      } else {
        failed = 1;

        size = 0;

        if (debug_write) {
          print(selfieName);
          print((uint64_t*) ": writing into virtual address ");
          printHexadecimal(vaddr, 8);
          print((uint64_t*) " failed because the address is unmapped");
          println();
        }
      }
    } else {
      failed = 1;

      size = 0;

      if (debug_write) {
        print(selfieName);
        print((uint64_t*) ": writing into virtual address ");
        printHexadecimal(vaddr, 8);
        print((uint64_t*) " failed because the address is invalid");
        println();
      }
    }
  }

  if (failed == 0)
    *(getRegs(context)+REG_V0) = writtenTotal;
  else
    *(getRegs(context)+REG_V0) = signShrink(-1, INT_BITWIDTH);

  if (debug_write) {
    print(selfieName);
    print((uint64_t*) ": actually wrote ");
    printInteger(writtenTotal);
    print((uint64_t*) " bytes into file with descriptor ");
    printInteger(fd);
    println();
  }
}

void emitOpen() {
  createSymbolTableEntry(LIBRARY_TABLE, (uint64_t*) "open", 0, PROCEDURE, UINT64_T, 0, binaryLength);

  emitIFormat(OP_LD, REG_SP, REG_A2, 0); // mode
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, REGISTERSIZE);

  emitIFormat(OP_LD, REG_SP, REG_A1, 0); // flags
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, REGISTERSIZE);

  emitIFormat(OP_LD, REG_SP, REG_A0, 0); // filename
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, REGISTERSIZE);

  emitIFormat(OP_DADDIU, REG_ZR, REG_V0, SYSCALL_OPEN);
  emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

  emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

uint64_t down_loadString(uint64_t* table, uint64_t vaddr, uint64_t* s) {
  uint64_t i;
  uint64_t j;
  uint64_t* paddr;

  i = 0;

  while (i < maxFilenameLength / SIZEOFUINT64) {
    if (isValidVirtualAddress(vaddr)) {
      if (isVirtualAddressMapped(table, vaddr)) {
        paddr = tlb(table, vaddr);

        *(s + i) = loadPhysicalMemory(paddr);

        j = 0;

        while (j < SIZEOFUINT64) {
          if (loadCharacter(paddr, j) == 0)
            return 1;

          j = j + 1;
        }

        vaddr = vaddr + SIZEOFUINT64;

        i = i + 1;
      } else {
        if (debug_open) {
          print(selfieName);
          print((uint64_t*) ": opening file with name at virtual address ");
          printHexadecimal(vaddr, 8);
          print((uint64_t*) " failed because the address is unmapped");
          println();
        }
      }
    } else {
      if (debug_open) {
        print(selfieName);
        print((uint64_t*) ": opening file with name at virtual address ");
        printHexadecimal(vaddr, 8);
        print((uint64_t*) " failed because the address is invalid");
        println();
      }
    }
  }

  return 0;
}

void implementOpen(uint64_t* context) {
  uint64_t mode;
  uint64_t flags;
  uint64_t vaddr;
  uint64_t fd;

  mode  = *(getRegs(context)+REG_A2);
  flags = *(getRegs(context)+REG_A1);
  vaddr = *(getRegs(context)+REG_A0);

  if (down_loadString(getPT(context), vaddr, filename_buffer)) {
    fd = open(filename_buffer, flags, mode);

    *(getRegs(context)+REG_V0) = fd;

    if (debug_open) {
      print(selfieName);
      print((uint64_t*) ": opened file ");
      printString(filename_buffer);
      print((uint64_t*) " with flags ");
      printHexadecimal(flags, 0);
      print((uint64_t*) " and mode ");
      printOctal(mode, 0);
      print((uint64_t*) " returning file descriptor ");
      printInteger(fd);
      println();
    }
  } else {
    *(getRegs(context)+REG_V0) = signShrink(-1, INT_BITWIDTH);

    if (debug_open) {
      print(selfieName);
      print((uint64_t*) ": opening file with name at virtual address ");
      printHexadecimal(vaddr, 8);
      print((uint64_t*) " failed because the name is too long");
      println();
    }
  }
}

void emitMalloc() {
  createSymbolTableEntry(LIBRARY_TABLE, (uint64_t*) "malloc", 0, PROCEDURE, UINT64STAR_T, 0, binaryLength);

  // on boot levels higher than zero, zalloc falls back to malloc
  // assuming that page frames are zeroed on boot level zero
  createSymbolTableEntry(LIBRARY_TABLE, (uint64_t*) "zalloc", 0, PROCEDURE, UINT64STAR_T, 0, binaryLength);

  emitIFormat(OP_LD, REG_SP, REG_A0, 0); // size
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, REGISTERSIZE);

  emitIFormat(OP_DADDIU, REG_ZR, REG_V0, SYSCALL_MALLOC);
  emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

  emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

uint64_t implementMalloc(uint64_t* context) {
  uint64_t size;
  uint64_t bump;
  uint64_t stackptr;

  if (debug_malloc) {
    print(selfieName);
    print((uint64_t*) ": trying to malloc ");
    printInteger(*(getRegs(context)+REG_A0));
    print((uint64_t*) " bytes");
    println();
  }

  size = roundUp(*(getRegs(context)+REG_A0), SIZEOFUINT64);

  bump = getProgramBreak(context);

  stackptr = *(getRegs(context)+REG_SP);

  if (size > stackptr - bump) {
    setExitCode(context, EXITCODE_OUTOFVIRTUALMEMORY);

    return EXIT;
  } else {
    *(getRegs(context)+REG_V0) = bump;

    setProgramBreak(context, bump + size);

    if (debug_malloc) {
      print(selfieName);
      print((uint64_t*) ": actually mallocating ");
      printInteger(size);
      print((uint64_t*) " bytes at virtual address ");
      printHexadecimal(bump, 8);
      println();
    }

    return DONOTEXIT;
  }
}

// -----------------------------------------------------------------
// ----------------------- HYPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emitSwitch() {
  createSymbolTableEntry(LIBRARY_TABLE, (uint64_t*) "hypster_switch", 0, PROCEDURE, UINT64STAR_T, 0, binaryLength);

  emitIFormat(OP_LD, REG_SP, REG_A1, 0); // number of instructions to execute
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, REGISTERSIZE);

  emitIFormat(OP_LD, REG_SP, REG_A0, 0); // context to which we switch
  emitIFormat(OP_DADDIU, REG_SP, REG_SP, REGISTERSIZE);

  emitIFormat(OP_DADDIU, REG_ZR, REG_V0, SYSCALL_SWITCH);
  emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

  // save context from which we are switching here in return register
  emitRFormat(OP_SPECIAL, REG_ZR, REG_V1, REG_V0, FCT_DADDU);

  emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

void doSwitch(uint64_t* toContext, uint64_t timeout) {
  uint64_t* fromContext;

  fromContext = currentContext;

  restoreContext(toContext);

  // restore machine state
  pc        = getPC(toContext);
  registers = getRegs(toContext);
  loReg     = getLoReg(toContext);
  hiReg     = getHiReg(toContext);
  pt        = getPT(toContext);

  // use REG_V1 instead of REG_V0 to avoid race condition with interrupt
  if (getParent(fromContext) != MY_CONTEXT)
    *(registers+REG_V1) = (uint64_t) getVirtualContext(fromContext);
  else
    *(registers+REG_V1) = (uint64_t) fromContext;

  currentContext = toContext;

  timer = timeout;

  if (debug_switch) {
    print(selfieName);
    print((uint64_t*) ": switched from context ");
    printHexadecimal((uint64_t) fromContext, 8);
    print((uint64_t*) " to context ");
    printHexadecimal((uint64_t) toContext, 8);
    if (signedGreaterThan(timeout, -1)) {
      print((uint64_t*) " to execute ");
      printInteger(timeout);
      print((uint64_t*) " instructions");
    }
    println();
  }
}

void implementSwitch() {
  saveContext(currentContext);

  // cache context on my boot level before switching
  doSwitch(cacheContext((uint64_t*) *(registers+REG_A0)), *(registers+REG_A1));
}

uint64_t* mipster_switch(uint64_t* toContext, uint64_t timeout) {
  doSwitch(toContext, timeout);

  runUntilException();

  saveContext(currentContext);

  return currentContext;
}

uint64_t* hypster_switch(uint64_t* toContext, uint64_t timeout) {
  // this procedure is only executed at boot level zero
  return mipster_switch(toContext, timeout);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

uint64_t loadPhysicalMemory(uint64_t* paddr) {
  return *paddr;
}

void storePhysicalMemory(uint64_t* paddr, uint64_t data) {
  *paddr = data;
}

uint64_t FrameForPage(uint64_t* table, uint64_t page) {
  return (uint64_t) (table + page);
}

uint64_t getFrameForPage(uint64_t* table, uint64_t page) {
  return *(table + page);
}

uint64_t isPageMapped(uint64_t* table, uint64_t page) {
  if (getFrameForPage(table, page) != 0)
    return 1;
  else
    return 0;
}

uint64_t isValidVirtualAddress(uint64_t vaddr) {
  if (vaddr < VIRTUALMEMORYSIZE)
    // memory must be word-addressed for lack of byte-sized data type
    if (vaddr % REGISTERSIZE == 0)
      return 1;

  return 0;
}

uint64_t getPageOfVirtualAddress(uint64_t vaddr) {
  return vaddr / PAGESIZE;
}

uint64_t isVirtualAddressMapped(uint64_t* table, uint64_t vaddr) {
  // assert: isValidVirtualAddress(vaddr) == 1

  return isPageMapped(table, getPageOfVirtualAddress(vaddr));
}

uint64_t* tlb(uint64_t* table, uint64_t vaddr) {
  uint64_t page;
  uint64_t frame;
  uint64_t paddr;

  // assert: isValidVirtualAddress(vaddr) == 1
  // assert: isVirtualAddressMapped(table, vaddr) == 1

  page = getPageOfVirtualAddress(vaddr);

  frame = getFrameForPage(table, page);

  // map virtual address to physical address
  paddr = vaddr - page * PAGESIZE + frame;

  if (debug_tlb) {
    print(selfieName);
    print((uint64_t*) ": tlb access:");
    println();
    print((uint64_t*) " vaddr: ");
    printBinary(vaddr, CPUBITWIDTH);
    println();
    print((uint64_t*) " page:  ");
    printBinary(page * PAGESIZE, CPUBITWIDTH);
    println();
    print((uint64_t*) " frame: ");
    printBinary(frame, CPUBITWIDTH);
    println();
    print((uint64_t*) " paddr: ");
    printBinary(paddr, CPUBITWIDTH);
    println();
  }

  return (uint64_t*) paddr;
}

uint64_t loadVirtualMemory(uint64_t* table, uint64_t vaddr) {
  // assert: isValidVirtualAddress(vaddr) == 1
  // assert: isVirtualAddressMapped(table, vaddr) == 1

  return loadPhysicalMemory(tlb(table, vaddr));
}

void storeVirtualMemory(uint64_t* table, uint64_t vaddr, uint64_t data) {
  // assert: isValidVirtualAddress(vaddr) == 1
  // assert: isVirtualAddressMapped(table, vaddr) == 1

  storePhysicalMemory(tlb(table, vaddr), data);
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

void fct_nop() {
  if (debug) {
    printFunction(function);
    println();
  }

  if (interpret)
    pc = pc + INSTRUCTIONSIZE;
}

void fct_daddu() {
  uint64_t s;
  uint64_t t;
  uint64_t d;
  uint64_t n;

  if (interpret) {
    s = *(registers+rs);
    t = *(registers+rt);
    d = *(registers+rd);

    n = s + t;
  }

  if (debug) {
    printFunction(function);
    print((uint64_t*) " ");
    printRegister(rd);
    print((uint64_t*) ",");
    printRegister(rs);
    print((uint64_t*) ",");
    printRegister(rt);
    if (interpret) {
      print((uint64_t*) ": ");
      printRegister(rd);
      print((uint64_t*) "=");
      printInteger(d);
      print((uint64_t*) ",");
      printRegister(rs);
      print((uint64_t*) "=");
      printInteger(s);
      print((uint64_t*) ",");
      printRegister(rt);
      print((uint64_t*) "=");
      printInteger(t);
      print((uint64_t*) " -> ");
      printRegister(rd);
      print((uint64_t*) "=");
      printInteger(n);
    }
    println();
  }

  if (interpret) {
    *(registers+rd) = n;

    pc = pc + INSTRUCTIONSIZE;
  }
}

void fct_dsubu() {
  uint64_t s;
  uint64_t t;
  uint64_t d;
  uint64_t n;

  if (interpret) {
    s = *(registers+rs);
    t = *(registers+rt);
    d = *(registers+rd);

    n = s - t;
  }

  if (debug) {
    printFunction(function);
    print((uint64_t*) " ");
    printRegister(rd);
    print((uint64_t*) ",");
    printRegister(rs);
    print((uint64_t*) ",");
    printRegister(rt);
    if (interpret) {
      print((uint64_t*) ": ");
      printRegister(rd);
      print((uint64_t*) "=");
      printInteger(d);
      print((uint64_t*) ",");
      printRegister(rs);
      print((uint64_t*) "=");
      printInteger(s);
      print((uint64_t*) ",");
      printRegister(rt);
      print((uint64_t*) "=");
      printInteger(t);
      print((uint64_t*) " -> ");
      printRegister(rd);
      print((uint64_t*) "=");
      printInteger(n);
    }
    println();
  }

  if (interpret) {
    *(registers+rd) = n;

    pc = pc + INSTRUCTIONSIZE;
  }
}

void fct_dmultu() {
  uint64_t s;
  uint64_t t;
  uint64_t n;

  if (interpret) {
    s = *(registers+rs);
    t = *(registers+rt);

    n = s * t;
  }

  if (debug) {
    printFunction(function);
    print((uint64_t*) " ");
    printRegister(rs);
    print((uint64_t*) ",");
    printRegister(rt);
    if (interpret) {
      print((uint64_t*) ": ");
      printRegister(rs);
      print((uint64_t*) "=");
      printInteger(s);
      print((uint64_t*) ",");
      printRegister(rt);
      print((uint64_t*) "=");
      printInteger(t);
      print((uint64_t*) ",$lo=");
      printInteger(loReg);
      print((uint64_t*) " -> $lo=");
      printInteger(n);
    }
    println();
  }

  if (interpret) {
    // TODO: 128-bit resolution currently not supported
    loReg = n;

    pc = pc + INSTRUCTIONSIZE;
  }
}

void fct_ddivu() {
  uint64_t s;
  uint64_t t;
  uint64_t l;
  uint64_t h;

  if (interpret) {
    s = *(registers+rs);
    t = *(registers+rt);

    if (t == 0) {
      // division by zero: the result for l and h is undefined
      l = 0;
      h = 0;

      if (debug_divisionByZero) {
        print((uint64_t*) "division-by-zero error: ");
        printInteger(s);
        print((uint64_t*) " / ");
        printInteger(t);
        println();
      }
    } else {
      l = s / t;
      h = s % t;
    }
  }

  if (debug) {
    printFunction(function);
    print((uint64_t*) " ");
    printRegister(rs);
    print((uint64_t*) ",");
    printRegister(rt);
    if (interpret) {
      print((uint64_t*) ": ");
      printRegister(rs);
      print((uint64_t*) "=");
      printInteger(s);
      print((uint64_t*) ",");
      printRegister(rt);
      print((uint64_t*) "=");
      printInteger(t);
      print((uint64_t*) ",$lo=");
      printInteger(loReg);
      print((uint64_t*) ",$hi=");
      printInteger(hiReg);
      print((uint64_t*) " -> $lo=");
      printInteger(l);
      print((uint64_t*) ",$hi=");
      printInteger(h);
    }
    println();
  }

  if (interpret) {
    loReg = l;
    hiReg = h;

    pc = pc + INSTRUCTIONSIZE;
  }
}

void fct_mfhi() {
  if (debug) {
    printFunction(function);
    print((uint64_t*) " ");
    printRegister(rd);
    if (interpret) {
      print((uint64_t*) ":");
      printRegister(rd);
      print((uint64_t*) "=");
      printInteger(*(registers+rd));
      print((uint64_t*) ",$hi=");
      printInteger(hiReg);
    }
  }

  if (interpret) {
    *(registers+rd) = hiReg;

    pc = pc + INSTRUCTIONSIZE;
  }

  if (debug) {
    if (interpret) {
      print((uint64_t*) " -> ");
      printRegister(rd);
      print((uint64_t*) "=");
      printInteger(*(registers+rd));
    }
    println();
  }
}

void fct_mflo() {
  if (debug) {
    printFunction(function);
    print((uint64_t*) " ");
    printRegister(rd);
    if (interpret) {
      print((uint64_t*) ": ");
      printRegister(rd);
      print((uint64_t*) "=");
      printInteger(*(registers+rd));
      print((uint64_t*) ",$lo=");
      printInteger(loReg);
    }
  }

  if (interpret) {
    *(registers+rd) = loReg;

    pc = pc + INSTRUCTIONSIZE;
  }

  if (debug) {
    if (interpret) {
      print((uint64_t*) " -> ");
      printRegister(rd);
      print((uint64_t*) "=");
      printInteger(*(registers+rd));
    }
    println();
  }
}

void fct_sltu() {
  if (debug) {
    printFunction(function);
    print((uint64_t*) " ");
    printRegister(rd);
    print((uint64_t*) ",");
    printRegister(rs);
    print((uint64_t*) ",");
    printRegister(rt);
    if (interpret) {
      print((uint64_t*) ": ");
      printRegister(rs);
      print((uint64_t*) "=");
      printInteger(*(registers+rs));
      print((uint64_t*) ",");
      printRegister(rt);
      print((uint64_t*) "=");
      printInteger(*(registers+rt));
    }
  }

  if (interpret) {
    if (*(registers+rs) < *(registers+rt))
      *(registers+rd) = 1;
    else
      *(registers+rd) = 0;

    pc = pc + INSTRUCTIONSIZE;
  }

  if (debug) {
    if (interpret) {
      print((uint64_t*) " -> ");
      printRegister(rd);
      print((uint64_t*) "=");
      printInteger(*(registers+rd));
    }
    println();
  }
}

void fct_jr() {
  if (debug) {
    printFunction(function);
    print((uint64_t*) " ");
    printRegister(rs);
    if (interpret) {
      print((uint64_t*) ": ");
      printRegister(rs);
      print((uint64_t*) "=");
      printHexadecimal(*(registers+rs), 0);
    }
  }

  if (interpret)
    pc = *(registers+rs);

  if (debug) {
    if (interpret) {
      print((uint64_t*) " -> $pc=");
      printHexadecimal(pc, 0);
    }
    println();
  }
}

void fct_syscall() {
  if (debug) {
    printFunction(function);
    println();
  }

  if (interpret) {
    pc = pc + INSTRUCTIONSIZE;

    if (*(registers+REG_V0) == SYSCALL_SWITCH)
      implementSwitch();
    else
      throwException(EXCEPTION_SYSCALL, 0);
  }
}

void op_daddiu() {
  if (debug) {
    printOpcode(opcode);
    print((uint64_t*) " ");
    printRegister(rt);
    print((uint64_t*) ",");
    printRegister(rs);
    print((uint64_t*) ",");
    printInteger(signExtend(immediate, 16));
    if (interpret) {
      print((uint64_t*) ": ");
      printRegister(rt);
      print((uint64_t*) "=");
      printInteger(*(registers+rt));
      print((uint64_t*) ",");
      printRegister(rs);
      print((uint64_t*) "=");
      printInteger(*(registers+rs));
    }
  }

  if (interpret) {
    *(registers+rt) = *(registers+rs) + signExtend(immediate, 16);

    pc = pc + INSTRUCTIONSIZE;
  }

  if (debug) {
    if (interpret) {
      print((uint64_t*) " -> ");
      printRegister(rt);
      print((uint64_t*) "=");
      printInteger(*(registers+rt));
    }
    println();
  }
}

void op_ld() {
  uint64_t vaddr;

  if (debug) {
    printOpcode(opcode);
    print((uint64_t*) " ");
    printRegister(rt);
    print((uint64_t*) ",");
    printInteger(signExtend(immediate, 16));
    print((uint64_t*) "(");
    printRegister(rs);
    print((uint64_t*) ")");
    if (interpret) {
      print((uint64_t*) ": ");
      printRegister(rt);
      print((uint64_t*) "=");
      printInteger(*(registers+rt));
      print((uint64_t*) ",");
      printRegister(rs);
      print((uint64_t*) "=");
      printHexadecimal(*(registers+rs), 0);
    }
  }

  if (interpret) {
    vaddr = *(registers+rs) + signExtend(immediate, 16);

    if (isValidVirtualAddress(vaddr)) {
      if (isVirtualAddressMapped(pt, vaddr)) {
        *(registers+rt) = loadVirtualMemory(pt, vaddr);

        // keep track of number of loads
        loads = loads + 1;

        *(loadsPerAddress + pc / INSTRUCTIONSIZE) = *(loadsPerAddress + pc / INSTRUCTIONSIZE) + 1;

        pc = pc + INSTRUCTIONSIZE;
      } else
        throwException(EXCEPTION_PAGEFAULT, getPageOfVirtualAddress(vaddr));
    } else
      // TODO: pass invalid vaddr
      throwException(EXCEPTION_INVALIDADDRESS, 0);
  }

  if (debug) {
    if (interpret) {
      print((uint64_t*) " -> ");
      printRegister(rt);
      print((uint64_t*) "=");
      printInteger(*(registers+rt));
      print((uint64_t*) "=memory[");
      printHexadecimal(vaddr, 0);
      print((uint64_t*) "]");
    }
    println();
  }
}

void op_sd() {
  uint64_t vaddr;

  if (debug) {
    printOpcode(opcode);
    print((uint64_t*) " ");
    printRegister(rt);
    print((uint64_t*) ",");
    printInteger(signExtend(immediate, 16));
    print((uint64_t*) "(");
    printRegister(rs);
    print((uint64_t*) ")");
    if (interpret) {
      print((uint64_t*) ": ");
      printRegister(rt);
      print((uint64_t*) "=");
      printInteger(*(registers+rt));
      print((uint64_t*) ",");
      printRegister(rs);
      print((uint64_t*) "=");
      printHexadecimal(*(registers+rs), 0);
    }
  }

  if (interpret) {
    vaddr = *(registers+rs) + signExtend(immediate, 16);

    if (isValidVirtualAddress(vaddr)) {
      if (isVirtualAddressMapped(pt, vaddr)) {
        storeVirtualMemory(pt, vaddr, *(registers+rt));

        // keep track of number of stores
        stores = stores + 1;

        *(storesPerAddress + pc / INSTRUCTIONSIZE) = *(storesPerAddress + pc / INSTRUCTIONSIZE) + 1;

        pc = pc + INSTRUCTIONSIZE;
      } else
        throwException(EXCEPTION_PAGEFAULT, getPageOfVirtualAddress(vaddr));
    } else
      // TODO: pass invalid vaddr
      throwException(EXCEPTION_INVALIDADDRESS, 0);
  }

  if (debug) {
    if (interpret) {
      print((uint64_t*) " -> memory[");
      printHexadecimal(vaddr, 0);
      print((uint64_t*) "]=");
      printInteger(*(registers+rt));
      print((uint64_t*) "=");
      printRegister(rt);
    }
    println();
  }
}

void op_beq() {
  if (debug) {
    printOpcode(opcode);
    print((uint64_t*) " ");
    printRegister(rs);
    print((uint64_t*) ",");
    printRegister(rt);
    print((uint64_t*) ",");
    printInteger(signExtend(immediate, 16));
    print((uint64_t*) "[");
    printHexadecimal(pc + INSTRUCTIONSIZE + signExtend(immediate, 16) * INSTRUCTIONSIZE, 0);
    print((uint64_t*) "]");
    if (interpret) {
      print((uint64_t*) ": ");
      printRegister(rs);
      print((uint64_t*) "=");
      printInteger(*(registers+rs));
      print((uint64_t*) ",");
      printRegister(rt);
      print((uint64_t*) "=");
      printInteger(*(registers+rt));
    }
  }

  if (interpret) {
    pc = pc + INSTRUCTIONSIZE;

    if (*(registers+rs) == *(registers+rt)) {
      pc = pc + signExtend(immediate, 16) * INSTRUCTIONSIZE;

      if (signedLessThan(signExtend(immediate, 16), 0)) {
        // keep track of number of loop iterations
        loops = loops + 1;

        *(loopsPerAddress + pc / INSTRUCTIONSIZE) = *(loopsPerAddress + pc / INSTRUCTIONSIZE) + 1;
      }

      // TODO: execute delay slot
    }
  }

  if (debug) {
    if (interpret) {
      print((uint64_t*) " -> $pc=");
      printHexadecimal(pc, 0);
    }
    println();
  }
}

void op_jal() {
  if (debug) {
    printOpcode(opcode);
    print((uint64_t*) " ");
    printHexadecimal(instr_index, 0);
    print((uint64_t*) "[");
    printHexadecimal(instr_index * INSTRUCTIONSIZE, 0);
    print((uint64_t*) "]");
    if (interpret) {
      print((uint64_t*) ": ");
      printRegister(REG_RA);
      print((uint64_t*) "=");
      printHexadecimal(*(registers+REG_RA), 0);
    }
  }

  if (interpret) {
    // skip over delay slot
    *(registers+REG_RA) = pc + 2 * INSTRUCTIONSIZE;

    pc = instr_index * INSTRUCTIONSIZE;

    // keep track of number of procedure calls
    calls = calls + 1;

    *(callsPerAddress + pc / INSTRUCTIONSIZE) = *(callsPerAddress + pc / INSTRUCTIONSIZE) + 1;

    // TODO: execute delay slot
  }

  if (debug) {
    if (interpret) {
      print((uint64_t*) " -> ");
      printRegister(REG_RA);
      print((uint64_t*) "=");
      printHexadecimal(*(registers+REG_RA), 0);
      print((uint64_t*) ",$pc=");
      printHexadecimal(pc, 0);
    }
    println();
  }
}

void op_j() {
  if (debug) {
    printOpcode(opcode);
    print((uint64_t*) " ");
    printHexadecimal(instr_index, 0);
    print((uint64_t*) "[");
    printHexadecimal(instr_index * INSTRUCTIONSIZE, 0);
    print((uint64_t*) "]");
  }

  if (interpret) {
    pc = instr_index * INSTRUCTIONSIZE;

    // TODO: execute delay slot
  }

  if (debug) {
    if (interpret) {
      print((uint64_t*) ": -> $pc=");
      printHexadecimal(pc, 0);
    }
    println();
  }
}

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void printException(uint64_t exception, uint64_t faultingPage) {
  print((uint64_t*) *(EXCEPTIONS + exception));

  if (exception == EXCEPTION_PAGEFAULT) {
    print((uint64_t*) " at ");
    printHexadecimal(faultingPage, 8);
  }
}

void throwException(uint64_t exception, uint64_t faultingPage) {
  setException(currentContext, exception);
  setFaultingPage(currentContext, faultingPage);

  trap = 1;

  if (debug_exception) {
    print(selfieName);
    print((uint64_t*) ": context ");
    printHexadecimal((uint64_t) currentContext, 8);
    print((uint64_t*) " throws ");
    printException(exception, faultingPage);
    print((uint64_t*) " exception");
    println();
  }
}

void fetch() {
  // assert: isValidVirtualAddress(pc) == 1
  // assert: isVirtualAddressMapped(pt, pc) == 1

  if (pc % REGISTERSIZE == 0)
    ir = getHighWord(loadVirtualMemory(pt, pc));
  else
    ir = getLowWord(loadVirtualMemory(pt, pc - INSTRUCTIONSIZE));
}

void execute() {
  if (debug) {
    if (interpret) {
      print(getName(currentContext));
      print((uint64_t*) ": $pc=");
    }
    printHexadecimal(pc, 0);
    if (sourceLineNumber != (uint64_t*) 0) {
      print((uint64_t*) "(~");
      printInteger(*(sourceLineNumber + pc / INSTRUCTIONSIZE));
      print((uint64_t*) ")");
    }
    print((uint64_t*) ": ");
    printHexadecimal(ir, 8);
    print((uint64_t*) ": ");
  }

  if (opcode == OP_SPECIAL) {
    if (function == FCT_NOP)
      fct_nop();
    else if (function == FCT_DADDU)
      fct_daddu();
    else if (function == FCT_DSUBU)
      fct_dsubu();
    else if (function == FCT_DMULTU)
      fct_dmultu();
    else if (function == FCT_DDIVU)
      fct_ddivu();
    else if (function == FCT_MFHI)
      fct_mfhi();
    else if (function == FCT_MFLO)
      fct_mflo();
    else if (function == FCT_SLTU)
      fct_sltu();
    else if (function == FCT_JR)
      fct_jr();
    else if (function == FCT_SYSCALL)
      fct_syscall();
    else
      throwException(EXCEPTION_UNKNOWNINSTRUCTION, 0);
  } else if (opcode == OP_DADDIU)
    op_daddiu();
  else if (opcode == OP_LD)
    op_ld();
  else if (opcode == OP_SD)
    op_sd();
  else if (opcode == OP_BEQ)
    op_beq();
  else if (opcode == OP_JAL)
    op_jal();
  else if (opcode == OP_J)
    op_j();
  else
    throwException(EXCEPTION_UNKNOWNINSTRUCTION, 0);
}

void interrupt() {
  if (timer > 0)
    timer = timer - 1;

  if (timer == 0)
    if (getException(currentContext) == EXCEPTION_NOEXCEPTION)
      // only throw exception if no other is pending
      // TODO: handle multiple pending exceptions
      throwException(EXCEPTION_TIMER, 0);
}

uint64_t* runUntilException() {
  trap = 0;

  while (trap == 0) {
    fetch();
    decode();
    execute();
    interrupt();
  }

  trap = 0;

  return currentContext;
}

uint64_t addressWithMaxCounter(uint64_t* counters, uint64_t max) {
  uint64_t a;
  uint64_t n;
  uint64_t i;
  uint64_t c;

  a = -1;

  n = 0;

  i = 0;

  while (i < maxBinaryLength / INSTRUCTIONSIZE) {
    c = *(counters + i);

    if (n < c)
      if (c < max) {
        n = c;
        a = i * INSTRUCTIONSIZE;
      }

    i = i + 1;
  }

  return a;
}

uint64_t printCounters(uint64_t total, uint64_t* counters, uint64_t max) {
  uint64_t a;
  uint64_t ratio;

  a = addressWithMaxCounter(counters, max);

  if (a == (uint64_t) (-1))
    ratio = 0;
  else
    ratio = *(counters + a / INSTRUCTIONSIZE);

  printInteger(ratio);

  print((uint64_t*) "(");
  printFixedPointPercentage(total, ratio);
  print((uint64_t*) "%)");

  if (ratio != 0) {
    print((uint64_t*) "@");
    printHexadecimal(a, 0);
    if (sourceLineNumber != (uint64_t*) 0) {
      print((uint64_t*) "(~");
      printInteger(*(sourceLineNumber + a / INSTRUCTIONSIZE));
      print((uint64_t*) ")");
    }
  }

  return ratio;
}

void printProfile(uint64_t* message, uint64_t total, uint64_t* counters) {
  uint64_t max;

  if (total > 0) {
    print(selfieName);
    print(message);
    printInteger(total);
    print((uint64_t*) ",");
    max = printCounters(total, counters, INT64_MAX); // max counter
    print((uint64_t*) ",");
    max = printCounters(total, counters, max); // 2nd max
    print((uint64_t*) ",");
    printCounters(total, counters, max); // 3rd max
    println();
  }
}

void selfie_disassemble() {
  assemblyName = getArgument();

  if (codeLength == 0) {
    print(selfieName);
    print((uint64_t*) ": nothing to disassemble to output file ");
    print(assemblyName);
    println();

    return;
  }

  // assert: assemblyName is mapped and not longer than maxFilenameLength

  assemblyFD = openWriteOnly(assemblyName);

  if (signedLessThan(assemblyFD, 0)) {
    print(selfieName);
    print((uint64_t*) ": could not create assembly output file ");
    print(assemblyName);
    println();

    exit(EXITCODE_IOERROR);
  }

  outputName = assemblyName;
  outputFD   = assemblyFD;

  interpret = 0;

  resetLibrary();
  resetInterpreter();

  debug = 1;

  while(pc < codeLength) {
    ir = loadInstruction(pc);

    decode();
    execute();

    pc = pc + INSTRUCTIONSIZE;
  }

  debug = 0;

  outputName = (uint64_t*) 0;
  outputFD   = 1;

  print(selfieName);
  print((uint64_t*) ": ");
  printInteger(numberOfWrittenCharacters);
  print((uint64_t*) " characters of assembly with ");
  printInteger(codeLength / INSTRUCTIONSIZE);
  print((uint64_t*) " instructions written into ");
  print(assemblyName);
  println();
}

// -----------------------------------------------------------------
// ---------------------------- CONTEXTS ---------------------------
// -----------------------------------------------------------------

uint64_t* allocateContext(uint64_t* parent, uint64_t* vctxt, uint64_t* in) {
  uint64_t* context;

  if (freeContexts == (uint64_t*) 0)
    context = smalloc(7 * SIZEOFUINT64STAR + 10 * SIZEOFUINT64);
  else {
    context = freeContexts;

    freeContexts = getNextContext(freeContexts);
  }

  setNextContext(context, in);
  setPrevContext(context, (uint64_t*) 0);

  if (in != (uint64_t*) 0)
    setPrevContext(in, context);

  setPC(context, 0);

  // allocate zeroed memory for general purpose registers
  // TODO: reuse memory
  setRegs(context, zalloc(NUMBEROFREGISTERS * SIZEOFUINT64));

  setLoReg(context, 0);
  setHiReg(context, 0);

  // allocate zeroed memory for page table
  // TODO: save and reuse memory for page table
  setPT(context, zalloc(VIRTUALMEMORYSIZE / PAGESIZE * SIZEOFUINT64));

  // determine range of recently mapped pages
  setLoPage(context, 0);
  setMePage(context, 0);
  setHiPage(context, getPageOfVirtualAddress(VIRTUALMEMORYSIZE - REGISTERSIZE));

  // heap starts where it is safe to start
  setProgramBreak(context, maxBinaryLength);

  setException(context, EXCEPTION_NOEXCEPTION);
  setFaultingPage(context, 0);

  setExitCode(context, EXITCODE_NOERROR);

  setParent(context, parent);
  setVirtualContext(context, vctxt);

  setName(context, (uint64_t*) 0);

  return context;
}

uint64_t* findContext(uint64_t* parent, uint64_t* vctxt, uint64_t* in) {
  uint64_t* context;

  context = in;

  while (context != (uint64_t*) 0) {
    if (getParent(context) == parent)
      if (getVirtualContext(context) == vctxt)
        return context;

    context = getNextContext(context);
  }

  return (uint64_t*) 0;
}

void freeContext(uint64_t* context) {
  setNextContext(context, freeContexts);

  freeContexts = context;
}

uint64_t* deleteContext(uint64_t* context, uint64_t* from) {
  if (getNextContext(context) != (uint64_t*) 0)
    setPrevContext(getNextContext(context), getPrevContext(context));

  if (getPrevContext(context) != (uint64_t*) 0) {
    setNextContext(getPrevContext(context), getNextContext(context));
    setPrevContext(context, (uint64_t*) 0);
  } else
    from = getNextContext(context);

  freeContext(context);

  return from;
}

// -----------------------------------------------------------------
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

uint64_t* createContext(uint64_t* parent, uint64_t* vctxt) {
  // TODO: check if context already exists
  usedContexts = allocateContext(parent, vctxt, usedContexts);

  if (currentContext == (uint64_t*) 0)
    currentContext = usedContexts;

  if (debug_create) {
    print(selfieName);
    print((uint64_t*) ": parent context ");
    printHexadecimal((uint64_t) parent, 8);
    print((uint64_t*) " created child context ");
    printHexadecimal((uint64_t) usedContexts, 8);
    println();
  }

  return usedContexts;
}

uint64_t* cacheContext(uint64_t* vctxt) {
  uint64_t* context;

  // find cached context on my boot level
  context = findContext(currentContext, vctxt, usedContexts);

  if (context == (uint64_t*) 0)
    // create cached context on my boot level
    context = createContext(currentContext, vctxt);

  return context;
}

void saveContext(uint64_t* context) {
  uint64_t* parentTable;
  uint64_t* vctxt;
  uint64_t r;
  uint64_t* regs;
  uint64_t* vregs;

  // save machine state
  setPC(context, pc);
  setLoReg(context, loReg);
  setHiReg(context, hiReg);

  if (getParent(context) != MY_CONTEXT) {
    parentTable = getPT(getParent(context));

    vctxt = getVirtualContext(context);

    storeVirtualMemory(parentTable, PC(vctxt), getPC(context));

    r = 0;

    regs = getRegs(context);

    vregs = (uint64_t*) loadVirtualMemory(parentTable, Regs(vctxt));

    while (r < NUMBEROFREGISTERS) {
      storeVirtualMemory(parentTable, (uint64_t) (vregs + r), *(regs + r));

      r = r + 1;
    }

    storeVirtualMemory(parentTable, LoReg(vctxt), getLoReg(context));
    storeVirtualMemory(parentTable, HiReg(vctxt), getHiReg(context));
    storeVirtualMemory(parentTable, ProgramBreak(vctxt), getProgramBreak(context));

    storeVirtualMemory(parentTable, Exception(vctxt), getException(context));
    storeVirtualMemory(parentTable, FaultingPage(vctxt), getFaultingPage(context));
    storeVirtualMemory(parentTable, ExitCode(vctxt), getExitCode(context));
  }
}

void mapPage(uint64_t* context, uint64_t page, uint64_t frame) {
  uint64_t* table;

  table = getPT(context);

  // assert: 0 <= page < VIRTUALMEMORYSIZE / PAGESIZE

  // on boot level zero frame may be any signed integer

  *(table + page) = frame;

  // exploit spatial locality in page table caching
  if (page != getHiPage(context)) {
    if (page < getLoPage(context)) {
      // strictly, touching is only necessary on boot levels higher than zero
      touch(table + page, (getLoPage(context) - page) * SIZEOFUINT64);

      setLoPage(context, page);
    } else if (getMePage(context) < page) {
      // strictly, touching is only necessary on boot levels higher than zero
      touch(table + getMePage(context), (page - getMePage(context)) * SIZEOFUINT64);

      setMePage(context, page);
    }
  }

  if (debug_map) {
    print(selfieName);
    print((uint64_t*) ": page ");
    printHexadecimal(page, 4);
    print((uint64_t*) " mapped to frame ");
    printHexadecimal(frame, 8);
    print((uint64_t*) " in context ");
    printHexadecimal((uint64_t) context, 8);
    println();
  }
}

void restoreContext(uint64_t* context) {
  uint64_t* parentTable;
  uint64_t* vctxt;
  uint64_t r;
  uint64_t* regs;
  uint64_t* vregs;
  uint64_t* table;
  uint64_t page;
  uint64_t me;
  uint64_t frame;

  if (getParent(context) != MY_CONTEXT) {
    parentTable = getPT(getParent(context));

    vctxt = getVirtualContext(context);

    setPC(context, loadVirtualMemory(parentTable, PC(vctxt)));

    r = 0;

    regs = getRegs(context);

    vregs = (uint64_t*) loadVirtualMemory(parentTable, Regs(vctxt));

    while (r < NUMBEROFREGISTERS) {
      *(regs + r) = loadVirtualMemory(parentTable, (uint64_t) (vregs + r));

      r = r + 1;
    }

    setLoReg(context, loadVirtualMemory(parentTable, LoReg(vctxt)));
    setHiReg(context, loadVirtualMemory(parentTable, HiReg(vctxt)));
    setProgramBreak(context, loadVirtualMemory(parentTable, ProgramBreak(vctxt)));

    setException(context, loadVirtualMemory(parentTable, Exception(vctxt)));
    setFaultingPage(context, loadVirtualMemory(parentTable, FaultingPage(vctxt)));
    setExitCode(context, loadVirtualMemory(parentTable, ExitCode(vctxt)));

    table = (uint64_t*) loadVirtualMemory(parentTable, PT(vctxt));

    // assert: context page table is only mapped from beginning up and end down

    page = loadVirtualMemory(parentTable, LoPage(vctxt));
    me   = loadVirtualMemory(parentTable, MePage(vctxt));

    while (page <= me) {
      frame = loadVirtualMemory(parentTable, FrameForPage(table, page));

      if (frame != 0)
        mapPage(context, page, getFrameForPage(parentTable, getPageOfVirtualAddress(frame)));

      page = page + 1;
    }

    storeVirtualMemory(parentTable, LoPage(vctxt), page);

    page  = loadVirtualMemory(parentTable, HiPage(vctxt));
    frame = loadVirtualMemory(parentTable, FrameForPage(table, page));

    while (frame != 0) {
      mapPage(context, page, getFrameForPage(parentTable, getPageOfVirtualAddress(frame)));

      page  = page - 1;
      frame = loadVirtualMemory(parentTable, FrameForPage(table, page));
    }

    storeVirtualMemory(parentTable, HiPage(vctxt), page);
  }
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

uint64_t pavailable() {
  if (freePageFrameMemory > 0)
    return 1;
  else if (usedPageFrameMemory + MEGABYTE <= pageFrameMemory)
    return 1;
  else
    return 0;
}

uint64_t pused() {
  return usedPageFrameMemory - freePageFrameMemory;
}

uint64_t* palloc() {
  uint64_t block;
  uint64_t frame;

  // assert: pageFrameMemory is equal to or a multiple of MEGABYTE
  // assert: PAGESIZE is a factor of MEGABYTE strictly less than MEGABYTE

  if (freePageFrameMemory == 0) {
    freePageFrameMemory = MEGABYTE;

    if (usedPageFrameMemory + freePageFrameMemory <= pageFrameMemory) {
      // on boot level zero allocate zeroed memory
      block = (uint64_t) zalloc(freePageFrameMemory);

      usedPageFrameMemory = usedPageFrameMemory + freePageFrameMemory;

      // page frames must be page-aligned to work as page table index
      nextPageFrame = roundUp(block, PAGESIZE);

      if (nextPageFrame > block)
        // losing one page frame to fragmentation
        freePageFrameMemory = freePageFrameMemory - PAGESIZE;
    } else {
      print(selfieName);
      print((uint64_t*) ": palloc out of physical memory");
      println();

      exit(EXITCODE_OUTOFPHYSICALMEMORY);
    }
  }

  frame = nextPageFrame;

  nextPageFrame = nextPageFrame + PAGESIZE;

  freePageFrameMemory = freePageFrameMemory - PAGESIZE;

  // strictly, touching is only necessary on boot levels higher than zero
  return touch((uint64_t*) frame, PAGESIZE);
}

void pfree(uint64_t* frame) {
  // TODO: implement free list of page frames
}

void mapAndStore(uint64_t* context, uint64_t vaddr, uint64_t data) {
  // assert: isValidVirtualAddress(vaddr) == 1

  if (isVirtualAddressMapped(getPT(context), vaddr) == 0)
    mapPage(context, getPageOfVirtualAddress(vaddr), (uint64_t) palloc());

  storeVirtualMemory(getPT(context), vaddr, data);
}

void up_loadBinary(uint64_t* context) {
  uint64_t vaddr;

  setName(context, binaryName);

  // binaries start at lowest virtual address
  vaddr = 0;

  while (vaddr < binaryLength) {
    mapAndStore(context, vaddr, loadData(vaddr));

    vaddr = vaddr + SIZEOFUINT64;
  }
}

uint64_t up_loadString(uint64_t* context, uint64_t* s, uint64_t SP) {
  uint64_t bytes;
  uint64_t i;

  bytes = roundUp(stringLength(s) + 1, REGISTERSIZE);

  // allocate memory for storing string
  SP = SP - bytes;

  i = 0;

  while (i < bytes) {
    mapAndStore(context, SP + i, *s);

    s = s + 1;

    i = i + REGISTERSIZE;
  }

  return SP;
}

void up_loadArguments(uint64_t* context, uint64_t argc, uint64_t* argv) {
  uint64_t SP;
  uint64_t vargv;
  uint64_t i_argc;
  uint64_t i_vargv;

  // arguments are pushed onto stack which starts at highest virtual address
  SP = VIRTUALMEMORYSIZE - REGISTERSIZE;

  // allocate memory for storing stack pointer later
  SP = SP - REGISTERSIZE;

  // allocate memory for storing *argv array
  SP = SP - argc * REGISTERSIZE;

  // vargv invalid if argc == 0
  vargv = SP + REGISTERSIZE;

  i_vargv = vargv;
  i_argc  = argc;

  while (i_argc > 0) {
    SP = up_loadString(context, (uint64_t*) *argv, SP);

    // store pointer to string in virtual *argv
    mapAndStore(context, i_vargv, SP);

    argv = argv + 1;

    i_vargv = i_vargv + REGISTERSIZE;

    i_argc = i_argc - 1;
  }

  // allocate memory for one word on the stack
  SP = SP - REGISTERSIZE;

  // push argc
  mapAndStore(context, SP, argc);

  // allocate memory for one word on the stack
  SP = SP - REGISTERSIZE;

  // push virtual argv
  mapAndStore(context, SP, vargv);

  // store stack pointer at highest virtual address for binary to retrieve
  mapAndStore(context, VIRTUALMEMORYSIZE - REGISTERSIZE, SP);
}

void mapUnmappedPages(uint64_t* context) {
  uint64_t page;

  // assert: page table is only mapped from beginning up and end down

  page = 0;

  while (isPageMapped(getPT(context), page))
    page = page + 1;

  while (pavailable()) {
    mapPage(context, page, (uint64_t) palloc());

    page = page + 1;
  }
}

uint64_t isBootLevelZero() {
  // in C99 malloc(0) returns either a null pointer or a unique pointer.
  // (see http://pubs.opengroup.org/onlinepubs/9699919799/)
  // selfie's malloc implementation, on the other hand,
  // returns the same not null address, if malloc(0) is called consecutively.
  uint64_t firstMalloc;
  uint64_t secondMalloc;

  firstMalloc = (uint64_t) malloc(0);
  secondMalloc = (uint64_t) malloc(0);

  if (firstMalloc == 0)
    return 1;
  if (firstMalloc != secondMalloc)
    return 1;

  // it is selfie's malloc, so it can not be boot level zero.
  return 0;
}

uint64_t handleSystemCalls(uint64_t* context) {
  uint64_t v0;

  if (getException(context) == EXCEPTION_SYSCALL) {
    v0 = *(getRegs(context)+REG_V0);

    if (v0 == SYSCALL_MALLOC)
      return implementMalloc(context);
    else if (v0 == SYSCALL_READ)
      implementRead(context);
    else if (v0 == SYSCALL_WRITE)
      implementWrite(context);
    else if (v0 == SYSCALL_OPEN)
      implementOpen(context);
    else if (v0 == SYSCALL_EXIT) {
      implementExit(context);

      // TODO: exit only if all contexts have exited
      return EXIT;
    } else {
      print(selfieName);
      print((uint64_t*) ": unknown system call ");
      printInteger(v0);
      println();

      setExitCode(context, EXITCODE_UNKNOWNSYSCALL);

      return EXIT;
    }
  } else if (getException(context) != EXCEPTION_TIMER) {
    print(selfieName);
    print((uint64_t*) ": context ");
    print(getName(context));
    print((uint64_t*) " throws uncaught ");
    printException(getException(context), getFaultingPage(context));
    println();

    setExitCode(context, EXITCODE_UNCAUGHTEXCEPTION);

    return EXIT;
  }

  return DONOTEXIT;
}

uint64_t mipster(uint64_t* toContext) {
  uint64_t timeout;
  uint64_t* fromContext;

  print((uint64_t*) "mipster");
  println();

  timeout = TIMESLICE;

  while (1) {
    fromContext = mipster_switch(toContext, timeout);

    if (getParent(fromContext) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      toContext = getParent(fromContext);

      timeout = TIMEROFF;
    } else {
       // we are the parent in charge of handling exceptions

      if (getException(fromContext) == EXCEPTION_PAGEFAULT)
        // TODO: use this table to unmap and reuse frames
        mapPage(fromContext, getFaultingPage(fromContext), (uint64_t) palloc());
      else if (handleSystemCalls(fromContext) == EXIT)
        return getExitCode(fromContext);

      setException(fromContext, EXCEPTION_NOEXCEPTION);

      toContext = fromContext;

      timeout = TIMESLICE;
    }
  }
}

uint64_t minster(uint64_t* toContext) {
  uint64_t timeout;
  uint64_t* fromContext;

  print((uint64_t*) "minster");
  println();

  timeout = TIMESLICE;

  // virtual is like physical memory in initial context up to memory size
  // by mapping unmapped pages (for the heap) to all available page frames
  // CAUTION: consumes memory even when not accessed
  mapUnmappedPages(toContext);

  while (1) {
    fromContext = mipster_switch(toContext, timeout);

    if (getParent(fromContext) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      toContext = getParent(fromContext);

      timeout = TIMEROFF;
    } else {
      // we are the parent in charge of handling exit exceptions

      if (handleSystemCalls(fromContext) == EXIT)
        return getExitCode(fromContext);

      setException(fromContext, EXCEPTION_NOEXCEPTION);

      toContext = fromContext;

      timeout = TIMESLICE;
    }
  }
}

uint64_t mobster(uint64_t* toContext) {
  uint64_t timeout;
  uint64_t* fromContext;

  print((uint64_t*) "mobster");
  println();

  timeout = TIMESLICE;

  while (1) {
    fromContext = mipster_switch(toContext, TIMESLICE);

    if (getParent(fromContext) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      toContext = getParent(fromContext);

      timeout = TIMEROFF;
    } else {
      // we are the parent in charge of handling exit exceptions

      if (handleSystemCalls(fromContext) == EXIT)
        return getExitCode(fromContext);

      setException(fromContext, EXCEPTION_NOEXCEPTION);

      toContext = fromContext;

      timeout = TIMESLICE;
    }
  }
}

uint64_t hypster(uint64_t* toContext) {
  uint64_t* fromContext;

  print((uint64_t*) "hypster");
  println();

  while (1) {
    fromContext = hypster_switch(toContext, TIMESLICE);

    if (getException(fromContext) == EXCEPTION_PAGEFAULT)
      // TODO: use this table to unmap and reuse frames
      mapPage(fromContext, getFaultingPage(fromContext), (uint64_t) palloc());
    else if (handleSystemCalls(fromContext) == EXIT)
      return getExitCode(fromContext);

    setException(fromContext, EXCEPTION_NOEXCEPTION);

    toContext = fromContext;
  }
}

uint64_t mixter(uint64_t* toContext, uint64_t mix) {
  // works with mipsters and hypsters
  uint64_t mslice;
  uint64_t timeout;
  uint64_t* fromContext;

  print((uint64_t*) "mixter (");
  printInteger(mix);
  print((uint64_t*) "% mipster/");
  printInteger(100 - mix);
  print((uint64_t*) "% hypster)");
  println();

  mslice = TIMESLICE;

  if (mslice <= INT64_MAX / 100)
    mslice = mslice * mix / 100;
  else if (mslice <= INT64_MAX / 10)
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
      fromContext = mipster_switch(toContext, TIMESLICE);
    else
      fromContext = hypster_switch(toContext, TIMESLICE);

    if (getParent(fromContext) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      toContext = getParent(fromContext);

      timeout = TIMEROFF;
    } else {
      // we are the parent in charge of handling exceptions

      if (getException(fromContext) == EXCEPTION_PAGEFAULT)
        // TODO: use this table to unmap and reuse frames
        mapPage(fromContext, getFaultingPage(fromContext), (uint64_t) palloc());
      else if (handleSystemCalls(fromContext) == EXIT)
        return getExitCode(fromContext);

      setException(fromContext, EXCEPTION_NOEXCEPTION);

      // TODO: scheduler should go here
      toContext = fromContext;

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

uint64_t selfie_run(uint64_t machine) {
  uint64_t exitCode;

  if (binaryLength == 0) {
    print(selfieName);
    print((uint64_t*) ": nothing to run, debug, or host");
    println();

    return -1;
  }

  initMemory(atoi(peekArgument()));

  interpret = 1;

  resetInterpreter();
  resetMicrokernel();

  createContext(MY_CONTEXT, 0);

  up_loadBinary(currentContext);

  // pass binary name as first argument by replacing memory size
  setArgument(binaryName);

  up_loadArguments(currentContext, numberOfRemainingArguments(), remainingArguments());

  print(selfieName);
  print((uint64_t*) ": this is selfie executing ");
  print(binaryName);
  print((uint64_t*) " with ");
  printInteger(pageFrameMemory / MEGABYTE);
  print((uint64_t*) "MB of physical memory on ");

  if (machine == MIPSTER)
    exitCode = mipster(currentContext);
  else if (machine == MINSTER)
    exitCode = minster(currentContext);
  else if (machine == MOBSTER)
    exitCode = mobster(currentContext);
  else if (machine == HYPSTER)
    if (isBootLevelZero())
      // no hypster on boot level zero
      exitCode = mipster(currentContext);
    else
      exitCode = hypster(currentContext);
  else
    // change 0 to anywhere between 0% to 100% mipster
    exitCode = mixter(currentContext, 0);

  interpret = 0;

  debug = 0;

  print(selfieName);
  print((uint64_t*) ": this is selfie terminating ");
  print(getName(currentContext));
  print((uint64_t*) " with exit code ");
  printInteger(exitCode);
  print((uint64_t*) " and ");
  printFixedPointRatio(pused(), MEGABYTE);
  print((uint64_t*) "MB of mapped memory");
  println();

  if (calls > 0) {
    print(selfieName);
    if (sourceLineNumber != (uint64_t*) 0)
      print((uint64_t*) ": profile: total,max(ratio%)@addr(line#),2max(ratio%)@addr(line#),3max(ratio%)@addr(line#)");
    else
      print((uint64_t*) ": profile: total,max(ratio%)@addr,2max(ratio%)@addr,3max(ratio%)@addr");
    println();
    printProfile((uint64_t*) ": calls: ", calls, callsPerAddress);
    printProfile((uint64_t*) ": loops: ", loops, loopsPerAddress);
    printProfile((uint64_t*) ": loads: ", loads, loadsPerAddress);
    printProfile((uint64_t*) ": stores: ", stores, storesPerAddress);
  }

  return exitCode;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------   T H E O R E M  P R O V E R    ----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// -------------------------- SAT Solver ---------------------------
// -----------------------------------------------------------------

uint64_t clauseMayBeTrue(uint64_t* clauseAddress, uint64_t depth) {
  uint64_t variable;

  variable = 0;

  while (variable <= depth) {
    if (*(SATAssignment + variable) == TRUE) {
      if (*(clauseAddress + 2 * variable))
        return TRUE;
    } else if (*(clauseAddress + 2 * variable + 1))
      // variable must be FALSE because variable <= depth
      return TRUE;

    variable = variable + 1;
  }

  while (variable < numberOfSATVariables) {
    // variable must be unassigned because variable > depth
    if (*(clauseAddress + 2 * variable))
      return TRUE;
    else if (*(clauseAddress + 2 * variable + 1))
      return TRUE;

    variable = variable + 1;
  }

  return FALSE;
}

uint64_t instanceMayBeTrue(uint64_t depth) {
  uint64_t clause;

  clause = 0;

  while (clause < numberOfSATClauses) {
    if (clauseMayBeTrue(SATInstance + clause * 2 * numberOfSATVariables, depth))
      clause = clause + 1;
    else
      // clause is FALSE under current assignment
      return FALSE;
  }

  return TRUE;
}

uint64_t babysat(uint64_t depth) {
  if (depth == numberOfSATVariables) return SAT;

  *(SATAssignment + depth) = TRUE;

  if (instanceMayBeTrue(depth)) if (babysat(depth + 1) == SAT) return SAT;

  *(SATAssignment + depth) = FALSE;

  if (instanceMayBeTrue(depth)) if (babysat(depth + 1) == SAT) return SAT;

  return UNSAT;
}

// -----------------------------------------------------------------
// ----------------------- DIMACS CNF PARSER -----------------------
// -----------------------------------------------------------------

void selfie_printDimacs() {
  uint64_t clause;
  uint64_t variable;

  print((uint64_t*) "p cnf ");
  printInteger(numberOfSATVariables);
  print((uint64_t*) " ");
  printInteger(numberOfSATClauses);
  println();

  clause = 0;

  while (clause < numberOfSATClauses) {
    variable = 0;

    while (variable < numberOfSATVariables) {
      if (*(SATInstance + clause * 2 * numberOfSATVariables + 2 * variable) == TRUE) {
        printInteger(variable + 1);
        print((uint64_t*) " ");
      } else if (*(SATInstance + clause * 2 * numberOfSATVariables + 2 * variable + 1) == TRUE) {
        printInteger(-(variable + 1));
        print((uint64_t*) " ");
      }

      variable = variable + 1;
    }

    print((uint64_t*) "0");
    println();

    clause = clause + 1;
  }
}

void dimacs_findNextCharacter(uint64_t newLine) {
  uint64_t inComment;

  // assuming we are not in a comment
  inComment = 0;

  // read and discard all whitespace and comments until a character is found
  // that is not whitespace and does not occur in a comment, or the file ends
  while (1) {
    if (inComment) {
      getCharacter();

      if (isCharacterNewLine())
        // comments end with new line
        inComment = 0;
      else if (character == CHAR_EOF)
        return;
      else
        // count the characters in comments as ignored characters
        // line feed and carriage return are counted below
        numberOfIgnoredCharacters = numberOfIgnoredCharacters + 1;
    } else if (newLine) {
      newLine = 0;

      if (character == 'c') {
        // 'c' at beginning of a line begins a comment
        inComment = 1;

        // count the number of comments
        numberOfComments = numberOfComments + 1;
      }
    } else if (isCharacterWhitespace()) {
      if (isCharacterNewLine()) {
        newLine = 1;

        // keep track of line numbers for error reporting and code annotation
        if (character == CHAR_LF)
          lineNumber = lineNumber + 1;
      } else
        newLine = 0;

      // count whitespace as ignored characters
      numberOfIgnoredCharacters = numberOfIgnoredCharacters + 1;

      getCharacter();
    } else
      // character found that is not whitespace and not occurring in a comment
      return;
  }
}

void dimacs_getSymbol() {
  dimacs_findNextCharacter(0);

  getSymbol();
}

void dimacs_word(uint64_t* word) {
  if (symbol == SYM_IDENTIFIER) {
    if (stringCompare(identifier, word)) {
      dimacs_getSymbol();

      return;
    } else
      syntaxErrorIdentifier(word);
  } else
    syntaxErrorSymbol(SYM_IDENTIFIER);

  exit(EXITCODE_PARSERERROR);
}

uint64_t dimacs_number() {
  uint64_t number;

  if (symbol == SYM_INTEGER) {
    number = literal;

    dimacs_getSymbol();

    return number;
  } else
    syntaxErrorSymbol(SYM_INTEGER);

  exit(EXITCODE_PARSERERROR);
}

void dimacs_getClause(uint64_t clause) {
  uint64_t not;

  while (1) {
    not = 0;

    if (symbol == SYM_MINUS) {
      not = 1;

      dimacs_getSymbol();
    }

    if (symbol == SYM_INTEGER) {
      if (literal <= 0) {
        // if literal < 0 it is equal to INT64_MIN which we treat here as 0
        dimacs_getSymbol();

        return;
      } else if (literal > numberOfSATVariables) {
        syntaxErrorMessage((uint64_t*) "clause exceeds declared number of variables");

        exit(EXITCODE_PARSERERROR);
      }

      // literal encoding starts at 0
      literal = literal - 1;

      if (not)
        *(SATInstance + clause * 2 * numberOfSATVariables + 2 * literal + 1) = TRUE;
      else
        *(SATInstance + clause * 2 * numberOfSATVariables + 2 * literal) = TRUE;
    } else if (symbol == SYM_EOF)
      return;
    else
      syntaxErrorSymbol(SYM_INTEGER);

    dimacs_getSymbol();
  }
}

void dimacs_getInstance() {
  uint64_t clauses;

  clauses = 0;

  while (clauses < numberOfSATClauses)
    if (symbol != SYM_EOF) {
      dimacs_getClause(clauses);

      clauses = clauses + 1;
    } else {
      syntaxErrorMessage((uint64_t*) "instance has fewer clauses than declared");

      exit(EXITCODE_PARSERERROR);
    }

  if (symbol != SYM_EOF) {
    syntaxErrorMessage((uint64_t*) "instance has more clauses than declared");

    exit(EXITCODE_PARSERERROR);
  }
}

void selfie_loadDimacs() {
  sourceName = getArgument();

  print(selfieName);
  print((uint64_t*) ": this is selfie loading SAT instance ");
  print(sourceName);
  println();

  // assert: sourceName is mapped and not longer than maxFilenameLength

  sourceFD = signExtend(open(sourceName, O_RDONLY, 0), INT_BITWIDTH);

  if (signedLessThan(sourceFD, 0)) {
    print(selfieName);
    print((uint64_t*) ": could not open input file ");
    print(sourceName);
    println();

    exit(EXITCODE_IOERROR);
  }

  resetScanner();

  // ignore all comments before problem
  dimacs_findNextCharacter(1);

  dimacs_getSymbol();

  dimacs_word((uint64_t*) "p");
  dimacs_word((uint64_t*) "cnf");

  numberOfSATVariables = dimacs_number();

  SATAssignment = (uint64_t*) smalloc(numberOfSATVariables * SIZEOFUINT64);

  numberOfSATClauses = dimacs_number();

  SATInstance = (uint64_t*) smalloc(numberOfSATClauses * 2 * numberOfSATVariables * SIZEOFUINT64);

  dimacs_getInstance();

  print(selfieName);
  print((uint64_t*) ": ");
  printInteger(numberOfSATClauses);
  print((uint64_t*) " clauses with ");
  printInteger(numberOfSATVariables);
  print((uint64_t*) " declared variables loaded from ");
  print(sourceName);
  println();

  dimacsName = sourceName;
}

void selfie_sat() {
  uint64_t variable;

  selfie_loadDimacs();

  if (dimacsName == (uint64_t*) 0) {
    print(selfieName);
    print((uint64_t*) ": nothing to SAT solve");
    println();

    return;
  }

  selfie_printDimacs();

  if (babysat(0) == SAT) {
    print(selfieName);
    print((uint64_t*) ": ");
    print(dimacsName);
    print((uint64_t*) " is satisfiable with ");

    variable = 0;

    while (variable < numberOfSATVariables) {
      if (*(SATAssignment + variable) == FALSE)
        print((uint64_t*) "-");

      printInteger(variable + 1);
      print((uint64_t*) " ");

      variable = variable + 1;
    }
  } else {
    print(selfieName);
    print((uint64_t*) ": ");
    print(dimacsName);
    print((uint64_t*) " is unsatisfiable");
  }

  println();
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

uint64_t numberOfRemainingArguments() {
  return selfie_argc;
}

uint64_t* remainingArguments() {
  return selfie_argv;
}

uint64_t* peekArgument() {
  if (numberOfRemainingArguments() > 0)
    return (uint64_t*) *selfie_argv;
  else
    return (uint64_t*) 0;
}

uint64_t* getArgument() {
  uint64_t* argument;

  argument = peekArgument();

  if (numberOfRemainingArguments() > 0) {
    selfie_argc = selfie_argc - 1;
    selfie_argv = selfie_argv + 1;
  }

  return argument;
}

void setArgument(uint64_t* argv) {
  *selfie_argv = (uint64_t) argv;
}

void printUsage() {
  print(selfieName);
  print((uint64_t*) ": usage: ");
  print((uint64_t*) "selfie { -c { source } | -o binary | -s assembly | -l binary | -sat dimacs } ");
  print((uint64_t*) "[ ( -m | -d | -y | -min | -mob ) size ... ]");
  println();
}

uint64_t selfie() {
  uint64_t* option;

  if (numberOfRemainingArguments() == 0)
    printUsage();
  else {
    initScanner();
    initRegister();
    initDecoder();
    initInterpreter();
    initKernel();

    while (numberOfRemainingArguments() > 0) {
      option = getArgument();

      if (stringCompare(option, (uint64_t*) "-c"))
        selfie_compile();
      else if (numberOfRemainingArguments() == 0) {
        // remaining options have at least one argument
        printUsage();

        return -1;
      } else if (stringCompare(option, (uint64_t*) "-o"))
        selfie_output();
      else if (stringCompare(option, (uint64_t*) "-s"))
        selfie_disassemble();
      else if (stringCompare(option, (uint64_t*) "-l"))
        selfie_load();
      else if (stringCompare(option, (uint64_t*) "-sat"))
        selfie_sat();
      else if (stringCompare(option, (uint64_t*) "-m"))
        return selfie_run(MIPSTER);
      else if (stringCompare(option, (uint64_t*) "-d")) {
        debug = 1;

        return selfie_run(MIPSTER);
      } else if (stringCompare(option, (uint64_t*) "-y"))
        return selfie_run(HYPSTER);
      else if (stringCompare(option, (uint64_t*) "-min"))
        return selfie_run(MINSTER);
      else if (stringCompare(option, (uint64_t*) "-mob"))
        return selfie_run(MOBSTER);
      else {
        printUsage();

        return -1;
      }
    }
  }

  return 0;
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  initSelfie((uint64_t) argc, (uint64_t*) argv);

  initLibrary();

  return signShrink(selfie(), INT_BITWIDTH);
}