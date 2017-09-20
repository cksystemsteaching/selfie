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
//    a tiny but powerful subset of MIPS32 called MIPSter,
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
// minimal operating system support in the form of MIPS32 o32 system calls
// built into the emulator.
//
// C* is a tiny Turing-complete subset of C that includes dereferencing
// (the * operator) but excludes composite data types, bitwise and Boolean
// operators, and many other features. There are only signed 32-bit
// integers and 32-bit pointers as well as character and string literals.
// This choice turns out to be helpful for students to understand the
// true role of composite data types such as arrays and records.
// Bitwise operations are implemented in libcstar using signed integer
// arithmetics helping students gain true understanding of two's complement.
// C* is supposed to be close to the minimum necessary for implementing
// a self-compiling, single-pass, recursive-descent compiler. C* can be
// taught in around two weeks of classes depending on student background.
//
// The compiler can readily be extended to compile features missing in C*
// and to improve performance of the generated code. The compiler generates
// MIPSter executables that can directly be executed by the emulator or
// written to a file in a simple, custom-defined format. Support of standard
// MIPS32 ELF binaries should be easy but remains future work.
//
// MIPSter is a tiny Turing-complete subset of the MIPS32 instruction set.
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

void exit(uint32_t code);
uint32_t read(uint32_t fd, uint32_t* buffer, uint32_t bytesToRead);
uint32_t write(uint32_t fd, uint32_t* buffer, uint32_t bytesToWrite);
uint32_t open(uint32_t* filename, uint32_t flags, uint32_t mode);
uint32_t* malloc(uint32_t size);

// -----------------------------------------------------------------
// ----------------------- LIBRARY PROCEDURES ----------------------
// -----------------------------------------------------------------

void initLibrary();
void resetLibrary();

uint32_t addWrap(uint32_t a, uint32_t b);
uint32_t subtractWrap(uint32_t a, uint32_t b);
uint32_t multiplyWrap(uint32_t a, uint32_t b);

void checkDivision(uint32_t a, uint32_t b);

uint32_t twoToThePowerOf(uint32_t p);
uint32_t leftShift(uint32_t n, uint32_t b);
uint32_t rightShift(uint32_t n, uint32_t b);
uint32_t signedLessThan(uint32_t lhs, uint32_t rhs);
uint32_t signedGreaterThan(uint32_t lhs, uint32_t rhs);

uint32_t  loadCharacter(uint32_t* s, uint32_t i);
uint32_t* storeCharacter(uint32_t* s, uint32_t i, uint32_t c);

uint32_t  stringLength(uint32_t* s);
void stringReverse(uint32_t* s);
uint32_t  stringCompare(uint32_t* s, uint32_t* t);

uint32_t  atoi(uint32_t* s);
uint32_t* itoa(uint32_t n, uint32_t* s, uint32_t b, uint32_t a, uint32_t p);

uint32_t fixedPointRatio(uint32_t a, uint32_t b);

void putCharacter(uint32_t c);

void print(uint32_t* s);
void println();

void printCharacter(uint32_t c);
void printString(uint32_t* s);
void printInteger(uint32_t n);
void printFixedPointPercentage(uint32_t a, uint32_t b);
void printFixedPointRatio(uint32_t a, uint32_t b);
void printHexadecimal(uint32_t n, uint32_t a);
void printOctal(uint32_t n, uint32_t a);
void printBinary(uint32_t n, uint32_t a);

uint32_t roundUp(uint32_t n, uint32_t m);

uint32_t* smalloc(uint32_t size);
uint32_t* zalloc(uint32_t size);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint32_t CHAR_EOF          = -1; // end of file
uint32_t CHAR_TAB          = 9;  // ASCII code 9  = tabulator
uint32_t CHAR_LF           = 10; // ASCII code 10 = line feed
uint32_t CHAR_CR           = 13; // ASCII code 13 = carriage return
uint32_t CHAR_SPACE        = ' ';
uint32_t CHAR_SEMICOLON    = ';';
uint32_t CHAR_PLUS         = '+';
uint32_t CHAR_DASH         = '-';
uint32_t CHAR_ASTERISK     = '*';
uint32_t CHAR_SLASH        = '/';
uint32_t CHAR_UNDERSCORE   = '_';
uint32_t CHAR_EQUAL        = '=';
uint32_t CHAR_LPARENTHESIS = '(';
uint32_t CHAR_RPARENTHESIS = ')';
uint32_t CHAR_LBRACE       = '{';
uint32_t CHAR_RBRACE       = '}';
uint32_t CHAR_COMMA        = ',';
uint32_t CHAR_LT           = '<';
uint32_t CHAR_GT           = '>';
uint32_t CHAR_EXCLAMATION  = '!';
uint32_t CHAR_PERCENTAGE   = '%';
uint32_t CHAR_SINGLEQUOTE  = 39; // ASCII code 39 = '
uint32_t CHAR_DOUBLEQUOTE  = '"';

uint32_t SIZEOFINT     = 4; // must be the same as WORDSIZE
uint32_t SIZEOFINTSTAR = 4; // must be the same as WORDSIZE

uint32_t* power_of_two_table;

uint32_t INT_MAX; // maximum numerical value of a signed 32-bit integer
uint32_t INT_MIN; // minimum numerical value of a signed 32-bit integer

uint32_t UINT_MAX; // maximum numerical value of a unsigned 32-bit integer
uint32_t UINT_MIN; // minimum numerical value of a unsigned 32-bit integer

uint32_t INT16_MAX; // maximum numerical value of a signed 16-bit integer
uint32_t INT16_MIN; // minimum numerical value of a signed 16-bit integer

uint32_t INT_OVERFLOW = 0; // indicates if an integer overflow occurred

uint32_t OVERFLOW_NO  = 0;
uint32_t OVERFLOW_YES = 1;

uint32_t maxFilenameLength = 128;

uint32_t* character_buffer; // buffer for reading and writing characters
uint32_t* integer_buffer;   // buffer for printing integers
uint32_t* filename_buffer;  // buffer for opening files
uint32_t* binary_buffer;    // buffer for binary I/O

// flags for opening read-only files
// LINUX:       0 = 0x0000 = O_RDONLY (0x0000)
// MAC:         0 = 0x0000 = O_RDONLY (0x0000)
// WINDOWS: 32768 = 0x8000 = _O_BINARY (0x8000) | _O_RDONLY (0x0000)
// since LINUX/MAC do not seem to mind about _O_BINARY set
// we use the WINDOWS flags as default
uint32_t O_RDONLY = 32768;

// flags for opening write-only files
// MAC: 1537 = 0x0601 = O_CREAT (0x0200) | O_TRUNC (0x0400) | O_WRONLY (0x0001)
uint32_t MAC_O_CREAT_TRUNC_WRONLY = 1537;

// LINUX: 577 = 0x0241 = O_CREAT (0x0040) | O_TRUNC (0x0200) | O_WRONLY (0x0001)
uint32_t LINUX_O_CREAT_TRUNC_WRONLY = 577;

// WINDOWS: 33537 = 0x8301 = _O_BINARY (0x8000) | _O_CREAT (0x0100) | _O_TRUNC (0x0200) | _O_WRONLY (0x0001)
uint32_t WINDOWS_O_BINARY_CREAT_TRUNC_WRONLY = 33537;

// flags for rw-r--r-- file permissions
// 420 = 00644 = S_IRUSR (00400) | S_IWUSR (00200) | S_IRGRP (00040) | S_IROTH (00004)
// these flags seem to be working for LINUX, MAC, and WINDOWS
uint32_t S_IRUSR_IWUSR_IRGRP_IROTH = 420;

// ------------------------ GLOBAL VARIABLES -----------------------

uint32_t numberOfWrittenCharacters = 0;

uint32_t* outputName = (uint32_t*) 0;
uint32_t  outputFD   = 1;

// ------------------------- INITIALIZATION ------------------------

void initLibrary() {
  uint32_t i;

  // powers of two table with 31 entries for 2^0 to 2^30
  // avoiding overflow for 2^31 and larger numbers with 32-bit signed integers
  power_of_two_table = smalloc(31 * SIZEOFINT);

  *power_of_two_table = 1; // 2^0 == 1

  i = 1;

  while (i < 31) {
    // compute powers of two incrementally using this recurrence relation
    *(power_of_two_table + i) = *(power_of_two_table + (i - 1)) * 2;

    i = i + 1;
  }

  // compute INT_MAX and INT_MIN without integer overflows
  INT_MAX = (twoToThePowerOf(30) - 1) * 2 + 1;
  INT_MIN = -INT_MAX - 1;

  UINT_MAX = (twoToThePowerOf(31) - 1) * 2 + 1;
  UINT_MIN = 0;

  INT16_MAX = twoToThePowerOf(15) - 1;
  INT16_MIN = -INT16_MAX - 1;

  // allocate and touch to make sure memory is mapped for read calls
  character_buffer  = smalloc(SIZEOFINT);
  *character_buffer = 0;

  // accommodate at least 32-bit numbers for itoa, no mapping needed
  integer_buffer = smalloc(33);

  // does not need to be mapped
  filename_buffer = smalloc(maxFilenameLength);

  // allocate and touch to make sure memory is mapped for read calls
  binary_buffer  = smalloc(SIZEOFINT);
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

void printSymbol(uint32_t symbol);
void printLineNumber(uint32_t* message, uint32_t line);

void syntaxErrorMessage(uint32_t* message);
void syntaxErrorCharacter(uint32_t character);
void syntaxErrorIdentifier(uint32_t* expected);

void getCharacter();

uint32_t isCharacterNewLine();
uint32_t isCharacterWhitespace();

uint32_t findNextCharacter();

uint32_t isCharacterLetter();
uint32_t isCharacterDigit();
uint32_t isCharacterLetterOrDigitOrUnderscore();
uint32_t isCharacterNotDoubleQuoteOrNewLineOrEOF();

uint32_t identifierStringMatch(uint32_t stringIndex);
uint32_t identifierOrKeyword();

void getSymbol();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint32_t SYM_EOF          = -1; // end of file
uint32_t SYM_IDENTIFIER   = 0;  // identifier
uint32_t SYM_INTEGER      = 1;  // integer
uint32_t SYM_VOID         = 2;  // VOID
uint32_t SYM_UINT32       = 3;  // uint32_t
uint32_t SYM_SEMICOLON    = 4;  // ;
uint32_t SYM_IF           = 5;  // IF
uint32_t SYM_ELSE         = 6;  // ELSE
uint32_t SYM_PLUS         = 7;  // +
uint32_t SYM_MINUS        = 8;  // -
uint32_t SYM_ASTERISK     = 9;  // *
uint32_t SYM_DIV          = 10; // /
uint32_t SYM_EQUALITY     = 11; // ==
uint32_t SYM_ASSIGN       = 12; // =
uint32_t SYM_LPARENTHESIS = 13; // (
uint32_t SYM_RPARENTHESIS = 14; // )
uint32_t SYM_LBRACE       = 15; // {
uint32_t SYM_RBRACE       = 16; // }
uint32_t SYM_WHILE        = 17; // WHILE
uint32_t SYM_RETURN       = 18; // RETURN
uint32_t SYM_COMMA        = 19; // ,
uint32_t SYM_LT           = 20; // <
uint32_t SYM_LEQ          = 21; // <=
uint32_t SYM_GT           = 22; // >
uint32_t SYM_GEQ          = 23; // >=
uint32_t SYM_NOTEQ        = 24; // !=
uint32_t SYM_MOD          = 25; // %
uint32_t SYM_CHARACTER    = 26; // character
uint32_t SYM_STRING       = 27; // string

uint32_t* SYMBOLS; // strings representing symbols

uint32_t maxIdentifierLength = 64; // maximum number of characters in an identifier
uint32_t maxIntegerLength    = 10; // maximum number of characters in an integer
uint32_t maxStringLength     = 128; // maximum number of characters in a string

// ------------------------ GLOBAL VARIABLES -----------------------

uint32_t lineNumber = 1; // current line number for error reporting

uint32_t* identifier = (uint32_t*) 0; // stores scanned identifier as string
uint32_t* integer    = (uint32_t*) 0; // stores scanned integer as string
uint32_t* string     = (uint32_t*) 0; // stores scanned string

uint32_t literal = 0; // stores numerical value of scanned integer or character

uint32_t mayBeINTMIN = 0; // allow INT_MIN if '-' was scanned before
uint32_t isINTMIN    = 0; // flag to indicate that INT_MIN was scanned

uint32_t character; // most recently read character

uint32_t numberOfReadCharacters = 0;

uint32_t symbol; // most recently recognized symbol

uint32_t numberOfIgnoredCharacters = 0;
uint32_t numberOfComments          = 0;
uint32_t numberOfScannedSymbols    = 0;

uint32_t* sourceName = (uint32_t*) 0; // name of source file
uint32_t  sourceFD   = 0;        // file descriptor of open source file

// ------------------------- INITIALIZATION ------------------------

void initScanner () {
  SYMBOLS = smalloc(28 * SIZEOFINTSTAR);

  *(SYMBOLS + SYM_IDENTIFIER)   = (uint32_t) "identifier";
  *(SYMBOLS + SYM_INTEGER)      = (uint32_t) "integer";
  *(SYMBOLS + SYM_VOID)         = (uint32_t) "void";
  *(SYMBOLS + SYM_UINT32)       = (uint32_t) "uint32_t";
  *(SYMBOLS + SYM_SEMICOLON)    = (uint32_t) ";";
  *(SYMBOLS + SYM_IF)           = (uint32_t) "if";
  *(SYMBOLS + SYM_ELSE)         = (uint32_t) "else";
  *(SYMBOLS + SYM_PLUS)         = (uint32_t) "+";
  *(SYMBOLS + SYM_MINUS)        = (uint32_t) "-";
  *(SYMBOLS + SYM_ASTERISK)     = (uint32_t) "*";
  *(SYMBOLS + SYM_DIV)          = (uint32_t) "/";
  *(SYMBOLS + SYM_EQUALITY)     = (uint32_t) "==";
  *(SYMBOLS + SYM_ASSIGN)       = (uint32_t) "=";
  *(SYMBOLS + SYM_LPARENTHESIS) = (uint32_t) "(";
  *(SYMBOLS + SYM_RPARENTHESIS) = (uint32_t) ")";
  *(SYMBOLS + SYM_LBRACE)       = (uint32_t) "{";
  *(SYMBOLS + SYM_RBRACE)       = (uint32_t) "}";
  *(SYMBOLS + SYM_WHILE)        = (uint32_t) "while";
  *(SYMBOLS + SYM_RETURN)       = (uint32_t) "return";
  *(SYMBOLS + SYM_COMMA)        = (uint32_t) ",";
  *(SYMBOLS + SYM_LT)           = (uint32_t) "<";
  *(SYMBOLS + SYM_LEQ)          = (uint32_t) "<=";
  *(SYMBOLS + SYM_GT)           = (uint32_t) ">";
  *(SYMBOLS + SYM_GEQ)          = (uint32_t) ">=";
  *(SYMBOLS + SYM_NOTEQ)        = (uint32_t) "!=";
  *(SYMBOLS + SYM_MOD)          = (uint32_t) "%";
  *(SYMBOLS + SYM_CHARACTER)    = (uint32_t) "character";
  *(SYMBOLS + SYM_STRING)       = (uint32_t) "string";

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

void createSymbolTableEntry(uint32_t which, uint32_t* string, uint32_t line, uint32_t class, uint32_t type, uint32_t value, uint32_t address);

uint32_t* searchSymbolTable(uint32_t* entry, uint32_t* string, uint32_t class);
uint32_t* getScopedSymbolTableEntry(uint32_t* string, uint32_t class);

uint32_t isUndefinedProcedure(uint32_t* entry);
uint32_t reportUndefinedProcedures();

// symbol table entry:
// +----+---------+
// |  0 | next    | pointer to next entry
// |  1 | string  | identifier string, string literal
// |  2 | line#   | source line number
// |  3 | class   | VARIABLE, PROCEDURE, STRING
// |  4 | type    | INT_T, INTSTAR_T, VOID_T
// |  5 | value   | VARIABLE: initial value
// |  6 | address | VARIABLE: offset, PROCEDURE: address, STRING: offset
// |  7 | scope   | REG_GP, REG_FP
// +----+---------+

uint32_t* getNextEntry(uint32_t* entry)  { return (uint32_t*) *entry; }
uint32_t* getString(uint32_t* entry)     { return (uint32_t*) *(entry + 1); }
uint32_t  getLineNumber(uint32_t* entry) { return        *(entry + 2); }
uint32_t  getClass(uint32_t* entry)      { return        *(entry + 3); }
uint32_t  getType(uint32_t* entry)       { return        *(entry + 4); }
uint32_t  getValue(uint32_t* entry)      { return        *(entry + 5); }
uint32_t  getAddress(uint32_t* entry)    { return        *(entry + 6); }
uint32_t  getScope(uint32_t* entry)      { return        *(entry + 7); }

void setNextEntry(uint32_t* entry, uint32_t* next)    { *entry       = (uint32_t) next; }
void setString(uint32_t* entry, uint32_t* identifier) { *(entry + 1) = (uint32_t) identifier; }
void setLineNumber(uint32_t* entry, uint32_t line)    { *(entry + 2) = line; }
void setClass(uint32_t* entry, uint32_t class)        { *(entry + 3) = class; }
void setType(uint32_t* entry, uint32_t type)          { *(entry + 4) = type; }
void setValue(uint32_t* entry, uint32_t value)        { *(entry + 5) = value; }
void setAddress(uint32_t* entry, uint32_t address)    { *(entry + 6) = address; }
void setScope(uint32_t* entry, uint32_t scope)        { *(entry + 7) = scope; }

// ------------------------ GLOBAL CONSTANTS -----------------------

// classes
uint32_t VARIABLE  = 1;
uint32_t PROCEDURE = 2;
uint32_t STRING    = 3;

// types
uint32_t INT_T     = 1;
uint32_t INTSTAR_T = 2;
uint32_t VOID_T    = 3;

// symbol tables
uint32_t GLOBAL_TABLE  = 1;
uint32_t LOCAL_TABLE   = 2;
uint32_t LIBRARY_TABLE = 3;

// ------------------------ GLOBAL VARIABLES -----------------------

// table pointers
uint32_t* global_symbol_table  = (uint32_t*) 0;
uint32_t* local_symbol_table   = (uint32_t*) 0;
uint32_t* library_symbol_table = (uint32_t*) 0;

uint32_t numberOfGlobalVariables = 0;
uint32_t numberOfProcedures      = 0;
uint32_t numberOfStrings         = 0;

// ------------------------- INITIALIZATION ------------------------

void resetSymbolTables() {
  global_symbol_table  = (uint32_t*) 0;
  local_symbol_table   = (uint32_t*) 0;
  library_symbol_table = (uint32_t*) 0;

  numberOfGlobalVariables = 0;
  numberOfProcedures      = 0;
  numberOfStrings         = 0;
}

// -----------------------------------------------------------------
// ---------------------------- PARSER -----------------------------
// -----------------------------------------------------------------

void resetParser();

uint32_t isNotRbraceOrEOF();
uint32_t isExpression();
uint32_t isLiteral();
uint32_t isStarOrDivOrModulo();
uint32_t isPlusOrMinus();
uint32_t isComparison();

uint32_t lookForFactor();
uint32_t lookForStatement();
uint32_t lookForType();

void save_temporaries();
void restore_temporaries(uint32_t numberOfTemporaries);

void syntaxErrorSymbol(uint32_t expected);
void syntaxErrorUnexpected();
void printType(uint32_t type);
void typeWarning(uint32_t expected, uint32_t found);

uint32_t* getVariable(uint32_t* variable);
uint32_t  load_variable(uint32_t* variable);
void load_integer(uint32_t value);
void load_string(uint32_t* string);

uint32_t  help_call_codegen(uint32_t* entry, uint32_t* procedure);
void help_procedure_prologue(uint32_t localVariables);
void help_procedure_epilogue(uint32_t parameters);

uint32_t  gr_call(uint32_t* procedure);
uint32_t  gr_factor();
uint32_t  gr_term();
uint32_t  gr_simpleExpression();
uint32_t  gr_expression();
void gr_while();
void gr_if();
void gr_return();
void gr_statement();
uint32_t  gr_type();
void gr_variable(uint32_t offset);
uint32_t  gr_initialization(uint32_t type);
void gr_procedure(uint32_t* procedure, uint32_t type);
void gr_cstar();

// ------------------------ GLOBAL VARIABLES -----------------------

uint32_t allocatedTemporaries = 0; // number of allocated temporaries

uint32_t allocatedMemory = 0; // number of bytes for global variables and strings

uint32_t returnBranches = 0; // fixup chain for return statements

uint32_t returnType = 0; // return type of currently parsed procedure

uint32_t mainJump = 0; // address where JAL instruction to main procedure is

uint32_t numberOfCalls       = 0;
uint32_t numberOfAssignments = 0;
uint32_t numberOfWhile       = 0;
uint32_t numberOfIf          = 0;
uint32_t numberOfReturn      = 0;

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

void emitLeftShiftBy(uint32_t reg, uint32_t b);
void emitRightShiftBy(uint32_t reg, uint32_t b);
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

void printRegister(uint32_t reg);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint32_t NUMBEROFREGISTERS = 32;

uint32_t REG_ZR = 0;
uint32_t REG_AT = 1;
uint32_t REG_V0 = 2;
uint32_t REG_V1 = 3;
uint32_t REG_A0 = 4;
uint32_t REG_A1 = 5;
uint32_t REG_A2 = 6;
uint32_t REG_A3 = 7;
uint32_t REG_T0 = 8;
uint32_t REG_T1 = 9;
uint32_t REG_T2 = 10;
uint32_t REG_T3 = 11;
uint32_t REG_T4 = 12;
uint32_t REG_T5 = 13;
uint32_t REG_T6 = 14;
uint32_t REG_T7 = 15;
uint32_t REG_S0 = 16;
uint32_t REG_S1 = 17;
uint32_t REG_S2 = 18;
uint32_t REG_S3 = 19;
uint32_t REG_S4 = 20;
uint32_t REG_S5 = 21;
uint32_t REG_S6 = 22;
uint32_t REG_S7 = 23;
uint32_t REG_T8 = 24;
uint32_t REG_T9 = 25;
uint32_t REG_K0 = 26;
uint32_t REG_K1 = 27;
uint32_t REG_GP = 28;
uint32_t REG_SP = 29;
uint32_t REG_FP = 30;
uint32_t REG_RA = 31;

uint32_t* REGISTERS; // strings representing registers

// ------------------------- INITIALIZATION ------------------------

void initRegister() {
  REGISTERS = smalloc(NUMBEROFREGISTERS * SIZEOFINTSTAR);

  *(REGISTERS + REG_ZR) = (uint32_t) "$zero";
  *(REGISTERS + REG_AT) = (uint32_t) "$at";
  *(REGISTERS + REG_V0) = (uint32_t) "$v0";
  *(REGISTERS + REG_V1) = (uint32_t) "$v1";
  *(REGISTERS + REG_A0) = (uint32_t) "$a0";
  *(REGISTERS + REG_A1) = (uint32_t) "$a1";
  *(REGISTERS + REG_A2) = (uint32_t) "$a2";
  *(REGISTERS + REG_A3) = (uint32_t) "$a3";
  *(REGISTERS + REG_T0) = (uint32_t) "$t0";
  *(REGISTERS + REG_T1) = (uint32_t) "$t1";
  *(REGISTERS + REG_T2) = (uint32_t) "$t2";
  *(REGISTERS + REG_T3) = (uint32_t) "$t3";
  *(REGISTERS + REG_T4) = (uint32_t) "$t4";
  *(REGISTERS + REG_T5) = (uint32_t) "$t5";
  *(REGISTERS + REG_T6) = (uint32_t) "$t6";
  *(REGISTERS + REG_T7) = (uint32_t) "$t7";
  *(REGISTERS + REG_S0) = (uint32_t) "$s0";
  *(REGISTERS + REG_S1) = (uint32_t) "$s1";
  *(REGISTERS + REG_S2) = (uint32_t) "$s2";
  *(REGISTERS + REG_S3) = (uint32_t) "$s3";
  *(REGISTERS + REG_S4) = (uint32_t) "$s4";
  *(REGISTERS + REG_S5) = (uint32_t) "$s5";
  *(REGISTERS + REG_S6) = (uint32_t) "$s6";
  *(REGISTERS + REG_S7) = (uint32_t) "$s7";
  *(REGISTERS + REG_T8) = (uint32_t) "$t8";
  *(REGISTERS + REG_T9) = (uint32_t) "$t9";
  *(REGISTERS + REG_K0) = (uint32_t) "$k0";
  *(REGISTERS + REG_K1) = (uint32_t) "$k1";
  *(REGISTERS + REG_GP) = (uint32_t) "$gp";
  *(REGISTERS + REG_SP) = (uint32_t) "$sp";
  *(REGISTERS + REG_FP) = (uint32_t) "$fp";
  *(REGISTERS + REG_RA) = (uint32_t) "$ra";
}

// -----------------------------------------------------------------
// ---------------------------- ENCODER ----------------------------
// -----------------------------------------------------------------

uint32_t encodeRFormat(uint32_t opcode, uint32_t rs, uint32_t rt, uint32_t rd, uint32_t function);
uint32_t encodeIFormat(uint32_t opcode, uint32_t rs, uint32_t rt, uint32_t immediate);
uint32_t encodeJFormat(uint32_t opcode, uint32_t instr_index);

// -----------------------------------------------------------------
// ---------------------------- DECODER ----------------------------
// -----------------------------------------------------------------

void initDecoder();

uint32_t getOpcode(uint32_t instruction);
uint32_t getRS(uint32_t instruction);
uint32_t getRT(uint32_t instruction);
uint32_t getRD(uint32_t instruction);
uint32_t getFunction(uint32_t instruction);
uint32_t getImmediate(uint32_t instruction);
uint32_t getInstrIndex(uint32_t instruction);
uint32_t signExtend(uint32_t immediate);

void decodeRFormat();
void decodeIFormat();
void decodeJFormat();

void decode();

void printOpcode(uint32_t opcode);
void printFunction(uint32_t function);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint32_t OP_SPECIAL = 0;
uint32_t OP_J       = 2;
uint32_t OP_JAL     = 3;
uint32_t OP_BEQ     = 4;
uint32_t OP_ADDIU   = 9;
uint32_t OP_LW      = 35;
uint32_t OP_SW      = 43;

uint32_t* OPCODES; // strings representing MIPS opcodes

uint32_t FCT_NOP     = 0;
uint32_t FCT_JR      = 8;
uint32_t FCT_SYSCALL = 12;
uint32_t FCT_MFHI    = 16;
uint32_t FCT_MFLO    = 18;
uint32_t FCT_MULTU   = 25;
uint32_t FCT_DIVU    = 27;
uint32_t FCT_ADDU    = 33;
uint32_t FCT_SUBU    = 35;
uint32_t FCT_SLT     = 42;

uint32_t* FUNCTIONS; // strings representing MIPS functions

// ------------------------ GLOBAL VARIABLES -----------------------

uint32_t opcode      = 0;
uint32_t rs          = 0;
uint32_t rt          = 0;
uint32_t rd          = 0;
uint32_t immediate   = 0;
uint32_t function    = 0;
uint32_t instr_index = 0;

// ------------------------- INITIALIZATION ------------------------

void initDecoder() {
  OPCODES = smalloc(44 * SIZEOFINTSTAR);

  *(OPCODES + OP_SPECIAL) = (uint32_t) "nop";
  *(OPCODES + OP_J)       = (uint32_t) "j";
  *(OPCODES + OP_JAL)     = (uint32_t) "jal";
  *(OPCODES + OP_BEQ)     = (uint32_t) "beq";
  *(OPCODES + OP_ADDIU)   = (uint32_t) "addiu";
  *(OPCODES + OP_LW)      = (uint32_t) "lw";
  *(OPCODES + OP_SW)      = (uint32_t) "sw";

  FUNCTIONS = smalloc(43 * SIZEOFINTSTAR);

  *(FUNCTIONS + FCT_NOP)     = (uint32_t) "nop";
  *(FUNCTIONS + FCT_JR)      = (uint32_t) "jr";
  *(FUNCTIONS + FCT_SYSCALL) = (uint32_t) "syscall";
  *(FUNCTIONS + FCT_MFHI)    = (uint32_t) "mfhi";
  *(FUNCTIONS + FCT_MFLO)    = (uint32_t) "mflo";
  *(FUNCTIONS + FCT_MULTU)   = (uint32_t) "multu";
  *(FUNCTIONS + FCT_DIVU)    = (uint32_t) "divu";
  *(FUNCTIONS + FCT_ADDU)    = (uint32_t) "addu";
  *(FUNCTIONS + FCT_SUBU)    = (uint32_t) "subu";
  *(FUNCTIONS + FCT_SLT)     = (uint32_t) "slt";
}

// -----------------------------------------------------------------
// ----------------------------- CODE ------------------------------
// -----------------------------------------------------------------

uint32_t  loadBinary(uint32_t baddr);
void storeBinary(uint32_t baddr, uint32_t instruction);

void emitInstruction(uint32_t instruction);
void emitRFormat(uint32_t opcode, uint32_t rs, uint32_t rt, uint32_t rd, uint32_t function);
void emitIFormat(uint32_t opcode, uint32_t rs, uint32_t rt, uint32_t immediate);
void emitJFormat(uint32_t opcode, uint32_t instr_index);

void fixup_relative(uint32_t fromAddress);
void fixup_absolute(uint32_t fromAddress, uint32_t toAddress);
void fixlink_absolute(uint32_t fromAddress, uint32_t toAddress);

uint32_t copyStringToBinary(uint32_t* s, uint32_t a);

void emitGlobalsStrings();

uint32_t openWriteOnly(uint32_t* name);

void selfie_output();

uint32_t* touch(uint32_t* memory, uint32_t length);

void selfie_load();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint32_t maxBinaryLength = 262144; // 256KB

// ------------------------ GLOBAL VARIABLES -----------------------

uint32_t* binary = (uint32_t*) 0; // binary of emitted instructions

uint32_t binaryLength = 0; // length of binary in bytes incl. globals & strings

uint32_t codeLength = 0; // length of code portion of binary in bytes

uint32_t* binaryName = (uint32_t*) 0; // file name of binary

uint32_t* sourceLineNumber = (uint32_t*) 0; // source line number per emitted instruction

uint32_t* assemblyName = (uint32_t*) 0; // name of assembly file
uint32_t  assemblyFD   = 0;        // file descriptor of open assembly file

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emitExit();
void implementExit(uint32_t* context);

void emitRead();
void implementRead(uint32_t* context);

void emitWrite();
void implementWrite(uint32_t* context);

void emitOpen();
uint32_t  down_loadString(uint32_t* table, uint32_t vaddr, uint32_t* s);
void implementOpen(uint32_t* context);

void emitMalloc();
uint32_t implementMalloc(uint32_t* context);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint32_t debug_read   = 0;
uint32_t debug_write  = 0;
uint32_t debug_open   = 0;

uint32_t debug_malloc = 0;

uint32_t SYSCALL_EXIT   = 4001;
uint32_t SYSCALL_READ   = 4003;
uint32_t SYSCALL_WRITE  = 4004;
uint32_t SYSCALL_OPEN   = 4005;

uint32_t SYSCALL_MALLOC = 4045;

// -----------------------------------------------------------------
// ----------------------- HYPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emitSwitch();
void doSwitch(uint32_t* toContext, uint32_t timeout);
void implementSwitch();
uint32_t* mipster_switch(uint32_t* toContext, uint32_t timeout);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint32_t SYSCALL_SWITCH = 4901;

uint32_t debug_switch = 0;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void initMemory(uint32_t megabytes);

uint32_t  loadPhysicalMemory(uint32_t* paddr);
void storePhysicalMemory(uint32_t* paddr, uint32_t data);

uint32_t FrameForPage(uint32_t* table, uint32_t page);
uint32_t getFrameForPage(uint32_t* table, uint32_t page);
uint32_t isPageMapped(uint32_t* table, uint32_t page);

uint32_t isValidVirtualAddress(uint32_t vaddr);
uint32_t getPageOfVirtualAddress(uint32_t vaddr);
uint32_t isVirtualAddressMapped(uint32_t* table, uint32_t vaddr);

uint32_t* tlb(uint32_t* table, uint32_t vaddr);

uint32_t  loadVirtualMemory(uint32_t* table, uint32_t vaddr);
void storeVirtualMemory(uint32_t* table, uint32_t vaddr, uint32_t data);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint32_t debug_tlb = 0;

// we use the unit [number of words] to prevent overflow problems in calculations
uint32_t MEGABYTE = 1048576;         // 1024 * 1024       one megabyte in [number of Bytes]
uint32_t MEGABYTEINWORDS = 262144;   // 1024 * 1024 / 4   one megabyte in [number of words]

uint32_t HIGHESTMEMORYADDRESS = -4;  // highest word aligned 32bit address in two's complement

uint32_t WORDSIZE = 4;               // must be the same as SIZEOFINT and SIZEOFINTSTAR

uint32_t PAGESIZE = 4096;            // we use standard 4KB pages [number of bytes] 
                                // (=> 12 pagebits: 2^12 == 4096)
uint32_t PAGESIZEINWORDS = 1024;     // page size in words [number of words]

uint32_t NUMBEROFPAGES = 1048576;    // 2^32 / PAGESIZE   maximum amount of pages in virtual memory.

// ------------------------ GLOBAL VARIABLES -----------------------

uint32_t pageFrameMemory = 0; // size of memory for frames [number of words]

// ------------------------- INITIALIZATION ------------------------

void initMemory(uint32_t megabytes) {
  if (megabytes < 0)
    megabytes = 0;
  else if (megabytes > 4096)
    megabytes = 4096;

  pageFrameMemory = megabytes * MEGABYTEINWORDS;
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

void fct_nop();
void fct_addu();
void fct_subu();
void fct_multu();
void fct_divu();
void fct_mfhi();
void fct_mflo();
void fct_slt();
void fct_jr();
void fct_syscall();

void op_addiu();
void op_lw();
void op_sw();
void op_beq();
void op_jal();
void op_j();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint32_t debug_overflow = 0;

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void initInterpreter();
void resetInterpreter();

void printException(uint32_t exception, uint32_t faultingPage);
void throwException(uint32_t exception, uint32_t faultingPage);

void fetch();
void execute();
void interrupt();

uint32_t* runUntilException();

uint32_t addressWithMaxCounter(uint32_t* counters, uint32_t max);

uint32_t  printCounters(uint32_t total, uint32_t* counters, uint32_t max);
void printProfile(uint32_t* message, uint32_t total, uint32_t* counters);

void selfie_disassemble();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint32_t EXCEPTION_NOEXCEPTION        = 0;
uint32_t EXCEPTION_PAGEFAULT          = 1;
uint32_t EXCEPTION_SYSCALL            = 2;
uint32_t EXCEPTION_TIMER              = 3;
uint32_t EXCEPTION_INVALIDADDRESS     = 4;
uint32_t EXCEPTION_UNKNOWNINSTRUCTION = 5;

uint32_t* EXCEPTIONS; // strings representing exceptions

uint32_t debug_exception = 0;

// number of instructions from context switch to timer interrupt
// CAUTION: avoid interrupting any kernel activities, keep TIMESLICE large
// TODO: implement proper interrupt controller to turn interrupts on and off
uint32_t TIMESLICE = 10000000;

uint32_t TIMEROFF = -1;

// ------------------------ GLOBAL VARIABLES -----------------------

uint32_t interpret = 0; // flag for executing or disassembling code

uint32_t debug = 0; // flag for logging code execution

// hardware thread state

uint32_t pc = 0; // program counter
uint32_t ir = 0; // instruction register

uint32_t* registers = (uint32_t*) 0; // general-purpose registers

uint32_t loReg = 0; // lo register for multiplication/division
uint32_t hiReg = 0; // hi register for multiplication/division

uint32_t* pt = (uint32_t*) 0; // page table

// core state

uint32_t timer = -1; // counter for timer interrupt

uint32_t trap = 0; // flag for creating a trap

uint32_t  calls           = 0;        // total number of executed procedure calls
uint32_t* callsPerAddress = (uint32_t*) 0; // number of executed calls of each procedure

uint32_t  loops           = 0;        // total number of executed loop iterations
uint32_t* loopsPerAddress = (uint32_t*) 0; // number of executed iterations of each loop

uint32_t  loads           = 0;        // total number of executed memory loads
uint32_t* loadsPerAddress = (uint32_t*) 0; // number of executed loads per load operation

uint32_t  stores           = 0;        // total number of executed memory stores
uint32_t* storesPerAddress = (uint32_t*) 0; // number of executed stores per store operation

// ------------------------- INITIALIZATION ------------------------

void initInterpreter() {
  EXCEPTIONS = smalloc(6 * SIZEOFINTSTAR);

  *(EXCEPTIONS + EXCEPTION_NOEXCEPTION)        = (uint32_t) "no exception";
  *(EXCEPTIONS + EXCEPTION_PAGEFAULT)          = (uint32_t) "page fault";
  *(EXCEPTIONS + EXCEPTION_SYSCALL)            = (uint32_t) "syscall";
  *(EXCEPTIONS + EXCEPTION_TIMER)              = (uint32_t) "timer interrupt";
  *(EXCEPTIONS + EXCEPTION_INVALIDADDRESS)     = (uint32_t) "invalid address";
  *(EXCEPTIONS + EXCEPTION_UNKNOWNINSTRUCTION) = (uint32_t) "unknown instruction";
}

void resetInterpreter() {
  pc = 0;
  ir = 0;

  registers = (uint32_t*) 0;

  loReg = 0;
  hiReg = 0;

  pt = (uint32_t*) 0;

  trap = 0;

  timer = TIMEROFF;

  if (interpret) {
    calls           = 0;
    callsPerAddress = zalloc(maxBinaryLength);

    loops           = 0;
    loopsPerAddress = zalloc(maxBinaryLength);

    loads           = 0;
    loadsPerAddress = zalloc(maxBinaryLength);

    stores           = 0;
    storesPerAddress = zalloc(maxBinaryLength);
  }
}

// -----------------------------------------------------------------
// ---------------------------- CONTEXTS ---------------------------
// -----------------------------------------------------------------

uint32_t* allocateContext(uint32_t* parent, uint32_t* vctxt, uint32_t* in);

uint32_t* findContext(uint32_t* parent, uint32_t* vctxt, uint32_t* in);

void freeContext(uint32_t* context);
uint32_t* deleteContext(uint32_t* context, uint32_t* from);

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

uint32_t nextContext(uint32_t* context)    { return (uint32_t) context; }
uint32_t prevContext(uint32_t* context)    { return (uint32_t) (context + 1); }
uint32_t PC(uint32_t* context)             { return (uint32_t) (context + 2); }
uint32_t Regs(uint32_t* context)           { return (uint32_t) (context + 3); }
uint32_t LoReg(uint32_t* context)          { return (uint32_t) (context + 4); }
uint32_t HiReg(uint32_t* context)          { return (uint32_t) (context + 5); }
uint32_t PT(uint32_t* context)             { return (uint32_t) (context + 6); }
uint32_t LoPage(uint32_t* context)         { return (uint32_t) (context + 7); }
uint32_t MePage(uint32_t* context)         { return (uint32_t) (context + 8); }
uint32_t HiPage(uint32_t* context)         { return (uint32_t) (context + 9); }
uint32_t ProgramBreak(uint32_t* context)   { return (uint32_t) (context + 10); }
uint32_t Exception(uint32_t* context)      { return (uint32_t) (context + 11); }
uint32_t FaultingPage(uint32_t* context)   { return (uint32_t) (context + 12); }
uint32_t ExitCode(uint32_t* context)       { return (uint32_t) (context + 13); }
uint32_t Parent(uint32_t* context)         { return (uint32_t) (context + 14); }
uint32_t VirtualContext(uint32_t* context) { return (uint32_t) (context + 15); }
uint32_t Name(uint32_t* context)           { return (uint32_t) (context + 16); }

uint32_t* getNextContext(uint32_t* context)    { return (uint32_t*) *context; }
uint32_t* getPrevContext(uint32_t* context)    { return (uint32_t*) *(context + 1); }
uint32_t  getPC(uint32_t* context)             { return        *(context + 2); }
uint32_t* getRegs(uint32_t* context)           { return (uint32_t*) *(context + 3); }
uint32_t  getLoReg(uint32_t* context)          { return        *(context + 4); }
uint32_t  getHiReg(uint32_t* context)          { return        *(context + 5); }
uint32_t* getPT(uint32_t* context)             { return (uint32_t*) *(context + 6); }
uint32_t  getLoPage(uint32_t* context)         { return        *(context + 7); }
uint32_t  getMePage(uint32_t* context)         { return        *(context + 8); }
uint32_t  getHiPage(uint32_t* context)         { return        *(context + 9); }
uint32_t  getProgramBreak(uint32_t* context)   { return        *(context + 10); }
uint32_t  getException(uint32_t* context)      { return        *(context + 11); }
uint32_t  getFaultingPage(uint32_t* context)   { return        *(context + 12); }
uint32_t  getExitCode(uint32_t* context)       { return        *(context + 13); }
uint32_t* getParent(uint32_t* context)         { return (uint32_t*) *(context + 14); }
uint32_t* getVirtualContext(uint32_t* context) { return (uint32_t*) *(context + 15); }
uint32_t* getName(uint32_t* context)           { return (uint32_t*) *(context + 16); }

void setNextContext(uint32_t* context, uint32_t* next) { *context       = (uint32_t) next; }
void setPrevContext(uint32_t* context, uint32_t* prev) { *(context + 1) = (uint32_t) prev; }
void setPC(uint32_t* context, uint32_t pc)             { *(context + 2) = pc; }
void setRegs(uint32_t* context, uint32_t* regs)        { *(context + 3) = (uint32_t) regs; }
void setLoReg(uint32_t* context, uint32_t loReg)       { *(context + 4) = loReg; }
void setHiReg(uint32_t* context, uint32_t hiReg)       { *(context + 5) = hiReg; }
void setPT(uint32_t* context, uint32_t* pt)            { *(context + 6) = (uint32_t) pt; }
void setLoPage(uint32_t* context, uint32_t loPage)     { *(context + 7) = loPage; }
void setMePage(uint32_t* context, uint32_t mePage)     { *(context + 8) = mePage; }
void setHiPage(uint32_t* context, uint32_t hiPage)     { *(context + 9) = hiPage; }
void setProgramBreak(uint32_t* context, uint32_t brk)  { *(context + 10) = brk; }
void setException(uint32_t* context, uint32_t exception) { *(context + 11) = exception; }
void setFaultingPage(uint32_t* context, uint32_t page) { *(context + 12) = page; }
void setExitCode(uint32_t* context, uint32_t code)     { *(context + 13) = code; }
void setParent(uint32_t* context, uint32_t* parent) { *(context + 14) = (uint32_t) parent; }
void setVirtualContext(uint32_t* context, uint32_t* vctxt) { *(context + 15) = (uint32_t) vctxt; }
void setName(uint32_t* context, uint32_t* name) { *(context + 16) = (uint32_t) name; }

// -----------------------------------------------------------------
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

void resetMicrokernel();

uint32_t* createContext(uint32_t* parent, uint32_t* vctxt);

uint32_t* cacheContext(uint32_t* vctxt);

void saveContext(uint32_t* context);

void mapPage(uint32_t* context, uint32_t page, uint32_t frame);

void restoreContext(uint32_t* context);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint32_t debug_create = 0;
uint32_t debug_map    = 0;

// ------------------------ GLOBAL VARIABLES -----------------------

uint32_t* currentContext = (uint32_t*) 0; // context currently running

uint32_t* usedContexts = (uint32_t*) 0; // doubly-linked list of used contexts
uint32_t* freeContexts = (uint32_t*) 0; // singly-linked list of free contexts

// ------------------------- INITIALIZATION ------------------------

void resetMicrokernel() {
  currentContext = (uint32_t*) 0;

  while (usedContexts != (uint32_t*) 0)
    usedContexts = deleteContext(usedContexts, usedContexts);
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

uint32_t pavailable();
uint32_t pused();

uint32_t* palloc();
void pfree(uint32_t* frame);

void mapAndStore(uint32_t* context, uint32_t vaddr, uint32_t data);

void up_loadBinary(uint32_t* context);

uint32_t  up_loadString(uint32_t* context, uint32_t* s, uint32_t SP);
void up_loadArguments(uint32_t* context, uint32_t argc, uint32_t* argv);

void mapUnmappedPages(uint32_t* context);

uint32_t isBootLevelZero();

uint32_t handleSystemCalls(uint32_t* context);

uint32_t mipster(uint32_t* toContext);
uint32_t minster(uint32_t* toContext);
uint32_t mobster(uint32_t* toContext);
uint32_t hypster(uint32_t* toContext);
uint32_t mixter(uint32_t* toContext, uint32_t mix);

uint32_t selfie_run(uint32_t machine);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint32_t* MY_CONTEXT = (uint32_t*) 0;

uint32_t DONOTEXIT = 0;
uint32_t EXIT = 1;

uint32_t EXITCODE_NOERROR = 0;
uint32_t EXITCODE_IOERROR = -1;
uint32_t EXITCODE_SCANNERERROR = -2;
uint32_t EXITCODE_PARSERERROR = -3;
uint32_t EXITCODE_COMPILERERROR = -4;
uint32_t EXITCODE_OUTOFVIRTUALMEMORY = -5;
uint32_t EXITCODE_OUTOFPHYSICALMEMORY = -6;
uint32_t EXITCODE_UNKNOWNSYSCALL = -7;
uint32_t EXITCODE_UNCAUGHTEXCEPTION = -8;

uint32_t MINSTER = 1;
uint32_t MIPSTER = 2;
uint32_t MOBSTER = 3;

uint32_t HYPSTER = 4;

// ------------------------ GLOBAL VARIABLES -----------------------

uint32_t nextPageFrame = 0;        // [number of words]

uint32_t usedPageFrameMemory = 0;  // [number of words]
uint32_t freePageFrameMemory = 0;  // [number of words]

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------   T H E O R E M  P R O V E R    ----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// -------------------------- SAT Solver ---------------------------
// -----------------------------------------------------------------

uint32_t FALSE = 0;
uint32_t TRUE  = 1;

uint32_t UNSAT = 0;
uint32_t SAT   = 1;

uint32_t* dimacsName = (uint32_t*) 0;

uint32_t numberOfSATVariables = 0;

 // numberOfSATVariables
uint32_t* SATAssignment = (uint32_t*) 0;

uint32_t numberOfSATClauses = 0;

// numberOfSATClauses * 2 * numberOfSATVariables
uint32_t* SATInstance = (uint32_t*) 0;

uint32_t clauseMayBeTrue(uint32_t* clauseAddress, uint32_t depth);
uint32_t instanceMayBeTrue(uint32_t depth);

uint32_t babysat(uint32_t depth);

// -----------------------------------------------------------------
// ----------------------- DIMACS CNF PARSER -----------------------
// -----------------------------------------------------------------

void selfie_printDimacs();

void dimacs_findNextCharacter(uint32_t newLine);
void dimacs_getSymbol();
void dimacs_word(uint32_t* word);
uint32_t  dimacs_number();
void dimacs_getClause(uint32_t clause);
void dimacs_getInstance();

void selfie_loadDimacs();

void selfie_sat();

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

void initSelfie(uint32_t argc, uint32_t* argv);

uint32_t numberOfRemainingArguments();
uint32_t* remainingArguments();

uint32_t* peekArgument();
uint32_t* getArgument();
void setArgument(uint32_t* argv);

void printUsage();

// ------------------------ GLOBAL VARIABLES -----------------------

uint32_t selfie_argc = 0;
uint32_t* selfie_argv = (uint32_t*) 0;

uint32_t* selfieName = (uint32_t*) 0;

// ------------------------- INITIALIZATION ------------------------

void initSelfie(uint32_t argc, uint32_t* argv) {
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

uint32_t addWrap(uint32_t a, uint32_t b) {
  // signed integer addition with wrap-around semantics and overflow detection
  // but without causing any integer overflow in the implementation

  if (b > 0) {
    if (a > INT_MAX - b) {
      INT_OVERFLOW = OVERFLOW_YES;

      // INT_MIN <= a + b <= -2 == INT_MAX + INT_MAX
      return INT_MIN + (a - ((INT_MAX - b) + 1));
    }
  } else if (a < INT_MIN - b) {
    INT_OVERFLOW = OVERFLOW_YES;

    // INT_MIN + INT_MIN == 0 <= a + b <= INT_MAX
    return INT_MAX + (a - ((INT_MIN - b) - 1));
  }

  INT_OVERFLOW = OVERFLOW_NO;

  // implementing addition with +
  return a + b;
}

uint32_t subtractWrap(uint32_t a, uint32_t b) {
  // signed integer subtraction with wrap-around semantics and overflow
  // detection but without causing any integer overflow in the implementation

  if (b > 0) {
    if (a < INT_MIN + b) {
      INT_OVERFLOW = OVERFLOW_YES;

      // INT_MIN - INT_MAX == 1 <= a - b <= INT_MAX
      return INT_MAX + (a - ((INT_MIN + b) - 1));
    }
  } else if (a > INT_MAX + b) {
    INT_OVERFLOW = OVERFLOW_YES;

    // INT_MIN <= a - b <= -1 == INT_MAX - INT_MIN
    return INT_MIN + (a - ((INT_MAX + b) + 1));
  }

  INT_OVERFLOW = OVERFLOW_NO;

  // implementing subtraction with -
  return a - b;
}

uint32_t multiplyWrap(uint32_t a, uint32_t b) {
  INT_OVERFLOW = OVERFLOW_NO;

  if (a > 0) {
    if (b > 0) {
      if (a > INT_MAX / b)
        INT_OVERFLOW = OVERFLOW_YES;
    } else {
      if (b < INT_MIN / a)
        INT_OVERFLOW = OVERFLOW_YES;
    }
  } else {
    if (b > 0) {
      if (a < INT_MIN / b)
        INT_OVERFLOW = OVERFLOW_YES;
    } else {
      if (a != 0)
        if (b < INT_MAX / a)
          INT_OVERFLOW = OVERFLOW_YES;
    }
  }

  // implementing multiplication with * but relying on
  // wrap-around semantics of bootstrapping compiler
  return a * b;
}

void checkDivision(uint32_t a, uint32_t b) {
  INT_OVERFLOW = OVERFLOW_NO;

  if (b == 0)
    INT_OVERFLOW = OVERFLOW_YES;
  else if (a == INT_MIN)
    if (b == -1)
      INT_OVERFLOW = OVERFLOW_YES;
}

uint32_t twoToThePowerOf(uint32_t p) {
  // assert: 0 <= p < 31
  return *(power_of_two_table + p);
}

uint32_t leftShift(uint32_t n, uint32_t b) {
  uint32_t t;

  if (b <= 0)
    return n;
  else if (b < 31) {
    // left shift of integers works by multiplication with powers of two,
    // to avoid integer overflow clear the b MSBs first

    // right shift by 32 - b bits, then left shift by 32 - b - 1 bits
    // since twoToThePowerOf(x) only works for 0 <= x < 31, and finally
    // left shift one more time by one more bit (multiply by 2)

    t = twoToThePowerOf(32 - b - 1);

    if (n >= 0)
      n = n - rightShift(n, 32 - b) * t * 2;
    else
      // reset sign bit, right and left shift, then set sign bit again
      n = n - (rightShift((n + 1) + INT_MAX, 32 - b) * t * 2 + INT_MIN);

    if (n < t)
      // the bit in n that will become the sign bit is not set
      return n * twoToThePowerOf(b);
    else
      // reset that bit first, then left shift, finally set sign bit
      return (n - t) * twoToThePowerOf(b) + INT_MIN;
  } else if (b == 31)
    // twoToThePowerOf(b) only works for 0 <= b < 31
    if (n % 2 == 1)
      // LSB becomes sign bit of INT_MIN when left shifting by 31 bits
      return INT_MIN;
    else
      return 0;
  else
    // left shift of a 32-bit integer by more than 31 bits is always 0
    return 0;
}

uint32_t rightShift(uint32_t n, uint32_t b) {
  if (b <= 0)
    return n;
  else if (b < 31) {
    if (n >= 0)
      // right shift of positive integers works by division with powers of two
      return n / twoToThePowerOf(b);
    else
      // right shift of negative integers requires resetting the sign bit and
      // then dividing with powers of two, and finally restoring the sign bit
      // but b bits to the right; this works even if n == INT_MIN
      return ((n + 1) + INT_MAX) / twoToThePowerOf(b) + (INT_MAX / twoToThePowerOf(b) + 1);
  } else if (b == 31)
    if (n < 0)
      // right shift of a negative 32-bit integer by 31 bits is 1 (sign bit)
      return 1;
    else
      return 0;
  else
    // right shift of a 32-bit integer by more than 31 bits is always 0
    return 0;
}

uint32_t signedLessThan(uint32_t lhs, uint32_t rhs) {
  // signed "<" operator: compare lhs and rhs in two's complement
  return lhs + INT_MIN < rhs + INT_MIN;
}

uint32_t signedGreaterThan(uint32_t lhs, uint32_t rhs) {
  // signed ">" operator: compare lhs and rhs in two's complement
  return lhs + INT_MIN > rhs + INT_MIN;
}

uint32_t loadCharacter(uint32_t* s, uint32_t i) {
  // assert: i >= 0
  uint32_t a;

  // a is the index of the word where the to-be-loaded i-th character in s is
  a = i / SIZEOFINT;

  // shift to-be-loaded character to the left resetting all bits to the left
  // then shift to-be-loaded character all the way to the right and return
  return rightShift(leftShift(*(s + a), ((SIZEOFINT - 1) - (i % SIZEOFINT)) * 8), (SIZEOFINT - 1) * 8);
}

uint32_t* storeCharacter(uint32_t* s, uint32_t i, uint32_t c) {
  // assert: i >= 0, all characters are 7-bit
  uint32_t a;

  // a is the index of the word where the with c
  // to-be-overwritten i-th character in s is
  a = i / SIZEOFINT;

  // subtract the to-be-overwritten character resetting its bits in s
  // then add c setting its bits at the i-th position in s
  *(s + a) = (*(s + a) - leftShift(loadCharacter(s, i), (i % SIZEOFINT) * 8)) + leftShift(c, (i % SIZEOFINT) * 8);

  return s;
}

uint32_t stringLength(uint32_t* s) {
  uint32_t i;

  i = 0;

  while (loadCharacter(s, i) != 0)
    i = i + 1;

  return i;
}

void stringReverse(uint32_t* s) {
  uint32_t i;
  uint32_t j;
  uint32_t tmp;

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

uint32_t stringCompare(uint32_t* s, uint32_t* t) {
  uint32_t i;

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

uint32_t atoi(uint32_t* s) {
  uint32_t i;
  uint32_t n;
  uint32_t c;

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

    if (c < 0)
      // c was not a decimal digit
      return -1;
    else if (c > 9)
      // c was not a decimal digit
      return -1;

    // assert: s contains a decimal number

    // use base 10 but avoid integer overflow
    if (n < INT_MAX / 10)
      n = n * 10 + c;
    else if (n == INT_MAX / 10) {
      if (c <= INT_MAX % 10)
        n = n * 10 + c;
      else if (c == (INT_MAX % 10) + 1)
        // s must be terminated next, check below
        n = INT_MIN;
      else
        // s contains a decimal number larger than INT_MAX
        return -1;
    } else
      // s contains a decimal number larger than INT_MAX
      return -1;

    // go to the next digit
    i = i + 1;

    // load character (one byte) at index i in s from memory
    // requires bit shifting since memory access is in words
    c = loadCharacter(s, i);

    if (n == INT_MIN)
      if (c != 0)
        // n == INT_MIN but s is not terminated yet
        return -1;
  }

  return n;
}

uint32_t* itoa(uint32_t n, uint32_t* s, uint32_t b, uint32_t a, uint32_t p) {
  // assert: b in {2,4,8,10,16}

  uint32_t i;
  uint32_t sign;
  uint32_t msb;

  // the conversion of the integer n to an ASCII string in s
  // with base b, alignment a, and fixed point p
  // begins with the leftmost digit in s
  i = 0;

  // for now assuming n is positive
  sign = 0;

  // and msb not set
  msb = 0;

  if (n == 0) {
    storeCharacter(s, 0, '0');

    i = 1;
  } else if (n < 0) {
    // convert n to a positive number but remember the sign
    sign = 1;

    if (b == 10) {
      if (n == INT_MIN) {
        // rightmost decimal digit of 32-bit INT_MIN
        storeCharacter(s, 0, '8');

        // avoids overflow
        n = -(n / 10);
        i = 1;
      } else
        n = -n;
    } else {
      if (n == INT_MIN) {
        // rightmost non-decimal digit of INT_MIN
        storeCharacter(s, 0, '0');

        // avoids setting n to 0
        n = (rightShift(INT_MIN, 1) / b) * 2;
        i = 1;
      } else {
        // reset msb, restore below
        n   = rightShift(leftShift(n, 1), 1);
        msb = 1;
      }
    }

    // assert: n > 0
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

    if (msb) {
      // restore msb from above
      n   = n + (rightShift(INT_MIN, 1) / b) * 2;
      msb = 0;
    }
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

uint32_t fixedPointRatio(uint32_t a, uint32_t b) {
  // compute fixed point ratio with 2 fractional digits

  // multiply a/b with 100 but avoid overflow

  if (a <= INT_MAX / 100) {
    if (b != 0)
      return a * 100 / b;
  } else if (a <= INT_MAX / 10) {
    if (b / 10 != 0)
      return a * 10 / (b / 10);
  } else {
    if (b / 100 != 0)
      return a / (b / 100);
  }

  return 0;
}

uint32_t fixedPointPercentage(uint32_t r) {
  if (r != 0)
    // 1000000 = 10000 (for 100.00%) * 100 (for 2 fractional digits of r)
    return 1000000 / r;
  else
    return 0;
}

void putCharacter(uint32_t c) {
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
      print((uint32_t*) ": could not write character to output file ");
      print(outputName);
      println();
    }

    exit(EXITCODE_IOERROR);
  }
}

void print(uint32_t* s) {
  uint32_t i;

  if (s == (uint32_t*) 0)
    print((uint32_t*) "NULL");
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

void printCharacter(uint32_t c) {
  putCharacter(CHAR_SINGLEQUOTE);

  if (c == CHAR_EOF)
    print((uint32_t*) "end of file");
  else if (c == CHAR_TAB)
    print((uint32_t*) "tabulator");
  else if (c == CHAR_LF)
    print((uint32_t*) "line feed");
  else if (c == CHAR_CR)
    print((uint32_t*) "carriage return");
  else
    putCharacter(c);

  putCharacter(CHAR_SINGLEQUOTE);
}

void printString(uint32_t* s) {
  putCharacter(CHAR_DOUBLEQUOTE);

  print(s);

  putCharacter(CHAR_DOUBLEQUOTE);
}

void printInteger(uint32_t n) {
  print(itoa(n, integer_buffer, 10, 0, 0));
}

void printFixedPointPercentage(uint32_t a, uint32_t b) {
  print(itoa(fixedPointPercentage(fixedPointRatio(a, b)), integer_buffer, 10, 0, 2));
}

void printFixedPointRatio(uint32_t a, uint32_t b) {
  print(itoa(fixedPointRatio(a, b), integer_buffer, 10, 0, 2));
}

void printHexadecimal(uint32_t n, uint32_t a) {
  print(itoa(n, integer_buffer, 16, a, 0));
}

void printOctal(uint32_t n, uint32_t a) {
  print(itoa(n, integer_buffer, 8, a, 0));
}

void printBinary(uint32_t n, uint32_t a) {
  print(itoa(n, integer_buffer, 2, a, 0));
}

uint32_t roundUp(uint32_t n, uint32_t m) {
  if (n % m == 0)
    return n;
  else if (n >= 0)
    return n + m - n % m;
  else
    return n - n % m;
}

uint32_t* smalloc(uint32_t size) {
  // this procedure ensures a defined program exit,
  // if no memory can be allocated
  uint32_t* memory;

  memory = malloc(size);

  if (size == 0)
    // any address including null
    return memory;
  else if ((uint32_t) memory == 0) {
    print(selfieName);
    print((uint32_t*) ": malloc out of memory");
    println();

    exit(EXITCODE_OUTOFVIRTUALMEMORY);
  }

  return memory;
}

uint32_t* zalloc(uint32_t size) {
  // this procedure is only executed at boot level zero
  // zalloc allocates size bytes rounded up to word size
  // and then zeroes that memory, similar to calloc, but
  // called zalloc to avoid redeclaring calloc
  uint32_t* memory;
  uint32_t  i;

  size = roundUp(size, WORDSIZE);

  memory = smalloc(size);

  size = size / WORDSIZE;

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

void printSymbol(uint32_t symbol) {
  putCharacter(CHAR_DOUBLEQUOTE);

  if (symbol == SYM_EOF)
    print((uint32_t*) "end of file");
  else
    print((uint32_t*) *(SYMBOLS + symbol));

  putCharacter(CHAR_DOUBLEQUOTE);
}

void printLineNumber(uint32_t* message, uint32_t line) {
  print(selfieName);
  print((uint32_t*) ": ");
  print(message);
  print((uint32_t*) " in ");
  print(sourceName);
  print((uint32_t*) " in line ");
  printInteger(line);
  print((uint32_t*) ": ");
}

void syntaxErrorMessage(uint32_t* message) {
  printLineNumber((uint32_t*) "error", lineNumber);

  print(message);

  println();
}

void syntaxErrorCharacter(uint32_t expected) {
  printLineNumber((uint32_t*) "error", lineNumber);

  printCharacter(expected);
  print((uint32_t*) " expected but ");

  printCharacter(character);
  print((uint32_t*) " found");

  println();
}

void syntaxErrorIdentifier(uint32_t* expected) {
  printLineNumber((uint32_t*) "error", lineNumber);

  print(expected);
  print((uint32_t*) " expected but ");

  print(identifier);
  print((uint32_t*) " found");

  println();
}

void getCharacter() {
  uint32_t numberOfReadBytes;

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
    print((uint32_t*) ": could not read character from input file ");
    print(sourceName);
    println();

    exit(EXITCODE_IOERROR);
  }
}

uint32_t isCharacterNewLine() {
  if (character == CHAR_LF)
    return 1;
  else if (character == CHAR_CR)
    return 1;
  else
    return 0;
}

uint32_t isCharacterWhitespace() {
  if (character == CHAR_SPACE)
    return 1;
  else if (character == CHAR_TAB)
    return 1;
  else
    return isCharacterNewLine();
}

uint32_t findNextCharacter() {
  uint32_t inComment;

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

uint32_t isCharacterLetter() {
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

uint32_t isCharacterDigit() {
  // ASCII codes for digits are in a contiguous interval
  if (character >= '0')
    if (character <= '9')
      return 1;
    else
      return 0;
  else
    return 0;
}

uint32_t isCharacterLetterOrDigitOrUnderscore() {
  if (isCharacterLetter())
    return 1;
  else if (isCharacterDigit())
    return 1;
  else if (character == CHAR_UNDERSCORE)
    return 1;
  else
    return 0;
}

uint32_t isCharacterNotDoubleQuoteOrNewLineOrEOF() {
  if (character == CHAR_DOUBLEQUOTE)
    return 0;
  else if (isCharacterNewLine())
    return 0;
  else if (character == CHAR_EOF)
    return 0;
  else
    return 1;
}

uint32_t identifierStringMatch(uint32_t keyword) {
  return stringCompare(identifier, (uint32_t*) *(SYMBOLS + keyword));
}

uint32_t identifierOrKeyword() {
  if (identifierStringMatch(SYM_WHILE))
    return SYM_WHILE;
  if (identifierStringMatch(SYM_IF))
    return SYM_IF;
  if (identifierStringMatch(SYM_UINT32))
    return SYM_UINT32;
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
  uint32_t i;

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
            syntaxErrorMessage((uint32_t*) "identifier too long");

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
            syntaxErrorMessage((uint32_t*) "integer out of bound");

            exit(EXITCODE_SCANNERERROR);
          }

          storeCharacter(integer, i, character);

          i = i + 1;

          getCharacter();
        }

        storeCharacter(integer, i, 0); // null-terminated string

        literal = atoi(integer);

        if (literal < 0) {
          if (literal == INT_MIN) {
            if (mayBeINTMIN)
              isINTMIN = 1;
            else {
              syntaxErrorMessage((uint32_t*) "integer out of bound");

              exit(EXITCODE_SCANNERERROR);
            }
          } else {
            syntaxErrorMessage((uint32_t*) "integer out of bound");

            exit(EXITCODE_SCANNERERROR);
          }
        }

        symbol = SYM_INTEGER;

      } else if (character == CHAR_SINGLEQUOTE) {
        getCharacter();

        literal = 0;

        if (character == CHAR_EOF) {
          syntaxErrorMessage((uint32_t*) "reached end of file looking for a character literal");

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
            syntaxErrorMessage((uint32_t*) "string too long");

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
        printLineNumber((uint32_t*) "error", lineNumber);
        print((uint32_t*) "found unknown character ");
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

void createSymbolTableEntry(uint32_t whichTable, uint32_t* string, uint32_t line, uint32_t class, uint32_t type, uint32_t value, uint32_t address) {
  uint32_t* newEntry;

  newEntry = smalloc(2 * SIZEOFINTSTAR + 6 * SIZEOFINT);

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

uint32_t* searchSymbolTable(uint32_t* entry, uint32_t* string, uint32_t class) {
  while (entry != (uint32_t*) 0) {
    if (stringCompare(string, getString(entry)))
      if (class == getClass(entry))
        return entry;

    // keep looking
    entry = getNextEntry(entry);
  }

  return (uint32_t*) 0;
}

uint32_t* getScopedSymbolTableEntry(uint32_t* string, uint32_t class) {
  uint32_t* entry;

  if (class == VARIABLE)
    // local variables override global variables
    entry = searchSymbolTable(local_symbol_table, string, VARIABLE);
  else if (class == PROCEDURE)
    // library procedures override declared or defined procedures
    entry = searchSymbolTable(library_symbol_table, string, PROCEDURE);
  else
    entry = (uint32_t*) 0;

  if (entry == (uint32_t*) 0)
    return searchSymbolTable(global_symbol_table, string, class);
  else
    return entry;
}

uint32_t isUndefinedProcedure(uint32_t* entry) {
  uint32_t* libraryEntry;

  if (getClass(entry) == PROCEDURE) {
    // library procedures override declared or defined procedures
    libraryEntry = searchSymbolTable(library_symbol_table, getString(entry), PROCEDURE);

    if (libraryEntry != (uint32_t*) 0)
      // procedure is library procedure
      return 0;
    else if (getAddress(entry) == 0)
      // procedure declared but not defined
      return 1;
    else if (getOpcode(loadBinary(getAddress(entry))) == OP_JAL)
      // procedure called but not defined
      return 1;
  }

  return 0;
}

uint32_t reportUndefinedProcedures() {
  uint32_t undefined;
  uint32_t* entry;

  undefined = 0;

  entry = global_symbol_table;

  while (entry != (uint32_t*) 0) {
    if (isUndefinedProcedure(entry)) {
      undefined = 1;

      printLineNumber((uint32_t*) "error", getLineNumber(entry));
      print((uint32_t*) "procedure ");
      print(getString(entry));
      print((uint32_t*) " undefined");
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

uint32_t isNotRbraceOrEOF() {
  if (symbol == SYM_RBRACE)
    return 0;
  else if (symbol == SYM_EOF)
    return 0;
  else
    return 1;
}

uint32_t isExpression() {
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

uint32_t isLiteral() {
  if (symbol == SYM_INTEGER)
    return 1;
  else if (symbol == SYM_CHARACTER)
    return 1;
  else
    return 0;
}

uint32_t isStarOrDivOrModulo() {
  if (symbol == SYM_ASTERISK)
    return 1;
  else if (symbol == SYM_DIV)
    return 1;
  else if (symbol == SYM_MOD)
    return 1;
  else
    return 0;
}

uint32_t isPlusOrMinus() {
  if (symbol == SYM_MINUS)
    return 1;
  else if (symbol == SYM_PLUS)
    return 1;
  else
    return 0;
}

uint32_t isComparison() {
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

uint32_t lookForFactor() {
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

uint32_t lookForStatement() {
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

uint32_t lookForType() {
  if (symbol == SYM_UINT32)
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
    syntaxErrorMessage((uint32_t*) "out of registers");

    exit(EXITCODE_COMPILERERROR);
  }
}

uint32_t currentTemporary() {
  if (allocatedTemporaries > 0)
    return allocatedTemporaries + REG_A3;
  else {
    syntaxErrorMessage((uint32_t*) "illegal register access");

    exit(EXITCODE_COMPILERERROR);
  }
}

uint32_t previousTemporary() {
  if (allocatedTemporaries > 1)
    return currentTemporary() - 1;
  else {
    syntaxErrorMessage((uint32_t*) "illegal register access");

    exit(EXITCODE_COMPILERERROR);
  }
}

uint32_t nextTemporary() {
  if (allocatedTemporaries < REG_T7 - REG_A3)
    return currentTemporary() + 1;
  else {
    syntaxErrorMessage((uint32_t*) "out of registers");

    exit(EXITCODE_COMPILERERROR);
  }
}

void tfree(uint32_t numberOfTemporaries) {
  allocatedTemporaries = allocatedTemporaries - numberOfTemporaries;

  if (allocatedTemporaries < 0) {
    syntaxErrorMessage((uint32_t*) "illegal register deallocation");

    exit(EXITCODE_COMPILERERROR);
  }
}

void save_temporaries() {
  while (allocatedTemporaries > 0) {
    // push temporary onto stack
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, -WORDSIZE);
    emitIFormat(OP_SW, REG_SP, currentTemporary(), 0);

    tfree(1);
  }
}

void restore_temporaries(uint32_t numberOfTemporaries) {
  while (allocatedTemporaries < numberOfTemporaries) {
    talloc();

    // restore temporary from stack
    emitIFormat(OP_LW, REG_SP, currentTemporary(), 0);
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);
  }
}

void syntaxErrorSymbol(uint32_t expected) {
  printLineNumber((uint32_t*) "error", lineNumber);

  printSymbol(expected);
  print((uint32_t*) " expected but ");

  printSymbol(symbol);
  print((uint32_t*) " found");

  println();
}

void syntaxErrorUnexpected() {
  printLineNumber((uint32_t*) "error", lineNumber);

  print((uint32_t*) "unexpected symbol ");
  printSymbol(symbol);
  print((uint32_t*) " found");

  println();
}

void printType(uint32_t type) {
  if (type == INT_T)
    print((uint32_t*) "int");
  else if (type == INTSTAR_T)
    print((uint32_t*) "uint32_t*");
  else if (type == VOID_T)
    print((uint32_t*) "void");
  else
    print((uint32_t*) "unknown");
}

void typeWarning(uint32_t expected, uint32_t found) {
  printLineNumber((uint32_t*) "warning", lineNumber);

  print((uint32_t*) "type mismatch, ");

  printType(expected);

  print((uint32_t*) " expected but ");

  printType(found);

  print((uint32_t*) " found");

  println();
}

uint32_t* getVariable(uint32_t* variable) {
  uint32_t* entry;

  entry = getScopedSymbolTableEntry(variable, VARIABLE);

  if (entry == (uint32_t*) 0) {
    printLineNumber((uint32_t*) "error", lineNumber);
    print(variable);
    print((uint32_t*) " undeclared");
    println();

    exit(EXITCODE_PARSERERROR);
  }

  return entry;
}

uint32_t load_variable(uint32_t* variable) {
  uint32_t* entry;

  entry = getVariable(variable);

  talloc();

  emitIFormat(OP_LW, getScope(entry), currentTemporary(), getAddress(entry));

  return getType(entry);
}

void load_integer(uint32_t value) {
  uint32_t isNegative;

  talloc();

  if (value != INT_MIN) {
    if (value < 0) {
      isNegative = 1;
      value = -value;
    } else 
      isNegative = 0;

    if (value < twoToThePowerOf(15))
      // ADDIU can only load numbers < 2^15 without sign extension
      emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), value);
    else if (value < twoToThePowerOf(28)) {
      // load 14 msbs of a 28-bit number first
      emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), rightShift(value, 14));

      // shift left by 14 bits
      emitLeftShiftBy(currentTemporary(), 14);

      // and finally add 14 lsbs
      emitIFormat(OP_ADDIU, currentTemporary(), currentTemporary(), rightShift(leftShift(value, 18), 18));
    } else {
      // load 14 msbs of a 31-bit number first
      emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), rightShift(value, 17));

      emitLeftShiftBy(currentTemporary(), 14);

      // then add the next 14 msbs
      emitIFormat(OP_ADDIU, currentTemporary(), currentTemporary(), rightShift(leftShift(value, 15), 18));

      emitLeftShiftBy(currentTemporary(), 3);

      // and finally add the remaining 3 lsbs
      emitIFormat(OP_ADDIU, currentTemporary(), currentTemporary(), rightShift(leftShift(value, 29), 29));
    }

    if (isNegative)
      emitRFormat(OP_SPECIAL, REG_ZR, currentTemporary(), currentTemporary(), FCT_SUBU);

  } else {
    // load largest positive 16-bit number with a single bit set: 2^14
    emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), -twoToThePowerOf(14));

    // and then multiply 2^14 by 2^14*2^3 to get to 2^31 == INT_MIN
    emitLeftShiftBy(currentTemporary(), 14);
    emitLeftShiftBy(currentTemporary(), 3);
  }
}

void load_string(uint32_t* string) {
  uint32_t length;

  length = stringLength(string) + 1;

  allocatedMemory = allocatedMemory + roundUp(length, WORDSIZE);

  createSymbolTableEntry(GLOBAL_TABLE, string, lineNumber, STRING, INTSTAR_T, 0, -allocatedMemory);

  talloc();

  emitIFormat(OP_ADDIU, REG_GP, currentTemporary(), -allocatedMemory);
}

uint32_t help_call_codegen(uint32_t* entry, uint32_t* procedure) {
  uint32_t type;

  if (entry == (uint32_t*) 0) {
    // procedure never called nor declared nor defined

    // default return type is "int"
    type = INT_T;

    createSymbolTableEntry(GLOBAL_TABLE, procedure, lineNumber, PROCEDURE, type, 0, binaryLength);

    emitJFormat(OP_JAL, 0);

  } else {
    type = getType(entry);

    if (getAddress(entry) == 0) {
      // procedure declared but never called nor defined
      setAddress(entry, binaryLength);

      emitJFormat(OP_JAL, 0);
    } else if (getOpcode(loadBinary(getAddress(entry))) == OP_JAL) {
      // procedure called and possibly declared but not defined

      // create fixup chain
      emitJFormat(OP_JAL, getAddress(entry) / WORDSIZE);
      setAddress(entry, binaryLength - 2 * WORDSIZE);
    } else
      // procedure defined, use address
      emitJFormat(OP_JAL, getAddress(entry) / WORDSIZE);
  }

  return type;
}

void help_procedure_prologue(uint32_t localVariables) {
  // allocate memory for return address
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, -WORDSIZE);

  // save return address
  emitIFormat(OP_SW, REG_SP, REG_RA, 0);

  // allocate memory for caller's frame pointer
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, -WORDSIZE);

  // save caller's frame pointer
  emitIFormat(OP_SW, REG_SP, REG_FP, 0);

  // set callee's frame pointer
  emitIFormat(OP_ADDIU, REG_SP, REG_FP, 0);

  // allocate memory for callee's local variables
  if (localVariables != 0)
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, -localVariables * WORDSIZE);
}

void help_procedure_epilogue(uint32_t parameters) {
  // deallocate memory for callee's frame pointer and local variables
  emitIFormat(OP_ADDIU, REG_FP, REG_SP, 0);

  // restore caller's frame pointer
  emitIFormat(OP_LW, REG_SP, REG_FP, 0);

  // deallocate memory for caller's frame pointer
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

  // restore return address
  emitIFormat(OP_LW, REG_SP, REG_RA, 0);

  // deallocate memory for return address and parameters
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, (parameters + 1) * WORDSIZE);

  // return
  emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

uint32_t gr_call(uint32_t* procedure) {
  uint32_t* entry;
  uint32_t numberOfTemporaries;
  uint32_t type;

  // assert: n = allocatedTemporaries

  entry = getScopedSymbolTableEntry(procedure, PROCEDURE);

  numberOfTemporaries = allocatedTemporaries;

  save_temporaries();

  // assert: allocatedTemporaries == 0

  if (isExpression()) {
    gr_expression();

    // TODO: check if types/number of parameters is correct

    // push first parameter onto stack
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, -WORDSIZE);
    emitIFormat(OP_SW, REG_SP, currentTemporary(), 0);

    tfree(1);

    while (symbol == SYM_COMMA) {
      getSymbol();

      gr_expression();

      // push more parameters onto stack
      emitIFormat(OP_ADDIU, REG_SP, REG_SP, -WORDSIZE);
      emitIFormat(OP_SW, REG_SP, currentTemporary(), 0);

      tfree(1);
    }

    if (symbol == SYM_RPARENTHESIS) {
      getSymbol();

      type = help_call_codegen(entry, procedure);
    } else {
      syntaxErrorSymbol(SYM_RPARENTHESIS);

      type = INT_T;
    }
  } else if (symbol == SYM_RPARENTHESIS) {
    getSymbol();

    type = help_call_codegen(entry, procedure);
  } else {
    syntaxErrorSymbol(SYM_RPARENTHESIS);

    type = INT_T;
  }

  // assert: allocatedTemporaries == 0

  restore_temporaries(numberOfTemporaries);

  numberOfCalls = numberOfCalls + 1;

  // assert: allocatedTemporaries == n

  return type;
}

uint32_t gr_factor() {
  uint32_t hasCast;
  uint32_t cast;
  uint32_t type;

  uint32_t* variableOrProcedureName;

  // assert: n = allocatedTemporaries

  hasCast = 0;

  type = INT_T;

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

    // cast: "(" "uint32_t" [ "*" ] ")"
    if (symbol == SYM_UINT32) {
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

    if (type != INTSTAR_T)
      typeWarning(INTSTAR_T, type);

    // dereference
    emitIFormat(OP_LW, currentTemporary(), currentTemporary(), 0);

    type = INT_T;

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
      emitIFormat(OP_ADDIU, REG_V0, currentTemporary(), 0);

      // reset return register to initial return value
      // for missing return expressions
      emitIFormat(OP_ADDIU, REG_ZR, REG_V0, 0);
    } else
      // variable access: identifier
      type = load_variable(variableOrProcedureName);

  // integer?
  } else if (symbol == SYM_INTEGER) {
    load_integer(literal);

    getSymbol();

    type = INT_T;

  // character?
  } else if (symbol == SYM_CHARACTER) {
    talloc();

    emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), literal);

    getSymbol();

    type = INT_T;

  // string?
  } else if (symbol == SYM_STRING) {
    load_string(string);

    getSymbol();

    type = INTSTAR_T;

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

uint32_t gr_term() {
  uint32_t ltype;
  uint32_t operatorSymbol;
  uint32_t rtype;

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
      emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), 0, FCT_MULTU);
      emitRFormat(OP_SPECIAL, 0, 0, previousTemporary(), FCT_MFLO);

    } else if (operatorSymbol == SYM_DIV) {
      emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), 0, FCT_DIVU);
      emitRFormat(OP_SPECIAL, 0, 0, previousTemporary(), FCT_MFLO);

    } else if (operatorSymbol == SYM_MOD) {
      emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), 0, FCT_DIVU);
      emitRFormat(OP_SPECIAL, 0, 0, previousTemporary(), FCT_MFHI);
    }

    tfree(1);
  }

  // assert: allocatedTemporaries == n + 1

  return ltype;
}

uint32_t gr_simpleExpression() {
  uint32_t sign;
  uint32_t ltype;
  uint32_t operatorSymbol;
  uint32_t rtype;

  // assert: n = allocatedTemporaries

  // optional: -
  if (symbol == SYM_MINUS) {
    sign = 1;

    mayBeINTMIN = 1;
    isINTMIN    = 0;

    getSymbol();

    mayBeINTMIN = 0;

    if (isINTMIN) {
      isINTMIN = 0;

      // avoids 0-INT_MIN overflow when bootstrapping
      // even though 0-INT_MIN == INT_MIN
      sign = 0;
    }
  } else
    sign = 0;

  ltype = gr_term();

  // assert: allocatedTemporaries == n + 1

  if (sign) {
    if (ltype != INT_T) {
      typeWarning(INT_T, ltype);

      ltype = INT_T;
    }

    emitRFormat(OP_SPECIAL, REG_ZR, currentTemporary(), currentTemporary(), FCT_SUBU);
  }

  // + or -?
  while (isPlusOrMinus()) {
    operatorSymbol = symbol;

    getSymbol();

    rtype = gr_term();

    // assert: allocatedTemporaries == n + 2

    if (operatorSymbol == SYM_PLUS) {
      if (ltype == INTSTAR_T) {
        if (rtype == INT_T)
          // INTSTAR_T + INT_T
          // pointer arithmetic: factor of 2^2 of integer operand
          emitLeftShiftBy(currentTemporary(), 2);
        else
          // INTSTAR_T + INTSTAR_T
          syntaxErrorMessage((uint32_t*) "(uint32_t*) + (uint32_t*) is undefined");
      } else if (rtype == INTSTAR_T) {
        // INT_T + INTSTAR_T
        // pointer arithmetic: factor of 2^2 of integer operand
        emitLeftShiftBy(previousTemporary(), 2);

        ltype = INTSTAR_T;
      }

      emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_ADDU);

    } else if (operatorSymbol == SYM_MINUS) {
      if (ltype == INTSTAR_T) {
        if (rtype == INT_T) {
          // INTSTAR_T - INT_T
          // pointer arithmetic: factor of 2^2 of integer operand
          emitLeftShiftBy(currentTemporary(), 2);
          emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_SUBU);
        } else {
          // INTSTAR_T - INTSTAR_T
          // pointer arithmetic: (left_term - right_term) / SIZEOFINT
          //                 <=> (left_term - right_term) >> 2
          emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_SUBU);
          emitRightShiftBy(previousTemporary(), 2);

          ltype = INT_T;
        }
      } else if (rtype == INTSTAR_T)
        // INT_T - INTSTAR_T
        syntaxErrorMessage((uint32_t*) "(uint32_t) - (uint32_t*) is undefined");
      else
        // INT_T - INT_T
        emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_SUBU);
    }

    tfree(1);
  }

  // assert: allocatedTemporaries == n + 1

  return ltype;
}

uint32_t gr_expression() {
  uint32_t ltype;
  uint32_t operatorSymbol;
  uint32_t rtype;

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

    if (ltype == INTSTAR_T)
      if (rtype == INTSTAR_T)
        if (operatorSymbol != SYM_EQUALITY)
          if (operatorSymbol != SYM_NOTEQ) {
            // pointer arithmetics: We need to compare pointers as unsigned integer
            // by subtracting a offset of INT_MIN (INT_MIN - INT_MIN = INT_MAX),
            // the variables can be compared with a signed comparison instruction (slt)
            load_integer(INT_MIN);

            tfree(1);

            emitRFormat(OP_SPECIAL, previousTemporary(), nextTemporary(), previousTemporary(), FCT_SUBU);
            emitRFormat(OP_SPECIAL, currentTemporary(), nextTemporary(), currentTemporary(), FCT_SUBU);
          }

    if (operatorSymbol == SYM_EQUALITY) {
      // if a == b load 1 else load 0
      emitIFormat(OP_BEQ, previousTemporary(), currentTemporary(), 4);

      tfree(1);

      emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), 0);
      emitIFormat(OP_BEQ, REG_ZR, REG_ZR, 2);
      emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), 1);

    } else if (operatorSymbol == SYM_NOTEQ) {
      // if a == b load 0 else load 1
      emitIFormat(OP_BEQ, previousTemporary(), currentTemporary(), 4);

      tfree(1);

      emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), 1);
      emitIFormat(OP_BEQ, REG_ZR, REG_ZR, 2);
      emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), 0);

    } else if (operatorSymbol == SYM_LT) {
      // if a < b load 1 else load 0
      emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_SLT);

      tfree(1);

    } else if (operatorSymbol == SYM_GT) {
      // if b < a load 1 else load 0
      emitRFormat(OP_SPECIAL, currentTemporary(), previousTemporary(), previousTemporary(), FCT_SLT);

      tfree(1);

    } else if (operatorSymbol == SYM_LEQ) {
      // if b < a load 0 else load 1
      emitRFormat(OP_SPECIAL, currentTemporary(), previousTemporary(), previousTemporary(), FCT_SLT);

      tfree(1);

      emitIFormat(OP_BEQ, REG_ZR, currentTemporary(), 4);
      emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), 0);
      emitIFormat(OP_BEQ, REG_ZR, REG_ZR, 2);
      emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), 1);

    } else if (operatorSymbol == SYM_GEQ) {
      // if a < b load 0 else load 1
      emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_SLT);

      tfree(1);

      emitIFormat(OP_BEQ, REG_ZR, currentTemporary(), 4);
      emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), 0);
      emitIFormat(OP_BEQ, REG_ZR, REG_ZR, 2);
      emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), 1);
    }
  }

  // assert: allocatedTemporaries == n + 1

  return ltype;
}

void gr_while() {
  uint32_t brBackToWhile;
  uint32_t brForwardToEnd;

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
  emitIFormat(OP_BEQ, REG_ZR, REG_ZR, (brBackToWhile - binaryLength - WORDSIZE) / WORDSIZE);

  if (brForwardToEnd != 0)
    // first instruction after loop comes here
    // now we have the address for the conditional branch from above
    fixup_relative(brForwardToEnd);

  // assert: allocatedTemporaries == 0

  numberOfWhile = numberOfWhile + 1;
}

void gr_if() {
  uint32_t brForwardToElseOrEnd;
  uint32_t brForwardToEnd;

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
  uint32_t type;

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
    emitRFormat(OP_SPECIAL, REG_ZR, currentTemporary(), REG_V0, FCT_ADDU);

    tfree(1);
  } else if (returnType != VOID_T)
    typeWarning(returnType, VOID_T);

  // unconditional branch to procedure epilogue
  // maintain fixup chain for later fixup
  emitJFormat(OP_J, returnBranches / WORDSIZE);

  // new head of fixup chain
  // offest is two words rather than one because of delay slot NOP
  returnBranches = binaryLength - 2 * WORDSIZE;

  // assert: allocatedTemporaries == 0

  numberOfReturn = numberOfReturn + 1;
}

void gr_statement() {
  uint32_t ltype;
  uint32_t rtype;
  uint32_t* variableOrProcedureName;
  uint32_t* entry;

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

      if (ltype != INTSTAR_T)
        typeWarning(INTSTAR_T, ltype);

      getSymbol();

      // "*" identifier "="
      if (symbol == SYM_ASSIGN) {
        getSymbol();

        rtype = gr_expression();

        if (rtype != INT_T)
          typeWarning(INT_T, rtype);

        emitIFormat(OP_SW, previousTemporary(), currentTemporary(), 0);

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

      if (ltype != INTSTAR_T)
        typeWarning(INTSTAR_T, ltype);

      if (symbol == SYM_RPARENTHESIS) {
        getSymbol();

        // "*" "(" expression ")" "="
        if (symbol == SYM_ASSIGN) {
          getSymbol();

          rtype = gr_expression();

          if (rtype != INT_T)
            typeWarning(INT_T, rtype);

          emitIFormat(OP_SW, previousTemporary(), currentTemporary(), 0);

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
      emitIFormat(OP_ADDIU, REG_ZR, REG_V0, 0);

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

      emitIFormat(OP_SW, getScope(entry), currentTemporary(), getAddress(entry));

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

uint32_t gr_type() {
  uint32_t type;

  type = INT_T;

  if (symbol == SYM_UINT32) {
    getSymbol();

    if (symbol == SYM_ASTERISK) {
      type = INTSTAR_T;

      getSymbol();
    }
  } else
    syntaxErrorSymbol(SYM_UINT32);

  return type;
}

void gr_variable(uint32_t offset) {
  uint32_t type;

  type = gr_type();

  if (symbol == SYM_IDENTIFIER) {
    // TODO: check if identifier has already been declared
    createSymbolTableEntry(LOCAL_TABLE, identifier, lineNumber, VARIABLE, type, 0, offset);

    getSymbol();
  } else {
    syntaxErrorSymbol(SYM_IDENTIFIER);

    createSymbolTableEntry(LOCAL_TABLE, (uint32_t*) "missing variable name", lineNumber, VARIABLE, type, 0, offset);
  }
}

uint32_t gr_initialization(uint32_t type) {
  uint32_t initialValue;
  uint32_t hasCast;
  uint32_t cast;
  uint32_t sign;

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
      sign = 1;

      mayBeINTMIN = 1;
      isINTMIN    = 0;

      getSymbol();

      mayBeINTMIN = 0;

      if (isINTMIN) {
        isINTMIN = 0;

        // avoids 0-INT_MIN overflow when bootstrapping
        // even though 0-INT_MIN == INT_MIN
        sign = 0;
      }
    } else
      sign = 0;

    if (isLiteral()) {
      initialValue = literal;

      getSymbol();

      if (sign)
        initialValue = -initialValue;
    } else
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
  } else if (type != INT_T)
    typeWarning(type, INT_T);

  return initialValue;
}

void gr_procedure(uint32_t* procedure, uint32_t type) {
  uint32_t isUndefined;
  uint32_t numberOfParameters;
  uint32_t parameters;
  uint32_t localVariables;
  uint32_t* entry;

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
        setAddress(entry, parameters * WORDSIZE + 2 * WORDSIZE);

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
    if (entry == (uint32_t*) 0)
      // procedure never called nor declared nor defined
      createSymbolTableEntry(GLOBAL_TABLE, procedure, lineNumber, PROCEDURE, type, 0, 0);
    else if (getType(entry) != type)
      // procedure already called, declared, or even defined
      // check return type but otherwise ignore
      typeWarning(getType(entry), type);

    getSymbol();

  } else if (symbol == SYM_LBRACE) {
    // this is a procedure definition
    if (entry == (uint32_t*) 0)
      // procedure never called nor declared nor defined
      createSymbolTableEntry(GLOBAL_TABLE, procedure, lineNumber, PROCEDURE, type, 0, binaryLength);
    else {
      // procedure already called or declared or defined
      if (getAddress(entry) != 0) {
        // procedure already called or defined
        if (getOpcode(loadBinary(getAddress(entry))) == OP_JAL) {
          // procedure already called but not defined
          fixlink_absolute(getAddress(entry), binaryLength);

          if (stringCompare(procedure, (uint32_t*) "main"))
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
        printLineNumber((uint32_t*) "warning", lineNumber);
        print((uint32_t*) "redefinition of procedure ");
        print(procedure);
        print((uint32_t*) " ignored");
        println();
      }
    }

    getSymbol();

    localVariables = 0;

    while (symbol == SYM_UINT32) {
      localVariables = localVariables + 1;

      gr_variable(-localVariables * WORDSIZE);

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

  local_symbol_table = (uint32_t*) 0;

  // assert: allocatedTemporaries == 0
}

void gr_cstar() {
  uint32_t type;
  uint32_t* variableOrProcedureName;
  uint32_t currentLineNumber;
  uint32_t initialValue;
  uint32_t* entry;

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

          if (entry == (uint32_t*) 0) {
            allocatedMemory = allocatedMemory + WORDSIZE;

            createSymbolTableEntry(GLOBAL_TABLE, variableOrProcedureName, currentLineNumber, VARIABLE, type, initialValue, -allocatedMemory);
          } else {
            // global variable already declared or defined
            printLineNumber((uint32_t*) "warning", currentLineNumber);
            print((uint32_t*) "redefinition of global variable ");
            print(variableOrProcedureName);
            print((uint32_t*) " ignored");
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

void emitLeftShiftBy(uint32_t reg, uint32_t b) {
  // assert: 0 <= b < 15

  // load multiplication factor less than 2^15 to avoid sign extension
  emitIFormat(OP_ADDIU, REG_ZR, nextTemporary(), twoToThePowerOf(b));
  emitRFormat(OP_SPECIAL, reg, nextTemporary(), 0, FCT_MULTU);
  emitRFormat(OP_SPECIAL, 0, 0, reg, FCT_MFLO);
}

void emitRightShiftBy(uint32_t reg, uint32_t b) {
  // assert: 0 <= b < 31;

  uint32_t brPositive;
  uint32_t brNegative;

  if (b == 0)
    return;

  // check if the number to be shifted is negative
  emitRFormat(OP_SPECIAL, reg, REG_ZR, nextTemporary(), FCT_SLT);

  brPositive = binaryLength;

  emitIFormat(OP_BEQ, nextTemporary(), REG_ZR, 0);

  // if the number is negative, calculate
  //                                     (number < 0)
  // (number - INT_MIN) / 2^b + 2^(31 - b)   <=>   number >> b
  load_integer(INT_MIN);
 
  emitRFormat(OP_SPECIAL, reg, currentTemporary(), reg, FCT_SUBU);

  tfree(1);

  emitIFormat(OP_ADDIU, REG_ZR, nextTemporary(), twoToThePowerOf(b));

  emitRFormat(OP_SPECIAL, reg, nextTemporary(), 0, FCT_DIVU);
  emitRFormat(OP_SPECIAL, 0, 0, reg, FCT_MFLO);

  load_integer(twoToThePowerOf(31 - b));

  emitRFormat(OP_SPECIAL, reg, currentTemporary(), reg, FCT_ADDU);

  tfree(1);

  brNegative = binaryLength;

  emitIFormat(OP_BEQ, REG_ZR, REG_ZR, 0);

  fixup_relative(brPositive);

  // if the number is positive, calculate
  //           (number >= 0)
  // number / 2^b   <=>   number >> b
  load_integer(twoToThePowerOf(b));

  emitRFormat(OP_SPECIAL, reg, currentTemporary(), 0, FCT_DIVU);
  emitRFormat(OP_SPECIAL, 0, 0, reg, FCT_MFLO);

  tfree(1);

  fixup_relative(brNegative);
}

void emitMainEntry() {
  uint32_t i;

  // the instruction at address zero cannot be fixed up
  // we therefore need at least one not-to-be-fixed-up instruction here

  // we generate NOPs to accommodate GP and SP register
  // initialization code that overwrites the NOPs later
  // when binaryLength is known

  i = 0;

  // 15 NOPs per register is enough for initialization
  // since we load integers -2^31 <= n < 2^31 which take
  // no more than 15 instructions each, see load_integer
  while (i < 30) {
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_NOP);

    i = i + 1;
  }

  mainJump = binaryLength;

  createSymbolTableEntry(GLOBAL_TABLE, (uint32_t*) "main", 0, PROCEDURE, INT_T, 0, mainJump);

  // jump and link to main, will return here only if there is no exit call
  emitJFormat(OP_JAL, 0);

  // we exit with exit code in return register pushed onto the stack
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, -WORDSIZE);
  emitIFormat(OP_SW, REG_SP, REG_V0, 0);

  // no need to reset return register here
}

void bootstrapCode() {
  uint32_t savedBinaryLength;

  savedBinaryLength = binaryLength;

  binaryLength = 0;

  // assert: allocatedTemporaries == 0

  load_integer(savedBinaryLength);

  // load binaryLength into GP register
  emitIFormat(OP_ADDIU, currentTemporary(), REG_GP, 0);

  tfree(1);

  // assert: allocatedTemporaries == 0

  // initial stack pointer is stored at highest virtual address
  load_integer(HIGHESTMEMORYADDRESS);

  // load initial stack pointer into SP register
  emitIFormat(OP_LW, currentTemporary(), REG_SP, 0);

  tfree(1);

  // assert: allocatedTemporaries == 0

  binaryLength = savedBinaryLength;

  if (reportUndefinedProcedures())
    // rather than jump and link to the main procedure
    // exit by continuing to the next instruction (with delay slot)
    fixup_absolute(mainJump, mainJump + 8);

  mainJump = 0;
}

// -----------------------------------------------------------------
// --------------------------- COMPILER ----------------------------
// -----------------------------------------------------------------

void selfie_compile() {
  uint32_t link;
  uint32_t numberOfSourceFiles;

  // link until next console option
  link = 1;

  numberOfSourceFiles = 0;

  sourceName = (uint32_t*) "library";

  binaryName = sourceName;

  // allocate memory for storing binary
  binary       = smalloc(maxBinaryLength);
  binaryLength = 0;

  // reset code length
  codeLength = 0;

  // allocate zeroed memory for storing source code line numbers
  sourceLineNumber = zalloc(maxBinaryLength);

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
      print((uint32_t*) ": this is selfie compiling ");
      print(sourceName);
      print((uint32_t*) " with starc");
      println();

      // assert: sourceName is mapped and not longer than maxFilenameLength

      sourceFD = open(sourceName, O_RDONLY, 0);

      if (signedLessThan(sourceFD, 0)) {
        print(selfieName);
        print((uint32_t*) ": could not open input file ");
        print(sourceName);
        println();

        exit(EXITCODE_IOERROR);
      }

      resetScanner();
      resetParser();

      // compile
      gr_cstar();

      print(selfieName);
      print((uint32_t*) ": ");
      printInteger(numberOfReadCharacters);
      print((uint32_t*) " characters read in ");
      printInteger(lineNumber - 1);
      print((uint32_t*) " lines and ");
      printInteger(numberOfComments);
      print((uint32_t*) " comments");
      println();

      print(selfieName);
      print((uint32_t*) ": with ");
      printInteger(numberOfReadCharacters - numberOfIgnoredCharacters);
      print((uint32_t*) "(");
      printFixedPointPercentage(numberOfReadCharacters, numberOfReadCharacters - numberOfIgnoredCharacters);
      print((uint32_t*) "%) characters in ");
      printInteger(numberOfScannedSymbols);
      print((uint32_t*) " actual symbols");
      println();

      print(selfieName);
      print((uint32_t*) ": ");
      printInteger(numberOfGlobalVariables);
      print((uint32_t*) " global variables, ");
      printInteger(numberOfProcedures);
      print((uint32_t*) " procedures, ");
      printInteger(numberOfStrings);
      print((uint32_t*) " string literals");
      println();

      print(selfieName);
      print((uint32_t*) ": ");
      printInteger(numberOfCalls);
      print((uint32_t*) " calls, ");
      printInteger(numberOfAssignments);
      print((uint32_t*) " assignments, ");
      printInteger(numberOfWhile);
      print((uint32_t*) " while, ");
      printInteger(numberOfIf);
      print((uint32_t*) " if, ");
      printInteger(numberOfReturn);
      print((uint32_t*) " return");
      println();
    }
  }

  if (numberOfSourceFiles == 0) {
    print(selfieName);
    print((uint32_t*) ": nothing to compile, only library generated");
    println();
  }

  codeLength = binaryLength;

  emitGlobalsStrings();

  bootstrapCode();

  print(selfieName);
  print((uint32_t*) ": ");
  printInteger(binaryLength + WORDSIZE);
  print((uint32_t*) " bytes generated with ");
  printInteger(codeLength / WORDSIZE);
  print((uint32_t*) " instructions and ");
  printInteger(binaryLength - codeLength + WORDSIZE);
  print((uint32_t*) " bytes of data");
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

void printRegister(uint32_t reg) {
  print((uint32_t*) *(REGISTERS + reg));
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
uint32_t encodeRFormat(uint32_t opcode, uint32_t rs, uint32_t rt, uint32_t rd, uint32_t function) {
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
uint32_t encodeIFormat(uint32_t opcode, uint32_t rs, uint32_t rt, uint32_t immediate) {
  // assert: 0 <= opcode < 2^6
  // assert: 0 <= rs < 2^5
  // assert: 0 <= rt < 2^5
  // assert: -2^15 <= immediate < 2^15

  // convert from 32-bit to 16-bit two's complement
  immediate = rightShift(leftShift(immediate, 16), 16);

  return leftShift(leftShift(leftShift(opcode, 5) + rs, 5) + rt, 16) + immediate;
}

// --------------------------------------------------------------
// 32 bit
//
// +------+--------------------------+
// |opcode|       instr_index        |
// +------+--------------------------+
//    6                26
uint32_t encodeJFormat(uint32_t opcode, uint32_t instr_index) {
  // assert: 0 <= opcode < 2^6
  // assert: 0 <= instr_index < 2^26
  return leftShift(opcode, 26) + instr_index;
}

// -----------------------------------------------------------------
// ---------------------------- DECODER ----------------------------
// -----------------------------------------------------------------

uint32_t getOpcode(uint32_t instruction) {
  return rightShift(instruction, 26);
}

uint32_t getRS(uint32_t instruction) {
  return rightShift(leftShift(instruction, 6), 27);
}

uint32_t getRT(uint32_t instruction) {
  return rightShift(leftShift(instruction, 11), 27);
}

uint32_t getRD(uint32_t instruction) {
  return rightShift(leftShift(instruction, 16), 27);
}

uint32_t getFunction(uint32_t instruction) {
  return rightShift(leftShift(instruction, 26), 26);
}

uint32_t getImmediate(uint32_t instruction) {
  return rightShift(leftShift(instruction, 16), 16);
}

uint32_t getInstrIndex(uint32_t instruction) {
  return rightShift(leftShift(instruction, 6), 6);
}

uint32_t signExtend(uint32_t immediate) {
  // sign-extend from 16-bit to 32-bit two's complement
  if (immediate < twoToThePowerOf(15))
    return immediate;
  else
    return immediate - twoToThePowerOf(16);
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

void printOpcode(uint32_t opcode) {
  print((uint32_t*) *(OPCODES + opcode));
}

void printFunction(uint32_t function) {
  print((uint32_t*) *(FUNCTIONS + function));
}

// -----------------------------------------------------------------
// ----------------------------- CODE ------------------------------
// -----------------------------------------------------------------

uint32_t loadBinary(uint32_t baddr) {
  return *(binary + baddr / WORDSIZE);
}

void storeBinary(uint32_t baddr, uint32_t instruction) {
  if (baddr >= maxBinaryLength) {
    syntaxErrorMessage((uint32_t*) "maximum binary length exceeded");

    exit(EXITCODE_COMPILERERROR);
  }

  *(binary + baddr / WORDSIZE) = instruction;
}

void emitInstruction(uint32_t instruction) {
  storeBinary(binaryLength, instruction);

  if (*(sourceLineNumber + binaryLength / WORDSIZE) == 0)
    *(sourceLineNumber + binaryLength / WORDSIZE) = lineNumber;

  binaryLength = binaryLength + WORDSIZE;
}

void emitRFormat(uint32_t opcode, uint32_t rs, uint32_t rt, uint32_t rd, uint32_t function) {
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

void emitIFormat(uint32_t opcode, uint32_t rs, uint32_t rt, uint32_t immediate) {
  emitInstruction(encodeIFormat(opcode, rs, rt, immediate));

  if (opcode == OP_BEQ)
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_NOP); // delay slot
}

void emitJFormat(uint32_t opcode, uint32_t instr_index) {
  emitInstruction(encodeJFormat(opcode, instr_index));

  emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_NOP); // delay slot
}

void fixup_relative(uint32_t fromAddress) {
  uint32_t instruction;

  instruction = loadBinary(fromAddress);

  storeBinary(fromAddress,
    encodeIFormat(getOpcode(instruction),
      getRS(instruction),
      getRT(instruction),
      (binaryLength - fromAddress - WORDSIZE) / WORDSIZE));
}

void fixup_absolute(uint32_t fromAddress, uint32_t toAddress) {
  storeBinary(fromAddress,
    encodeJFormat(getOpcode(loadBinary(fromAddress)), toAddress / WORDSIZE));
}

void fixlink_absolute(uint32_t fromAddress, uint32_t toAddress) {
  uint32_t previousAddress;

  while (fromAddress != 0) {
    previousAddress = getInstrIndex(loadBinary(fromAddress)) * WORDSIZE;

    fixup_absolute(fromAddress, toAddress);

    fromAddress = previousAddress;
  }
}

uint32_t copyStringToBinary(uint32_t* s, uint32_t baddr) {
  uint32_t next;

  next = baddr + roundUp(stringLength(s) + 1, WORDSIZE);

  while (baddr < next) {
    storeBinary(baddr, *s);

    s = s + 1;

    baddr = baddr + WORDSIZE;
  }

  return next;
}

void emitGlobalsStrings() {
  uint32_t* entry;

  entry = global_symbol_table;

  // assert: n = binaryLength

  // allocate space for global variables and copy strings
  while ((uint32_t) entry != 0) {
    if (getClass(entry) == VARIABLE) {
      storeBinary(binaryLength, getValue(entry));

      binaryLength = binaryLength + WORDSIZE;
    } else if (getClass(entry) == STRING)
      binaryLength = copyStringToBinary(getString(entry), binaryLength);

    entry = getNextEntry(entry);
  }

  // assert: binaryLength == n + allocatedMemory

  allocatedMemory = 0;
}

uint32_t openWriteOnly(uint32_t* name) {
  // we try opening write-only files using platform-specific flags
  // to make selfie platform-independent, this may nevertheless
  // not always work and require intervention
  uint32_t fd;

  // try Mac flags
  fd = open(name, MAC_O_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH);

  if (signedLessThan(fd, 0)) {
    // try Linux flags
    fd = open(name, LINUX_O_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH);

    if (signedLessThan(fd, 0))
      // try Windows flags
      fd = open(name, WINDOWS_O_BINARY_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH);
  }

  return fd;
}

void selfie_output() {
  uint32_t fd;

  binaryName = getArgument();

  if (binaryLength == 0) {
    print(selfieName);
    print((uint32_t*) ": nothing to emit to output file ");
    print(binaryName);
    println();

    return;
  }

  // assert: binaryName is mapped and not longer than maxFilenameLength

  fd = openWriteOnly(binaryName);

  if (signedLessThan(fd, 0)) {
    print(selfieName);
    print((uint32_t*) ": could not create binary output file ");
    print(binaryName);
    println();

    exit(EXITCODE_IOERROR);
  }

  *binary_buffer = codeLength;

  // assert: binary_buffer is mapped

  // first write code length
  write(fd, binary_buffer, WORDSIZE);

  // assert: binary is mapped

  // then write binary
  write(fd, binary, binaryLength);

  print(selfieName);
  print((uint32_t*) ": ");
  printInteger(binaryLength + WORDSIZE);
  print((uint32_t*) " bytes with ");
  printInteger(codeLength / WORDSIZE);
  print((uint32_t*) " instructions and ");
  printInteger(binaryLength - codeLength + WORDSIZE);
  print((uint32_t*) " bytes of data written into ");
  print(binaryName);
  println();
}

uint32_t* touch(uint32_t* memory, uint32_t length) {
  uint32_t* m;
  uint32_t n;

  m = memory;

  if (length > 0)
    // touch memory at beginning
    n = *m;

  while (length > PAGESIZE) {
    length = length - PAGESIZE;

    m = m + PAGESIZEINWORDS;

    // touch every following page
    n = *m;
  }

  if (length > 0) {
    m = m + (length - 1) / WORDSIZE;

    // touch at end
    n = *m;
  }

  // avoids unused warning for n
  n = 0; n = n + 1;

  return memory;
}

void selfie_load() {
  uint32_t fd;
  uint32_t numberOfReadBytes;

  binaryName = getArgument();

  // assert: binaryName is mapped and not longer than maxFilenameLength

  fd = open(binaryName, O_RDONLY, 0);

  if (signedLessThan(fd, 0)) {
    print(selfieName);
    print((uint32_t*) ": could not open input file ");
    print(binaryName);
    println();

    exit(EXITCODE_IOERROR);
  }

  // make sure binary is mapped
  binary = touch(smalloc(maxBinaryLength), maxBinaryLength);

  binaryLength = 0;
  codeLength   = 0;

  // no source line numbers in binaries
  sourceLineNumber = (uint32_t*) 0;

  // assert: binary_buffer is mapped

  // read code length first
  numberOfReadBytes = read(fd, binary_buffer, WORDSIZE);

  if (numberOfReadBytes == WORDSIZE) {
    codeLength = *binary_buffer;

    if (codeLength <= maxBinaryLength) {
      // assert: binary is mapped

      // now read binary including global variables and strings
      numberOfReadBytes = read(fd, binary, maxBinaryLength);

      if (signedGreaterThan(numberOfReadBytes, 0)) {
        binaryLength = numberOfReadBytes;

        // check if we are really at EOF
        if (read(fd, binary_buffer, WORDSIZE) == 0) {
          print(selfieName);
          print((uint32_t*) ": ");
          printInteger(binaryLength + WORDSIZE);
          print((uint32_t*) " bytes with ");
          printInteger(codeLength / WORDSIZE);
          print((uint32_t*) " instructions and ");
          printInteger(binaryLength - codeLength + WORDSIZE);
          print((uint32_t*) " bytes of data loaded from ");
          print(binaryName);
          println();

          return;
        }
      }
    }
  }

  print(selfieName);
  print((uint32_t*) ": failed to load code from input file ");
  print(binaryName);
  println();

  exit(EXITCODE_IOERROR);
}

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emitExit() {
  createSymbolTableEntry(LIBRARY_TABLE, (uint32_t*) "exit", 0, PROCEDURE, VOID_T, 0, binaryLength);

  // load argument for exit
  emitIFormat(OP_LW, REG_SP, REG_A0, 0); // exit code

  // remove the argument from the stack
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

  // load the correct syscall number and invoke syscall
  emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_EXIT);
  emitRFormat(0, 0, 0, 0, FCT_SYSCALL);

  // never returns here
}

void implementExit(uint32_t* context) {
  setExitCode(context, *(getRegs(context)+REG_A0));

  print(selfieName);
  print((uint32_t*) ": ");
  print(getName(context));
  print((uint32_t*) " exiting with exit code ");
  printInteger(getExitCode(context));
  print((uint32_t*) " and ");
  printFixedPointRatio(getProgramBreak(context) - maxBinaryLength, MEGABYTE);
  print((uint32_t*) "MB of mallocated memory");
  println();
}

void emitRead() {
  createSymbolTableEntry(LIBRARY_TABLE, (uint32_t*) "read", 0, PROCEDURE, INT_T, 0, binaryLength);

  emitIFormat(OP_LW, REG_SP, REG_A2, 0); // size
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

  emitIFormat(OP_LW, REG_SP, REG_A1, 0); // *buffer
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

  emitIFormat(OP_LW, REG_SP, REG_A0, 0); // fd
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

  emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_READ);
  emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

  // jump back to caller, return value is in REG_V0
  emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

void implementRead(uint32_t* context) {
  uint32_t size;
  uint32_t vaddr;
  uint32_t fd;
  uint32_t readTotal;
  uint32_t bytesToRead;
  uint32_t* buffer;
  uint32_t actuallyRead;
  uint32_t failed;

  // assert: read buffer is mapped

  size  = *(getRegs(context)+REG_A2);
  vaddr = *(getRegs(context)+REG_A1);
  fd    = *(getRegs(context)+REG_A0);

  if (debug_read) {
    print(selfieName);
    print((uint32_t*) ": trying to read ");
    printInteger(size);
    print((uint32_t*) " bytes from file with descriptor ");
    printInteger(fd);
    print((uint32_t*) " into buffer at virtual address ");
    printHexadecimal(vaddr, 8);
    println();
  }

  readTotal   = 0;
  bytesToRead = WORDSIZE;

  failed = 0;

  while (size > 0) {
    if (isValidVirtualAddress(vaddr)) {
      if (isVirtualAddressMapped(getPT(context), vaddr)) {
        buffer = tlb(getPT(context), vaddr);

        if (size < bytesToRead)
          bytesToRead = size;

        actuallyRead = read(fd, buffer, bytesToRead);

        if (actuallyRead == bytesToRead) {
          readTotal = readTotal + actuallyRead;

          size = size - actuallyRead;

          if (size > 0)
            vaddr = vaddr + WORDSIZE;
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
          print((uint32_t*) ": reading into virtual address ");
          printHexadecimal(vaddr, 8);
          print((uint32_t*) " failed because the address is unmapped");
          println();
        }
      }
    } else {
      failed = 1;

      size = 0;

      if (debug_read) {
        print(selfieName);
        print((uint32_t*) ": reading into virtual address ");
        printHexadecimal(vaddr, 8);
        print((uint32_t*) " failed because the address is invalid");
        println();
      }
    }
  }

  if (failed == 0)
    *(getRegs(context)+REG_V0) = readTotal;
  else
    *(getRegs(context)+REG_V0) = -1;

  if (debug_read) {
    print(selfieName);
    print((uint32_t*) ": actually read ");
    printInteger(readTotal);
    print((uint32_t*) " bytes from file with descriptor ");
    printInteger(fd);
    println();
  }
}

void emitWrite() {
  createSymbolTableEntry(LIBRARY_TABLE, (uint32_t*) "write", 0, PROCEDURE, INT_T, 0, binaryLength);

  emitIFormat(OP_LW, REG_SP, REG_A2, 0); // size
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

  emitIFormat(OP_LW, REG_SP, REG_A1, 0); // *buffer
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

  emitIFormat(OP_LW, REG_SP, REG_A0, 0); // fd
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

  emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_WRITE);
  emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

  emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

void implementWrite(uint32_t* context) {
  uint32_t size;
  uint32_t vaddr;
  uint32_t fd;
  uint32_t writtenTotal;
  uint32_t bytesToWrite;
  uint32_t* buffer;
  uint32_t actuallyWritten;
  uint32_t failed;

  // assert: write buffer is mapped

  size  = *(getRegs(context)+REG_A2);
  vaddr = *(getRegs(context)+REG_A1);
  fd    = *(getRegs(context)+REG_A0);

  if (debug_write) {
    print(selfieName);
    print((uint32_t*) ": trying to write ");
    printInteger(size);
    print((uint32_t*) " bytes from buffer at virtual address ");
    printHexadecimal(vaddr, 8);
    print((uint32_t*) " into file with descriptor ");
    printInteger(fd);
    println();
  }

  writtenTotal = 0;
  bytesToWrite = WORDSIZE;

  failed = 0;

  while (size > 0) {
    if (isValidVirtualAddress(vaddr)) {
      if (isVirtualAddressMapped(getPT(context), vaddr)) {
        buffer = tlb(getPT(context), vaddr);

        if (size < bytesToWrite)
          bytesToWrite = size;

        actuallyWritten = write(fd, buffer, bytesToWrite);

        if (actuallyWritten == bytesToWrite) {
          writtenTotal = writtenTotal + actuallyWritten;

          size = size - actuallyWritten;

          if (size > 0)
            vaddr = vaddr + WORDSIZE;
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
          print((uint32_t*) ": writing into virtual address ");
          printHexadecimal(vaddr, 8);
          print((uint32_t*) " failed because the address is unmapped");
          println();
        }
      }
    } else {
      failed = 1;

      size = 0;

      if (debug_write) {
        print(selfieName);
        print((uint32_t*) ": writing into virtual address ");
        printHexadecimal(vaddr, 8);
        print((uint32_t*) " failed because the address is invalid");
        println();
      }
    }
  }

  if (failed == 0)
    *(getRegs(context)+REG_V0) = writtenTotal;
  else
    *(getRegs(context)+REG_V0) = -1;

  if (debug_write) {
    print(selfieName);
    print((uint32_t*) ": actually wrote ");
    printInteger(writtenTotal);
    print((uint32_t*) " bytes into file with descriptor ");
    printInteger(fd);
    println();
  }
}

void emitOpen() {
  createSymbolTableEntry(LIBRARY_TABLE, (uint32_t*) "open", 0, PROCEDURE, INT_T, 0, binaryLength);

  emitIFormat(OP_LW, REG_SP, REG_A2, 0); // mode
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

  emitIFormat(OP_LW, REG_SP, REG_A1, 0); // flags
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

  emitIFormat(OP_LW, REG_SP, REG_A0, 0); // filename
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

  emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_OPEN);
  emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

  emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

uint32_t down_loadString(uint32_t* table, uint32_t vaddr, uint32_t* s) {
  uint32_t i;
  uint32_t* paddr;

  i = 0;

  while (i < maxFilenameLength / WORDSIZE) {
    if (isValidVirtualAddress(vaddr)) {
      if (isVirtualAddressMapped(table, vaddr)) {
        paddr = tlb(table, vaddr);

        *(s + i) = loadPhysicalMemory(paddr);

        if (loadCharacter(paddr, 0) == 0)
          return 1;
        else if (loadCharacter(paddr, 1) == 0)
          return 1;
        else if (loadCharacter(paddr, 2) == 0)
          return 1;
        else if (loadCharacter(paddr, 3) == 0)
          return 1;

        vaddr = vaddr + WORDSIZE;

        i = i + 1;
      } else {
        if (debug_open) {
          print(selfieName);
          print((uint32_t*) ": opening file with name at virtual address ");
          printHexadecimal(vaddr, 8);
          print((uint32_t*) " failed because the address is unmapped");
          println();
        }
      }
    } else {
      if (debug_open) {
        print(selfieName);
        print((uint32_t*) ": opening file with name at virtual address ");
        printHexadecimal(vaddr, 8);
        print((uint32_t*) " failed because the address is invalid");
        println();
      }
    }
  }

  return 0;
}

void implementOpen(uint32_t* context) {
  uint32_t mode;
  uint32_t flags;
  uint32_t vaddr;
  uint32_t fd;

  mode  = *(getRegs(context)+REG_A2);
  flags = *(getRegs(context)+REG_A1);
  vaddr = *(getRegs(context)+REG_A0);

  if (down_loadString(getPT(context), vaddr, filename_buffer)) {
    fd = open(filename_buffer, flags, mode);

    *(getRegs(context)+REG_V0) = fd;

    if (debug_open) {
      print(selfieName);
      print((uint32_t*) ": opened file ");
      printString(filename_buffer);
      print((uint32_t*) " with flags ");
      printHexadecimal(flags, 0);
      print((uint32_t*) " and mode ");
      printOctal(mode, 0);
      print((uint32_t*) " returning file descriptor ");
      printInteger(fd);
      println();
    }
  } else {
    *(getRegs(context)+REG_V0) = -1;

    if (debug_open) {
      print(selfieName);
      print((uint32_t*) ": opening file with name at virtual address ");
      printHexadecimal(vaddr, 8);
      print((uint32_t*) " failed because the name is too long");
      println();
    }
  }
}

void emitMalloc() {
  createSymbolTableEntry(LIBRARY_TABLE, (uint32_t*) "malloc", 0, PROCEDURE, INTSTAR_T, 0, binaryLength);

  // on boot levels higher than zero, zalloc falls back to malloc
  // assuming that page frames are zeroed on boot level zero
  createSymbolTableEntry(LIBRARY_TABLE, (uint32_t*) "zalloc", 0, PROCEDURE, INTSTAR_T, 0, binaryLength);

  emitIFormat(OP_LW, REG_SP, REG_A0, 0); // size
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

  emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_MALLOC);
  emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

  emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

uint32_t implementMalloc(uint32_t* context) {
  uint32_t size;
  uint32_t bump;
  uint32_t stackptr;
  uint32_t available;
  uint32_t temp;

  if (debug_malloc) {
    print(selfieName);
    print((uint32_t*) ": trying to malloc ");
    printInteger(*(getRegs(context)+REG_A0));
    print((uint32_t*) " bytes");
    println();
  }

  size = roundUp(*(getRegs(context)+REG_A0), WORDSIZE);

  bump = getProgramBreak(context);

  stackptr = *(getRegs(context)+REG_SP);

  available = stackptr - bump;

  if (size > available) {
    setExitCode(context, EXITCODE_OUTOFVIRTUALMEMORY);

    return EXIT;
  } else {
    *(getRegs(context)+REG_V0) = bump;

    setProgramBreak(context, bump + size);

    if (debug_malloc) {
      print(selfieName);
      print((uint32_t*) ": actually mallocating ");
      printInteger(size);
      print((uint32_t*) " bytes at virtual address ");
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
  createSymbolTableEntry(LIBRARY_TABLE, (uint32_t*) "hypster_switch", 0, PROCEDURE, INTSTAR_T, 0, binaryLength);

  emitIFormat(OP_LW, REG_SP, REG_A1, 0); // number of instructions to execute
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

  emitIFormat(OP_LW, REG_SP, REG_A0, 0); // context to which we switch
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

  emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_SWITCH);
  emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

  // save context from which we are switching here in return register
  emitRFormat(OP_SPECIAL, REG_ZR, REG_V1, REG_V0, FCT_ADDU);

  emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

void doSwitch(uint32_t* toContext, uint32_t timeout) {
  uint32_t* fromContext;

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
    *(registers+REG_V1) = (uint32_t) getVirtualContext(fromContext);
  else
    *(registers+REG_V1) = (uint32_t) fromContext;

  currentContext = toContext;

  timer = timeout;

  if (debug_switch) {
    print(selfieName);
    print((uint32_t*) ": switched from context ");
    printHexadecimal((uint32_t) fromContext, 8);
    print((uint32_t*) " to context ");
    printHexadecimal((uint32_t) toContext, 8);
    if (timeout >= 0) {
      print((uint32_t*) " to execute ");
      printInteger(timeout);
      print((uint32_t*) " instructions");
    }
    println();
  }
}

void implementSwitch() {
  saveContext(currentContext);

  // cache context on my boot level before switching
  doSwitch(cacheContext((uint32_t*) *(registers+REG_A0)), *(registers+REG_A1));
}

uint32_t* mipster_switch(uint32_t* toContext, uint32_t timeout) {
  doSwitch(toContext, timeout);

  runUntilException();

  saveContext(currentContext);

  return currentContext;
}

uint32_t* hypster_switch(uint32_t* toContext, uint32_t timeout) {
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

uint32_t loadPhysicalMemory(uint32_t* paddr) {
  return *paddr;
}

void storePhysicalMemory(uint32_t* paddr, uint32_t data) {
  *paddr = data;
}

uint32_t FrameForPage(uint32_t* table, uint32_t page) {
  return (uint32_t) (table + page);
}

uint32_t getFrameForPage(uint32_t* table, uint32_t page) {
  return *(table + page);
}

uint32_t isPageMapped(uint32_t* table, uint32_t page) {
  if (getFrameForPage(table, page) != 0)
    return 1;
  else
    return 0;
}

uint32_t isValidVirtualAddress(uint32_t vaddr) {
  // memory must be word-addressed for lack of byte-sized data type
  return vaddr % WORDSIZE == 0;
}

uint32_t getPageOfVirtualAddress(uint32_t vaddr) {
  if (vaddr < 0)
    return (vaddr - INT_MIN) / PAGESIZE + NUMBEROFPAGES / 2;

  return vaddr / PAGESIZE;
}

uint32_t isVirtualAddressMapped(uint32_t* table, uint32_t vaddr) {
  // assert: isValidVirtualAddress(vaddr) == 1

  return isPageMapped(table, getPageOfVirtualAddress(vaddr));
}

uint32_t* tlb(uint32_t* table, uint32_t vaddr) {
  uint32_t page;
  uint32_t frame;
  uint32_t paddr;

  // assert: isValidVirtualAddress(vaddr) == 1
  // assert: isVirtualAddressMapped(table, vaddr) == 1

  page = getPageOfVirtualAddress(vaddr);

  frame = getFrameForPage(table, page);

  // map virtual address to physical address
  if (vaddr < 0)
    paddr = vaddr - INT_MIN - (page - NUMBEROFPAGES / 2) * PAGESIZE + frame;
  else
    paddr = vaddr - page * PAGESIZE + frame;

  if (debug_tlb) {
    print(selfieName);
    print((uint32_t*) ": tlb access:");
    println();
    print((uint32_t*) " vaddr: ");
    printBinary(vaddr, 32);
    println();
    print((uint32_t*) " page:  ");
    if (page < NUMBEROFPAGES / 2)
      printBinary(page * PAGESIZE, 32);
    else
      printBinary(INT_MIN + (page - NUMBEROFPAGES / 2) * PAGESIZE, 32);
    printBinary(page * PAGESIZE, 32);
    println();
    print((uint32_t*) " frame: ");
    printBinary(frame, 32);
    println();
    print((uint32_t*) " paddr: ");
    printBinary(paddr, 32);
    println();
  }

  return (uint32_t*) paddr;
}

uint32_t loadVirtualMemory(uint32_t* table, uint32_t vaddr) {
  // assert: isValidVirtualAddress(vaddr) == 1
  // assert: isVirtualAddressMapped(table, vaddr) == 1

  return loadPhysicalMemory(tlb(table, vaddr));
}

void storeVirtualMemory(uint32_t* table, uint32_t vaddr, uint32_t data) {
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
    pc = pc + WORDSIZE;
}

void fct_addu() {
  uint32_t s;
  uint32_t t;
  uint32_t d;
  uint32_t n;

  if (interpret) {
    s = *(registers+rs);
    t = *(registers+rt);
    d = *(registers+rd);

    n = addWrap(s, t);
  }

  if (debug) {
    printFunction(function);
    print((uint32_t*) " ");
    printRegister(rd);
    print((uint32_t*) ",");
    printRegister(rs);
    print((uint32_t*) ",");
    printRegister(rt);
    if (interpret) {
      print((uint32_t*) ": ");
      printRegister(rd);
      print((uint32_t*) "=");
      printInteger(d);
      print((uint32_t*) ",");
      printRegister(rs);
      print((uint32_t*) "=");
      printInteger(s);
      print((uint32_t*) ",");
      printRegister(rt);
      print((uint32_t*) "=");
      printInteger(t);
      print((uint32_t*) " -> ");
      printRegister(rd);
      print((uint32_t*) "=");
      printInteger(n);
    }
    println();
  }

  if (interpret) {
    *(registers+rd) = n;

    pc = pc + WORDSIZE;

    if (debug_overflow)
      if (INT_OVERFLOW == OVERFLOW_YES) {
        print((uint32_t*) "overflow: ");
        printInteger(s);
        print((uint32_t*) " + ");
        printInteger(t);
        print((uint32_t*) " ~ ");
        printInteger(n);
        println();
      }
  }
}

void fct_subu() {
  uint32_t s;
  uint32_t t;
  uint32_t d;
  uint32_t n;

  if (interpret) {
    s = *(registers+rs);
    t = *(registers+rt);
    d = *(registers+rd);

    n = subtractWrap(s, t);
  }

  if (debug) {
    printFunction(function);
    print((uint32_t*) " ");
    printRegister(rd);
    print((uint32_t*) ",");
    printRegister(rs);
    print((uint32_t*) ",");
    printRegister(rt);
    if (interpret) {
      print((uint32_t*) ": ");
      printRegister(rd);
      print((uint32_t*) "=");
      printInteger(d);
      print((uint32_t*) ",");
      printRegister(rs);
      print((uint32_t*) "=");
      printInteger(s);
      print((uint32_t*) ",");
      printRegister(rt);
      print((uint32_t*) "=");
      printInteger(t);
      print((uint32_t*) " -> ");
      printRegister(rd);
      print((uint32_t*) "=");
      printInteger(n);
    }
    println();
  }

  if (interpret) {
    *(registers+rd) = n;

    pc = pc + WORDSIZE;

    if (debug_overflow)
      if (INT_OVERFLOW == OVERFLOW_YES) {
        print((uint32_t*) "overflow: ");
        printInteger(s);
        print((uint32_t*) " - ");
        printInteger(t);
        print((uint32_t*) " ~ ");
        printInteger(n);
        println();
      }
  }
}

void fct_multu() {
  uint32_t s;
  uint32_t t;
  uint32_t n;

  if (interpret) {
    s = *(registers+rs);
    t = *(registers+rt);

    n = multiplyWrap(s, t);
  }

  if (debug) {
    printFunction(function);
    print((uint32_t*) " ");
    printRegister(rs);
    print((uint32_t*) ",");
    printRegister(rt);
    if (interpret) {
      print((uint32_t*) ": ");
      printRegister(rs);
      print((uint32_t*) "=");
      printInteger(s);
      print((uint32_t*) ",");
      printRegister(rt);
      print((uint32_t*) "=");
      printInteger(t);
      print((uint32_t*) ",$lo=");
      printInteger(loReg);
      print((uint32_t*) " -> $lo=");
      printInteger(n);
    }
    println();
  }

  if (interpret) {
    // TODO: 64-bit resolution currently not supported
    loReg = n;

    pc = pc + WORDSIZE;

    if (debug_overflow)
      if (INT_OVERFLOW == OVERFLOW_YES) {
        print((uint32_t*) "overflow: ");
        printInteger(s);
        print((uint32_t*) " * ");
        printInteger(t);
        print((uint32_t*) " ~ ");
        printInteger(n);
        println();
      }
  }
}

void fct_divu() {
  uint32_t s;
  uint32_t t;
  uint32_t l;
  uint32_t h;

  if (interpret) {
    s = *(registers+rs);
    t = *(registers+rt);

    checkDivision(s, t);

    if (debug_overflow)
      if (INT_OVERFLOW == OVERFLOW_YES) {
        if (t == 0)
          print((uint32_t*) "division-by-zero error: ");
        else
          print((uint32_t*) "signed integer error: ");
        printInteger(s);
        print((uint32_t*) " / ");
        printInteger(t);
        println();
      }

    // this will fail if t == 0 or (s == INT_MIN and t == -1)
    l = s / t;
    h = s % t;
  }

  if (debug) {
    printFunction(function);
    print((uint32_t*) " ");
    printRegister(rs);
    print((uint32_t*) ",");
    printRegister(rt);
    if (interpret) {
      print((uint32_t*) ": ");
      printRegister(rs);
      print((uint32_t*) "=");
      printInteger(s);
      print((uint32_t*) ",");
      printRegister(rt);
      print((uint32_t*) "=");
      printInteger(t);
      print((uint32_t*) ",$lo=");
      printInteger(loReg);
      print((uint32_t*) ",$hi=");
      printInteger(hiReg);
      print((uint32_t*) " -> $lo=");
      printInteger(l);
      print((uint32_t*) ",$hi=");
      printInteger(h);
    }
  }

  if (interpret) {
    loReg = l;
    hiReg = h;

    pc = pc + WORDSIZE;
  }
}

void fct_mfhi() {
  if (debug) {
    printFunction(function);
    print((uint32_t*) " ");
    printRegister(rd);
    if (interpret) {
      print((uint32_t*) ":");
      printRegister(rd);
      print((uint32_t*) "=");
      printInteger(*(registers+rd));
      print((uint32_t*) ",$hi=");
      printInteger(hiReg);
    }
  }

  if (interpret) {
    *(registers+rd) = hiReg;

    pc = pc + WORDSIZE;
  }

  if (debug) {
    if (interpret) {
      print((uint32_t*) " -> ");
      printRegister(rd);
      print((uint32_t*) "=");
      printInteger(*(registers+rd));
    }
    println();
  }
}

void fct_mflo() {
  if (debug) {
    printFunction(function);
    print((uint32_t*) " ");
    printRegister(rd);
    if (interpret) {
      print((uint32_t*) ": ");
      printRegister(rd);
      print((uint32_t*) "=");
      printInteger(*(registers+rd));
      print((uint32_t*) ",$lo=");
      printInteger(loReg);
    }
  }

  if (interpret) {
    *(registers+rd) = loReg;

    pc = pc + WORDSIZE;
  }

  if (debug) {
    if (interpret) {
      print((uint32_t*) " -> ");
      printRegister(rd);
      print((uint32_t*) "=");
      printInteger(*(registers+rd));
    }
    println();
  }
}

void fct_slt() {
  if (debug) {
    printFunction(function);
    print((uint32_t*) " ");
    printRegister(rd);
    print((uint32_t*) ",");
    printRegister(rs);
    print((uint32_t*) ",");
    printRegister(rt);
    if (interpret) {
      print((uint32_t*) ": ");
      printRegister(rs);
      print((uint32_t*) "=");
      printInteger(*(registers+rs));
      print((uint32_t*) ",");
      printRegister(rt);
      print((uint32_t*) "=");
      printInteger(*(registers+rt));
    }
  }

  if (interpret) {
    if (*(registers+rs) < *(registers+rt))
      *(registers+rd) = 1;
    else
      *(registers+rd) = 0;

    pc = pc + WORDSIZE;
  }

  if (debug) {
    if (interpret) {
      print((uint32_t*) " -> ");
      printRegister(rd);
      print((uint32_t*) "=");
      printInteger(*(registers+rd));
    }
    println();
  }
}

void fct_jr() {
  if (debug) {
    printFunction(function);
    print((uint32_t*) " ");
    printRegister(rs);
    if (interpret) {
      print((uint32_t*) ": ");
      printRegister(rs);
      print((uint32_t*) "=");
      printHexadecimal(*(registers+rs), 0);
    }
  }

  if (interpret)
    pc = *(registers+rs);

  if (debug) {
    if (interpret) {
      print((uint32_t*) " -> $pc=");
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
    pc = pc + WORDSIZE;

    if (*(registers+REG_V0) == SYSCALL_SWITCH)
      implementSwitch();
    else
      throwException(EXCEPTION_SYSCALL, 0);
  }
}

void op_addiu() {
  if (debug) {
    printOpcode(opcode);
    print((uint32_t*) " ");
    printRegister(rt);
    print((uint32_t*) ",");
    printRegister(rs);
    print((uint32_t*) ",");
    printInteger(signExtend(immediate));
    if (interpret) {
      print((uint32_t*) ": ");
      printRegister(rt);
      print((uint32_t*) "=");
      printInteger(*(registers+rt));
      print((uint32_t*) ",");
      printRegister(rs);
      print((uint32_t*) "=");
      printInteger(*(registers+rs));
    }
  }

  if (interpret) {
    *(registers+rt) = *(registers+rs) + signExtend(immediate);

    // TODO: check for overflow

    pc = pc + WORDSIZE;
  }

  if (debug) {
    if (interpret) {
      print((uint32_t*) " -> ");
      printRegister(rt);
      print((uint32_t*) "=");
      printInteger(*(registers+rt));
    }
    println();
  }
}

void op_lw() {
  uint32_t vaddr;

  if (debug) {
    printOpcode(opcode);
    print((uint32_t*) " ");
    printRegister(rt);
    print((uint32_t*) ",");
    printInteger(signExtend(immediate));
    print((uint32_t*) "(");
    printRegister(rs);
    print((uint32_t*) ")");
    if (interpret) {
      print((uint32_t*) ": ");
      printRegister(rt);
      print((uint32_t*) "=");
      printInteger(*(registers+rt));
      print((uint32_t*) ",");
      printRegister(rs);
      print((uint32_t*) "=");
      printHexadecimal(*(registers+rs), 0);
    }
  }

  if (interpret) {
    vaddr = *(registers+rs) + signExtend(immediate);

    if (isValidVirtualAddress(vaddr)) {
      if (isVirtualAddressMapped(pt, vaddr)) {
        *(registers+rt) = loadVirtualMemory(pt, vaddr);

        // keep track of number of loads
        loads = loads + 1;

        *(loadsPerAddress + pc / WORDSIZE) = *(loadsPerAddress + pc / WORDSIZE) + 1;

        pc = pc + WORDSIZE;
      } else
        throwException(EXCEPTION_PAGEFAULT, getPageOfVirtualAddress(vaddr));
    } else
      // TODO: pass invalid vaddr
      throwException(EXCEPTION_INVALIDADDRESS, 0);
  }

  if (debug) {
    if (interpret) {
      print((uint32_t*) " -> ");
      printRegister(rt);
      print((uint32_t*) "=");
      printInteger(*(registers+rt));
      print((uint32_t*) "=memory[");
      printHexadecimal(vaddr, 0);
      print((uint32_t*) "]");
    }
    println();
  }
}

void op_sw() {
  uint32_t vaddr;

  if (debug) {
    printOpcode(opcode);
    print((uint32_t*) " ");
    printRegister(rt);
    print((uint32_t*) ",");
    printInteger(signExtend(immediate));
    print((uint32_t*) "(");
    printRegister(rs);
    print((uint32_t*) ")");
    if (interpret) {
      print((uint32_t*) ": ");
      printRegister(rt);
      print((uint32_t*) "=");
      printInteger(*(registers+rt));
      print((uint32_t*) ",");
      printRegister(rs);
      print((uint32_t*) "=");
      printHexadecimal(*(registers+rs), 0);
    }
  }

  if (interpret) {
    vaddr = *(registers+rs) + signExtend(immediate);

    if (isValidVirtualAddress(vaddr)) {
      if (isVirtualAddressMapped(pt, vaddr)) {
        storeVirtualMemory(pt, vaddr, *(registers+rt));

        // keep track of number of stores
        stores = stores + 1;

        *(storesPerAddress + pc / WORDSIZE) = *(storesPerAddress + pc / WORDSIZE) + 1;

        pc = pc + WORDSIZE;
      } else
        throwException(EXCEPTION_PAGEFAULT, getPageOfVirtualAddress(vaddr));
    } else
      // TODO: pass invalid vaddr
      throwException(EXCEPTION_INVALIDADDRESS, 0);
  }

  if (debug) {
    if (interpret) {
      print((uint32_t*) " -> memory[");
      printHexadecimal(vaddr, 0);
      print((uint32_t*) "]=");
      printInteger(*(registers+rt));
      print((uint32_t*) "=");
      printRegister(rt);
    }
    println();
  }
}

void op_beq() {
  if (debug) {
    printOpcode(opcode);
    print((uint32_t*) " ");
    printRegister(rs);
    print((uint32_t*) ",");
    printRegister(rt);
    print((uint32_t*) ",");
    printInteger(signExtend(immediate));
    print((uint32_t*) "[");
    printHexadecimal(pc + WORDSIZE + signExtend(immediate) * WORDSIZE, 0);
    print((uint32_t*) "]");
    if (interpret) {
      print((uint32_t*) ": ");
      printRegister(rs);
      print((uint32_t*) "=");
      printInteger(*(registers+rs));
      print((uint32_t*) ",");
      printRegister(rt);
      print((uint32_t*) "=");
      printInteger(*(registers+rt));
    }
  }

  if (interpret) {
    pc = pc + WORDSIZE;

    if (*(registers+rs) == *(registers+rt)) {
      pc = pc + signExtend(immediate) * WORDSIZE;

      if (signedLessThan(signExtend(immediate), 0)) {
        // keep track of number of loop iterations
        loops = loops + 1;

        *(loopsPerAddress + pc / WORDSIZE) = *(loopsPerAddress + pc / WORDSIZE) + 1;
      }

      // TODO: execute delay slot
    }
  }

  if (debug) {
    if (interpret) {
      print((uint32_t*) " -> $pc=");
      printHexadecimal(pc, 0);
    }
    println();
  }
}

void op_jal() {
  if (debug) {
    printOpcode(opcode);
    print((uint32_t*) " ");
    printHexadecimal(instr_index, 0);
    print((uint32_t*) "[");
    printHexadecimal(instr_index * WORDSIZE, 0);
    print((uint32_t*) "]");
    if (interpret) {
      print((uint32_t*) ": ");
      printRegister(REG_RA);
      print((uint32_t*) "=");
      printHexadecimal(*(registers+REG_RA), 0);
    }
  }

  if (interpret) {
    // skip over delay slot
    *(registers+REG_RA) = pc + 8;

    pc = instr_index * WORDSIZE;

    // keep track of number of procedure calls
    calls = calls + 1;

    *(callsPerAddress + pc / WORDSIZE) = *(callsPerAddress + pc / WORDSIZE) + 1;

    // TODO: execute delay slot
  }

  if (debug) {
    if (interpret) {
      print((uint32_t*) " -> ");
      printRegister(REG_RA);
      print((uint32_t*) "=");
      printHexadecimal(*(registers+REG_RA), 0);
      print((uint32_t*) ",$pc=");
      printHexadecimal(pc, 0);
    }
    println();
  }
}

void op_j() {
  if (debug) {
    printOpcode(opcode);
    print((uint32_t*) " ");
    printHexadecimal(instr_index, 0);
    print((uint32_t*) "[");
    printHexadecimal(instr_index * WORDSIZE, 0);
    print((uint32_t*) "]");
  }

  if (interpret) {
    pc = instr_index * WORDSIZE;

    // TODO: execute delay slot
  }

  if (debug) {
    if (interpret) {
      print((uint32_t*) ": -> $pc=");
      printHexadecimal(pc, 0);
    }
    println();
  }
}

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void printException(uint32_t exception, uint32_t faultingPage) {
  print((uint32_t*) *(EXCEPTIONS + exception));

  if (exception == EXCEPTION_PAGEFAULT) {
    print((uint32_t*) " at ");
    printHexadecimal(faultingPage, 8);
  }
}

void throwException(uint32_t exception, uint32_t faultingPage) {
  setException(currentContext, exception);
  setFaultingPage(currentContext, faultingPage);

  trap = 1;

  if (debug_exception) {
    print(selfieName);
    print((uint32_t*) ": context ");
    printHexadecimal((uint32_t) currentContext, 8);
    print((uint32_t*) " throws ");
    printException(exception, faultingPage);
    print((uint32_t*) " exception");
    println();
  }
}

void fetch() {
  // assert: isValidVirtualAddress(pc) == 1
  // assert: isVirtualAddressMapped(pt, pc) == 1

  ir = loadVirtualMemory(pt, pc);
}

void execute() {
  if (debug) {
    if (interpret) {
      print(getName(currentContext));
      print((uint32_t*) ": $pc=");
    }
    printHexadecimal(pc, 0);
    if (sourceLineNumber != (uint32_t*) 0) {
      print((uint32_t*) "(~");
      printInteger(*(sourceLineNumber + pc / WORDSIZE));
      print((uint32_t*) ")");
    }
    print((uint32_t*) ": ");
    printHexadecimal(ir, 8);
    print((uint32_t*) ": ");
  }

  if (opcode == OP_SPECIAL) {
    if (function == FCT_NOP)
      fct_nop();
    else if (function == FCT_ADDU)
      fct_addu();
    else if (function == FCT_SUBU)
      fct_subu();
    else if (function == FCT_MULTU)
      fct_multu();
    else if (function == FCT_DIVU)
      fct_divu();
    else if (function == FCT_MFHI)
      fct_mfhi();
    else if (function == FCT_MFLO)
      fct_mflo();
    else if (function == FCT_SLT)
      fct_slt();
    else if (function == FCT_JR)
      fct_jr();
    else if (function == FCT_SYSCALL)
      fct_syscall();
    else
      throwException(EXCEPTION_UNKNOWNINSTRUCTION, 0);
  } else if (opcode == OP_ADDIU)
    op_addiu();
  else if (opcode == OP_LW)
    op_lw();
  else if (opcode == OP_SW)
    op_sw();
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

uint32_t* runUntilException() {
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

uint32_t addressWithMaxCounter(uint32_t* counters, uint32_t max) {
  uint32_t a;
  uint32_t n;
  uint32_t i;
  uint32_t c;

  a = -1;

  n = 0;

  i = 0;

  while (i < maxBinaryLength / WORDSIZE) {
    c = *(counters + i);

    if (n < c)
      if (c < max) {
        n = c;
        a = i * WORDSIZE;
      }

    i = i + 1;
  }

  return a;
}

uint32_t printCounters(uint32_t total, uint32_t* counters, uint32_t max) {
  uint32_t a;

  a = addressWithMaxCounter(counters, max);

  printInteger(*(counters + a / WORDSIZE));

  print((uint32_t*) "(");
  printFixedPointPercentage(total, *(counters + a / WORDSIZE));
  print((uint32_t*) "%)");

  if (*(counters + a / WORDSIZE) != 0) {
    print((uint32_t*) "@");
    printHexadecimal(a, 0);
    if (sourceLineNumber != (uint32_t*) 0) {
      print((uint32_t*) "(~");
      printInteger(*(sourceLineNumber + a / WORDSIZE));
      print((uint32_t*) ")");
    }
  }

  return a;
}

void printProfile(uint32_t* message, uint32_t total, uint32_t* counters) {
  uint32_t a;

  if (total > 0) {
    print(selfieName);
    print(message);
    printInteger(total);
    print((uint32_t*) ",");
    a = printCounters(total, counters, INT_MAX); // max counter
    print((uint32_t*) ",");
    a = printCounters(total, counters, *(counters + a / WORDSIZE)); // 2nd max
    print((uint32_t*) ",");
    a = printCounters(total, counters, *(counters + a / WORDSIZE)); // 3rd max
    println();
  }
}

void selfie_disassemble() {
  assemblyName = getArgument();

  if (codeLength == 0) {
    print(selfieName);
    print((uint32_t*) ": nothing to disassemble to output file ");
    print(assemblyName);
    println();

    return;
  }

  // assert: assemblyName is mapped and not longer than maxFilenameLength

  assemblyFD = openWriteOnly(assemblyName);

  if (signedLessThan(assemblyFD, 0)) {
    print(selfieName);
    print((uint32_t*) ": could not create assembly output file ");
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
    ir = loadBinary(pc);

    decode();
    execute();

    pc = pc + WORDSIZE;
  }

  debug = 0;

  outputName = (uint32_t*) 0;
  outputFD   = 1;

  print(selfieName);
  print((uint32_t*) ": ");
  printInteger(numberOfWrittenCharacters);
  print((uint32_t*) " characters of assembly with ");
  printInteger(codeLength / WORDSIZE);
  print((uint32_t*) " instructions written into ");
  print(assemblyName);
  println();
}

// -----------------------------------------------------------------
// ---------------------------- CONTEXTS ---------------------------
// -----------------------------------------------------------------

uint32_t* allocateContext(uint32_t* parent, uint32_t* vctxt, uint32_t* in) {
  uint32_t* context;

  if (freeContexts == (uint32_t*) 0)
    context = smalloc(6 * SIZEOFINTSTAR + 11 * SIZEOFINT);
  else {
    context = freeContexts;

    freeContexts = getNextContext(freeContexts);
  }

  setNextContext(context, in);
  setPrevContext(context, (uint32_t*) 0);

  if (in != (uint32_t*) 0)
    setPrevContext(in, context);

  setPC(context, 0);

  // allocate zeroed memory for general purpose registers
  // TODO: reuse memory
  setRegs(context, zalloc(NUMBEROFREGISTERS * WORDSIZE));

  setLoReg(context, 0);
  setHiReg(context, 0);

  // allocate zeroed memory for page table
  // TODO: save and reuse memory for page table
  setPT(context, zalloc(NUMBEROFPAGES * WORDSIZE));

  // determine range of recently mapped pages
  setLoPage(context, 0);
  setMePage(context, 0);
  setHiPage(context, getPageOfVirtualAddress(HIGHESTMEMORYADDRESS));

  // heap starts where it is safe to start
  setProgramBreak(context, maxBinaryLength);

  setException(context, EXCEPTION_NOEXCEPTION);
  setFaultingPage(context, 0);

  setExitCode(context, EXITCODE_NOERROR);

  setParent(context, parent);
  setVirtualContext(context, vctxt);

  setName(context, (uint32_t*) 0);

  return context;
}

uint32_t* findContext(uint32_t* parent, uint32_t* vctxt, uint32_t* in) {
  uint32_t* context;

  context = in;

  while (context != (uint32_t*) 0) {
    if (getParent(context) == parent)
      if (getVirtualContext(context) == vctxt)
        return context;

    context = getNextContext(context);
  }

  return (uint32_t*) 0;
}

void freeContext(uint32_t* context) {
  setNextContext(context, freeContexts);

  freeContexts = context;
}

uint32_t* deleteContext(uint32_t* context, uint32_t* from) {
  if (getNextContext(context) != (uint32_t*) 0)
    setPrevContext(getNextContext(context), getPrevContext(context));

  if (getPrevContext(context) != (uint32_t*) 0) {
    setNextContext(getPrevContext(context), getNextContext(context));
    setPrevContext(context, (uint32_t*) 0);
  } else
    from = getNextContext(context);

  freeContext(context);

  return from;
}

// -----------------------------------------------------------------
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

uint32_t* createContext(uint32_t* parent, uint32_t* vctxt) {
  // TODO: check if context already exists
  usedContexts = allocateContext(parent, vctxt, usedContexts);

  if (currentContext == (uint32_t*) 0)
    currentContext = usedContexts;

  if (debug_create) {
    print(selfieName);
    print((uint32_t*) ": parent context ");
    printHexadecimal((uint32_t) parent, 8);
    print((uint32_t*) " created child context ");
    printHexadecimal((uint32_t) usedContexts, 8);
    println();
  }

  return usedContexts;
}

uint32_t* cacheContext(uint32_t* vctxt) {
  uint32_t* context;

  // find cached context on my boot level
  context = findContext(currentContext, vctxt, usedContexts);

  if (context == (uint32_t*) 0)
    // create cached context on my boot level
    context = createContext(currentContext, vctxt);

  return context;
}

void saveContext(uint32_t* context) {
  uint32_t* parentTable;
  uint32_t* vctxt;
  uint32_t r;
  uint32_t* regs;
  uint32_t* vregs;

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

    vregs = (uint32_t*) loadVirtualMemory(parentTable, Regs(vctxt));

    while (r < NUMBEROFREGISTERS) {
      storeVirtualMemory(parentTable, (uint32_t) (vregs + r), *(regs + r));

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

void mapPage(uint32_t* context, uint32_t page, uint32_t frame) {
  uint32_t* table;

  table = getPT(context);

  // assert: 0 <= page < NUMBEROFPAGES

  // on boot level zero frame may be any signed integer

  *(table + page) = frame;

  // exploit spatial locality in page table caching
  if (page != getHiPage(context)) {
    if (page < getLoPage(context))
      setLoPage(context, page);
    else if (getMePage(context) < page)
      setMePage(context, page);
  }

  if (debug_map) {
    print(selfieName);
    print((uint32_t*) ": page ");
    printHexadecimal(page, 4);
    print((uint32_t*) " mapped to frame ");
    printHexadecimal(frame, 8);
    print((uint32_t*) " in context ");
    printHexadecimal((uint32_t) context, 8);
    println();
  }
}

void restoreContext(uint32_t* context) {
  uint32_t* parentTable;
  uint32_t* vctxt;
  uint32_t r;
  uint32_t* regs;
  uint32_t* vregs;
  uint32_t* table;
  uint32_t page;
  uint32_t me;
  uint32_t frame;

  if (getParent(context) != MY_CONTEXT) {
    parentTable = getPT(getParent(context));

    vctxt = getVirtualContext(context);

    setPC(context, loadVirtualMemory(parentTable, PC(vctxt)));

    r = 0;

    regs = getRegs(context);

    vregs = (uint32_t*) loadVirtualMemory(parentTable, Regs(vctxt));

    while (r < NUMBEROFREGISTERS) {
      *(regs + r) = loadVirtualMemory(parentTable, (uint32_t) (vregs + r));

      r = r + 1;
    }

    setLoReg(context, loadVirtualMemory(parentTable, LoReg(vctxt)));
    setHiReg(context, loadVirtualMemory(parentTable, HiReg(vctxt)));
    setProgramBreak(context, loadVirtualMemory(parentTable, ProgramBreak(vctxt)));

    setException(context, loadVirtualMemory(parentTable, Exception(vctxt)));
    setFaultingPage(context, loadVirtualMemory(parentTable, FaultingPage(vctxt)));
    setExitCode(context, loadVirtualMemory(parentTable, ExitCode(vctxt)));

    table = (uint32_t*) loadVirtualMemory(parentTable, PT(vctxt));

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

uint32_t pavailable() {
  if (freePageFrameMemory > 0)
    return 1;
  else if (usedPageFrameMemory + MEGABYTEINWORDS <= pageFrameMemory)
    return 1;
  else
    return 0;
}

uint32_t pused() {
  return usedPageFrameMemory - freePageFrameMemory;
}

uint32_t* palloc() {
  // CAUTION: on boot level zero palloc may return frame addresses < 0
  uint32_t block;
  uint32_t frame;

  // assert: pageFrameMemory is equal to or a multiple of MEGABYTEINWORDS
  // assert: PAGESIZEINWORDS is a factor of MEGABYTEINWORDS strictly less than MEGABYTEINWORDS

  if (freePageFrameMemory == 0) {
    freePageFrameMemory = MEGABYTEINWORDS;

    if (usedPageFrameMemory + freePageFrameMemory <= pageFrameMemory) {
      // on boot level zero allocate zeroed memory
      block = (uint32_t) zalloc(freePageFrameMemory * WORDSIZE);

      usedPageFrameMemory = usedPageFrameMemory + freePageFrameMemory;

      // page frames must be page-aligned to work as page table index
      nextPageFrame = roundUp(block, PAGESIZE) / WORDSIZE;

      if (nextPageFrame > block)
        // losing one page frame to fragmentation
        freePageFrameMemory = freePageFrameMemory - PAGESIZEINWORDS;
    } else {
      print(selfieName);
      print((uint32_t*) ": palloc out of physical memory");
      println();

      exit(EXITCODE_OUTOFPHYSICALMEMORY);
    }
  }

  // frame[number of bytes] = nextPageFrame[number of words] * WORDSIZE
  frame = nextPageFrame * WORDSIZE;

  nextPageFrame = nextPageFrame + PAGESIZEINWORDS;

  freePageFrameMemory = freePageFrameMemory - PAGESIZEINWORDS;

  // strictly, touching is only necessary on boot levels higher than zero
  return touch((uint32_t*) frame, PAGESIZE);
}

void pfree(uint32_t* frame) {
  // TODO: implement free list of page frames
}

void mapAndStore(uint32_t* context, uint32_t vaddr, uint32_t data) {
  // assert: isValidVirtualAddress(vaddr) == 1

  if (isVirtualAddressMapped(getPT(context), vaddr) == 0)
    mapPage(context, getPageOfVirtualAddress(vaddr), (uint32_t) palloc());

  storeVirtualMemory(getPT(context), vaddr, data);
}

void up_loadBinary(uint32_t* context) {
  uint32_t vaddr;

  setName(context, binaryName);

  // binaries start at lowest virtual address
  vaddr = 0;

  while (vaddr < binaryLength) {
    mapAndStore(context, vaddr, loadBinary(vaddr));

    vaddr = vaddr + WORDSIZE;
  }
}

uint32_t up_loadString(uint32_t* context, uint32_t* s, uint32_t SP) {
  uint32_t bytes;
  uint32_t i;

  bytes = roundUp(stringLength(s) + 1, WORDSIZE);

  // allocate memory for storing string
  SP = SP - bytes;

  i = 0;

  while (i < bytes) {
    mapAndStore(context, SP + i, *s);

    s = s + 1;

    i = i + WORDSIZE;
  }

  return SP;
}

void up_loadArguments(uint32_t* context, uint32_t argc, uint32_t* argv) {
  uint32_t SP;
  uint32_t vargv;
  uint32_t i_argc;
  uint32_t i_vargv;

  // arguments are pushed onto stack which starts at highest virtual address
  SP = HIGHESTMEMORYADDRESS;

  // allocate memory for storing stack pointer later
  SP = SP - WORDSIZE;

  // allocate memory for storing *argv array
  SP = SP - argc * WORDSIZE;

  // vargv invalid if argc == 0
  vargv = SP + WORDSIZE;

  i_vargv = vargv;
  i_argc  = argc;

  while (i_argc > 0) {
    SP = up_loadString(context, (uint32_t*) *argv, SP);

    // store pointer to string in virtual *argv
    mapAndStore(context, i_vargv, SP);

    argv = argv + 1;

    i_vargv = i_vargv + WORDSIZE;

    i_argc = i_argc - 1;
  }

  // allocate memory for one word on the stack
  SP = SP - WORDSIZE;

  // push argc
  mapAndStore(context, SP, argc);

  // allocate memory for one word on the stack
  SP = SP - WORDSIZE;

  // push virtual argv
  mapAndStore(context, SP, vargv);

  // store stack pointer at highest virtual address for binary to retrieve
  mapAndStore(context, HIGHESTMEMORYADDRESS, SP);
}

void mapUnmappedPages(uint32_t* context) {
  uint32_t page;

  // assert: page table is only mapped from beginning up and end down

  page = 0;

  while (isPageMapped(getPT(context), page))
    page = page + 1;

  while (pavailable()) {
    mapPage(context, page, (uint32_t) palloc());

    page = page + 1;
  }
}

uint32_t isBootLevelZero() {
  // in C99 malloc(0) returns either a null pointer or a unique pointer. 
  // (see http://pubs.opengroup.org/onlinepubs/9699919799/)
  // selfie's malloc implementation, on the other hand, 
  // returns the same not null address, if malloc(0) is called consecutively.
  uint32_t firstMalloc;
  uint32_t secondMalloc;

  firstMalloc = (uint32_t) malloc(0);
  secondMalloc = (uint32_t) malloc(0);

  if (firstMalloc == 0)
    return 1;
  if (firstMalloc != secondMalloc)
    return 1;

  // it is selfie's malloc, so it can not be boot level zero.
  return 0;
}

uint32_t handleSystemCalls(uint32_t* context) {
  uint32_t v0;

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
      print((uint32_t*) ": unknown system call ");
      printInteger(v0);
      println();

      setExitCode(context, EXITCODE_UNKNOWNSYSCALL);

      return EXIT;
    }
  } else if (getException(context) != EXCEPTION_TIMER) {
    print(selfieName);
    print((uint32_t*) ": context ");
    print(getName(context));
    print((uint32_t*) " throws uncaught ");
    printException(getException(context), getFaultingPage(context));
    println();

    setExitCode(context, EXITCODE_UNCAUGHTEXCEPTION);

    return EXIT;
  }

  return DONOTEXIT;
}

uint32_t mipster(uint32_t* toContext) {
  uint32_t timeout;
  uint32_t* fromContext;

  print((uint32_t*) "mipster");
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
        mapPage(fromContext, getFaultingPage(fromContext), (uint32_t) palloc());
      else if (handleSystemCalls(fromContext) == EXIT)
        return getExitCode(fromContext);

      setException(fromContext, EXCEPTION_NOEXCEPTION);

      toContext = fromContext;

      timeout = TIMESLICE;
    }
  }
}

uint32_t minster(uint32_t* toContext) {
  uint32_t timeout;
  uint32_t* fromContext;

  print((uint32_t*) "minster");
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

uint32_t mobster(uint32_t* toContext) {
  uint32_t timeout;
  uint32_t* fromContext;

  print((uint32_t*) "mobster");
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

uint32_t hypster(uint32_t* toContext) {
  uint32_t* fromContext;

  print((uint32_t*) "hypster");
  println();

  while (1) {
    fromContext = hypster_switch(toContext, TIMESLICE);

    if (getException(fromContext) == EXCEPTION_PAGEFAULT)
      // TODO: use this table to unmap and reuse frames
      mapPage(fromContext, getFaultingPage(fromContext), (uint32_t) palloc());
    else if (handleSystemCalls(fromContext) == EXIT)
      return getExitCode(fromContext);

    setException(fromContext, EXCEPTION_NOEXCEPTION);

    toContext = fromContext;
  }
}

uint32_t mixter(uint32_t* toContext, uint32_t mix) {
  // works with mipsters and hypsters
  uint32_t mslice;
  uint32_t timeout;
  uint32_t* fromContext;

  print((uint32_t*) "mixter (");
  printInteger(mix);
  print((uint32_t*) "% mipster/");
  printInteger(100 - mix);
  print((uint32_t*) "% hypster)");
  println();

  mslice = TIMESLICE;

  if (mslice <= INT_MAX / 100)
    mslice = mslice * mix / 100;
  else if (mslice <= INT_MAX / 10)
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
        mapPage(fromContext, getFaultingPage(fromContext), (uint32_t) palloc());
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

uint32_t selfie_run(uint32_t machine) {
  uint32_t exitCode;

  if (binaryLength == 0) {
    print(selfieName);
    print((uint32_t*) ": nothing to run, debug, or host");
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
  print((uint32_t*) ": this is selfie executing ");
  print(binaryName);
  print((uint32_t*) " with ");
  printInteger(pageFrameMemory / MEGABYTEINWORDS);
  print((uint32_t*) "MB of physical memory on ");

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
  print((uint32_t*) ": this is selfie terminating ");
  print(getName(currentContext));
  print((uint32_t*) " with exit code ");
  printInteger(exitCode);
  print((uint32_t*) " and ");
  printFixedPointRatio(pused(), MEGABYTEINWORDS);
  print((uint32_t*) "MB of mapped memory");
  println();

  if (calls > 0) {
    print(selfieName);
    if (sourceLineNumber != (uint32_t*) 0)
      print((uint32_t*) ": profile: total,max(ratio%)@addr(line#),2max(ratio%)@addr(line#),3max(ratio%)@addr(line#)");
    else
      print((uint32_t*) ": profile: total,max(ratio%)@addr,2max(ratio%)@addr,3max(ratio%)@addr");
    println();
    printProfile((uint32_t*) ": calls: ", calls, callsPerAddress);
    printProfile((uint32_t*) ": loops: ", loops, loopsPerAddress);
    printProfile((uint32_t*) ": loads: ", loads, loadsPerAddress);
    printProfile((uint32_t*) ": stores: ", stores, storesPerAddress);
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

uint32_t clauseMayBeTrue(uint32_t* clauseAddress, uint32_t depth) {
  uint32_t variable;

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

uint32_t instanceMayBeTrue(uint32_t depth) {
  uint32_t clause;

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

uint32_t babysat(uint32_t depth) {
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
  uint32_t clause;
  uint32_t variable;

  print((uint32_t*) "p cnf ");
  printInteger(numberOfSATVariables);
  print((uint32_t*) " ");
  printInteger(numberOfSATClauses);
  println();

  clause = 0;

  while (clause < numberOfSATClauses) {
    variable = 0;

    while (variable < numberOfSATVariables) {
      if (*(SATInstance + clause * 2 * numberOfSATVariables + 2 * variable) == TRUE) {
        printInteger(variable + 1);
        print((uint32_t*) " ");
      } else if (*(SATInstance + clause * 2 * numberOfSATVariables + 2 * variable + 1) == TRUE) {
        printInteger(-(variable + 1));
        print((uint32_t*) " ");
      }

      variable = variable + 1;
    }

    print((uint32_t*) "0");
    println();

    clause = clause + 1;
  }
}

void dimacs_findNextCharacter(uint32_t newLine) {
  uint32_t inComment;

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

void dimacs_word(uint32_t* word) {
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

uint32_t dimacs_number() {
  uint32_t number;

  if (symbol == SYM_INTEGER) {
    number = literal;

    dimacs_getSymbol();

    return number;
  } else
    syntaxErrorSymbol(SYM_INTEGER);

  exit(EXITCODE_PARSERERROR);
}

void dimacs_getClause(uint32_t clause) {
  uint32_t not;

  while (1) {
    not = 0;

    if (symbol == SYM_MINUS) {
      not = 1;

      dimacs_getSymbol();
    }

    if (symbol == SYM_INTEGER) {
      if (literal <= 0) {
        // if literal < 0 it is equal to INT_MIN which we treat here as 0
        dimacs_getSymbol();

        return;
      } else if (literal > numberOfSATVariables) {
        syntaxErrorMessage((uint32_t*) "clause exceeds declared number of variables");

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
  uint32_t clauses;

  clauses = 0;

  while (clauses < numberOfSATClauses)
    if (symbol != SYM_EOF) {
      dimacs_getClause(clauses);

      clauses = clauses + 1;
    } else {
      syntaxErrorMessage((uint32_t*) "instance has fewer clauses than declared");

      exit(EXITCODE_PARSERERROR);
    }

  if (symbol != SYM_EOF) {
    syntaxErrorMessage((uint32_t*) "instance has more clauses than declared");

    exit(EXITCODE_PARSERERROR);
  }
}

void selfie_loadDimacs() {
  sourceName = getArgument();

  print(selfieName);
  print((uint32_t*) ": this is selfie loading SAT instance ");
  print(sourceName);
  println();

  // assert: sourceName is mapped and not longer than maxFilenameLength

  sourceFD = open(sourceName, O_RDONLY, 0);

  if (signedLessThan(sourceFD, 0)) {
    print(selfieName);
    print((uint32_t*) ": could not open input file ");
    print(sourceName);
    println();

    exit(EXITCODE_IOERROR);
  }

  resetScanner();

  // ignore all comments before problem
  dimacs_findNextCharacter(1);

  dimacs_getSymbol();

  dimacs_word((uint32_t*) "p");
  dimacs_word((uint32_t*) "cnf");

  numberOfSATVariables = dimacs_number();

  SATAssignment = (uint32_t*) smalloc(numberOfSATVariables * WORDSIZE);

  numberOfSATClauses = dimacs_number();

  SATInstance = (uint32_t*) smalloc(numberOfSATClauses * 2 * numberOfSATVariables * WORDSIZE);

  dimacs_getInstance();

  print(selfieName);
  print((uint32_t*) ": ");
  printInteger(numberOfSATClauses);
  print((uint32_t*) " clauses with ");
  printInteger(numberOfSATVariables);
  print((uint32_t*) " declared variables loaded from ");
  print(sourceName);
  println();

  dimacsName = sourceName;
}

void selfie_sat() {
  uint32_t variable;

  selfie_loadDimacs();

  if (dimacsName == (uint32_t*) 0) {
    print(selfieName);
    print((uint32_t*) ": nothing to SAT solve");
    println();

    return;
  }

  selfie_printDimacs();

  if (babysat(0) == SAT) {
    print(selfieName);
    print((uint32_t*) ": ");
    print(dimacsName);
    print((uint32_t*) " is satisfiable with ");

    variable = 0;

    while (variable < numberOfSATVariables) {
      if (*(SATAssignment + variable) == FALSE)
        print((uint32_t*) "-");

      printInteger(variable + 1);
      print((uint32_t*) " ");

      variable = variable + 1;
    }
  } else {
    print(selfieName);
    print((uint32_t*) ": ");
    print(dimacsName);
    print((uint32_t*) " is unsatisfiable");
  }

  println();
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

uint32_t numberOfRemainingArguments() {
  return selfie_argc;
}

uint32_t* remainingArguments() {
  return selfie_argv;
}

uint32_t* peekArgument() {
  if (numberOfRemainingArguments() > 0)
    return (uint32_t*) *selfie_argv;
  else
    return (uint32_t*) 0;
}

uint32_t* getArgument() {
  uint32_t* argument;

  argument = peekArgument();

  if (numberOfRemainingArguments() > 0) {
    selfie_argc = selfie_argc - 1;
    selfie_argv = selfie_argv + 1;
  }

  return argument;
}

void setArgument(uint32_t* argv) {
  *selfie_argv = (uint32_t) argv;
}

void printUsage() {
  print(selfieName);
  print((uint32_t*) ": usage: ");
  print((uint32_t*) "selfie { -c { source } | -o binary | -s assembly | -l binary | -sat dimacs } ");
  print((uint32_t*) "[ ( -m | -d | -y | -min | -mob ) size ... ]");
  println();
}

uint32_t selfie() {
  uint32_t* option;

  if (numberOfRemainingArguments() == 0)
    printUsage();
  else {
    initScanner();
    initRegister();
    initDecoder();
    initInterpreter();

    while (numberOfRemainingArguments() > 0) {
      option = getArgument();

      if (stringCompare(option, (uint32_t*) "-c"))
        selfie_compile();
      else if (numberOfRemainingArguments() == 0) {
        // remaining options have at least one argument
        printUsage();

        return -1;
      } else if (stringCompare(option, (uint32_t*) "-o"))
        selfie_output();
      else if (stringCompare(option, (uint32_t*) "-s"))
        selfie_disassemble();
      else if (stringCompare(option, (uint32_t*) "-l"))
        selfie_load();
      else if (stringCompare(option, (uint32_t*) "-sat"))
        selfie_sat();
      else if (stringCompare(option, (uint32_t*) "-m"))
        return selfie_run(MIPSTER);
      else if (stringCompare(option, (uint32_t*) "-d")) {
        debug = 1;

        return selfie_run(MIPSTER);
      } else if (stringCompare(option, (uint32_t*) "-y"))
        return selfie_run(HYPSTER);
      else if (stringCompare(option, (uint32_t*) "-min"))
        return selfie_run(MINSTER);
      else if (stringCompare(option, (uint32_t*) "-mob"))
        return selfie_run(MOBSTER);
      else {
        printUsage();

        return -1;
      }
    }
  }

  return 0;
}

uint32_t main(uint32_t argc, uint32_t* argv) {
  initSelfie(argc, (uint32_t*) argv);

  initLibrary();

  return selfie();
}