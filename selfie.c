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
uint64_t tenToThePowerOf(uint64_t p);

uint64_t leftShift(uint64_t n, uint64_t b);
uint64_t rightShift(uint64_t n, uint64_t b);

uint64_t getBits(uint64_t n, uint64_t i, uint64_t b);
uint64_t getLowWord(uint64_t n);
uint64_t getHighWord(uint64_t n);

uint64_t abs(uint64_t n);

uint64_t signedLessThan(uint64_t a, uint64_t b);
uint64_t signedDivision(uint64_t a, uint64_t b);

uint64_t isSignedInteger(uint64_t n, uint64_t b);
uint64_t signExtend(uint64_t n, uint64_t b);
uint64_t signShrink(uint64_t n, uint64_t b);

uint64_t  loadCharacter(uint64_t* s, uint64_t i);
uint64_t* storeCharacter(uint64_t* s, uint64_t i, uint64_t c);

uint64_t stringLength(uint64_t* s);
void     stringReverse(uint64_t* s);
uint64_t stringCompare(uint64_t* s, uint64_t* t);

uint64_t  atoi(uint64_t* s);
uint64_t* itoa(uint64_t n, uint64_t* s, uint64_t b, uint64_t a);

uint64_t fixedPointRatio(uint64_t a, uint64_t b, uint64_t f);
uint64_t fixedPointPercentage(uint64_t r, uint64_t f);

void putCharacter(uint64_t c);

void print(uint64_t* s);
void println();

void printCharacter(uint64_t c);
void printString(uint64_t* s);
void printInteger(uint64_t n);
void unprintInteger(uint64_t n);
void printHexadecimal(uint64_t n, uint64_t a);
void printOctal(uint64_t n, uint64_t a);
void printBinary(uint64_t n, uint64_t a);

uint64_t printFormat0(uint64_t* s, uint64_t i);
uint64_t printFormat1(uint64_t* s, uint64_t i, uint64_t* a);

void printf1(uint64_t* s, uint64_t* a1);
void printf2(uint64_t* s, uint64_t* a1, uint64_t* a2);
void printf3(uint64_t* s, uint64_t* a1, uint64_t* a2, uint64_t* a3);
void printf4(uint64_t* s, uint64_t* a1, uint64_t* a2, uint64_t* a3, uint64_t* a4);
void printf5(uint64_t* s, uint64_t* a1, uint64_t* a2, uint64_t* a3, uint64_t* a4, uint64_t* a5);
void printf6(uint64_t* s, uint64_t* a1, uint64_t* a2, uint64_t* a3, uint64_t* a4, uint64_t* a5, uint64_t* a6);

uint64_t roundUp(uint64_t n, uint64_t m);

uint64_t* smalloc(uint64_t size);
uint64_t* zalloc(uint64_t size);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t CHAR_EOF          =  -1; // end of file
uint64_t CHAR_BACKSPACE    =   8; // ASCII code 8  = backspace
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
uint64_t CHAR_BACKSLASH    =  92; // ASCII code 92 = backslash

uint64_t CPUBITWIDTH = 64;

uint64_t SIZEOFUINT64     = 8; // must be the same as REGISTERSIZE
uint64_t SIZEOFUINT64STAR = 8; // must be the same as REGISTERSIZE

uint64_t* power_of_two_table;

uint64_t INT64_MAX; // maximum numerical value of a signed 64-bit integer
uint64_t INT64_MIN; // minimum numerical value of a signed 64-bit integer

uint64_t UINT64_MAX; // maximum numerical value of an unsigned 64-bit integer

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
uint64_t  outputFD   = 1; // 1 is file descriptor of standard output

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

  // compute 64-bit signed integer range using unsigned integer arithmetic
  INT64_MIN = twoToThePowerOf(CPUBITWIDTH - 1);
  INT64_MAX = INT64_MIN - 1;

  // compute 64-bit unsigned integer range using signed integer arithmetic
  UINT64_MAX = -1;

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

void handleEscapeSequence();

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
uint64_t maxIntegerLength    = 20;  // maximum number of characters in an unsigned integer
uint64_t maxStringLength     = 128; // maximum number of characters in a string

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t lineNumber = 1; // current line number for error reporting

uint64_t* identifier = (uint64_t*) 0; // stores scanned identifier as string
uint64_t* integer    = (uint64_t*) 0; // stores scanned integer as string
uint64_t* string     = (uint64_t*) 0; // stores scanned string

uint64_t literal = 0; // stores numerical value of scanned integer or character

uint64_t integerIsSigned = 0; // enforce INT64_MIN limit if '-' was scanned before

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
// |  3 | class   | VARIABLE, BIGINT, STRING, PROCEDURE
// |  4 | type    | UINT64_T, UINT64STAR_T, VOID_T
// |  5 | value   | VARIABLE: initial value
// |  6 | address | VARIABLE, BIGINT, STRING: offset, PROCEDURE: address
// |  7 | scope   | REG_GP, REG_FP
// +----+---------+

uint64_t* getNextEntry(uint64_t* entry)  { return (uint64_t*) *entry; }
uint64_t* getString(uint64_t* entry)     { return (uint64_t*) *(entry + 1); }
uint64_t  getLineNumber(uint64_t* entry) { return             *(entry + 2); }
uint64_t  getClass(uint64_t* entry)      { return             *(entry + 3); }
uint64_t  getType(uint64_t* entry)       { return             *(entry + 4); }
uint64_t  getValue(uint64_t* entry)      { return             *(entry + 5); }
uint64_t  getAddress(uint64_t* entry)    { return             *(entry + 6); }
uint64_t  getScope(uint64_t* entry)      { return             *(entry + 7); }

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

uint64_t* getVariableOrBigInt(uint64_t* variable, uint64_t class);
void      load_upperBaseAddress(uint64_t* entry);
uint64_t  load_variableOrBigInt(uint64_t* variable, uint64_t class);
void      load_integer(uint64_t value);
void      load_string(uint64_t* string);

uint64_t help_call_codegen(uint64_t* entry, uint64_t* procedure);
void     help_procedure_prologue(uint64_t numberOfLocalVariableBytes);
void     help_procedure_epilogue(uint64_t numberOfParameterBytes);

uint64_t compile_call(uint64_t* procedure);
uint64_t compile_factor();
uint64_t compile_term();
uint64_t compile_simpleExpression();
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

uint64_t allocatedTemporaries = 0; // number of allocated temporaries

uint64_t allocatedMemory = 0; // number of bytes for global variables and strings

uint64_t returnBranches = 0; // fixup chain for return statements

uint64_t returnType = 0; // return type of currently parsed procedure

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

void emitRoundUp(uint64_t reg, uint64_t m);
void emitLeftShiftBy(uint64_t reg, uint64_t b);
void emitProgramEntry();
void emitStart();

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

uint64_t* getRegisterName(uint64_t reg);
void      printRegisterName(uint64_t reg);

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

void initRegister() {
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

void checkImmediateRange(uint64_t found, uint64_t bits);

uint64_t encodeRFormat(uint64_t funct7, uint64_t rs2, uint64_t rs1, uint64_t funct3, uint64_t rd, uint64_t opcode);
uint64_t getFunct7(uint64_t instruction);
uint64_t getRS2(uint64_t instruction);
uint64_t getRS1(uint64_t instruction);
uint64_t getFunct3(uint64_t instruction);
uint64_t getRD(uint64_t instruction);
uint64_t getOpcode(uint64_t instruction);
void     decodeRFormat();

uint64_t encodeIFormat(uint64_t immediate, uint64_t rs1, uint64_t funct3, uint64_t rd, uint64_t opcode);
uint64_t getImmediateIFormat(uint64_t instruction);
void     decodeIFormat();

uint64_t encodeSFormat(uint64_t immediate, uint64_t rs2, uint64_t rs1, uint64_t funct3, uint64_t opcode);
uint64_t getImmediateSFormat(uint64_t instruction);
void     decodeSFormat();

uint64_t encodeBFormat(uint64_t immediate, uint64_t rs2, uint64_t rs1, uint64_t funct3, uint64_t opcode);
uint64_t getImmediateBFormat(uint64_t instruction);
void     decodeBFormat();

uint64_t encodeJFormat(uint64_t immediate, uint64_t rd, uint64_t opcode);
uint64_t getImmediateJFormat(uint64_t instruction);
void     decodeJFormat();

uint64_t encodeUFormat(uint64_t immediate, uint64_t rd, uint64_t opcode);
uint64_t getImmediateUFormat(uint64_t instruction);
void     decodeUFormat();

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

void resetInstructionCounters();

uint64_t getTotalNumberOfInstructions();

void printInstructionCounter(uint64_t total, uint64_t counter, uint64_t* mnemonics);
void printInstructionCounters();

uint64_t loadInstruction(uint64_t baddr);
void     storeInstruction(uint64_t baddr, uint64_t instruction);

uint64_t loadData(uint64_t baddr);
void     storeData(uint64_t baddr, uint64_t data);

void emitInstruction(uint64_t instruction);

void emitNOP();

void emitLUI(uint64_t rd, uint64_t immediate);
void emitADDI(uint64_t rd, uint64_t rs1, uint64_t immediate);

void emitADD(uint64_t rd, uint64_t rs1, uint64_t rs2);
void emitSUB(uint64_t rd, uint64_t rs1, uint64_t rs2);
void emitMUL(uint64_t rd, uint64_t rs1, uint64_t rs2);
void emitDIVU(uint64_t rd, uint64_t rs1, uint64_t rs2);
void emitREMU(uint64_t rd, uint64_t rs1, uint64_t rs2);
void emitSLTU(uint64_t rd, uint64_t rs1, uint64_t rs2);

void emitLD(uint64_t rd, uint64_t rs1, uint64_t immediate);
void emitSD(uint64_t rs1, uint64_t immediate, uint64_t rs2);

void emitBEQ(uint64_t rs1, uint64_t rs2, uint64_t immediate);

void emitJAL(uint64_t rd, uint64_t immediate);
void emitJALR(uint64_t rd, uint64_t rs1, uint64_t immediate);

void emitECALL();

void fixup_relative_BFormat(uint64_t fromAddress);
void fixup_relative_JFormat(uint64_t fromAddress, uint64_t toAddress);
void fixlink_relative(uint64_t fromAddress, uint64_t toAddress);

uint64_t copyStringToBinary(uint64_t* s, uint64_t a);

void emitGlobalsStringsBigIntegers();

uint64_t* createELFHeader(uint64_t binaryLength);
uint64_t  parseELFHeader(uint64_t* header);

uint64_t openWriteOnly(uint64_t* name);

void selfie_output();

uint64_t* touch(uint64_t* memory, uint64_t length);

void selfie_load();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t maxBinaryLength = 262144; // 256KB

uint64_t ELF_HEADER_LEN  = 120;   // = 64 + 56 bytes (file + program header)

// is determined by RISC-V pk
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

uint64_t* binary       = (uint64_t*) 0; // binary of emitted instructions and data segment
uint64_t  binaryLength = 0;             // length of binary in bytes including data segment
uint64_t* binaryName   = (uint64_t*) 0; // file name of binary

uint64_t codeLength = 0; // length of code segment in binary in bytes
uint64_t entryPoint = 0; // entry point of code segment in virtual address space

uint64_t* sourceLineNumber = (uint64_t*) 0; // source line number per emitted instruction

uint64_t* assemblyName = (uint64_t*) 0; // name of assembly file
uint64_t  assemblyFD   = 0;             // file descriptor of open assembly file

uint64_t* ELF_header = (uint64_t*) 0;

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
uint64_t down_loadString(uint64_t* table, uint64_t vstring, uint64_t* s);
void     implementOpen(uint64_t* context);

void emitMalloc();
void implementBrk(uint64_t* context);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t debug_read  = 0;
uint64_t debug_write = 0;
uint64_t debug_open  = 0;
uint64_t debug_brk   = 0;

uint64_t SYSCALL_EXIT  = 93;
uint64_t SYSCALL_READ  = 63;
uint64_t SYSCALL_WRITE = 64;
uint64_t SYSCALL_OPEN  = 1024;
uint64_t SYSCALL_BRK   = 214;

// -----------------------------------------------------------------
// ----------------------- HYPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void      emitSwitch();
void      doSwitch(uint64_t* toContext, uint64_t timeout);
void      implementSwitch();
uint64_t* mipster_switch(uint64_t* toContext, uint64_t timeout);

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

uint64_t MEGABYTE = 1048576; // 1MB

uint64_t VIRTUALMEMORYSIZE = 4294967296; // 4GB of virtual memory

uint64_t WORDSIZE       = 4; // in bytes
uint64_t WORDSIZEINBITS = 32;

uint64_t INSTRUCTIONSIZE = 4; // must be the same as WORDSIZE
uint64_t REGISTERSIZE    = 8; // must be twice of WORDSIZE

uint64_t PAGESIZE = 4096; // we use standard 4KB pages

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

void printSourceLineNumberOfInstruction(uint64_t a);
void printInstructionContext();

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

void print_add_sub_mul_divu_remu_sltu(uint64_t *mnemonics);
void print_add_sub_mul_divu_remu_sltu_before();

void do_add();
void constrain_add();

void do_sub();
void constrain_sub();

void do_mul();
void constrain_mul();

void record_divu_remu();
void do_divu();
void constrain_divu();

void do_remu();
void constrain_remu();

void do_sltu();
void constrain_sltu();
void backtrack_sltu();

void     print_ld();
void     print_ld_before();
void     print_ld_after(uint64_t vaddr);
void     record_ld();
uint64_t do_ld();
uint64_t constrain_ld();

void     print_sd();
void     print_sd_before();
void     print_sd_after(uint64_t vaddr);
void     record_sd();
uint64_t do_sd();
void     undo_sd();
uint64_t constrain_sd();
void     backtrack_sd();

void print_beq();
void print_beq_before();
void print_beq_after();
void record_beq();
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
void record_ecall();
void do_ecall();
void undo_ecall();
void backtrack_ecall();

// -----------------------------------------------------------------
// -------------------------- REPLAY ENGINE ------------------------
// -----------------------------------------------------------------

void initReplayEngine();

void recordState(uint64_t value);

void replayTrace();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t maxReplayLength = 100;

// trace

uint64_t tc = 0; // trace counter

uint64_t* pcs    = (uint64_t*) 0; // trace of program counter values
uint64_t* values = (uint64_t*) 0; // trace of values

// ------------------------- INITIALIZATION ------------------------

void initReplayEngine() {
  pcs    = zalloc(maxReplayLength * SIZEOFUINT64);
  values = zalloc(maxReplayLength * SIZEOFUINT64);
}

// -----------------------------------------------------------------
// ------------------- SYMBOLIC EXECUTION ENGINE -------------------
// -----------------------------------------------------------------

void initSymbolicEngine();

void printSymbolicMemory(uint64_t svc);

uint64_t cardinality(uint64_t lo, uint64_t up);
uint64_t combinedCardinality(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2);

uint64_t isSymbolicValue(uint64_t type, uint64_t lo, uint64_t up);
uint64_t isSafeAddress(uint64_t vaddr, uint64_t reg);
uint64_t loadSymbolicMemory(uint64_t* pt, uint64_t vaddr);

uint64_t isTraceSpaceAvailable();

void ealloc();
void efree();

void storeSymbolicMemory(uint64_t* pt, uint64_t vaddr, uint64_t value, uint64_t type, uint64_t lo, uint64_t up, uint64_t trb);

void storeConstrainedMemory(uint64_t vaddr, uint64_t lo, uint64_t up, uint64_t trb);
void storeRegisterMemory(uint64_t reg, uint64_t value);

void constrainMemory(uint64_t reg, uint64_t lo, uint64_t up, uint64_t trb);

void setConstraint(uint64_t reg, uint64_t hasco, uint64_t vaddr, uint64_t hasmn, uint64_t colos, uint64_t coups);

void takeBranch(uint64_t b, uint64_t howManyMore);
void createConstraints(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2, uint64_t trb, uint64_t howManyMore);

uint64_t fuzzLo(uint64_t value);
uint64_t fuzzUp(uint64_t value);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t maxTraceLength = 100000;

uint64_t debug_symbolic = 0;

// ------------------------ GLOBAL VARIABLES -----------------------

// trace

uint64_t* tcs = (uint64_t*) 0; // trace of trace counters to previous values

uint64_t* types = (uint64_t*) 0; // memory range or integer interval

uint64_t* los = (uint64_t*) 0; // trace of lower bounds on values
uint64_t* ups = (uint64_t*) 0; // trace of upper bounds on values

uint64_t* vaddrs = (uint64_t*) 0; // trace of virtual addresses

// read history

uint64_t rc = 0; // read counter

uint64_t* read_values = (uint64_t*) 0;

uint64_t* read_los = (uint64_t*) 0;
uint64_t* read_ups = (uint64_t*) 0;

// registers

uint64_t* reg_typ = (uint64_t*) 0; // memory range or integer interval
uint64_t* reg_los = (uint64_t*) 0; // lower bound on register value
uint64_t* reg_ups = (uint64_t*) 0; // upper bound on register value

// register constraints on memory

uint64_t* reg_hasco = (uint64_t*) 0; // register has constraint
uint64_t* reg_vaddr = (uint64_t*) 0; // vaddr of constrained memory
uint64_t* reg_hasmn = (uint64_t*) 0; // constraint has minuend
uint64_t* reg_colos = (uint64_t*) 0; // offset on lower bound
uint64_t* reg_coups = (uint64_t*) 0; // offset on upper bound

// trace counter of most recent constraint

uint64_t mrcc = 0;

// fuzzing

uint64_t fuzz = 0; // power-of-two fuzzing factor for read calls

// ------------------------- INITIALIZATION ------------------------

void initSymbolicEngine() {
  pcs    = zalloc(maxTraceLength * SIZEOFUINT64);
  tcs    = zalloc(maxTraceLength * SIZEOFUINT64);
  values = zalloc(maxTraceLength * SIZEOFUINT64);
  types  = zalloc(maxTraceLength * SIZEOFUINT64);
  los    = zalloc(maxTraceLength * SIZEOFUINT64);
  ups    = zalloc(maxTraceLength * SIZEOFUINT64);
  vaddrs = zalloc(maxTraceLength * SIZEOFUINT64);

  read_values = zalloc(maxTraceLength * SIZEOFUINT64);
  read_los    = zalloc(maxTraceLength * SIZEOFUINT64);
  read_ups    = zalloc(maxTraceLength * SIZEOFUINT64);

  reg_typ = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_los = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_ups = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);

  reg_hasco = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_vaddr = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_hasmn = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_colos = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
  reg_coups = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);
}

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void initInterpreter();
void resetInterpreter();

void     printRegisterHexadecimal(uint64_t reg);
uint64_t isSystemRegister(uint64_t reg);
void     printRegisterValue(uint64_t reg);

void printException(uint64_t exception, uint64_t faultingPage);
void throwException(uint64_t exception, uint64_t faultingPage);

void fetch();
void decode_execute();
void interrupt();

uint64_t* runUntilException();

uint64_t instructionWithMaxCounter(uint64_t* counters, uint64_t max);
uint64_t printPerInstructionCounter(uint64_t total, uint64_t* counters, uint64_t max);
void     printPerInstructionProfile(uint64_t* message, uint64_t total, uint64_t* counters);

void printProfile();

void selfie_disassemble();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t EXCEPTION_NOEXCEPTION        = 0;
uint64_t EXCEPTION_PAGEFAULT          = 1;
uint64_t EXCEPTION_SYSCALL            = 2;
uint64_t EXCEPTION_TIMER              = 3;
uint64_t EXCEPTION_INVALIDADDRESS     = 4;
uint64_t EXCEPTION_DIVISIONBYZERO     = 5;
uint64_t EXCEPTION_UNKNOWNINSTRUCTION = 6;
uint64_t EXCEPTION_MAXTRACE           = 7;

uint64_t* EXCEPTIONS; // strings representing exceptions

uint64_t debug_exception = 0;

// enables recording, disassembling, debugging, and symbolically executing code
uint64_t debug = 0;

uint64_t execute     = 0; // flag for executing code
uint64_t record      = 0; // flag for recording code execution
uint64_t undo        = 0; // flag for undoing code execution
uint64_t redo        = 0; // flag for redoing code execution
uint64_t disassemble = 0; // flag for disassembling code
uint64_t symbolic    = 0; // flag for symbolically executing code
uint64_t backtrack   = 0; // flag for backtracking symbolic execution

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

uint64_t  calls             = 0;             // total number of executed procedure calls
uint64_t* callsPerProcedure = (uint64_t*) 0; // number of executed calls of each procedure

uint64_t  iterations        = 0;             // total number of executed loop iterations
uint64_t* iterationsPerLoop = (uint64_t*) 0; // number of executed iterations of each loop

uint64_t* loadsPerInstruction  = (uint64_t*) 0; // number of executed loads per load instruction
uint64_t* storesPerInstruction = (uint64_t*) 0; // number of executed stores per store instruction

// ------------------------- INITIALIZATION ------------------------

void initInterpreter() {
  EXCEPTIONS = smalloc((EXCEPTION_MAXTRACE + 1) * SIZEOFUINT64STAR);

  *(EXCEPTIONS + EXCEPTION_NOEXCEPTION)        = (uint64_t) "no exception";
  *(EXCEPTIONS + EXCEPTION_PAGEFAULT)          = (uint64_t) "page fault";
  *(EXCEPTIONS + EXCEPTION_SYSCALL)            = (uint64_t) "syscall";
  *(EXCEPTIONS + EXCEPTION_TIMER)              = (uint64_t) "timer interrupt";
  *(EXCEPTIONS + EXCEPTION_INVALIDADDRESS)     = (uint64_t) "invalid address";
  *(EXCEPTIONS + EXCEPTION_DIVISIONBYZERO)     = (uint64_t) "division by zero";
  *(EXCEPTIONS + EXCEPTION_UNKNOWNINSTRUCTION) = (uint64_t) "unknown instruction";
  *(EXCEPTIONS + EXCEPTION_MAXTRACE)           = (uint64_t) "trace length exceeded";
}

void resetInterpreter() {
  pc = 0;
  ir = 0;

  registers = (uint64_t*) 0;

  pt = (uint64_t*) 0;

  trap = 0;

  timer = TIMEROFF;

  if (execute) {
    resetInstructionCounters();

    calls             = 0;
    callsPerProcedure = zalloc(maxBinaryLength / INSTRUCTIONSIZE * SIZEOFUINT64);

    iterations        = 0;
    iterationsPerLoop = zalloc(maxBinaryLength / INSTRUCTIONSIZE * SIZEOFUINT64);

    loadsPerInstruction  = zalloc(maxBinaryLength / INSTRUCTIONSIZE * SIZEOFUINT64);
    storesPerInstruction = zalloc(maxBinaryLength / INSTRUCTIONSIZE * SIZEOFUINT64);
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
// |  4 | pt             | pointer to page table
// |  5 | loPage         | lowest low unmapped page
// |  6 | mePage         | highest low unmapped page
// |  7 | hiPage         | highest high unmapped page
// |  8 | original break | original end of data segment
// |  9 | program break  | end of data segment
// | 10 | exception      | exception ID
// | 11 | faultingPage   | faulting page
// | 12 | exitCode       | exit code
// | 13 | parent         | context that created this context
// | 14 | virtualContext | virtual context address
// | 15 | name           | binary name loaded into context
// +----+----------------+

uint64_t nextContext(uint64_t* context)    { return (uint64_t) context; }
uint64_t prevContext(uint64_t* context)    { return (uint64_t) (context + 1); }
uint64_t PC(uint64_t* context)             { return (uint64_t) (context + 2); }
uint64_t Regs(uint64_t* context)           { return (uint64_t) (context + 3); }
uint64_t PT(uint64_t* context)             { return (uint64_t) (context + 4); }
uint64_t LoPage(uint64_t* context)         { return (uint64_t) (context + 5); }
uint64_t MePage(uint64_t* context)         { return (uint64_t) (context + 6); }
uint64_t HiPage(uint64_t* context)         { return (uint64_t) (context + 7); }
uint64_t OriginalBreak(uint64_t* context)  { return (uint64_t) (context + 8); }
uint64_t ProgramBreak(uint64_t* context)   { return (uint64_t) (context + 9); }
uint64_t Exception(uint64_t* context)      { return (uint64_t) (context + 10); }
uint64_t FaultingPage(uint64_t* context)   { return (uint64_t) (context + 11); }
uint64_t ExitCode(uint64_t* context)       { return (uint64_t) (context + 12); }
uint64_t Parent(uint64_t* context)         { return (uint64_t) (context + 13); }
uint64_t VirtualContext(uint64_t* context) { return (uint64_t) (context + 14); }
uint64_t Name(uint64_t* context)           { return (uint64_t) (context + 15); }

uint64_t* getNextContext(uint64_t* context)    { return (uint64_t*) *context; }
uint64_t* getPrevContext(uint64_t* context)    { return (uint64_t*) *(context + 1); }
uint64_t  getPC(uint64_t* context)             { return             *(context + 2); }
uint64_t* getRegs(uint64_t* context)           { return (uint64_t*) *(context + 3); }
uint64_t* getPT(uint64_t* context)             { return (uint64_t*) *(context + 4); }
uint64_t  getLoPage(uint64_t* context)         { return             *(context + 5); }
uint64_t  getMePage(uint64_t* context)         { return             *(context + 6); }
uint64_t  getHiPage(uint64_t* context)         { return             *(context + 7); }
uint64_t  getOriginalBreak(uint64_t* context)  { return             *(context + 8); }
uint64_t  getProgramBreak(uint64_t* context)   { return             *(context + 9); }
uint64_t  getException(uint64_t* context)      { return             *(context + 10); }
uint64_t  getFaultingPage(uint64_t* context)   { return             *(context + 11); }
uint64_t  getExitCode(uint64_t* context)       { return             *(context + 12); }
uint64_t* getParent(uint64_t* context)         { return (uint64_t*) *(context + 13); }
uint64_t* getVirtualContext(uint64_t* context) { return (uint64_t*) *(context + 14); }
uint64_t* getName(uint64_t* context)           { return (uint64_t*) *(context + 15); }

void setNextContext(uint64_t* context, uint64_t* next)     { *context        = (uint64_t) next; }
void setPrevContext(uint64_t* context, uint64_t* prev)     { *(context + 1)  = (uint64_t) prev; }
void setPC(uint64_t* context, uint64_t pc)                 { *(context + 2)  = pc; }
void setRegs(uint64_t* context, uint64_t* regs)            { *(context + 3)  = (uint64_t) regs; }
void setPT(uint64_t* context, uint64_t* pt)                { *(context + 4)  = (uint64_t) pt; }
void setLoPage(uint64_t* context, uint64_t loPage)         { *(context + 5)  = loPage; }
void setMePage(uint64_t* context, uint64_t mePage)         { *(context + 6)  = mePage; }
void setHiPage(uint64_t* context, uint64_t hiPage)         { *(context + 7)  = hiPage; }
void setOriginalBreak(uint64_t* context, uint64_t brk)     { *(context + 8)  = brk; }
void setProgramBreak(uint64_t* context, uint64_t brk)      { *(context + 9)  = brk; }
void setException(uint64_t* context, uint64_t exception)   { *(context + 10) = exception; }
void setFaultingPage(uint64_t* context, uint64_t page)     { *(context + 11) = page; }
void setExitCode(uint64_t* context, uint64_t code)         { *(context + 12) = code; }
void setParent(uint64_t* context, uint64_t* parent)        { *(context + 13) = (uint64_t) parent; }
void setVirtualContext(uint64_t* context, uint64_t* vctxt) { *(context + 14) = (uint64_t) vctxt; }
void setName(uint64_t* context, uint64_t* name)            { *(context + 15) = (uint64_t) name; }

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

uint64_t pavailable();
uint64_t pused();

uint64_t* palloc();
void      pfree(uint64_t* frame);

void mapAndStore(uint64_t* context, uint64_t vaddr, uint64_t data);

void up_loadBinary(uint64_t* context);

uint64_t up_loadString(uint64_t* context, uint64_t* s, uint64_t SP);
void     up_loadArguments(uint64_t* context, uint64_t argc, uint64_t* argv);

uint64_t handleSystemCall(uint64_t* context);
uint64_t handlePageFault(uint64_t* context);
uint64_t handleDivisionByZero(uint64_t* context);
uint64_t handleMaxTrace(uint64_t* context);
uint64_t handleTimer(uint64_t* context);

uint64_t handleException(uint64_t* context);

uint64_t mipster(uint64_t* toContext);
uint64_t hypster(uint64_t* toContext);

uint64_t mixter(uint64_t* toContext, uint64_t mix);

uint64_t minmob(uint64_t* toContext);
void     mapUnmappedPages(uint64_t* context);
uint64_t minster(uint64_t* toContext);
uint64_t mobster(uint64_t* toContext);

void     backtrackTrace(uint64_t* context);
uint64_t monster(uint64_t* toContext);

uint64_t isBootLevelZero();

uint64_t selfie_run(uint64_t machine);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t* MY_CONTEXT = (uint64_t*) 0;

uint64_t DONOTEXIT = 0;
uint64_t EXIT = 1;

uint64_t EXITCODE_NOERROR = 0;
uint64_t EXITCODE_BADARGUMENTS = 1;
uint64_t EXITCODE_IOERROR = 2;
uint64_t EXITCODE_SCANNERERROR = 3;
uint64_t EXITCODE_PARSERERROR = 4;
uint64_t EXITCODE_COMPILERERROR = 5;
uint64_t EXITCODE_OUTOFVIRTUALMEMORY = 6;
uint64_t EXITCODE_OUTOFPHYSICALMEMORY = 7;
uint64_t EXITCODE_DIVISIONBYZERO = 8;
uint64_t EXITCODE_UNKNOWNINSTRUCTION = 9;
uint64_t EXITCODE_UNKNOWNSYSCALL = 10;
uint64_t EXITCODE_MULTIPLEEXCEPTIONERROR = 11;
uint64_t EXITCODE_SYMBOLICEXECUTIONERROR = 12;
uint64_t EXITCODE_OUTOFTRACEMEMORY = 13;
uint64_t EXITCODE_UNCAUGHTEXCEPTION = 14;

uint64_t SYSCALL_BITWIDTH = 32; // integer bit width for system calls

uint64_t MIPSTER = 1;
uint64_t DIPSTER = 2;
uint64_t RIPSTER = 3;

uint64_t MONSTER = 4;

uint64_t MINSTER = 5;
uint64_t MOBSTER = 6;

uint64_t HYPSTER = 7;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t nextPageFrame = 0;

uint64_t usedPageFrameMemory = 0;
uint64_t freePageFrameMemory = 0;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------   T H E O R E M  P R O V E R    ----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// -------------------------- SAT Solver ---------------------------
// -----------------------------------------------------------------

uint64_t clauseMayBeTrue(uint64_t* clauseAddress, uint64_t depth);
uint64_t instanceMayBeTrue(uint64_t depth);

uint64_t babysat(uint64_t depth);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t FALSE = 0;
uint64_t TRUE  = 1;

uint64_t UNSAT = 0;
uint64_t SAT   = 1;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* dimacsName = (uint64_t*) 0;

uint64_t numberOfSATVariables = 0;

// numberOfSATVariables
uint64_t* SATAssignment = (uint64_t*) 0;

uint64_t numberOfSATClauses = 0;

// numberOfSATClauses * 2 * numberOfSATVariables
uint64_t* SATInstance = (uint64_t*) 0;

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

uint64_t tenToThePowerOf(uint64_t p) {
  // use recursion for simplicity and educational value
  // for p close to 0 performance is not relevant
  if (p == 0)
    return 1;
  else
    return tenToThePowerOf(p - 1) * 10;
}

uint64_t leftShift(uint64_t n, uint64_t b) {
  // assert: 0 <= b < CPUBITWIDTH
  return n * twoToThePowerOf(b);
}

uint64_t rightShift(uint64_t n, uint64_t b) {
  // assert: 0 <= b < CPUBITWIDTH
  return n / twoToThePowerOf(b);
}

uint64_t getBits(uint64_t n, uint64_t i, uint64_t b) {
  // assert: 0 < b <= i + b < CPUBITWIDTH
  if (i == 0)
    return n % twoToThePowerOf(b);
  else
    // shift to-be-loaded bits all the way to the left
    // to reset all bits to the left of them, then
    // shift to-be-loaded bits all the way to the right and return
    return rightShift(leftShift(n, CPUBITWIDTH - (i + b)), CPUBITWIDTH - b);
}

uint64_t getLowWord(uint64_t n) {
  return getBits(n, 0, WORDSIZEINBITS);
}

uint64_t getHighWord(uint64_t n) {
  return getBits(n, WORDSIZEINBITS, WORDSIZEINBITS);
}

uint64_t abs(uint64_t n) {
  if (signedLessThan(n, 0))
    return -n;
  else
    return n;
}

uint64_t signedLessThan(uint64_t a, uint64_t b) {
  // INT64_MIN <= n <= INT64_MAX iff
  // INT64_MIN + INT64_MIN <= n + INT64_MIN <= INT64_MAX + INT64_MIN iff
  // -2^64 <= n + INT64_MIN <= 2^64 - 1 (sign-extended to 65 bits) iff
  // 0 <= n + INT64_MIN <= UINT64_MAX
  return a + INT64_MIN < b + INT64_MIN;
}

uint64_t signedDivision(uint64_t a, uint64_t b) {
  // assert: b != 0
  // assert: a == INT64_MIN -> b != -1
  if (a == INT64_MIN)
    if (b == INT64_MIN)
      return 1;
    else if (signedLessThan(b, 0))
      return INT64_MIN / abs(b);
    else
      return -(INT64_MIN / b);
  else if (b == INT64_MIN)
    return 0;
  else if (signedLessThan(a, 0))
    if (signedLessThan(b, 0))
      return abs(a) / abs(b);
    else
      return -(abs(a) / b);
  else if (signedLessThan(b, 0))
    return -(a / abs(b));
  else
    return a / b;
}

uint64_t isSignedInteger(uint64_t n, uint64_t b) {
  // assert: 0 < b <= CPUBITWIDTH
  if (n < twoToThePowerOf(b - 1))
    // assert: 0 <= n < 2^(b - 1)
    return 1;
  else if (n >= -twoToThePowerOf(b - 1))
    // assert: -2^(b - 1) <= n < 2^64
    return 1;
  else
    return 0;
}

uint64_t signExtend(uint64_t n, uint64_t b) {
  // assert: 0 <= n <= 2^b
  // assert: 0 < b < CPUBITWIDTH
  if (n < twoToThePowerOf(b - 1))
    return n;
  else
    return n - twoToThePowerOf(b);
}

uint64_t signShrink(uint64_t n, uint64_t b) {
  // assert: -2^(b - 1) <= n < 2^(b - 1)
  // assert: 0 < b < CPUBITWIDTH
  return getBits(n, 0, b);
}

uint64_t loadCharacter(uint64_t* s, uint64_t i) {
  // assert: i >= 0
  uint64_t a;

  // a is the index of the double word where
  // the to-be-loaded i-th character in s is
  a = i / SIZEOFUINT64;

  // return i-th 8-bit character in s
  return getBits(*(s + a), (i % SIZEOFUINT64) * 8, 8);
}

uint64_t* storeCharacter(uint64_t* s, uint64_t i, uint64_t c) {
  // assert: i >= 0, 0 <= c < 2^8 (all characters are 8-bit)
  uint64_t a;

  // a is the index of the double word where
  // the with c to-be-overwritten i-th character in s is
  a = i / SIZEOFUINT64;

  // subtract the to-be-overwritten character to reset its bits in s
  // then add c to set its bits at the i-th position in s
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

  // load character (one byte) at index i in s from memory requires
  // bit shifting since memory access can only be done in double words
  c = loadCharacter(s, i);

  // loop until s is terminated
  while (c != 0) {
    // the numerical value of ASCII-encoded decimal digits
    // is offset by the ASCII code of '0' (which is 48)
    c = c - '0';

    if (c > 9) {
      printf2((uint64_t*) "%s: cannot convert non-decimal number %s\n", selfieName, s);

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
        printf2((uint64_t*) "%s: cannot convert out-of-bound number %s\n", selfieName, s);

        exit(EXITCODE_BADARGUMENTS);
      }
    else {
      // s contains a decimal number larger than UINT64_MAX
      printf2((uint64_t*) "%s: cannot convert out-of-bound number %s\n", selfieName, s);

      exit(EXITCODE_BADARGUMENTS);
    }

    // go to the next digit
    i = i + 1;

    // load character (one byte) at index i in s from memory requires
    // bit shifting since memory access can only be done in double words
    c = loadCharacter(s, i);
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

uint64_t fixedPointRatio(uint64_t a, uint64_t b, uint64_t f) {
  // compute fixed point ratio with f fractional digits
  // multiply a/b with 10^f but avoid wrap around

  uint64_t p;

  p = f;

  while (p > 0) {
    if (a <= UINT64_MAX / tenToThePowerOf(p)) {
      if (b / tenToThePowerOf(f - p) != 0)
        return (a * tenToThePowerOf(p)) / (b / tenToThePowerOf(f - p));
    }

    p = p - 1;
  }

  return 0;
}

uint64_t fixedPointPercentage(uint64_t r, uint64_t f) {
  if (r != 0)
    // 10^4 (for 100.00%) * 10^f (for f fractional digits of r)
    return tenToThePowerOf(4 + f) / r;
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
      // to report the error we may thus still write to the console
      outputFD = 1;

      printf2((uint64_t*) "%s: could not write character to output file %s\n", selfieName, outputName);
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
  print(itoa(n, integer_buffer, 10, 0));
}

void unprintInteger(uint64_t n) {
  n = stringLength(itoa(n, integer_buffer, 10, 0));

  while (n > 0) {
    putCharacter(CHAR_BACKSPACE);

    n = n - 1;
  }
}

void printHexadecimal(uint64_t n, uint64_t a) {
  print(itoa(n, integer_buffer, 16, a));
}

void printOctal(uint64_t n, uint64_t a) {
  print(itoa(n, integer_buffer, 8, a));
}

void printBinary(uint64_t n, uint64_t a) {
  print(itoa(n, integer_buffer, 2, a));
}

uint64_t printFormat0(uint64_t* s, uint64_t i) {
  // print string s from index i on
  // ignore % formatting codes except for %%
  if (s == (uint64_t*) 0)
    return 0;
  else {
    while (loadCharacter(s, i) != 0) {
      if (loadCharacter(s, i) != '%') {
        putCharacter(loadCharacter(s, i));

        i = i + 1;
      } else if (loadCharacter(s, i + 1) == '%') {
        // for %% print just one %
        putCharacter('%');

        i = i + 2;
      } else {
        putCharacter(loadCharacter(s, i));

        i = i + 1;
      }
    }

    return i;
  }
}

uint64_t printFormat1(uint64_t* s, uint64_t i, uint64_t* a) {
  // print string s from index i on until next % formatting code except for %%
  // then print argument a according to the encountered % formatting code

  uint64_t p;

  if (s == (uint64_t*) 0)
    return 0;
  else {
    while (loadCharacter(s, i) != 0) {
      if (loadCharacter(s, i) != '%') {
        putCharacter(loadCharacter(s, i));

        i = i + 1;
      } else if (loadCharacter(s, i + 1) == 's') {
        print(a);

        return i + 2;
      } else if (loadCharacter(s, i + 1) == 'c') {
        putCharacter((uint64_t) a);

        return i + 2;
      } else if (loadCharacter(s, i + 1) == 'd') {
        printInteger((uint64_t) a);

        return i + 2;
      } else if (loadCharacter(s, i + 1) == '.') {
        // for simplicity we support a single digit only
        p = loadCharacter(s, i + 2) - '0';

        if (p < 10) {
          // the character at i + 2 is in fact a digit
          printInteger((uint64_t) a / tenToThePowerOf(p));
          if (p > 0) {
            putCharacter('.');
            printInteger((uint64_t) a % tenToThePowerOf(p));
          }

          return i + 4;
        } else {
          putCharacter(loadCharacter(s, i));

          i = i + 1;
        }
      } else if (loadCharacter(s, i + 1) == 'p') {
        printHexadecimal((uint64_t) a, SIZEOFUINT64STAR);

        return i + 2;
      } else if (loadCharacter(s, i + 1) == 'x') {
        printHexadecimal((uint64_t) a, 0);

        return i + 2;
      } else if (loadCharacter(s, i + 1) == 'o') {
        printOctal((uint64_t) a, 0);

        return i + 2;
      } else if (loadCharacter(s, i + 1) == 'b') {
        printBinary((uint64_t) a, 0);

        return i + 2;
      } else if (loadCharacter(s, i + 1) == '%') {
        // for %% print just one %
        putCharacter('%');

        i = i + 2;
      } else {
        putCharacter(loadCharacter(s, i));

        i = i + 1;
      }
    }

    return i;
  }
}

void printf1(uint64_t* s, uint64_t* a1) {
  printFormat0(s, printFormat1(s, 0, a1));
}

void printf2(uint64_t* s, uint64_t* a1, uint64_t* a2) {
  printFormat0(s, printFormat1(s, printFormat1(s, 0, a1), a2));
}

void printf3(uint64_t* s, uint64_t* a1, uint64_t* a2, uint64_t* a3) {
  printFormat0(s, printFormat1(s, printFormat1(s, printFormat1(s, 0, a1), a2), a3));
}

void printf4(uint64_t* s, uint64_t* a1, uint64_t* a2, uint64_t* a3, uint64_t* a4) {
  printFormat0(s, printFormat1(s, printFormat1(s, printFormat1(s, printFormat1(s, 0, a1), a2), a3), a4));
}

void printf5(uint64_t* s, uint64_t* a1, uint64_t* a2, uint64_t* a3, uint64_t* a4, uint64_t* a5) {
  printFormat0(s, printFormat1(s, printFormat1(s, printFormat1(s, printFormat1(s, printFormat1(s, 0, a1), a2), a3), a4), a5));
}

void printf6(uint64_t* s, uint64_t* a1, uint64_t* a2, uint64_t* a3, uint64_t* a4, uint64_t* a5, uint64_t* a6) {
  printFormat0(s, printFormat1(s, printFormat1(s, printFormat1(s, printFormat1(s, printFormat1(s, printFormat1(s, 0, a1), a2), a3), a4), a5), a6));
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
    printf1((uint64_t*) "%s: malloc out of memory\n", selfieName);

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

  size = roundUp(size, REGISTERSIZE);

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

void printSymbol(uint64_t symbol) {
  putCharacter(CHAR_DOUBLEQUOTE);

  if (symbol == SYM_EOF)
    print((uint64_t*) "end of file");
  else
    print((uint64_t*) *(SYMBOLS + symbol));

  putCharacter(CHAR_DOUBLEQUOTE);
}

void printLineNumber(uint64_t* message, uint64_t line) {
  printf4((uint64_t*) "%s: %s in %s in line %d: ", selfieName, message, sourceName, (uint64_t*) line);
}

void syntaxErrorMessage(uint64_t* message) {
  printLineNumber((uint64_t*) "syntax error", lineNumber);
  printf1((uint64_t*) "%s\n", message);
}

void syntaxErrorCharacter(uint64_t expected) {
  printLineNumber((uint64_t*) "syntax error", lineNumber);
  printCharacter(expected);
  print((uint64_t*) " expected but ");
  printCharacter(character);
  print((uint64_t*) " found\n");
}

void syntaxErrorIdentifier(uint64_t* expected) {
  printLineNumber((uint64_t*) "syntax error", lineNumber);
  printString(expected);
  print((uint64_t*) " expected but ");
  printString(identifier);
  print((uint64_t*) " found\n");
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

    // keep track of line numbers for error reporting and code annotation
    if (character == CHAR_LF)
      // only linefeeds count, not carriage returns
      lineNumber = lineNumber + 1;
  } else if (numberOfReadBytes == 0)
    // reached end of file
    character = CHAR_EOF;
  else {
    printf2((uint64_t*) "%s: could not read character from input file %s\n", selfieName, sourceName);

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
  uint64_t inSingleLineComment;
  uint64_t inMultiLineComment;

  // assuming we are not in a comment
  inSingleLineComment = 0;
  inMultiLineComment  = 0;

  // read and discard all whitespace and comments until a character is found
  // that is not whitespace and does not occur in a comment, or the file ends
  while (1) {
    if (inSingleLineComment) {
      getCharacter();

      if (isCharacterNewLine())
        // single-line comments end with new line
        inSingleLineComment = 0;
      else if (character == CHAR_EOF)
        return character;
      else
        // count the characters in comments as ignored characters
        numberOfIgnoredCharacters = numberOfIgnoredCharacters + 1;

    } else if (inMultiLineComment) {
      getCharacter();

      if (character == CHAR_ASTERISK) {
        getCharacter();

        if (character == CHAR_SLASH) {
          // multi-line comments end with "*/"
          inMultiLineComment = 0;

          getCharacter();
        }
      }

      if (character == CHAR_EOF) {
        if (inMultiLineComment) {
          // multi-line comment is not terminated
          syntaxErrorMessage((uint64_t*) "runaway multi-line comment");

      	  exit(EXITCODE_SCANNERERROR);
        } else
          // this is redundant but easier to understand
          return character;
      } else if (inMultiLineComment)
        // count the characters in comments as ignored characters
        numberOfIgnoredCharacters = numberOfIgnoredCharacters + 1;
      else
        // count '*/' as ignored characters
        numberOfIgnoredCharacters = numberOfIgnoredCharacters + 2;

    } else if (isCharacterWhitespace()) {
      getCharacter();

      // also count line feed and carriage return as ignored characters
      numberOfIgnoredCharacters = numberOfIgnoredCharacters + 1;

    } else if (character == CHAR_SLASH) {
      getCharacter();

      if (character == CHAR_SLASH) {
        // "//" begins a comment
        inSingleLineComment = 1;

        // count both slashes as ignored characters
        numberOfIgnoredCharacters = numberOfIgnoredCharacters + 2;

        numberOfComments = numberOfComments + 1;
      } else if (character == CHAR_ASTERISK) {
        // "/*" begins a multi-line comment
        inMultiLineComment = 1;

        // count both slash and asterisk as ignored characters
        numberOfIgnoredCharacters = numberOfIgnoredCharacters + 2;

        numberOfComments = numberOfComments + 1;
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
            if (integerIsSigned)
              syntaxErrorMessage((uint64_t*) "signed integer out of bound");
            else
              syntaxErrorMessage((uint64_t*) "integer out of bound");

            exit(EXITCODE_SCANNERERROR);
          }

          storeCharacter(integer, i, character);

          i = i + 1;

          getCharacter();
        }

        storeCharacter(integer, i, 0); // null-terminated string

        literal = atoi(integer);

        if (integerIsSigned)
          if (literal > INT64_MIN) {
              syntaxErrorMessage((uint64_t*) "signed integer out of bound");

              exit(EXITCODE_SCANNERERROR);
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

        // accommodate string and null for termination,
        // allocate zeroed memory since strings are emitted
        // in double words but may end non-word-aligned
        string = zalloc(maxStringLength + 1);

        i = 0;

        while (isCharacterNotDoubleQuoteOrNewLineOrEOF()) {
          if (i >= maxStringLength) {
            syntaxErrorMessage((uint64_t*) "string too long");

            exit(EXITCODE_SCANNERERROR);
          }

          if (character == CHAR_BACKSLASH)
            handleEscapeSequence();

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
        printLineNumber((uint64_t*) "syntax error", lineNumber);
        print((uint64_t*) "found unknown character ");
        printCharacter(character);
        println();

        exit(EXITCODE_SCANNERERROR);
      }
    }

    numberOfScannedSymbols = numberOfScannedSymbols + 1;
  }
}

void handleEscapeSequence() {
  // ignoring the backslash
  numberOfIgnoredCharacters = numberOfIgnoredCharacters + 1;

  getCharacter();

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
    syntaxErrorMessage((uint64_t*) "unknown escape sequence found");

    exit(EXITCODE_SCANNERERROR);
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

      printLineNumber((uint64_t*) "syntax error", getLineNumber(entry));
      printf1((uint64_t*) "procedure %s undefined\n", getString(entry));
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
  // we use registers REG_T0-REG_T6 for temporaries
  if (allocatedTemporaries < NUMBEROFTEMPORARIES)
    allocatedTemporaries = allocatedTemporaries + 1;
  else {
    syntaxErrorMessage((uint64_t*) "out of registers");

    exit(EXITCODE_COMPILERERROR);
  }
}

uint64_t currentTemporary() {
  if (allocatedTemporaries > 0)
    if (allocatedTemporaries < 4)
      return REG_TP + allocatedTemporaries;
    else
      return REG_S11 + allocatedTemporaries - 3;
  else {
    syntaxErrorMessage((uint64_t*) "illegal register access");

    exit(EXITCODE_COMPILERERROR);
  }
}

uint64_t previousTemporary() {
  if (allocatedTemporaries > 1)
    if (allocatedTemporaries == 4)
      return REG_T2;
    else
      return currentTemporary() - 1;
  else {
    syntaxErrorMessage((uint64_t*) "illegal register access");

    exit(EXITCODE_COMPILERERROR);
  }
}

uint64_t nextTemporary() {
  if (allocatedTemporaries < NUMBEROFTEMPORARIES)
    if (allocatedTemporaries == 3)
      return REG_T3;
    else
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
    emitADDI(REG_SP, REG_SP, -REGISTERSIZE);
    emitSD(REG_SP, 0, currentTemporary());

    tfree(1);
  }
}

void restore_temporaries(uint64_t numberOfTemporaries) {
  while (allocatedTemporaries < numberOfTemporaries) {
    talloc();

    // restore temporary from stack
    emitLD(currentTemporary(), REG_SP, 0);
    emitADDI(REG_SP, REG_SP, REGISTERSIZE);
  }
}

void syntaxErrorSymbol(uint64_t expected) {
  printLineNumber((uint64_t*) "syntax error", lineNumber);
  printSymbol(expected);
  print((uint64_t*) " expected but ");
  printSymbol(symbol);
  print((uint64_t*) " found\n");
}

void syntaxErrorUnexpected() {
  printLineNumber((uint64_t*) "syntax error", lineNumber);
  print((uint64_t*) "unexpected symbol ");
  printSymbol(symbol);
  print((uint64_t*) " found\n");
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
  print((uint64_t*) " found\n");
}

uint64_t* getVariableOrBigInt(uint64_t* variableOrBigInt, uint64_t class) {
  uint64_t* entry;

  if (class == BIGINT)
    return searchSymbolTable(global_symbol_table, variableOrBigInt, class);
  else {
    entry = getScopedSymbolTableEntry(variableOrBigInt, class);

    if (entry == (uint64_t*) 0) {
      printLineNumber((uint64_t*) "syntax error", lineNumber);
      printf1((uint64_t*) "%s undeclared\n", variableOrBigInt);

      exit(EXITCODE_PARSERERROR);
    }

    return entry;
  }
}

void load_upperBaseAddress(uint64_t* entry) {
  uint64_t lower;
  uint64_t upper;

  // assert: n = allocatedTemporaries

  lower = getBits(getAddress(entry),  0, 12);
  upper = getBits(getAddress(entry), 12, 20);

  if (lower >= twoToThePowerOf(11))
    // add 1 which is effectively 2^12 to cancel sign extension of lower
    upper = upper + 1;

  talloc();

  // calculate upper part of base address relative to global or frame pointer
  emitLUI(currentTemporary(), signExtend(upper, 20));
  emitADD(currentTemporary(), getScope(entry), currentTemporary());

  // assert: allocatedTemporaries == n + 1
}

uint64_t load_variableOrBigInt(uint64_t* variableOrBigInt, uint64_t class) {
  uint64_t* entry;
  uint64_t offset;

  // assert: n = allocatedTemporaries

  entry = getVariableOrBigInt(variableOrBigInt, class);

  offset = getAddress(entry);

  if (isSignedInteger(offset, 12)) {
    talloc();

    emitLD(currentTemporary(), getScope(entry), offset);
  } else {
    load_upperBaseAddress(entry);

    emitLD(currentTemporary(), currentTemporary(), signExtend(getBits(offset, 0, 12), 12));
  }

  // assert: allocatedTemporaries == n + 1

  return getType(entry);
}

void load_integer(uint64_t value) {
  uint64_t lower;
  uint64_t upper;
  uint64_t* entry;

  // assert: n = allocatedTemporaries

  if (isSignedInteger(value, 12)) {
    // integers greater than or equal to -2^11 and less than 2^11
    // are loaded with one addi into a register

    talloc();

    emitADDI(currentTemporary(), REG_ZR, value);

  } else if (isSignedInteger(value, 32)) {
    // integers greater than or equal to -2^31 and less than 2^31
    // are loaded with one addi and one lui into a register

    lower = getBits(value,  0, 12);
    upper = getBits(value, 12, 20);

    talloc();

    if (lower >= twoToThePowerOf(11)) {
      // add 1 which is effectively 2^12 to cancel sign extension of lower
      upper = upper + 1;

      // assert: 0 < upper <= 2^(32-12)
      emitLUI(currentTemporary(), signExtend(upper, 20));

      if (upper == twoToThePowerOf(19))
        // upper overflowed, cancel sign extension
        emitSUB(currentTemporary(), REG_ZR, currentTemporary());
    } else
      // assert: 0 < upper < 2^(32-12)
      emitLUI(currentTemporary(), signExtend(upper, 20));

    emitADDI(currentTemporary(), currentTemporary(), signExtend(lower, 12));

  } else {
    // integers less than -2^31 or greater than or equal to 2^31 are stored in data segment
    entry = searchSymbolTable(global_symbol_table, integer, BIGINT);

    if (entry == (uint64_t*) 0) {
      allocatedMemory = allocatedMemory + REGISTERSIZE;

      createSymbolTableEntry(GLOBAL_TABLE, integer, lineNumber, BIGINT, UINT64_T, value, -allocatedMemory);
    }

    load_variableOrBigInt(integer, BIGINT);
  }

  // assert: allocatedTemporaries == n + 1
}

void load_string(uint64_t* string) {
  uint64_t length;

  // assert: n = allocatedTemporaries

  length = stringLength(string) + 1;

  allocatedMemory = allocatedMemory + roundUp(length, REGISTERSIZE);

  createSymbolTableEntry(GLOBAL_TABLE, string, lineNumber, STRING, UINT64STAR_T, 0, -allocatedMemory);

  load_integer(-allocatedMemory);

  emitADD(currentTemporary(), REG_GP, currentTemporary());

  // assert: allocatedTemporaries == n + 1
}

uint64_t help_call_codegen(uint64_t* entry, uint64_t* procedure) {
  uint64_t type;

  if (entry == (uint64_t*) 0) {
    // procedure never called nor declared nor defined

    // default return type is "int"
    type = UINT64_T;

    createSymbolTableEntry(GLOBAL_TABLE, procedure, lineNumber, PROCEDURE, type, 0, binaryLength);

    emitJAL(REG_RA, 0);

  } else {
    type = getType(entry);

    if (getAddress(entry) == 0) {
      // procedure declared but never called nor defined
      setAddress(entry, binaryLength);

      emitJAL(REG_RA, 0);
    } else if (getOpcode(loadInstruction(getAddress(entry))) == OP_JAL) {
      // procedure called and possibly declared but not defined

      // create fixup chain using absolute address
      emitJAL(REG_RA, getAddress(entry));
      setAddress(entry, binaryLength - INSTRUCTIONSIZE);
    } else
      // procedure defined, use relative address
      emitJAL(REG_RA, getAddress(entry) - binaryLength);
  }

  return type;
}

void help_procedure_prologue(uint64_t numberOfLocalVariableBytes) {
  // allocate memory for return address
  emitADDI(REG_SP, REG_SP, -REGISTERSIZE);

  // save return address
  emitSD(REG_SP, 0, REG_RA);

  // allocate memory for caller's frame pointer
  emitADDI(REG_SP, REG_SP, -REGISTERSIZE);

  // save caller's frame pointer
  emitSD(REG_SP, 0, REG_FP);

  // set callee's frame pointer
  emitADDI(REG_FP, REG_SP, 0);

  // allocate memory for callee's local variables
  if (numberOfLocalVariableBytes > 0) {
    if (isSignedInteger(-numberOfLocalVariableBytes, 12))
      emitADDI(REG_SP, REG_SP, -numberOfLocalVariableBytes);
    else {
      load_integer(-numberOfLocalVariableBytes);

      emitADD(REG_SP, REG_SP, currentTemporary());

      tfree(1);
    }
  }
}

void help_procedure_epilogue(uint64_t numberOfParameterBytes) {
  // deallocate memory for callee's frame pointer and local variables
  emitADDI(REG_SP, REG_FP, 0);

  // restore caller's frame pointer
  emitLD(REG_FP, REG_SP, 0);

  // deallocate memory for caller's frame pointer
  emitADDI(REG_SP, REG_SP, REGISTERSIZE);

  // restore return address
  emitLD(REG_RA, REG_SP, 0);

  // deallocate memory for return address and parameters
  emitADDI(REG_SP, REG_SP, REGISTERSIZE + numberOfParameterBytes);

  // return
  emitJALR(REG_ZR, REG_RA, 0);
}

uint64_t compile_call(uint64_t* procedure) {
  uint64_t* entry;
  uint64_t numberOfTemporaries;
  uint64_t type;

  // assert: n = allocatedTemporaries

  entry = getScopedSymbolTableEntry(procedure, PROCEDURE);

  numberOfTemporaries = allocatedTemporaries;

  save_temporaries();

  // assert: allocatedTemporaries == 0

  if (isExpression()) {
    compile_expression();

    // TODO: check if types/number of parameters is correct

    // push first parameter onto stack
    emitADDI(REG_SP, REG_SP, -REGISTERSIZE);
    emitSD(REG_SP, 0, currentTemporary());

    tfree(1);

    while (symbol == SYM_COMMA) {
      getSymbol();

      compile_expression();

      // push more parameters onto stack
      emitADDI(REG_SP, REG_SP, -REGISTERSIZE);
      emitSD(REG_SP, 0, currentTemporary());

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

uint64_t compile_factor() {
  uint64_t hasCast;
  uint64_t cast;
  uint64_t type;
  uint64_t negative;
  uint64_t dereference;
  uint64_t* variableOrProcedureName;

  // assert: n = allocatedTemporaries

  while (lookForFactor()) {
    syntaxErrorUnexpected();

    if (symbol == SYM_EOF)
      exit(EXITCODE_PARSERERROR);
    else
      getSymbol();
  }

  // optional: [ cast ]
  if (symbol == SYM_LPARENTHESIS) {
    getSymbol();

    // cast: "(" "uint64_t" [ "*" ] ")"
    if (symbol == SYM_UINT64) {
      hasCast = 1;

      cast = compile_type();

      if (symbol == SYM_RPARENTHESIS)
        getSymbol();
      else
        syntaxErrorSymbol(SYM_RPARENTHESIS);

    // not a cast: "(" expression ")"
    } else {
      type = compile_expression();

      if (symbol == SYM_RPARENTHESIS)
        getSymbol();
      else
        syntaxErrorSymbol(SYM_RPARENTHESIS);

      // assert: allocatedTemporaries == n + 1

      return type;
    }
  } else
    hasCast = 0;

  // optional: -
  if (symbol == SYM_MINUS) {
    negative = 1;

    integerIsSigned = 1;

    getSymbol();

    integerIsSigned = 0;
  } else
    negative = 0;

  // optional: dereference
  if (symbol == SYM_ASTERISK) {
    dereference = 1;

    getSymbol();
  } else
    dereference = 0;

  // identifier or call?
  if (symbol == SYM_IDENTIFIER) {
    variableOrProcedureName = identifier;

    getSymbol();

    if (symbol == SYM_LPARENTHESIS) {
      getSymbol();

      // procedure call: identifier "(" ... ")"
      type = compile_call(variableOrProcedureName);

      talloc();

      // retrieve return value
      emitADDI(currentTemporary(), REG_A0, 0);

      // reset return register to initial return value
      // for missing return expressions
      emitADDI(REG_A0, REG_ZR, 0);
    } else
      // variable access: identifier
      type = load_variableOrBigInt(variableOrProcedureName, VARIABLE);

  // integer?
  } else if (symbol == SYM_INTEGER) {
    load_integer(literal);

    getSymbol();

    type = UINT64_T;

  // character?
  } else if (symbol == SYM_CHARACTER) {
    talloc();

    emitADDI(currentTemporary(), REG_ZR, literal);

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

    type = compile_expression();

    if (symbol == SYM_RPARENTHESIS)
      getSymbol();
    else
      syntaxErrorSymbol(SYM_RPARENTHESIS);
  } else {
    syntaxErrorUnexpected();

    type = UINT64_T;
  }

  if (dereference) {
    if (type != UINT64STAR_T)
      typeWarning(UINT64STAR_T, type);

    // dereference
    emitLD(currentTemporary(), currentTemporary(), 0);

    type = UINT64_T;
  }

  if (negative) {
    if (type != UINT64_T) {
      typeWarning(UINT64_T, type);

      type = UINT64_T;
    }

    emitSUB(currentTemporary(), REG_ZR, currentTemporary());
  }

  // assert: allocatedTemporaries == n + 1

  if (hasCast)
    return cast;
  else
    return type;
}

uint64_t compile_term() {
  uint64_t ltype;
  uint64_t operatorSymbol;
  uint64_t rtype;

  // assert: n = allocatedTemporaries

  ltype = compile_factor();

  // assert: allocatedTemporaries == n + 1

  // * / or % ?
  while (isStarOrDivOrModulo()) {
    operatorSymbol = symbol;

    getSymbol();

    rtype = compile_factor();

    // assert: allocatedTemporaries == n + 2

    if (ltype != rtype)
      typeWarning(ltype, rtype);

    if (operatorSymbol == SYM_ASTERISK)
      emitMUL(previousTemporary(), previousTemporary(), currentTemporary());
    else if (operatorSymbol == SYM_DIV)
      emitDIVU(previousTemporary(), previousTemporary(), currentTemporary());
    else if (operatorSymbol == SYM_MOD)
      emitREMU(previousTemporary(), previousTemporary(), currentTemporary());

    tfree(1);
  }

  // assert: allocatedTemporaries == n + 1

  return ltype;
}

uint64_t compile_simpleExpression() {
  uint64_t ltype;
  uint64_t operatorSymbol;
  uint64_t rtype;

  // assert: n = allocatedTemporaries

  ltype = compile_term();

  // assert: allocatedTemporaries == n + 1

  // + or - ?
  while (isPlusOrMinus()) {
    operatorSymbol = symbol;

    getSymbol();

    rtype = compile_term();

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

      emitADD(previousTemporary(), previousTemporary(), currentTemporary());

    } else if (operatorSymbol == SYM_MINUS) {
      if (ltype == UINT64STAR_T) {
        if (rtype == UINT64_T) {
          // UINT64STAR_T - UINT64_T
          // pointer arithmetic: factor of 2^3 of integer operand
          emitLeftShiftBy(currentTemporary(), 3);
          emitSUB(previousTemporary(), previousTemporary(), currentTemporary());
        } else {
          // UINT64STAR_T - UINT64STAR_T
          // pointer arithmetic: (left_term - right_term) / SIZEOFUINT64
          emitSUB(previousTemporary(), previousTemporary(), currentTemporary());
          emitADDI(currentTemporary(), REG_ZR, SIZEOFUINT64);
          emitDIVU(previousTemporary(), previousTemporary(), currentTemporary());

          ltype = UINT64_T;
        }
      } else if (rtype == UINT64STAR_T)
        // UINT64_T - UINT64STAR_T
        syntaxErrorMessage((uint64_t*) "(uint64_t) - (uint64_t*) is undefined");
      else
        // UINT64_T - UINT64_T
        emitSUB(previousTemporary(), previousTemporary(), currentTemporary());
    }

    tfree(1);
  }

  // assert: allocatedTemporaries == n + 1

  return ltype;
}

uint64_t compile_expression() {
  uint64_t ltype;
  uint64_t operatorSymbol;
  uint64_t rtype;

  // assert: n = allocatedTemporaries

  ltype = compile_simpleExpression();

  // assert: allocatedTemporaries == n + 1

  //optional: ==, !=, <, >, <=, >= simpleExpression
  if (isComparison()) {
    operatorSymbol = symbol;

    getSymbol();

    rtype = compile_simpleExpression();

    // assert: allocatedTemporaries == n + 2

    if (ltype != rtype)
      typeWarning(ltype, rtype);

    if (operatorSymbol == SYM_EQUALITY) {
      // a == b iff unsigned b - a < 1
      emitSUB(previousTemporary(), currentTemporary(), previousTemporary());
      emitADDI(currentTemporary(), REG_ZR, 1);
      emitSLTU(previousTemporary(), previousTemporary(), currentTemporary());

      tfree(1);

    } else if (operatorSymbol == SYM_NOTEQ) {
      // a != b iff unsigned 0 < b - a
      emitSUB(previousTemporary(), currentTemporary(), previousTemporary());

      tfree(1);

      emitSLTU(currentTemporary(), REG_ZR, currentTemporary());

    } else if (operatorSymbol == SYM_LT) {
      // a < b
      emitSLTU(previousTemporary(), previousTemporary(), currentTemporary());

      tfree(1);

    } else if (operatorSymbol == SYM_GT) {
      // a > b iff b < a
      emitSLTU(previousTemporary(), currentTemporary(), previousTemporary());

      tfree(1);

    } else if (operatorSymbol == SYM_LEQ) {
      // a <= b iff 1 - (b < a)
      emitSLTU(previousTemporary(), currentTemporary(), previousTemporary());
      emitADDI(currentTemporary(), REG_ZR, 1);
      emitSUB(previousTemporary(), currentTemporary(), previousTemporary());

      tfree(1);

    } else if (operatorSymbol == SYM_GEQ) {
      // a >= b iff 1 - (a < b)
      emitSLTU(previousTemporary(), previousTemporary(), currentTemporary());
      emitADDI(currentTemporary(), REG_ZR, 1);
      emitSUB(previousTemporary(), currentTemporary(), previousTemporary());

      tfree(1);
    }
  }

  // assert: allocatedTemporaries == n + 1

  return ltype;
}

void compile_while() {
  uint64_t jumpBackToWhile;
  uint64_t branchForwardToEnd;

  // assert: allocatedTemporaries == 0

  jumpBackToWhile = binaryLength;

  branchForwardToEnd = 0;

  // while ( expression )
  if (symbol == SYM_WHILE) {
    getSymbol();

    if (symbol == SYM_LPARENTHESIS) {
      getSymbol();

      compile_expression();

      // we do not know where to branch, fixup later
      branchForwardToEnd = binaryLength;

      emitBEQ(currentTemporary(), REG_ZR, 0);

      tfree(1);

      if (symbol == SYM_RPARENTHESIS) {
        getSymbol();

        // zero or more statements: { statement }
        if (symbol == SYM_LBRACE) {
          getSymbol();

          while (isNotRbraceOrEOF())
            compile_statement();

          if (symbol == SYM_RBRACE)
            getSymbol();
          else {
            syntaxErrorSymbol(SYM_RBRACE);

            exit(EXITCODE_PARSERERROR);
          }
        } else
          // only one statement without {}
          compile_statement();
      } else
        syntaxErrorSymbol(SYM_RPARENTHESIS);
    } else
      syntaxErrorSymbol(SYM_LPARENTHESIS);
  } else
    syntaxErrorSymbol(SYM_WHILE);

  // we use JAL for the unconditional jump back to the loop condition because:
  // 1. the RISC-V doc recommends to do so to not disturb branch prediction
  // 2. GCC also uses JAL for the unconditional back jump of a while loop
  emitJAL(REG_ZR, jumpBackToWhile - binaryLength);

  if (branchForwardToEnd != 0)
    // first instruction after loop body will be generated here
    // now we have the address for the conditional branch from above
    fixup_relative_BFormat(branchForwardToEnd);

  // assert: allocatedTemporaries == 0

  numberOfWhile = numberOfWhile + 1;
}

void compile_if() {
  uint64_t branchForwardToElseOrEnd;
  uint64_t jumpForwardToEnd;

  // assert: allocatedTemporaries == 0

  // if ( expression )
  if (symbol == SYM_IF) {
    getSymbol();

    if (symbol == SYM_LPARENTHESIS) {
      getSymbol();

      compile_expression();

      // if the "if" case is not true we branch to "else" (if provided)
      branchForwardToElseOrEnd = binaryLength;

      emitBEQ(currentTemporary(), REG_ZR, 0);

      tfree(1);

      if (symbol == SYM_RPARENTHESIS) {
        getSymbol();

        // zero or more statements: { statement }
        if (symbol == SYM_LBRACE) {
          getSymbol();

          while (isNotRbraceOrEOF())
            compile_statement();

          if (symbol == SYM_RBRACE)
            getSymbol();
          else {
            syntaxErrorSymbol(SYM_RBRACE);

            exit(EXITCODE_PARSERERROR);
          }
        } else
        // only one statement without {}
          compile_statement();

        //optional: else
        if (symbol == SYM_ELSE) {
          getSymbol();

          // if the "if" case was true we skip the "else" case
          // by unconditionally jumping to the end
          jumpForwardToEnd = binaryLength;

          emitJAL(REG_ZR, 0);

          // if the "if" case was not true we branch here
          fixup_relative_BFormat(branchForwardToElseOrEnd);

          // zero or more statements: { statement }
          if (symbol == SYM_LBRACE) {
            getSymbol();

            while (isNotRbraceOrEOF())
              compile_statement();

            if (symbol == SYM_RBRACE)
              getSymbol();
            else {
              syntaxErrorSymbol(SYM_RBRACE);

              exit(EXITCODE_PARSERERROR);
            }

          // only one statement without {}
          } else
            compile_statement();

          // if the "if" case was true we unconditionally jump here
          fixup_relative_JFormat(jumpForwardToEnd, binaryLength);
        } else
          // if the "if" case was not true we branch here
          fixup_relative_BFormat(branchForwardToElseOrEnd);
      } else
        syntaxErrorSymbol(SYM_RPARENTHESIS);
    } else
      syntaxErrorSymbol(SYM_LPARENTHESIS);
  } else
    syntaxErrorSymbol(SYM_IF);

  // assert: allocatedTemporaries == 0

  numberOfIf = numberOfIf + 1;
}

void compile_return() {
  uint64_t type;

  // assert: allocatedTemporaries == 0

  if (symbol == SYM_RETURN)
    getSymbol();
  else
    syntaxErrorSymbol(SYM_RETURN);

  // optional: expression
  if (symbol != SYM_SEMICOLON) {
    type = compile_expression();

    if (type != returnType)
      typeWarning(returnType, type);

    // save value of expression in return register
    emitADD(REG_A0, REG_ZR, currentTemporary());

    tfree(1);
  } else if (returnType != VOID_T)
    typeWarning(returnType, VOID_T);

  // jump to procedure epilogue through fixup chain using absolute address
  emitJAL(REG_ZR, returnBranches);

  // new head of fixup chain
  returnBranches = binaryLength - INSTRUCTIONSIZE;

  // assert: allocatedTemporaries == 0

  numberOfReturn = numberOfReturn + 1;
}

void compile_statement() {
  uint64_t ltype;
  uint64_t rtype;
  uint64_t* variableOrProcedureName;
  uint64_t* entry;
  uint64_t offset;

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
      ltype = load_variableOrBigInt(identifier, VARIABLE);

      if (ltype != UINT64STAR_T)
        typeWarning(UINT64STAR_T, ltype);

      getSymbol();

      // "*" identifier "="
      if (symbol == SYM_ASSIGN) {
        getSymbol();

        rtype = compile_expression();

        if (rtype != UINT64_T)
          typeWarning(UINT64_T, rtype);

        emitSD(previousTemporary(), 0, currentTemporary());

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

      ltype = compile_expression();

      if (ltype != UINT64STAR_T)
        typeWarning(UINT64STAR_T, ltype);

      if (symbol == SYM_RPARENTHESIS) {
        getSymbol();

        // "*" "(" expression ")" "="
        if (symbol == SYM_ASSIGN) {
          getSymbol();

          rtype = compile_expression();

          if (rtype != UINT64_T)
            typeWarning(UINT64_T, rtype);

          emitSD(previousTemporary(), 0, currentTemporary());

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

      compile_call(variableOrProcedureName);

      // reset return register to initial return value
      // for missing return expressions
      emitADDI(REG_A0, REG_ZR, 0);

      if (symbol == SYM_SEMICOLON)
        getSymbol();
      else
        syntaxErrorSymbol(SYM_SEMICOLON);

    // identifier = expression
    } else if (symbol == SYM_ASSIGN) {
      entry = getVariableOrBigInt(variableOrProcedureName, VARIABLE);

      ltype = getType(entry);

      getSymbol();

      rtype = compile_expression();

      if (ltype != rtype)
        typeWarning(ltype, rtype);

      offset = getAddress(entry);

      if (isSignedInteger(offset, 12)) {
        emitSD(getScope(entry), offset, currentTemporary());

        tfree(1);
      } else {
        load_upperBaseAddress(entry);

        emitSD(currentTemporary(), signExtend(getBits(offset, 0, 12), 12), previousTemporary());

        tfree(2);
      }

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
      getSymbol();
    else
      syntaxErrorSymbol(SYM_SEMICOLON);
  }
}

uint64_t compile_type() {
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

void compile_variable(uint64_t offset) {
  uint64_t type;

  type = compile_type();

  if (symbol == SYM_IDENTIFIER) {
    // TODO: check if identifier has already been declared
    createSymbolTableEntry(LOCAL_TABLE, identifier, lineNumber, VARIABLE, type, 0, offset);

    getSymbol();
  } else {
    syntaxErrorSymbol(SYM_IDENTIFIER);

    createSymbolTableEntry(LOCAL_TABLE, (uint64_t*) "missing variable name", lineNumber, VARIABLE, type, 0, offset);
  }
}

uint64_t compile_initialization(uint64_t type) {
  uint64_t initialValue;
  uint64_t hasCast;
  uint64_t cast;

  initialValue = 0;

  hasCast = 0;

  if (symbol == SYM_ASSIGN) {
    getSymbol();

    // optional: [ cast ]
    if (symbol == SYM_LPARENTHESIS) {
      hasCast = 1;

      getSymbol();

      cast = compile_type();

      if (symbol == SYM_RPARENTHESIS)
        getSymbol();
      else
        syntaxErrorSymbol(SYM_RPARENTHESIS);
    }

    // optional: -
    if (symbol == SYM_MINUS) {
      integerIsSigned = 1;

      getSymbol();

      integerIsSigned = 0;

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

void compile_procedure(uint64_t* procedure, uint64_t type) {
  uint64_t isUndefined;
  uint64_t numberOfParameters;
  uint64_t parameters;
  uint64_t numberOfLocalVariableBytes;
  uint64_t* entry;

  // assuming procedure is undefined
  isUndefined = 1;

  numberOfParameters = 0;

  // try parsing formal parameters
  if (symbol == SYM_LPARENTHESIS) {
    getSymbol();

    if (symbol != SYM_RPARENTHESIS) {
      compile_variable(0);

      numberOfParameters = 1;

      while (symbol == SYM_COMMA) {
        getSymbol();

        compile_variable(0);

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
        if (getOpcode(loadInstruction(getAddress(entry))) == OP_JAL)
          // procedure already called but not defined
          fixlink_relative(getAddress(entry), binaryLength);
        else
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

        if (stringCompare(procedure, (uint64_t*) "main"))
          // first source containing main procedure provides binary name
          binaryName = sourceName;
      } else {
        // procedure already defined
        printLineNumber((uint64_t*) "warning", lineNumber);
        printf1((uint64_t*) "redefinition of procedure %s ignored\n", procedure);
      }
    }

    getSymbol();

    numberOfLocalVariableBytes = 0;

    while (symbol == SYM_UINT64) {
      numberOfLocalVariableBytes = numberOfLocalVariableBytes + REGISTERSIZE;

      // offset of local variables relative to frame pointer is negative
      compile_variable(-numberOfLocalVariableBytes);

      if (symbol == SYM_SEMICOLON)
        getSymbol();
      else
        syntaxErrorSymbol(SYM_SEMICOLON);
    }

    help_procedure_prologue(numberOfLocalVariableBytes);

    // create a fixup chain for return statements
    returnBranches = 0;

    returnType = type;

    while (isNotRbraceOrEOF())
      compile_statement();

    returnType = 0;

    if (symbol == SYM_RBRACE)
      getSymbol();
    else {
      syntaxErrorSymbol(SYM_RBRACE);

      exit(EXITCODE_PARSERERROR);
    }

    fixlink_relative(returnBranches, binaryLength);

    returnBranches = 0;

    help_procedure_epilogue(numberOfParameters * REGISTERSIZE);

  } else
    syntaxErrorUnexpected();

  local_symbol_table = (uint64_t*) 0;

  // assert: allocatedTemporaries == 0
}

void compile_cstar() {
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

        compile_procedure(variableOrProcedureName, type);
      } else
        syntaxErrorSymbol(SYM_IDENTIFIER);
    } else {
      type = compile_type();

      if (symbol == SYM_IDENTIFIER) {
        variableOrProcedureName = identifier;

        getSymbol();

        if (symbol == SYM_LPARENTHESIS)
          // type identifier "(" ...
          // procedure declaration or definition
          compile_procedure(variableOrProcedureName, type);
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
            initialValue = compile_initialization(type);

          entry = searchSymbolTable(global_symbol_table, variableOrProcedureName, VARIABLE);

          if (entry == (uint64_t*) 0) {
            allocatedMemory = allocatedMemory + REGISTERSIZE;

            createSymbolTableEntry(GLOBAL_TABLE, variableOrProcedureName, currentLineNumber, VARIABLE, type, initialValue, -allocatedMemory);
          } else {
            // global variable already declared or defined
            printLineNumber((uint64_t*) "warning", currentLineNumber);
            printf1((uint64_t*) "redefinition of global variable %s ignored\n", variableOrProcedureName);
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

void emitRoundUp(uint64_t reg, uint64_t m) {
  talloc();

  // computes value(reg) + m - 1 - (value(reg) + m - 1) % m
  emitADDI(reg, reg, m - 1);
  emitADDI(currentTemporary(), REG_ZR, m);
  emitREMU(currentTemporary(), reg, currentTemporary());
  emitSUB(reg, reg, currentTemporary());

  tfree(1);
}

void emitLeftShiftBy(uint64_t reg, uint64_t b) {
  // assert: 0 <= b < 11

  // load multiplication factor less than 2^11 to avoid sign extension
  emitADDI(nextTemporary(), REG_ZR, twoToThePowerOf(b));
  emitMUL(reg, reg, nextTemporary());
}

void emitProgramEntry() {
  // jump and link to the _start procedure
  emitJAL(REG_RA, 0);
}

void emitStart() {
  /* 1. fixup initial jump to here
     2. push argv pointer onto stack
     3. initialize global pointer
     4. initialize malloc's bump pointer
     5. call main procedure
     6. call exit procedure */
  uint64_t gp;
  uint64_t padding;
  uint64_t lower;
  uint64_t upper;
  uint64_t* entry;

  // fixup jump at address 0 to here
  fixup_relative_JFormat(0, binaryLength);

  // allocate memory for argv variable
  emitADDI(REG_SP, REG_SP, -REGISTERSIZE);

  talloc();

  // push argv pointer onto the stack
  //      ______________
  //     |              V
  // | &argv | argc | argv[0] | argv[1] | ... | argv[n]
  emitADDI(currentTemporary(), REG_SP, 2 * REGISTERSIZE);
  emitSD(REG_SP, 0, currentTemporary());

  tfree(1);

  // calculate the global pointer value accommodating 16 more instructions
  gp = ELF_ENTRY_POINT + binaryLength + 16 * INSTRUCTIONSIZE + allocatedMemory;

  // make sure gp is double-word-aligned
  padding = gp % REGISTERSIZE;
  gp      = gp + padding;

  // assert: 0 <= gp < 2^31-2^11 (to avoid sign extension for upper)

  lower = getBits(gp,  0, 12);
  upper = getBits(gp, 12, 19);

  if (lower >= twoToThePowerOf(11)) {
    // add 1 which is effectively 2^12 to cancel sign extension of lower
    emitLUI(REG_GP, upper + 1);
    emitADDI(REG_GP, REG_GP, signExtend(lower, 12));
  } else {
    emitLUI(REG_GP, upper);
    emitADDI(REG_GP, REG_GP, lower);
  }

  // retrieve current program break
  emitADDI(REG_A0, REG_ZR, 0);
  emitADDI(REG_A7, REG_ZR, SYSCALL_BRK);
  emitECALL();

  // align current program break for double-word access
  emitRoundUp(REG_A0, SIZEOFUINT64);

  // set program break to aligned program break
  emitADDI(REG_A7, REG_ZR, SYSCALL_BRK);
  emitECALL();

  // declare global variable _bump for storing malloc's bump pointer
  entry = searchSymbolTable(global_symbol_table, (uint64_t*) "_bump", VARIABLE);

  // store aligned program break in _bump
  emitSD(getScope(entry), getAddress(entry), REG_A0);

  if (reportUndefinedProcedures())
    // rather than jump and link to the main procedure
    // exit by continuing to the next instruction
    emitADDI(REG_A0, REG_ZR, 0);
  else {
    entry = getScopedSymbolTableEntry((uint64_t*) "main", PROCEDURE);

    help_call_codegen(entry, (uint64_t*) "main");
  }

  // we exit with exit code in return register pushed onto the stack
  emitADDI(REG_SP, REG_SP, -REGISTERSIZE);
  emitSD(REG_SP, 0, REG_A0);

  entry = getScopedSymbolTableEntry((uint64_t*) "exit", PROCEDURE);

  help_call_codegen(entry, (uint64_t*) "exit");

  if (padding != 0)
    emitNOP();

  codeLength = binaryLength;
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
  resetInstructionCounters();

  emitProgramEntry();

  // emit system call wrappers
  emitExit();
  emitRead();
  emitWrite();
  emitOpen();
  emitMalloc();
  emitSwitch();

  // declare mandatory main procedure
  createSymbolTableEntry(GLOBAL_TABLE, (uint64_t*) "main", 0, PROCEDURE, UINT64_T, 0, 0);

  while (link) {
    if (numberOfRemainingArguments() == 0)
      link = 0;
    else if (loadCharacter(peekArgument(), 0) == '-')
      link = 0;
    else {
      sourceName = getArgument();

      numberOfSourceFiles = numberOfSourceFiles + 1;

      printf2((uint64_t*) "%s: selfie compiling %s with starc\n", selfieName, sourceName);

      // assert: sourceName is mapped and not longer than maxFilenameLength

      sourceFD = signExtend(open(sourceName, O_RDONLY, 0), SYSCALL_BITWIDTH);

      if (signedLessThan(sourceFD, 0)) {
        printf2((uint64_t*) "%s: could not open input file %s\n", selfieName, sourceName);

        exit(EXITCODE_IOERROR);
      }

      resetScanner();
      resetParser();

      compile_cstar();

      printf4((uint64_t*) "%s: %d characters read in %d lines and %d comments\n", selfieName,
        (uint64_t*) numberOfReadCharacters,
        (uint64_t*) lineNumber,
        (uint64_t*) numberOfComments);

      printf4((uint64_t*) "%s: with %d(%.2d%%) characters in %d actual symbols\n", selfieName,
        (uint64_t*) (numberOfReadCharacters - numberOfIgnoredCharacters),
        (uint64_t*) fixedPointPercentage(fixedPointRatio(numberOfReadCharacters, numberOfReadCharacters - numberOfIgnoredCharacters, 4), 4),
        (uint64_t*) numberOfScannedSymbols);

      printf4((uint64_t*) "%s: %d global variables, %d procedures, %d string literals\n", selfieName,
        (uint64_t*) numberOfGlobalVariables,
        (uint64_t*) numberOfProcedures,
        (uint64_t*) numberOfStrings);

      printf6((uint64_t*) "%s: %d calls, %d assignments, %d while, %d if, %d return\n", selfieName,
        (uint64_t*) numberOfCalls,
        (uint64_t*) numberOfAssignments,
        (uint64_t*) numberOfWhile,
        (uint64_t*) numberOfIf,
        (uint64_t*) numberOfReturn);
    }
  }

  if (numberOfSourceFiles == 0)
    printf1((uint64_t*) "%s: nothing to compile, only library generated\n", selfieName);

  emitStart();

  emitGlobalsStringsBigIntegers();

  ELF_header = createELFHeader(binaryLength);

  entryPoint = ELF_ENTRY_POINT;

  printf4((uint64_t*) "%s: %d bytes generated with %d instructions and %d bytes of data\n", selfieName,
    (uint64_t*) (ELF_HEADER_LEN + SIZEOFUINT64 + binaryLength),
    (uint64_t*) (codeLength / INSTRUCTIONSIZE),
    (uint64_t*) (binaryLength - codeLength));

  printInstructionCounters();
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// --------------------------- REGISTER ----------------------------
// -----------------------------------------------------------------

uint64_t* getRegisterName(uint64_t reg) {
  return (uint64_t*) *(REGISTERS + reg);
}

void printRegisterName(uint64_t reg) {
  print(getRegisterName(reg));
}

// -----------------------------------------------------------------
// ------------------------ ENCODER/DECODER ------------------------
// -----------------------------------------------------------------

void checkImmediateRange(uint64_t immediate, uint64_t bits) {
  if (isSignedInteger(immediate, bits) == 0) {
    printLineNumber((uint64_t*) "encoding error", lineNumber);
    printf3((uint64_t*) "%d expected between %d and %d\n",
      (uint64_t*) immediate,
      (uint64_t*) -twoToThePowerOf(bits - 1),
      (uint64_t*) twoToThePowerOf(bits - 1) - 1);

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

uint64_t encodeRFormat(uint64_t funct7, uint64_t rs2, uint64_t rs1, uint64_t funct3, uint64_t rd, uint64_t opcode) {
  // assert: 0 <= funct7 < 2^7
  // assert: 0 <= rs2 < 2^5
  // assert: 0 <= rs1 < 2^5
  // assert: 0 <= funct3 < 2^3
  // assert: 0 <= rd < 2^5
  // assert: 0 <= opcode < 2^7

  return leftShift(leftShift(leftShift(leftShift(leftShift(funct7, 5) + rs2, 5) + rs1, 3) + funct3, 5) + rd, 7) + opcode;
}

uint64_t getFunct7(uint64_t instruction) {
  return getBits(instruction, 25, 7);
}

uint64_t getRS2(uint64_t instruction) {
  return getBits(instruction, 20, 5);
}

uint64_t getRS1(uint64_t instruction) {
  return getBits(instruction, 15, 5);
}

uint64_t getFunct3(uint64_t instruction) {
  return getBits(instruction, 12, 3);
}

uint64_t getRD(uint64_t instruction) {
  return getBits(instruction, 7, 5);
}

uint64_t getOpcode(uint64_t instruction) {
  return getBits(instruction, 0, 7);
}

void decodeRFormat() {
  funct7 = getFunct7(ir);
  rs2    = getRS2(ir);
  rs1    = getRS1(ir);
  funct3 = getFunct3(ir);
  rd     = getRD(ir);
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

uint64_t encodeIFormat(uint64_t immediate, uint64_t rs1, uint64_t funct3, uint64_t rd, uint64_t opcode) {
  // assert: -2^11 <= immediate < 2^11
  // assert: 0 <= rs1 < 2^5
  // assert: 0 <= funct3 < 2^3
  // assert: 0 <= rd < 2^5
  // assert: 0 <= opcode < 2^7

  checkImmediateRange(immediate, 12);

  immediate = signShrink(immediate, 12);

  return leftShift(leftShift(leftShift(leftShift(immediate, 5) + rs1, 3) + funct3, 5) + rd, 7) + opcode;
}

uint64_t getImmediateIFormat(uint64_t instruction) {
  return signExtend(getBits(instruction, 20, 12), 12);
}

void decodeIFormat() {
  funct7 = 0;
  rs2    = 0;
  rs1    = getRS1(ir);
  funct3 = getFunct3(ir);
  rd     = getRD(ir);
  imm    = getImmediateIFormat(ir);
}

// RISC-V S Format
// ----------------------------------------------------------------
// |        7         |  5  |  5  |  3   |        5        |  7   |
// +------------------+-----+-----+------+-----------------+------+
// |    imm1[11:5]    | rs2 | rs1 |funct3|    imm2[4:0]    |opcode|
// +------------------+-----+-----+------+-----------------+------+
// |31              25|24 20|19 15|14  12|11              7|6    0|
// ----------------------------------------------------------------

uint64_t encodeSFormat(uint64_t immediate, uint64_t rs2, uint64_t rs1, uint64_t funct3, uint64_t opcode) {
  // assert: -2^11 <= immediate < 2^11
  // assert: 0 <= rs2 < 2^5
  // assert: 0 <= rs1 < 2^5
  // assert: 0 <= funct3 < 2^3
  // assert: 0 <= opcode < 2^7
  uint64_t imm1;
  uint64_t imm2;

  checkImmediateRange(immediate, 12);

  immediate = signShrink(immediate, 12);

  imm1 = getBits(immediate, 5, 7);
  imm2 = getBits(immediate, 0, 5);

  return leftShift(leftShift(leftShift(leftShift(leftShift(imm1, 5) + rs2, 5) + rs1, 3) + funct3, 5) + imm2, 7) + opcode;
}

uint64_t getImmediateSFormat(uint64_t instruction) {
  uint64_t imm1;
  uint64_t imm2;

  imm1 = getBits(instruction, 25, 7);
  imm2 = getBits(instruction,  7, 5);

  return signExtend(leftShift(imm1, 5) + imm2, 12);
}

void decodeSFormat() {
  funct7 = 0;
  rs2    = getRS2(ir);
  rs1    = getRS1(ir);
  funct3 = getFunct3(ir);
  rd     = 0;
  imm    = getImmediateSFormat(ir);
}

// RISC-V B Format
// ----------------------------------------------------------------
// |        7         |  5  |  5  |  3   |        5        |  7   |
// +------------------+-----+-----+------+-----------------+------+
// |imm1[12]imm2[10:5]| rs2 | rs1 |funct3|imm3[4:1]imm4[11]|opcode|
// +------------------+-----+-----+------+-----------------+------+
// |31              25|24 20|19 15|14  12|11              7|6    0|
// ----------------------------------------------------------------

uint64_t encodeBFormat(uint64_t immediate, uint64_t rs2, uint64_t rs1, uint64_t funct3, uint64_t opcode) {
  // assert: -2^12 <= immediate < 2^12
  // assert: 0 <= rs2 < 2^5
  // assert: 0 <= rs1 < 2^5
  // assert: 0 <= funct3 < 2^3
  // assert: 0 <= opcode < 2^7
  uint64_t imm1;
  uint64_t imm2;
  uint64_t imm3;
  uint64_t imm4;

  checkImmediateRange(immediate, 13);

  immediate = signShrink(immediate, 13);

  // LSB of immediate is lost
  imm1 = getBits(immediate, 12, 1);
  imm2 = getBits(immediate,  5, 6);
  imm3 = getBits(immediate,  1, 4);
  imm4 = getBits(immediate, 11, 1);

  return leftShift(leftShift(leftShift(leftShift(leftShift(leftShift(leftShift(imm1, 6) + imm2, 5) + rs2, 5) + rs1, 3) + funct3, 4) + imm3, 1) + imm4, 7) + opcode;
}

uint64_t getImmediateBFormat(uint64_t instruction) {
  uint64_t imm1;
  uint64_t imm2;
  uint64_t imm3;
  uint64_t imm4;

  imm1 = getBits(instruction, 31, 1);
  imm2 = getBits(instruction, 25, 6);
  imm3 = getBits(instruction,  8, 4);
  imm4 = getBits(instruction,  7, 1);

  // reassemble immediate and add trailing zero
  return signExtend(leftShift(leftShift(leftShift(leftShift(imm1, 1) + imm4, 6) + imm2, 4) + imm3, 1), 13);
}

void decodeBFormat() {
  funct7 = 0;
  rs2    = getRS2(ir);
  rs1    = getRS1(ir);
  funct3 = getFunct3(ir);
  rd     = 0;
  imm    = getImmediateBFormat(ir);
}

// RISC-V J Format
// ----------------------------------------------------------------
// |                  20                 |        5        |  7   |
// +-------------------------------------+-----------------+------+
// |imm1[20]imm2[10:1]imm3[11]imm4[19:12]|       rd        |opcode|
// +-------------------------------------+-----------------+------+
// |31                                 12|11              7|6    0|
// ----------------------------------------------------------------

uint64_t encodeJFormat(uint64_t immediate, uint64_t rd, uint64_t opcode) {
  // assert: -2^20 <= immediate < 2^20
  // assert: 0 <= rd < 2^5
  // assert: 0 <= opcode < 2^7
  uint64_t imm1;
  uint64_t imm2;
  uint64_t imm3;
  uint64_t imm4;

  checkImmediateRange(immediate, 21);

  immediate = signShrink(immediate, 21);

  // LSB of immediate is lost
  imm1 = getBits(immediate, 20,  1);
  imm2 = getBits(immediate,  1, 10);
  imm3 = getBits(immediate, 11,  1);
  imm4 = getBits(immediate, 12,  8);

  return leftShift(leftShift(leftShift(leftShift(leftShift(imm1, 10) + imm2, 1) + imm3, 8) + imm4, 5) + rd, 7) + opcode;
}

uint64_t getImmediateJFormat(uint64_t instruction) {
  uint64_t imm1;
  uint64_t imm2;
  uint64_t imm3;
  uint64_t imm4;

  imm1 = getBits(instruction, 31,  1);
  imm2 = getBits(instruction, 21, 10);
  imm3 = getBits(instruction, 20,  1);
  imm4 = getBits(instruction, 12,  8);

  // reassemble immediate and add trailing zero
  return signExtend(leftShift(leftShift(leftShift(leftShift(imm1, 8) + imm4, 1) + imm3, 10) + imm2, 1), 21);
}

void decodeJFormat() {
  funct7 = 0;
  rs2    = 0;
  rs1    = 0;
  funct3 = 0;
  rd     = getRD(ir);
  imm    = getImmediateJFormat(ir);
}

// RISC-V U Format
// ----------------------------------------------------------------
// |                  20                 |        5        |  7   |
// +-------------------------------------+-----------------+------+
// |           immediate[19:0]           |       rd        |opcode|
// +-------------------------------------+-----------------+------+
// |31                                 12|11              7|6    0|
// ----------------------------------------------------------------

uint64_t encodeUFormat(uint64_t immediate, uint64_t rd, uint64_t opcode) {
  // assert: -2^19 <= immediate < 2^19
  // assert: 0 <= rd < 2^5
  // assert: 0 <= opcode < 2^7

  checkImmediateRange(immediate, 20);

  immediate = signShrink(immediate, 20);

  return leftShift(leftShift(immediate, 5) + rd, 7) + opcode;
}

uint64_t getImmediateUFormat(uint64_t instruction) {
  return signExtend(getBits(instruction, 12, 20), 20);
}

void decodeUFormat() {
  funct7 = 0;
  rs2    = 0;
  rs1    = 0;
  funct3 = 0;
  rd     = getRD(ir);
  imm    = getImmediateUFormat(ir);
}

// -----------------------------------------------------------------
// ---------------------------- BINARY -----------------------------
// -----------------------------------------------------------------

void resetInstructionCounters() {
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

uint64_t getTotalNumberOfInstructions() {
  return ic_lui + ic_addi + ic_add + ic_sub + ic_mul + ic_divu + ic_remu + ic_sltu + ic_ld + ic_sd + ic_beq + ic_jal + ic_jalr + ic_ecall;
}

void printInstructionCounter(uint64_t total, uint64_t counter, uint64_t* mnemonics) {
  printf3((uint64_t*)
    "%s: %d(%.2d%%)",
    mnemonics,
    (uint64_t*) counter,
    (uint64_t*) fixedPointPercentage(fixedPointRatio(total, counter, 4), 4));
}

void printInstructionCounters() {
  uint64_t ic;

  ic = getTotalNumberOfInstructions();

  printf1((uint64_t*) "%s: init:    ", selfieName);
  printInstructionCounter(ic, ic_lui, (uint64_t*) "lui");
  print((uint64_t*) ", ");
  printInstructionCounter(ic, ic_addi, (uint64_t*) "addi");
  println();

  printf1((uint64_t*) "%s: memory:  ", selfieName);
  printInstructionCounter(ic, ic_ld, (uint64_t*) "ld");
  print((uint64_t*) ", ");
  printInstructionCounter(ic, ic_sd, (uint64_t*) "sd");
  println();

  printf1((uint64_t*) "%s: compute: ", selfieName);
  printInstructionCounter(ic, ic_add, (uint64_t*) "add");
  print((uint64_t*) ", ");
  printInstructionCounter(ic, ic_sub, (uint64_t*) "sub");
  print((uint64_t*) ", ");
  printInstructionCounter(ic, ic_mul, (uint64_t*) "mul");
  print((uint64_t*) ", ");
  printInstructionCounter(ic, ic_divu, (uint64_t*) "divu");
  print((uint64_t*) ", ");
  printInstructionCounter(ic, ic_remu, (uint64_t*) "remu");
  println();

  printf1((uint64_t*) "%s: control: ", selfieName);
  printInstructionCounter(ic, ic_sltu, (uint64_t*) "sltu");
  print((uint64_t*) ", ");
  printInstructionCounter(ic, ic_beq, (uint64_t*) "beq");
  print((uint64_t*) ", ");
  printInstructionCounter(ic, ic_jal, (uint64_t*) "jal");
  print((uint64_t*) ", ");
  printInstructionCounter(ic, ic_jalr, (uint64_t*) "jalr");
  print((uint64_t*) ", ");
  printInstructionCounter(ic, ic_ecall, (uint64_t*) "ecall");
  println();
}

uint64_t loadInstruction(uint64_t baddr) {
  if (baddr % REGISTERSIZE == 0)
    return getLowWord(*(binary + baddr / REGISTERSIZE));
  else
    return getHighWord(*(binary + baddr / REGISTERSIZE));
}

void storeInstruction(uint64_t baddr, uint64_t instruction) {
  uint64_t temp;

  if (baddr >= maxBinaryLength) {
    syntaxErrorMessage((uint64_t*) "maximum binary length exceeded");

    exit(EXITCODE_COMPILERERROR);
  }

  temp = *(binary + baddr / REGISTERSIZE);

  if (baddr % REGISTERSIZE == 0)
    // replace low word
    temp = leftShift(getHighWord(temp), WORDSIZEINBITS) + instruction;
  else
    // replace high word
    temp = leftShift(instruction, WORDSIZEINBITS) + getLowWord(temp);

  *(binary + baddr / REGISTERSIZE) = temp;
}

uint64_t loadData(uint64_t baddr) {
  return *(binary + baddr / REGISTERSIZE);
}

void storeData(uint64_t baddr, uint64_t data) {
  if (baddr >= maxBinaryLength) {
    syntaxErrorMessage((uint64_t*) "maximum binary length exceeded");

    exit(EXITCODE_COMPILERERROR);
  }

  *(binary + baddr / REGISTERSIZE) = data;
}

void emitInstruction(uint64_t instruction) {
  storeInstruction(binaryLength, instruction);

  if (*(sourceLineNumber + binaryLength / INSTRUCTIONSIZE) == 0)
    *(sourceLineNumber + binaryLength / INSTRUCTIONSIZE) = lineNumber;

  binaryLength = binaryLength + INSTRUCTIONSIZE;
}

void emitNOP() {
  emitInstruction(encodeIFormat(0, REG_ZR, F3_NOP, REG_ZR, OP_IMM));

  ic_addi = ic_addi + 1;
}

void emitLUI(uint64_t rd, uint64_t immediate) {
  emitInstruction(encodeUFormat(immediate, rd, OP_LUI));

  ic_lui = ic_lui + 1;
}

void emitADDI(uint64_t rd, uint64_t rs1, uint64_t immediate) {
  emitInstruction(encodeIFormat(immediate, rs1, F3_ADDI, rd, OP_IMM));

  ic_addi = ic_addi + 1;
}

void emitADD(uint64_t rd, uint64_t rs1, uint64_t rs2) {
  emitInstruction(encodeRFormat(F7_ADD, rs2, rs1, F3_ADD, rd, OP_OP));

  ic_add = ic_add + 1;
}

void emitSUB(uint64_t rd, uint64_t rs1, uint64_t rs2) {
  emitInstruction(encodeRFormat(F7_SUB, rs2, rs1, F3_SUB, rd, OP_OP));

  ic_sub = ic_sub + 1;
}

void emitMUL(uint64_t rd, uint64_t rs1, uint64_t rs2) {
  emitInstruction(encodeRFormat(F7_MUL, rs2, rs1, F3_MUL, rd, OP_OP));

  ic_mul = ic_mul + 1;
}

void emitDIVU(uint64_t rd, uint64_t rs1, uint64_t rs2) {
  emitInstruction(encodeRFormat(F7_DIVU, rs2, rs1, F3_DIVU, rd, OP_OP));

  ic_divu = ic_divu + 1;
}

void emitREMU(uint64_t rd, uint64_t rs1, uint64_t rs2) {
  emitInstruction(encodeRFormat(F7_REMU, rs2, rs1, F3_REMU, rd, OP_OP));

  ic_remu = ic_remu + 1;
}

void emitSLTU(uint64_t rd, uint64_t rs1, uint64_t rs2) {
  emitInstruction(encodeRFormat(F7_SLTU, rs2, rs1, F3_SLTU, rd, OP_OP));

  ic_sltu = ic_sltu + 1;
}

void emitLD(uint64_t rd, uint64_t rs1, uint64_t immediate) {
  emitInstruction(encodeIFormat(immediate, rs1, F3_LD, rd, OP_LD));

  ic_ld = ic_ld + 1;
}

void emitSD(uint64_t rs1, uint64_t immediate, uint64_t rs2) {
  emitInstruction(encodeSFormat(immediate, rs2, rs1, F3_SD, OP_SD));

  ic_sd = ic_sd + 1;
}

void emitBEQ(uint64_t rs1, uint64_t rs2, uint64_t immediate) {
  emitInstruction(encodeBFormat(immediate, rs2, rs1, F3_BEQ, OP_BRANCH));

  ic_beq = ic_beq + 1;
}

void emitJAL(uint64_t rd, uint64_t immediate) {
  emitInstruction(encodeJFormat(immediate, rd, OP_JAL));

  ic_jal = ic_jal + 1;
}

void emitJALR(uint64_t rd, uint64_t rs1, uint64_t immediate) {
  emitInstruction(encodeIFormat(immediate, rs1, F3_JALR, rd, OP_JALR));

  ic_jalr = ic_jalr + 1;
}

void emitECALL() {
  emitInstruction(encodeIFormat(F12_ECALL, REG_ZR, F3_ECALL, REG_ZR, OP_SYSTEM));

  ic_ecall = ic_ecall + 1;
}

void fixup_relative_BFormat(uint64_t fromAddress) {
  uint64_t instruction;

  instruction = loadInstruction(fromAddress);

  storeInstruction(fromAddress,
    encodeBFormat(binaryLength - fromAddress,
      getRS2(instruction),
      getRS1(instruction),
      getFunct3(instruction),
      getOpcode(instruction)));
}

void fixup_relative_JFormat(uint64_t fromAddress, uint64_t toAddress) {
  uint64_t instruction;

  instruction = loadInstruction(fromAddress);

  storeInstruction(fromAddress,
    encodeJFormat(toAddress - fromAddress,
      getRD(instruction),
      getOpcode(instruction)));
}

void fixlink_relative(uint64_t fromAddress, uint64_t toAddress) {
  uint64_t previousAddress;

  while (fromAddress != 0) {
    previousAddress = getImmediateJFormat(loadInstruction(fromAddress));

    fixup_relative_JFormat(fromAddress, toAddress);

    fromAddress = previousAddress;
  }
}

uint64_t copyStringToBinary(uint64_t* s, uint64_t baddr) {
  uint64_t next;

  next = baddr + roundUp(stringLength(s) + 1, REGISTERSIZE);

  while (baddr < next) {
    storeData(baddr, *s);

    s = s + 1;

    baddr = baddr + REGISTERSIZE;
  }

  return next;
}

void emitGlobalsStringsBigIntegers() {
  uint64_t* entry;

  entry = global_symbol_table;

  // assert: n = binaryLength

  // allocate space for global variables and copy strings and big integers
  while ((uint64_t) entry != 0) {
    if (getClass(entry) == VARIABLE) {
      storeData(binaryLength, getValue(entry));

      binaryLength = binaryLength + REGISTERSIZE;
    } else if (getClass(entry) == STRING)
      binaryLength = copyStringToBinary(getString(entry), binaryLength);
    else if (getClass(entry) == BIGINT) {
      storeData(binaryLength, getValue(entry));

      binaryLength = binaryLength + REGISTERSIZE;
    }

    entry = getNextEntry(entry);
  }

  // assert: binaryLength == n + allocatedMemory

  allocatedMemory = 0;
}

uint64_t* createELFHeader(uint64_t binaryLength) {
  uint64_t* header;

  // store all numbers necessary to create a minimal and valid
  // ELF64 header incl. program header.
  header = smalloc(ELF_HEADER_LEN);

  // RISC-U ELF64 file header:
  *(header + 0) = 127                              // magic number part 0 is 0x7F
                + leftShift((uint64_t) 'E', 8)     // magic number part 1
                + leftShift((uint64_t) 'L', 16)    // magic number part 2
                + leftShift((uint64_t) 'F', 24)    // magic number part 3
                + leftShift(2, 32)                 // file class is ELFCLASS64
                + leftShift(1, 40)                 // object file data structures endianess is ELFDATA2LSB
                + leftShift(1, 48);                // version of the object file format
  *(header + 1) = 0;                               // ABI version and start of padding bytes
  *(header + 2) = 2                                // object file type is ET_EXEC
                + leftShift(243, 16)               // target architecture is RV64
                + leftShift(1, 32);                // version of the object file format
  *(header + 3) = ELF_ENTRY_POINT;                 // entry point address
  *(header + 4) = 8 * SIZEOFUINT64;                // program header offset
  *(header + 5) = 0;                               // section header offset
  *(header + 6) = leftShift(8 * SIZEOFUINT64, 32)  // elf header size
                + leftShift(7 * SIZEOFUINT64, 48); // size of program header entry
  *(header + 7) = 1;                               // number of program header entries

  // RISC-U ELF64 program header table:
  *(header + 8)  = 1                              // type of segment is LOAD
                 + leftShift(7, 32);              // segment attributes is RWX
  *(header + 9)  = ELF_HEADER_LEN + SIZEOFUINT64; // segment offset in file
  *(header + 10) = ELF_ENTRY_POINT;               // virtual address in memory
  *(header + 11) = 0;                             // physical address (reserved)
  *(header + 12) = binaryLength;                  // size of segment in file
  *(header + 13) = binaryLength;                  // size of segment in memory
  *(header + 14) = PAGESIZE;                      // alignment of segment

  return header;
}

uint64_t parseELFHeader(uint64_t* header) {
  uint64_t  newEntryPoint;
  uint64_t  newBinaryLength;
  uint64_t  position;
  uint64_t* valid;

  newEntryPoint = *(header + 10);

  newBinaryLength = *(header + 12);

  if (newBinaryLength != *(header + 13))
    // segment size in file is not the same as segement size in memory
    return 0;

  if (newEntryPoint > VIRTUALMEMORYSIZE - PAGESIZE - newBinaryLength)
    // binary does not fit into virtual address space
    return 0;

  valid = createELFHeader(newBinaryLength);

  position = 0;

  while (position < ELF_HEADER_LEN / SIZEOFUINT64) {
    if (*(header + position) != *(valid + position))
      return 0;

    position = position + 1;
  }

  entryPoint = newEntryPoint;

  binaryLength = newBinaryLength;

  return 1;
}

uint64_t openWriteOnly(uint64_t* name) {
  // we try opening write-only files using platform-specific flags
  // to make selfie platform-independent, this may nevertheless
  // not always work and require intervention
  uint64_t fd;

  // try Mac flags
  fd = signExtend(open(name, MAC_O_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH), SYSCALL_BITWIDTH);

  if (signedLessThan(fd, 0)) {
    // try Linux flags
    fd = signExtend(open(name, LINUX_O_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH), SYSCALL_BITWIDTH);

    if (signedLessThan(fd, 0))
      // try Windows flags
      fd = signExtend(open(name, WINDOWS_O_BINARY_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH), SYSCALL_BITWIDTH);
  }

  return fd;
}

void selfie_output() {
  uint64_t fd;

  binaryName = getArgument();

  if (binaryLength == 0) {
    printf2((uint64_t*) "%s: nothing to emit to output file %s\n", selfieName, binaryName);

    return;
  }

  // assert: binaryName is mapped and not longer than maxFilenameLength

  fd = openWriteOnly(binaryName);

  if (signedLessThan(fd, 0)) {
    printf2((uint64_t*) "%s: could not create binary output file %s\n", selfieName, binaryName);

    exit(EXITCODE_IOERROR);
  }

  // assert: ELF_header is mapped

  // first write ELF header
  if (write(fd, ELF_header, ELF_HEADER_LEN) != ELF_HEADER_LEN) {
    printf2((uint64_t*) "%s: could not write ELF header of binary output file %s\n", selfieName, binaryName);

    exit(EXITCODE_IOERROR);
  }

  // then write code length
  *binary_buffer = codeLength;

  if (write(fd, binary_buffer, SIZEOFUINT64) != SIZEOFUINT64) {
    printf2((uint64_t*) "%s: could not write code length of binary output file %s\n", selfieName, binaryName);

    exit(EXITCODE_IOERROR);
  }

  // assert: binary is mapped

  // then write binary
  if (write(fd, binary, binaryLength) != binaryLength) {
    printf2((uint64_t*) "%s: could not write binary into binary output file %s\n", selfieName, binaryName);

    exit(EXITCODE_IOERROR);
  }

  printf5((uint64_t*) "%s: %d bytes with %d instructions and %d bytes of data written into %s\n",
    selfieName,
    (uint64_t*) (ELF_HEADER_LEN + SIZEOFUINT64 + binaryLength),
    (uint64_t*) (codeLength / INSTRUCTIONSIZE),
    (uint64_t*) (binaryLength - codeLength),
    binaryName);
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
  uint64_t numberOfReadBytes;

  binaryName = getArgument();

  // assert: binaryName is mapped and not longer than maxFilenameLength

  fd = signExtend(open(binaryName, O_RDONLY, 0), SYSCALL_BITWIDTH);

  if (signedLessThan(fd, 0)) {
    printf2((uint64_t*) "%s: could not open input file %s\n", selfieName, binaryName);

    exit(EXITCODE_IOERROR);
  }

  // make sure binary is mapped for reading into it
  binary = touch(smalloc(maxBinaryLength), maxBinaryLength);

  binaryLength = 0;
  codeLength   = 0;
  entryPoint   = 0;

  // no source line numbers in binaries
  sourceLineNumber = (uint64_t*) 0;

  // make sure ELF_header is mapped for reading into it
  ELF_header = touch(smalloc(ELF_HEADER_LEN), ELF_HEADER_LEN);

  // read ELF_header first
  numberOfReadBytes = read(fd, ELF_header, ELF_HEADER_LEN);

  if (numberOfReadBytes == ELF_HEADER_LEN) {
    if (parseELFHeader(ELF_header)) {
      // now read code length
      numberOfReadBytes = read(fd, binary_buffer, SIZEOFUINT64);

      if (numberOfReadBytes == SIZEOFUINT64) {
        codeLength = *binary_buffer;

        if (binaryLength <= maxBinaryLength) {
          // now read binary including global variables and strings
          numberOfReadBytes = signExtend(read(fd, binary, binaryLength), SYSCALL_BITWIDTH);

          if (signedLessThan(0, numberOfReadBytes)) {
            // check if we are really at EOF
            if (read(fd, binary_buffer, SIZEOFUINT64) == 0) {
              printf5((uint64_t*) "%s: %d bytes with %d instructions and %d bytes of data loaded from %s\n",
                selfieName,
                (uint64_t*) (ELF_HEADER_LEN + SIZEOFUINT64 + binaryLength),
                (uint64_t*) (codeLength / INSTRUCTIONSIZE),
                (uint64_t*) (binaryLength - codeLength),
                binaryName);

              return;
            }
          }
        }
      }
    }
  }

  printf2((uint64_t*) "%s: failed to load code from input file %s\n", selfieName, binaryName);

  exit(EXITCODE_IOERROR);
}

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emitExit() {
  createSymbolTableEntry(LIBRARY_TABLE, (uint64_t*) "exit", 0, PROCEDURE, VOID_T, 0, binaryLength);

  // load signed 32-bit integer argument for exit
  emitLD(REG_A0, REG_SP, 0);

  // remove the argument from the stack
  emitADDI(REG_SP, REG_SP, REGISTERSIZE);

  // load the correct syscall number and invoke syscall
  emitADDI(REG_A7, REG_ZR, SYSCALL_EXIT);

  emitECALL();

  // never returns here
}

void implementExit(uint64_t* context) {
  setExitCode(context, signShrink(*(getRegs(context) + REG_A0), SYSCALL_BITWIDTH));

  if (symbolic)
    return;

  printf4((uint64_t*)
    "%s: %s exiting with exit code %d and %.2dMB mallocated memory\n",
    selfieName,
    getName(context),
    (uint64_t*) signExtend(getExitCode(context), SYSCALL_BITWIDTH),
    (uint64_t*) fixedPointRatio(getProgramBreak(context) - getOriginalBreak(context), MEGABYTE, 2));
}

void emitRead() {
  createSymbolTableEntry(LIBRARY_TABLE, (uint64_t*) "read", 0, PROCEDURE, UINT64_T, 0, binaryLength);

  emitLD(REG_A2, REG_SP, 0); // size
  emitADDI(REG_SP, REG_SP, REGISTERSIZE);

  emitLD(REG_A1, REG_SP, 0); // *buffer
  emitADDI(REG_SP, REG_SP, REGISTERSIZE);

  emitLD(REG_A0, REG_SP, 0); // fd
  emitADDI(REG_SP, REG_SP, REGISTERSIZE);

  emitADDI(REG_A7, REG_ZR, SYSCALL_READ);

  emitECALL();

  // jump back to caller, return value is in REG_A0
  emitJALR(REG_ZR, REG_RA, 0);
}

void implementRead(uint64_t* context) {
  // parameters
  uint64_t fd;
  uint64_t vbuffer;
  uint64_t size;

  // local variables
  uint64_t readTotal;
  uint64_t bytesToRead;
  uint64_t failed;
  uint64_t* buffer;
  uint64_t actuallyRead;
  uint64_t value;
  uint64_t lo;
  uint64_t up;
  uint64_t mrvc;

  fd      = *(getRegs(context) + REG_A0);
  vbuffer = *(getRegs(context) + REG_A1);
  size    = *(getRegs(context) + REG_A2);

  if (debug_read)
    printf4((uint64_t*) "%s: trying to read %d bytes from file with descriptor %d into buffer at virtual address %p\n", selfieName, (uint64_t*) size, (uint64_t*) fd, (uint64_t*) vbuffer);

  readTotal   = 0;
  bytesToRead = SIZEOFUINT64;

  failed = 0;

  while (size > 0) {
    if (isValidVirtualAddress(vbuffer)) {
      if (isVirtualAddressMapped(getPT(context), vbuffer)) {
        buffer = tlb(getPT(context), vbuffer);

        if (size < bytesToRead)
          bytesToRead = size;

        if (symbolic) {
          if (isTraceSpaceAvailable()) {
            if (rc > 0) {
              // do not read but reuse value, lower and upper bound
              value = *(read_values + rc);

              lo = *(read_los + rc);
              up = *(read_ups + rc);

              actuallyRead = bytesToRead;

              rc = rc - 1;
            } else {
              // save mrvc in buffer
              mrvc = loadPhysicalMemory(buffer);

              // caution: read only overwrites bytesToRead number of bytes
              // we therefore need to restore the actual value in buffer
              // to preserve the original read semantics
              storePhysicalMemory(buffer, *(values + loadSymbolicMemory(getPT(context), vbuffer)));

              actuallyRead = signExtend(read(fd, buffer, bytesToRead), SYSCALL_BITWIDTH);

              // retrieve read value
              value = loadPhysicalMemory(buffer);

              // fuzz read value
              lo = fuzzLo(value);
              up = fuzzUp(value);

              // restore mrvc in buffer
              storePhysicalMemory(buffer, mrvc);
            }

            if (mrcc == 0)
              // no branching yet, we may overwrite symbolic memory
              storeSymbolicMemory(getPT(context), vbuffer, value, 0, lo, up, 0);
            else
              storeSymbolicMemory(getPT(context), vbuffer, value, 0, lo, up, tc);
          } else {
            actuallyRead = 0;

            throwException(EXCEPTION_MAXTRACE, 0);
          }
        } else
          actuallyRead = signExtend(read(fd, buffer, bytesToRead), SYSCALL_BITWIDTH);

        if (actuallyRead == bytesToRead) {
          readTotal = readTotal + actuallyRead;

          size = size - actuallyRead;

          if (size > 0)
            vbuffer = vbuffer + SIZEOFUINT64;
        } else {
          if (signedLessThan(0, actuallyRead))
            readTotal = readTotal + actuallyRead;

          size = 0;
        }
      } else {
        failed = 1;

        size = 0;

        if (debug_read)
          printf2((uint64_t*) "%s: reading into virtual address %p failed because the address is unmapped\n", selfieName, (uint64_t*) vbuffer);
      }
    } else {
      failed = 1;

      size = 0;

      if (debug_read)
        printf2((uint64_t*) "%s: reading into virtual address %p failed because the address is invalid\n", selfieName, (uint64_t*) vbuffer);
    }
  }

  if (failed == 0)
    *(getRegs(context) + REG_A0) = readTotal;
  else
    *(getRegs(context) + REG_A0) = signShrink(-1, SYSCALL_BITWIDTH);

  if (symbolic) {
    *(reg_typ + REG_A0) = 0;

    *(reg_los + REG_A0) = *(getRegs(context) + REG_A0);
    *(reg_ups + REG_A0) = *(getRegs(context) + REG_A0);
  }

  setPC(context, getPC(context) + INSTRUCTIONSIZE);

  if (debug_read)
    printf3((uint64_t*) "%s: actually read %d bytes from file with descriptor %d\n", selfieName, (uint64_t*) readTotal, (uint64_t*) fd);
}

void emitWrite() {
  createSymbolTableEntry(LIBRARY_TABLE, (uint64_t*) "write", 0, PROCEDURE, UINT64_T, 0, binaryLength);

  emitLD(REG_A2, REG_SP, 0); // size
  emitADDI(REG_SP, REG_SP, REGISTERSIZE);

  emitLD(REG_A1, REG_SP, 0); // *buffer
  emitADDI(REG_SP, REG_SP, REGISTERSIZE);

  emitLD(REG_A0, REG_SP, 0); // fd
  emitADDI(REG_SP, REG_SP, REGISTERSIZE);

  emitADDI(REG_A7, REG_ZR, SYSCALL_WRITE);

  emitECALL();

  emitJALR(REG_ZR, REG_RA, 0);
}

void implementWrite(uint64_t* context) {
  // parameters
  uint64_t fd;
  uint64_t vbuffer;
  uint64_t size;

  // local variables
  uint64_t writtenTotal;
  uint64_t bytesToWrite;
  uint64_t failed;
  uint64_t* buffer;
  uint64_t actuallyWritten;

  fd      = *(getRegs(context) + REG_A0);
  vbuffer = *(getRegs(context) + REG_A1);
  size    = *(getRegs(context) + REG_A2);

  if (debug_write)
    printf4((uint64_t*) "%s: trying to write %d bytes from buffer at virtual address %p into file with descriptor %d\n", selfieName, (uint64_t*) size, (uint64_t*) vbuffer, (uint64_t*) fd);

  writtenTotal = 0;
  bytesToWrite = SIZEOFUINT64;

  failed = 0;

  while (size > 0) {
    if (isValidVirtualAddress(vbuffer)) {
      if (isVirtualAddressMapped(getPT(context), vbuffer)) {
        buffer = tlb(getPT(context), vbuffer);

        if (size < bytesToWrite)
          bytesToWrite = size;

        if (symbolic)
          // TODO: What should symbolically executed code output?
          // buffer points to a trace counter that refers to the actual value
          // actuallyWritten = signExtend(write(fd, values + loadPhysicalMemory(buffer), bytesToWrite), SYSCALL_BITWIDTH);
          actuallyWritten = bytesToWrite;
        else
          actuallyWritten = signExtend(write(fd, buffer, bytesToWrite), SYSCALL_BITWIDTH);

        if (actuallyWritten == bytesToWrite) {
          writtenTotal = writtenTotal + actuallyWritten;

          size = size - actuallyWritten;

          if (size > 0)
            vbuffer = vbuffer + SIZEOFUINT64;
        } else {
          if (signedLessThan(0, actuallyWritten))
            writtenTotal = writtenTotal + actuallyWritten;

          size = 0;
        }
      } else {
        failed = 1;

        size = 0;

        if (debug_write)
          printf2((uint64_t*) "%s: writing into virtual address %p failed because the address is unmapped\n", selfieName, (uint64_t*) vbuffer);
      }
    } else {
      failed = 1;

      size = 0;

      if (debug_write)
        printf2((uint64_t*) "%s: writing into virtual address %p failed because the address is invalid\n", selfieName, (uint64_t*) vbuffer);
    }
  }

  if (failed == 0)
    *(getRegs(context) + REG_A0) = writtenTotal;
  else
    *(getRegs(context) + REG_A0) = signShrink(-1, SYSCALL_BITWIDTH);

  if (symbolic) {
    *(reg_typ + REG_A0) = 0;

    *(reg_los + REG_A0) = *(getRegs(context) + REG_A0);
    *(reg_ups + REG_A0) = *(getRegs(context) + REG_A0);
  }

  setPC(context, getPC(context) + INSTRUCTIONSIZE);

  if (debug_write)
    printf3((uint64_t*) "%s: actually wrote %d bytes into file with descriptor %d\n", selfieName, (uint64_t*) writtenTotal, (uint64_t*) fd);
}

void emitOpen() {
  createSymbolTableEntry(LIBRARY_TABLE, (uint64_t*) "open", 0, PROCEDURE, UINT64_T, 0, binaryLength);

  emitLD(REG_A2, REG_SP, 0); // mode
  emitADDI(REG_SP, REG_SP, REGISTERSIZE);

  emitLD(REG_A1, REG_SP, 0); // flags
  emitADDI(REG_SP, REG_SP, REGISTERSIZE);

  emitLD(REG_A0, REG_SP, 0); // filename
  emitADDI(REG_SP, REG_SP, REGISTERSIZE);

  emitADDI(REG_A7, REG_ZR, SYSCALL_OPEN);

  emitECALL();

  emitJALR(REG_ZR, REG_RA, 0);
}

uint64_t down_loadString(uint64_t* table, uint64_t vaddr, uint64_t* s) {
  uint64_t mrvc;
  uint64_t i;
  uint64_t j;

  i = 0;

  while (i < maxFilenameLength / SIZEOFUINT64) {
    if (isValidVirtualAddress(vaddr)) {
      if (isVirtualAddressMapped(table, vaddr)) {
        if (symbolic) {
          mrvc = loadSymbolicMemory(table, vaddr);

          *(s + i) = *(values + mrvc);

          if (isSymbolicValue(*(types + mrvc), *(los + mrvc), *(ups + mrvc))) {
            printf1((uint64_t*) "%s: detected symbolic value ", selfieName);
            printSymbolicMemory(mrvc);
            print((uint64_t*) " in filename of open call\n");

            exit(EXITCODE_SYMBOLICEXECUTIONERROR);
          }
        } else
          *(s + i) = loadVirtualMemory(table, vaddr);

        j = 0;

        // check if string ends in the current machine word
        while (j < SIZEOFUINT64) {
          if (loadCharacter(s + i, j) == 0)
            return 1;

          j = j + 1;
        }

        // advance to the next machine word in virtual memory
        vaddr = vaddr + SIZEOFUINT64;

        // advance to the next machine word in our memory
        i = i + 1;
      } else if (debug_open)
        printf2((uint64_t*) "%s: opening file with name at virtual address %p failed because the address is unmapped\n", selfieName, (uint64_t*) vaddr);
    } else if (debug_open)
      printf2((uint64_t*) "%s: opening file with name at virtual address %p failed because the address is invalid\n", selfieName, (uint64_t*) vaddr);
  }

  return 0;
}

void implementOpen(uint64_t* context) {
  // parameters
  uint64_t vfilename;
  uint64_t flags;
  uint64_t mode;

  // return value
  uint64_t fd;

  vfilename = *(getRegs(context) + REG_A0);
  flags     = *(getRegs(context) + REG_A1);
  mode      = *(getRegs(context) + REG_A2);

  if (down_loadString(getPT(context), vfilename, filename_buffer)) {
    fd = signExtend(open(filename_buffer, flags, mode), SYSCALL_BITWIDTH);

    *(getRegs(context) + REG_A0) = fd;

    if (debug_open)
      printf5((uint64_t*) "%s: opened file %s with flags %x and mode %o returning file descriptor %d\n", selfieName, filename_buffer, (uint64_t*) flags, (uint64_t*) mode, (uint64_t*) fd);
  } else {
    *(getRegs(context) + REG_A0) = signShrink(-1, SYSCALL_BITWIDTH);

    if (debug_open)
      printf2((uint64_t*) "%s: opening file with name at virtual address %p failed because the name is too long\n", selfieName, (uint64_t*) vfilename);
  }

  if (symbolic) {
    *(reg_typ + REG_A0) = 0;

    *(reg_los + REG_A0) = *(getRegs(context) + REG_A0);
    *(reg_ups + REG_A0) = *(getRegs(context) + REG_A0);
  }

  setPC(context, getPC(context) + INSTRUCTIONSIZE);
}

void emitMalloc() {
  uint64_t* entry;

  createSymbolTableEntry(LIBRARY_TABLE, (uint64_t*) "malloc", 0, PROCEDURE, UINT64STAR_T, 0, binaryLength);

  // on boot levels higher than zero, zalloc falls back to malloc
  // assuming that page frames are zeroed on boot level zero
  createSymbolTableEntry(LIBRARY_TABLE, (uint64_t*) "zalloc", 0, PROCEDURE, UINT64STAR_T, 0, binaryLength);

  // allocate memory in data segment for recording state of
  // malloc (bump pointer) in compiler-declared global variable
  allocatedMemory = allocatedMemory + REGISTERSIZE;

  createSymbolTableEntry(GLOBAL_TABLE, (uint64_t*) "_bump", 0, VARIABLE, UINT64_T, 0, -allocatedMemory);

  entry = searchSymbolTable(global_symbol_table, (uint64_t*) "_bump", VARIABLE);

  // allocate register for size parameter
  talloc();

  emitLD(currentTemporary(), REG_SP, 0); // size
  emitADDI(REG_SP, REG_SP, REGISTERSIZE);

  // round up size to double-word alignment
  emitRoundUp(currentTemporary(), SIZEOFUINT64);

  // allocate register to compute new bump pointer
  talloc();

  // get current _bump (which will be returned upon success)
  emitLD(currentTemporary(), getScope(entry), getAddress(entry));

  // call brk syscall to set new program break to _bump + size
  emitADD(REG_A0, currentTemporary(), previousTemporary());
  emitADDI(REG_A7, REG_ZR, SYSCALL_BRK);
  emitECALL();

  // return 0 if memory allocation failed, that is,
  // if new program break is still _bump and size !=0
  emitBEQ(REG_A0, currentTemporary(), 2 * INSTRUCTIONSIZE);
  emitBEQ(REG_ZR, REG_ZR, 4 * INSTRUCTIONSIZE);
  emitBEQ(REG_ZR, previousTemporary(), 3 * INSTRUCTIONSIZE);
  emitADDI(REG_A0, REG_ZR, 0);
  emitBEQ(REG_ZR, REG_ZR, 3 * INSTRUCTIONSIZE);

  // if memory was successfully allocated
  // set _bump to new program break
  // and then return original _bump
  emitSD(getScope(entry), getAddress(entry), REG_A0);
  emitADDI(REG_A0, currentTemporary(), 0);

  tfree(2);

  emitJALR(REG_ZR, REG_RA,0);
}

void implementBrk(uint64_t* context) {
  // parameter
  uint64_t programBreak;

  // local variables
  uint64_t previousProgramBreak;
  uint64_t valid;
  uint64_t size;

  programBreak = *(getRegs(context) + REG_A0);

  previousProgramBreak = getProgramBreak(context);

  valid = 0;

  if (programBreak >= previousProgramBreak)
    if (programBreak < *(getRegs(context) + REG_SP))
      if (programBreak % SIZEOFUINT64 == 0)
        valid = 1;

  if (valid) {
    if (debug_brk)
      printf2((uint64_t*) "%s: setting program break to %p\n", selfieName, (uint64_t*) programBreak);

    setProgramBreak(context, programBreak);

    if (symbolic) {
      size = programBreak - previousProgramBreak;

      // interval is memory range, not symbolic value
      *(reg_typ + REG_A0) = 1;

      // remember start and size of memory block for checking memory safety
      *(reg_los + REG_A0) = previousProgramBreak;
      *(reg_ups + REG_A0) = size;

      if (mrcc > 0) {
        if (isTraceSpaceAvailable())
          // since there has been branching record brk using vaddr == 0
          storeSymbolicMemory(getPT(context), 0, previousProgramBreak, 1, previousProgramBreak, size, tc);
        else {
          throwException(EXCEPTION_MAXTRACE, 0);

          return;
        }
      }
    }
  } else {
    // error returns current program break
    programBreak = previousProgramBreak;

    if (debug_brk)
      printf2((uint64_t*) "%s: retrieving current program break %p\n", selfieName, (uint64_t*) programBreak);

    *(getRegs(context) + REG_A0) = programBreak;

    if (symbolic) {
      *(reg_typ + REG_A0) = 0;

      *(reg_los + REG_A0) = 0;
      *(reg_ups + REG_A0) = 0;
    }
  }

  setPC(context, getPC(context) + INSTRUCTIONSIZE);
}


// -----------------------------------------------------------------
// ----------------------- HYPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emitSwitch() {
  createSymbolTableEntry(LIBRARY_TABLE, (uint64_t*) "hypster_switch", 0, PROCEDURE, UINT64STAR_T, 0, binaryLength);

  emitLD(REG_A1, REG_SP, 0); // number of instructions to execute
  emitADDI(REG_SP, REG_SP, REGISTERSIZE);

  emitLD(REG_A0, REG_SP, 0); // context to which we switch
  emitADDI(REG_SP, REG_SP, REGISTERSIZE);

  emitADDI(REG_A7, REG_ZR, SYSCALL_SWITCH);

  emitECALL();

  // save context from which we are switching here in return register
  emitADD(REG_A0, REG_ZR, REG_A1);

  emitJALR(REG_ZR, REG_RA, 0);
}

void doSwitch(uint64_t* toContext, uint64_t timeout) {
  uint64_t* fromContext;

  fromContext = currentContext;

  restoreContext(toContext);

  // restore machine state
  pc        = getPC(toContext);
  registers = getRegs(toContext);
  pt        = getPT(toContext);

  // use REG_A1 instead of REG_A0 to avoid race condition with interrupt
  if (getParent(fromContext) != MY_CONTEXT)
    *(registers + REG_A1) = (uint64_t) getVirtualContext(fromContext);
  else
    *(registers + REG_A1) = (uint64_t) fromContext;

  currentContext = toContext;

  timer = timeout;

  if (debug_switch) {
    printf3((uint64_t*) "%s: switched from context %p to context %p", selfieName, fromContext, toContext);
    if (timer != TIMEROFF)
      printf1((uint64_t*) " to execute %d instructions", (uint64_t*) timer);
    println();
  }
}

void implementSwitch() {
  saveContext(currentContext);

  // cache context on my boot level before switching
  doSwitch(cacheContext((uint64_t*) *(registers + REG_A0)), *(registers + REG_A1));
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

  if (debug_tlb)
    printf5((uint64_t*) "%s: tlb access:\n vaddr: %p\n page:  %p\n frame: %p\n paddr: %p\n", selfieName, (uint64_t*) vaddr, (uint64_t*) (page * PAGESIZE), (uint64_t*) frame, (uint64_t*) paddr);

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

void printSourceLineNumberOfInstruction(uint64_t a) {
  if (sourceLineNumber != (uint64_t*) 0)
    printf1((uint64_t*) "(~%d)", (uint64_t*) *(sourceLineNumber + a / INSTRUCTIONSIZE));
}

void printInstructionContext() {
  if (execute) {
    printf2((uint64_t*) "%s: $pc=%x", binaryName, (uint64_t*) pc);
    printSourceLineNumberOfInstruction(pc - entryPoint);
  } else {
    printf1((uint64_t*) "%x", (uint64_t*) pc);
    printSourceLineNumberOfInstruction(pc);
  }
  printf1((uint64_t*) ": %p: ", (uint64_t*) ir);
}

void print_lui() {
  printInstructionContext();
  printf2((uint64_t*) "lui %s,%x", getRegisterName(rd), (uint64_t*) imm);
}

void print_lui_before() {
  print((uint64_t*) ": |- ");
  printRegisterHexadecimal(rd);
}

void print_lui_after() {
  print((uint64_t*) " -> ");
  printRegisterHexadecimal(rd);
}

void record_lui_addi_add_sub_mul_sltu_jal_jalr() {
  recordState(*(registers + rd));
}

void do_lui() {
  // load upper immediate

  if (rd != REG_ZR)
    // semantics of lui
    *(registers + rd) = leftShift(imm, 12);

  pc = pc + INSTRUCTIONSIZE;

  ic_lui = ic_lui + 1;
}

void undo_lui_addi_add_sub_mul_divu_remu_sltu_ld_jal_jalr() {
  *(registers + rd) = *(values + (tc % maxReplayLength));
}

void constrain_lui() {
  if (rd != REG_ZR) {
    *(reg_typ + rd) = 0;

    // interval semantics of lui
    *(reg_los + rd) = leftShift(imm, 12);
    *(reg_ups + rd) = leftShift(imm, 12);

    // rd has no constraint
    setConstraint(rd, 0, 0, 0, 0, 0);
  }
}

void print_addi() {
  printInstructionContext();

  if (rd == REG_ZR)
    if (rs1 == REG_ZR)
      if (imm == 0) {
        print((uint64_t*) "nop");

        return;
      }

  printf3((uint64_t*) "addi %s,%s,%d", getRegisterName(rd), getRegisterName(rs1), (uint64_t*) imm);
}

void print_addi_before() {
  print((uint64_t*) ": ");
  printRegisterValue(rs1);
  print((uint64_t*) " |- ");
  printRegisterValue(rd);
}

void print_addi_add_sub_mul_divu_remu_sltu_after() {
  print((uint64_t*) " -> ");
  printRegisterValue(rd);
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
    if (*(reg_typ + rs1)) {
      *(reg_typ + rd) = *(reg_typ + rs1);

      *(reg_los + rd) = *(reg_los + rs1);
      *(reg_ups + rd) = *(reg_ups + rs1);

      // rd has no constraint if rs1 is memory range
      setConstraint(rd, 0, 0, 0, 0, 0);

      return;
    }

    *(reg_typ + rd) = 0;

    // interval semantics of addi
    *(reg_los + rd) = *(reg_los + rs1) + imm;
    *(reg_ups + rd) = *(reg_ups + rs1) + imm;

    if (*(reg_hasco + rs1)) {
      if (*(reg_hasmn + rs1)) {
        // rs1 constraint has already minuend and cannot have another addend
        printf2((uint64_t*) "%s: detected invalid minuend expression in operand of addi at %x", selfieName, (uint64_t*) pc);
        printSourceLineNumberOfInstruction(pc - entryPoint);
        println();

        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      } else
        // rd inherits rs1 constraint
        setConstraint(rd, *(reg_hasco + rs1), *(reg_vaddr + rs1), 0, *(reg_colos + rs1) + imm, *(reg_coups + rs1) + imm);
    } else
      // rd has no constraint if rs1 has none
      setConstraint(rd, 0, 0, 0, 0, 0);
  }
}

void print_add_sub_mul_divu_remu_sltu(uint64_t *mnemonics) {
  printInstructionContext();
  printf4((uint64_t*) "%s %s,%s,%s", mnemonics, getRegisterName(rd), getRegisterName(rs1), getRegisterName(rs2));
}

void print_add_sub_mul_divu_remu_sltu_before() {
  print((uint64_t*) ": ");
  printRegisterValue(rs1);
  print((uint64_t*) ",");
  printRegisterValue(rs2);
  print((uint64_t*) " |- ");
  printRegisterValue(rd);
}

void do_add() {
  if (rd != REG_ZR)
    // semantics of add
    *(registers + rd) = *(registers + rs1) + *(registers + rs2);

  pc = pc + INSTRUCTIONSIZE;

  ic_add = ic_add + 1;
}

void constrain_add() {
  if (rd != REG_ZR) {
    if (*(reg_typ + rs1)) {
      if (*(reg_typ + rs2)) {
        // adding two pointers is undefined
        printf2((uint64_t*) "%s: undefined addition of two pointers at %x", selfieName, (uint64_t*) pc);
        printSourceLineNumberOfInstruction(pc - entryPoint);
        println();

        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }

      *(reg_typ + rd) = *(reg_typ + rs1);

      *(reg_los + rd) = *(reg_los + rs1);
      *(reg_ups + rd) = *(reg_ups + rs1);

      // rd has no constraint if rs1 is memory range
      setConstraint(rd, 0, 0, 0, 0, 0);

      return;
    } else if (*(reg_typ + rs2)) {
      *(reg_typ + rd) = *(reg_typ + rs2);

      *(reg_los + rd) = *(reg_los + rs2);
      *(reg_ups + rd) = *(reg_ups + rs2);

      // rd has no constraint if rs2 is memory range
      setConstraint(rd, 0, 0, 0, 0, 0);

      return;
    }

    *(reg_typ + rd) = 0;

    // interval semantics of add
    if (combinedCardinality(*(reg_los + rs1), *(reg_ups + rs1), *(reg_los + rs2), *(reg_ups + rs2)) == 0) {
      *(reg_los + rd) = 0;
      *(reg_ups + rd) = UINT64_MAX;
    } else {
      *(reg_los + rd) = *(reg_los + rs1) + *(reg_los + rs2);
      *(reg_ups + rd) = *(reg_ups + rs1) + *(reg_ups + rs2);
    }

    if (*(reg_hasco + rs1)) {
      if (*(reg_hasco + rs2))
        // we cannot keep track of more than one constraint for add but
        // need to warn about their earlier presence if used in comparisons
        setConstraint(rd, *(reg_hasco + rs1) + *(reg_hasco + rs2), 0, 0, 0, 0);
      else if (*(reg_hasmn + rs1)) {
        // rs1 constraint has already minuend and cannot have another addend
        printf2((uint64_t*) "%s: detected invalid minuend expression in left operand of add at %x", selfieName, (uint64_t*) pc);
        printSourceLineNumberOfInstruction(pc - entryPoint);
        println();

        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      } else
        // rd inherits rs1 constraint since rs2 has none
        setConstraint(rd, *(reg_hasco + rs1), *(reg_vaddr + rs1), 0, *(reg_colos + rs1) + *(reg_los + rs2), *(reg_coups + rs1) + *(reg_ups + rs2));
    } else if (*(reg_hasco + rs2)) {
      if (*(reg_hasmn + rs2)) {
        // rs2 constraint has already minuend and cannot have another addend
        printf2((uint64_t*) "%s: detected invalid minuend expression in right operand of add at %x", selfieName, (uint64_t*) pc);
        printSourceLineNumberOfInstruction(pc - entryPoint);
        println();

        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      } else
        // rd inherits rs2 constraint since rs1 has none
        setConstraint(rd, *(reg_hasco + rs2), *(reg_vaddr + rs2), 0, *(reg_los + rs1) + *(reg_colos + rs2), *(reg_ups + rs1) + *(reg_coups + rs2));
    } else
      // rd has no constraint if both rs1 and rs2 have no constraints
      setConstraint(rd, 0, 0, 0, 0, 0);
  }
}

void do_sub() {
  if (rd != REG_ZR)
    // semantics of sub
    *(registers + rd) = *(registers + rs1) - *(registers + rs2);

  pc = pc + INSTRUCTIONSIZE;

  ic_sub = ic_sub + 1;
}

void constrain_sub() {
  uint64_t sub_los;
  uint64_t sub_ups;

  if (rd != REG_ZR) {
    if (*(reg_typ + rs1)) {
      if (*(reg_typ + rs2)) {
        if (*(reg_los + rs1) == *(reg_los + rs2))
          if (*(reg_ups + rs1) == *(reg_ups + rs2)) {
            *(reg_typ + rd) = 0;

            *(reg_los + rd) = *(registers + rd);
            *(reg_ups + rd) = *(registers + rd);

            // rd has no constraint if rs1 and rs2 are memory range
            setConstraint(rd, 0, 0, 0, 0, 0);

            return;
          }

        // subtracting incompatible pointers
        throwException(EXCEPTION_INVALIDADDRESS, 0);

        return;
      } else {
        *(reg_typ + rd) = *(reg_typ + rs1);

        *(reg_los + rd) = *(reg_los + rs1);
        *(reg_ups + rd) = *(reg_ups + rs1);

        // rd has no constraint if rs1 is memory range
        setConstraint(rd, 0, 0, 0, 0, 0);

        return;
      }
    } else if (*(reg_typ + rs2)) {
      *(reg_typ + rd) = *(reg_typ + rs2);

      *(reg_los + rd) = *(reg_los + rs2);
      *(reg_ups + rd) = *(reg_ups + rs2);

      // rd has no constraint if rs2 is memory range
      setConstraint(rd, 0, 0, 0, 0, 0);

      return;
    }

    *(reg_typ + rd) = 0;

    // interval semantics of sub
    if (combinedCardinality(*(reg_los + rs1), *(reg_ups + rs1), *(reg_los + rs2), *(reg_ups + rs2)) == 0) {
      *(reg_los + rd) = 0;
      *(reg_ups + rd) = UINT64_MAX;
    } else {
      // use temporary variables since rd may be rs1 or rs2
      sub_los = *(reg_los + rs1) - *(reg_ups + rs2);
      sub_ups = *(reg_ups + rs1) - *(reg_los + rs2);

      *(reg_los + rd) = sub_los;
      *(reg_ups + rd) = sub_ups;
    }

    if (*(reg_hasco + rs1)) {
      if (*(reg_hasco + rs2))
        // we cannot keep track of more than one constraint for sub but
        // need to warn about their earlier presence if used in comparisons
        setConstraint(rd, *(reg_hasco + rs1) + *(reg_hasco + rs2), 0, 0, 0, 0);
      else if (*(reg_hasmn + rs1)) {
        // rs1 constraint has already minuend and cannot have another subtrahend
        printf2((uint64_t*) "%s: detected invalid minuend expression in left operand of sub at %x", selfieName, (uint64_t*) pc);
        printSourceLineNumberOfInstruction(pc - entryPoint);
        println();

        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      } else
        // rd inherits rs1 constraint since rs2 has none
        setConstraint(rd, *(reg_hasco + rs1), *(reg_vaddr + rs1), 0, *(reg_colos + rs1) - *(reg_ups + rs2), *(reg_coups + rs1) - *(reg_los + rs2));
    } else if (*(reg_hasco + rs2)) {
      if (*(reg_hasmn + rs2)) {
        // rs2 constraint has already minuend and cannot have another minuend
        printf2((uint64_t*) "%s: detected invalid minuend expression in right operand of sub at %x", selfieName, (uint64_t*) pc);
        printSourceLineNumberOfInstruction(pc - entryPoint);
        println();

        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      } else
        // rd inherits rs2 constraint since rs1 has none
        setConstraint(rd, *(reg_hasco + rs2), *(reg_vaddr + rs2), 1, *(reg_los + rs1) - *(reg_coups + rs2), *(reg_ups + rs1) - *(reg_colos + rs2));
    } else
      // rd has no constraint if both rs1 and rs2 have no constraints
      setConstraint(rd, 0, 0, 0, 0, 0);
  }
}

void do_mul() {
  if (rd != REG_ZR)
    // semantics of mul
    *(registers + rd) = *(registers + rs1) * *(registers + rs2);

  // TODO: 128-bit resolution currently not supported

  pc = pc + INSTRUCTIONSIZE;

  ic_mul = ic_mul + 1;
}

void constrain_mul() {
  if (rd != REG_ZR) {
    *(reg_typ + rd) = 0;

    // interval semantics of mul
    *(reg_los + rd) = *(reg_los + rs1) * *(reg_los + rs2);
    *(reg_ups + rd) = *(reg_ups + rs1) * *(reg_ups + rs2);

    if (*(reg_hasco + rs1)) {
      if (*(reg_hasco + rs2)) {
        // non-linear expressions are not supported
        printf2((uint64_t*) "%s: detected non-linear expression in mul at %x", selfieName, (uint64_t*) pc);
        printSourceLineNumberOfInstruction(pc - entryPoint);
        println();

        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      } else if (*(reg_hasmn + rs1)) {
        // rs1 constraint has already minuend and cannot have another multiplier
        printf2((uint64_t*) "%s: detected invalid minuend expression in left operand of mul at %x", selfieName, (uint64_t*) pc);
        printSourceLineNumberOfInstruction(pc - entryPoint);
        println();

        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      } else
        // rd inherits rs1 constraint since rs2 has none
        // assert: rs2 interval is singleton
        setConstraint(rd, *(reg_hasco + rs1), *(reg_vaddr + rs1), 0,
          *(reg_colos + rs1) + *(reg_los + rs1) * (*(reg_los + rs2) - 1), *(reg_coups + rs1) + *(reg_ups + rs1) * (*(reg_ups + rs2) - 1));
    } else if (*(reg_hasco + rs2)) {
      if (*(reg_hasmn + rs2)) {
        // rs2 constraint has already minuend and cannot have another multiplicand
        printf2((uint64_t*) "%s: detected invalid minuend expression in right operand of mul at %x", selfieName, (uint64_t*) pc);
        printSourceLineNumberOfInstruction(pc - entryPoint);
        println();

        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      } else
        // rd inherits rs2 constraint since rs1 has none
        // assert: rs1 interval is singleton
        setConstraint(rd, *(reg_hasco + rs2), *(reg_vaddr + rs2), 0,
          (*(reg_los + rs1) - 1) * *(reg_los + rs2) + *(reg_colos + rs2),
          (*(reg_ups + rs1) - 1) * *(reg_ups + rs2) + *(reg_coups + rs2));
    } else
      // rd has no constraint if both rs1 and rs2 have no constraints
      setConstraint(rd, 0, 0, 0, 0, 0);
  }
}

void record_divu_remu() {
  // record even for division by zero
  recordState(*(registers + rd));
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
    throwException(EXCEPTION_DIVISIONBYZERO, 0);
}

void constrain_divu() {
  if (*(reg_los + rs2) != 0) {
    if (*(reg_ups + rs2) >= *(reg_los + rs2)) {
      // 0 is not in interval
      if (rd != REG_ZR) {
        *(reg_typ + rd) = 0;

        // interval semantics of divu
        *(reg_los + rd) = *(reg_los + rs1) / *(reg_los + rs2);
        *(reg_ups + rd) = *(reg_ups + rs1) / *(reg_ups + rs2);

        if (*(reg_hasco + rs1)) {
          if (*(reg_hasco + rs2)) {
            // non-linear expressions are not supported
            printf2((uint64_t*) "%s: detected non-linear expression in divu at %x", selfieName, (uint64_t*) pc);
            printSourceLineNumberOfInstruction(pc - entryPoint);
            println();

            exit(EXITCODE_SYMBOLICEXECUTIONERROR);
          } else if (*(reg_hasmn + rs1)) {
            // rs1 constraint has already minuend and cannot have another divisor
            printf2((uint64_t*) "%s: detected invalid minuend expression in left operand of divu at %x", selfieName, (uint64_t*) pc);
            printSourceLineNumberOfInstruction(pc - entryPoint);
            println();

            exit(EXITCODE_SYMBOLICEXECUTIONERROR);
          } else
            // rd inherits rs1 constraint since rs2 has none
            // assert: rs2 interval is singleton
            setConstraint(rd, *(reg_hasco + rs1), *(reg_vaddr + rs1), 0,
              *(reg_colos + rs1) -
                (*(reg_los + rs1) - *(reg_los + rs1) / *(reg_los + rs2)),
              *(reg_coups + rs1) -
                (*(reg_ups + rs1) - *(reg_ups + rs1) / *(reg_ups + rs2)));
        } else if (*(reg_hasco + rs2)) {
          if (*(reg_hasmn + rs2)) {
            // rs2 constraint has already minuend and cannot have another dividend
            printf2((uint64_t*) "%s: detected invalid minuend expression in right operand of divu at %x", selfieName, (uint64_t*) pc);
            printSourceLineNumberOfInstruction(pc - entryPoint);
            println();

            exit(EXITCODE_SYMBOLICEXECUTIONERROR);
          } else
            // rd inherits rs2 constraint since rs1 has none
            // assert: rs1 interval is singleton
            setConstraint(rd, *(reg_hasco + rs2), *(reg_vaddr + rs2), 0,
              *(reg_colos + rs2) -
                (*(reg_los + rs2) - *(reg_los + rs1) / *(reg_los + rs2)),
              *(reg_coups + rs2) -
                (*(reg_ups + rs2) - *(reg_ups + rs1) / *(reg_ups + rs2)));
        } else
          // rd has no constraint if both rs1 and rs2 have no constraints
          setConstraint(rd, 0, 0, 0, 0, 0);
      }
    } else
      throwException(EXCEPTION_DIVISIONBYZERO, 0);
  }
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
    throwException(EXCEPTION_DIVISIONBYZERO, 0);
}

void constrain_remu() {
  if (*(reg_los + rs2) != 0) {
    if (*(reg_ups + rs2) >= *(reg_los + rs2)) {
      // 0 is not in interval
      if (rd != REG_ZR) {
        *(reg_typ + rd) = 0;

        // interval semantics of remu
        *(reg_los + rd) = *(reg_los + rs1) % *(reg_los + rs2);
        *(reg_ups + rd) = *(reg_ups + rs1) % *(reg_ups + rs2);

        if (*(reg_hasco + rs1)) {
          if (*(reg_hasco + rs2)) {
            // non-linear expressions are not supported
            printf2((uint64_t*) "%s: detected non-linear expression in remu at %x", selfieName, (uint64_t*) pc);
            printSourceLineNumberOfInstruction(pc - entryPoint);
            println();

            exit(EXITCODE_SYMBOLICEXECUTIONERROR);
          } else if (*(reg_hasmn + rs1)) {
            // rs1 constraint has already minuend and cannot have another divisor
            printf2((uint64_t*) "%s: detected invalid minuend expression in left operand of remu at %x", selfieName, (uint64_t*) pc);
            printSourceLineNumberOfInstruction(pc - entryPoint);
            println();

            exit(EXITCODE_SYMBOLICEXECUTIONERROR);
          } else
            // rd inherits rs1 constraint since rs2 has none
            // assert: rs2 interval is singleton
            setConstraint(rd, *(reg_hasco + rs1), *(reg_vaddr + rs1), 0,
              *(reg_colos + rs1) -
                (*(reg_los + rs1) - *(reg_los + rs1) % *(reg_los + rs2)),
              *(reg_coups + rs1) -
                (*(reg_ups + rs1) - *(reg_ups + rs1) % *(reg_ups + rs2)));
        } else if (*(reg_hasco + rs2)) {
          if (*(reg_hasmn + rs2)) {
            // rs2 constraint has already minuend and cannot have another dividend
            printf2((uint64_t*) "%s: detected invalid minuend expression in right operand of remu at %x", selfieName, (uint64_t*) pc);
            printSourceLineNumberOfInstruction(pc - entryPoint);
            println();

            exit(EXITCODE_SYMBOLICEXECUTIONERROR);
          } else
            // rd inherits rs2 constraint since rs1 has none
            // assert: rs1 interval is singleton
            setConstraint(rd, *(reg_hasco + rs2), *(reg_vaddr + rs2), 0,
              *(reg_colos + rs2) -
                (*(reg_los + rs2) - *(reg_los + rs1) % *(reg_los + rs2)),
              *(reg_coups + rs2) -
                (*(reg_ups + rs2) - *(reg_ups + rs1) % *(reg_ups + rs2)));
        } else
          // rd has no constraint if both rs1 and rs2 have no constraints
          setConstraint(rd, 0, 0, 0, 0, 0);
      }
    } else
      throwException(EXCEPTION_DIVISIONBYZERO, 0);
  }
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
    if (*(reg_hasco + rs1)) {
      if (*(reg_vaddr + rs1) == 0) {
        // constrained memory at vaddr 0 means that there is more than
        // one constrained memory location in the sltu operand
        printf3((uint64_t*) "%s: %d constrained memory locations in left sltu operand at %x", selfieName, (uint64_t*) *(reg_hasco + rs1), (uint64_t*) pc);
        printSourceLineNumberOfInstruction(pc - entryPoint);
        println();

        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }
    }

    if (*(reg_hasco + rs2)) {
      if (*(reg_vaddr + rs2) == 0) {
        // constrained memory at vaddr 0 means that there is more than
        // one constrained memory location in the sltu operand
        printf3((uint64_t*) "%s: %d constrained memory locations in right sltu operand at %x", selfieName, (uint64_t*) *(reg_hasco + rs2), (uint64_t*) pc);
        printSourceLineNumberOfInstruction(pc - entryPoint);
        println();

        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }
    }

    // take local copy of mrcc to make sure that alias check considers old mrcc
    if (*(reg_typ + rs1))
      if (*(reg_typ + rs2))
        createConstraints(*(registers + rs1), *(registers + rs1), *(registers + rs2), *(registers + rs2), mrcc, 0);
      else
        createConstraints(*(registers + rs1), *(registers + rs1), *(reg_los + rs2), *(reg_ups + rs2), mrcc, 0);
    else if (*(reg_typ + rs2))
      createConstraints(*(reg_los + rs1), *(reg_ups + rs1), *(registers + rs2), *(registers + rs2), mrcc, 0);
    else
      createConstraints(*(reg_los + rs1), *(reg_ups + rs1), *(reg_los + rs2), *(reg_ups + rs2), mrcc, 0);
  }

  pc = pc + INSTRUCTIONSIZE;

  ic_sltu = ic_sltu + 1;
}

void backtrack_sltu() {
  uint64_t vaddr;

  if (debug_symbolic) {
    printf1((uint64_t*) "%s: backtracking sltu ", selfieName);
    printSymbolicMemory(tc);
  }

  vaddr = *(vaddrs + tc);

  if (vaddr < NUMBEROFREGISTERS) {
    if (vaddr > 0) {
      // the register is identified by vaddr
      *(registers + vaddr) = *(values + tc);

      *(reg_typ + vaddr) = *(types + tc);

      *(reg_los + vaddr) = *(los + tc);
      *(reg_ups + vaddr) = *(ups + tc);

      setConstraint(vaddr, 0, 0, 0, 0, 0);

      // restoring mrcc
      mrcc = *(tcs + tc);

      if (vaddr != REG_FP)
        if (vaddr != REG_SP) {
          // stop backtracking and try next case
          pc = pc + INSTRUCTIONSIZE;

          ic_sltu = ic_sltu + 1;
        }
    }
  } else
    storeVirtualMemory(pt, vaddr, *(tcs + tc));

  efree();
}

void print_ld() {
  printInstructionContext();
  printf3((uint64_t*) "ld %s,%d(%s)", getRegisterName(rd), (uint64_t*) imm, getRegisterName(rs1));
}

void print_ld_before() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  print((uint64_t*) ": ");
  printRegisterHexadecimal(rs1);

  if (isValidVirtualAddress(vaddr))
    if (isVirtualAddressMapped(pt, vaddr)) {
      if (isSystemRegister(rd))
        printf2((uint64_t*) ",mem[%x]=%x |- ", (uint64_t*) vaddr, (uint64_t*) loadVirtualMemory(pt, vaddr));
      else
        printf2((uint64_t*) ",mem[%x]=%d |- ", (uint64_t*) vaddr, (uint64_t*) loadVirtualMemory(pt, vaddr));
      printRegisterValue(rd);

      return;
    }

  print((uint64_t*) " |-");
}

void print_ld_after(uint64_t vaddr) {
  if (isValidVirtualAddress(vaddr))
    if (isVirtualAddressMapped(pt, vaddr)) {
      print((uint64_t*) " -> ");
      printRegisterValue(rd);
      printf1((uint64_t*) "=mem[%x]", (uint64_t*) vaddr);
    }
}

void record_ld() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  if (isValidVirtualAddress(vaddr))
    if (isVirtualAddressMapped(pt, vaddr))
      recordState(*(registers + rd));
}

uint64_t do_ld() {
  uint64_t vaddr;
  uint64_t a;

  // load double word

  vaddr = *(registers + rs1) + imm;

  if (isValidVirtualAddress(vaddr)) {
    if (isVirtualAddressMapped(pt, vaddr)) {
      if (rd != REG_ZR)
        // semantics of ld
        *(registers + rd) = loadVirtualMemory(pt, vaddr);

      pc = pc + INSTRUCTIONSIZE;

      ic_ld = ic_ld + 1;

      // keep track of number of loads per instruction
      a = (pc - entryPoint) / INSTRUCTIONSIZE;

      *(loadsPerInstruction + a) = *(loadsPerInstruction + a) + 1;
    } else
      throwException(EXCEPTION_PAGEFAULT, getPageOfVirtualAddress(vaddr));
  } else
    throwException(EXCEPTION_INVALIDADDRESS, vaddr);

  return vaddr;
}

uint64_t constrain_ld() {
  uint64_t vaddr;
  uint64_t mrvc;
  uint64_t a;

  // load double word

  vaddr = *(registers + rs1) + imm;

  if (isSafeAddress(vaddr, rs1)) {
    if (isVirtualAddressMapped(pt, vaddr)) {
      if (rd != REG_ZR) {
        mrvc = loadSymbolicMemory(pt, vaddr);

        // interval semantics of ld
        *(registers + rd) = *(values + mrvc);

        *(reg_typ + rd) = *(types + mrvc);

        *(reg_los + rd) = *(los + mrvc);
        *(reg_ups + rd) = *(ups + mrvc);

        // assert: vaddr == *(vaddrs + mrvc)

        if (isSymbolicValue(*(reg_typ + rd), *(reg_los + rd), *(reg_ups + rd)))
          // vaddr is constrained by rd if value interval is not singleton
          setConstraint(rd, 1, vaddr, 0, 0, 0);
        else
          setConstraint(rd, 0, 0, 0, 0, 0);
      }

      pc = pc + INSTRUCTIONSIZE;

      ic_ld = ic_ld + 1;

      // keep track of number of loads per instruction
      a = (pc - entryPoint) / INSTRUCTIONSIZE;

      *(loadsPerInstruction + a) = *(loadsPerInstruction + a) + 1;
    } else
      throwException(EXCEPTION_PAGEFAULT, getPageOfVirtualAddress(vaddr));
  } else
    throwException(EXCEPTION_INVALIDADDRESS, vaddr);

  return vaddr;
}

void print_sd() {
  printInstructionContext();
  printf3((uint64_t*) "sd %s,%d(%s)", getRegisterName(rs2), (uint64_t*) imm, getRegisterName(rs1));
}

void print_sd_before() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  print((uint64_t*) ": ");
  printRegisterHexadecimal(rs1);

  if (isValidVirtualAddress(vaddr))
    if (isVirtualAddressMapped(pt, vaddr)) {
      print((uint64_t*) ",");
      printRegisterValue(rs2);
      if (isSystemRegister(rd))
        printf2((uint64_t*) " |- mem[%x]=%x", (uint64_t*) vaddr, (uint64_t*) loadVirtualMemory(pt, vaddr));
      else
        printf2((uint64_t*) " |- mem[%x]=%d", (uint64_t*) vaddr, (uint64_t*) loadVirtualMemory(pt, vaddr));

      return;
    }

  print((uint64_t*) " |-");
}

void print_sd_after(uint64_t vaddr) {
  if (isValidVirtualAddress(vaddr))
    if (isVirtualAddressMapped(pt, vaddr)) {
      printf1((uint64_t*) " -> mem[%x]=", (uint64_t*) vaddr);
      printRegisterValue(rs2);
    }
}

void record_sd() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  if (isValidVirtualAddress(vaddr))
    if (isVirtualAddressMapped(pt, vaddr))
      recordState(loadVirtualMemory(pt, vaddr));
}

uint64_t do_sd() {
  uint64_t vaddr;
  uint64_t a;

  // store double word

  vaddr = *(registers + rs1) + imm;

  if (isValidVirtualAddress(vaddr)) {
    if (isVirtualAddressMapped(pt, vaddr)) {
      // semantics of sd
      storeVirtualMemory(pt, vaddr, *(registers + rs2));

      pc = pc + INSTRUCTIONSIZE;

      ic_sd = ic_sd + 1;

      // keep track of number of stores per instruction
      a = (pc - entryPoint) / INSTRUCTIONSIZE;

      *(storesPerInstruction + a) = *(storesPerInstruction + a) + 1;
    } else
      throwException(EXCEPTION_PAGEFAULT, getPageOfVirtualAddress(vaddr));
  } else
    throwException(EXCEPTION_INVALIDADDRESS, vaddr);

  return vaddr;
}

uint64_t constrain_sd() {
  uint64_t vaddr;
  uint64_t a;

  // store double word

  vaddr = *(registers + rs1) + imm;

  if (isSafeAddress(vaddr, rs1)) {
    if (isVirtualAddressMapped(pt, vaddr)) {
      // interval semantics of sd
      if (*(reg_hasco + rs2)) {
        if (*(reg_vaddr + rs2) == 0) {
          // constrained memory at vaddr 0 means that there is more than
          // one constrained memory location in the sd operand
          printf3((uint64_t*) "%s: %d constrained memory locations in sd operand at %x", selfieName, (uint64_t*) *(reg_hasco + rs2), (uint64_t*) pc);
          printSourceLineNumberOfInstruction(pc - entryPoint);
          println();

          //exit(EXITCODE_SYMBOLICEXECUTIONERROR);
        }
      }

      storeSymbolicMemory(pt, vaddr, *(registers + rs2), *(reg_typ + rs2), *(reg_los + rs2), *(reg_ups + rs2), mrcc);

      pc = pc + INSTRUCTIONSIZE;

      ic_sd = ic_sd + 1;

      // keep track of number of stores per instruction
      a = (pc - entryPoint) / INSTRUCTIONSIZE;

      *(storesPerInstruction + a) = *(storesPerInstruction + a) + 1;
    } else
      throwException(EXCEPTION_PAGEFAULT, getPageOfVirtualAddress(vaddr));
  } else
    throwException(EXCEPTION_INVALIDADDRESS, vaddr);

  return vaddr;
}

void backtrack_sd() {
  if (debug_symbolic) {
    printf1((uint64_t*) "%s: backtracking sd ", selfieName);
    printSymbolicMemory(tc);
  }

  storeVirtualMemory(pt, *(vaddrs + tc), *(tcs + tc));

  efree();
}

void undo_sd() {
  uint64_t vaddr;

  vaddr = *(registers + rs1) + imm;

  storeVirtualMemory(pt, vaddr, *(values + (tc % maxReplayLength)));
}

void print_beq() {
  printInstructionContext();
  printf4((uint64_t*) "beq %s,%s,%d[%x]", getRegisterName(rs1), getRegisterName(rs2), (uint64_t*) signedDivision(imm, INSTRUCTIONSIZE), (uint64_t*) (pc + imm));
}

void print_beq_before() {
  print((uint64_t*) ": ");
  printRegisterValue(rs1);
  print((uint64_t*) ",");
  printRegisterValue(rs2);
  printf1((uint64_t*) " |- $pc=%x", (uint64_t*) pc);
}

void print_beq_after() {
  printf1((uint64_t*) " -> $pc=%x", (uint64_t*) pc);
}

void record_beq() {
  recordState(0);
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

void print_jal() {
  printInstructionContext();
  printf3((uint64_t*) "jal %s,%d[%x]", getRegisterName(rd), (uint64_t*) signedDivision(imm, INSTRUCTIONSIZE), (uint64_t*) (pc + imm));
}

void print_jal_before() {
  print((uint64_t*) ": |- ");
  if (rd != REG_ZR) {
    printRegisterHexadecimal(rd);
    print((uint64_t*) ",");
  }
  printf1((uint64_t*) "$pc=%x", (uint64_t*) pc);
}

void print_jal_jalr_after() {
  print_beq_after();
  if (rd != REG_ZR) {
    print((uint64_t*) ",");
    printRegisterHexadecimal(rd);
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

    // keep track of number of procedure calls
    calls = calls + 1;

    a = (pc - entryPoint) / INSTRUCTIONSIZE;

    *(callsPerProcedure + a) = *(callsPerProcedure + a) + 1;
  } else if (signedLessThan(imm, 0)) {
    // just jump backwards to check for another loop iteration
    pc = pc + imm;

    // keep track of number of loop iterations
    iterations = iterations + 1;

    a = (pc - entryPoint) / INSTRUCTIONSIZE;

    *(iterationsPerLoop + a) = *(iterationsPerLoop + a) + 1;
  } else
    // just jump forward
    pc = pc + imm;

  ic_jal = ic_jal + 1;
}

void constrain_jal_jalr() {
  if (rd != REG_ZR) {
    *(reg_los + rd) = *(registers + rd);
    *(reg_ups + rd) = *(registers + rd);
  }
}

void print_jalr() {
  printInstructionContext();
  printf3((uint64_t*) "jalr %s,%d(%s)", getRegisterName(rd), (uint64_t*) signedDivision(imm, INSTRUCTIONSIZE), getRegisterName(rs1));
}

void print_jalr_before() {
  print((uint64_t*) ": ");
  printRegisterHexadecimal(rs1);
  print((uint64_t*) " |- ");
  if (rd != REG_ZR) {
    printRegisterHexadecimal(rd);
    print((uint64_t*) ",");
  }
  printf1((uint64_t*) "$pc=%x", (uint64_t*) pc);
}

void do_jalr() {
  uint64_t next_pc;

  // jump and link register

  if (rd == REG_ZR)
    // fast path: just return by jumping rs1-relative with LSB reset
    pc = leftShift(rightShift(*(registers + rs1) + imm, 1), 1);
  else {
    // slow path: first prepare jump, then link, just in case rd == rs1

    // prepare jump with LSB reset
    next_pc = leftShift(rightShift(*(registers + rs1) + imm, 1), 1);

    // link to next instruction
    *(registers + rd) = pc + INSTRUCTIONSIZE;

    // jump
    pc = next_pc;
  }

  ic_jalr = ic_jalr + 1;
}

void print_ecall() {
  printInstructionContext();
  print((uint64_t*) "ecall");
}

void print_ecall_before() {
  print((uint64_t*) ": |- ");
  printRegisterHexadecimal(REG_A0);
}

void print_ecall_after() {
  print((uint64_t*) " -> ");
  printRegisterHexadecimal(REG_A0);
}

void record_ecall() {
  // TODO: record all side effects
  recordState(*(registers + REG_A0));
}

void do_ecall() {
  ic_ecall = ic_ecall + 1;

  if (redo) {
    // TODO: redo all side effects
    *(registers + REG_A0) = *(values + (tc % maxReplayLength));

    pc = pc + INSTRUCTIONSIZE;
  } else if (*(registers + REG_A7) == SYSCALL_SWITCH)
    if (record) {
      printf1((uint64_t*) "%s: context switching during recording is unsupported\n", selfieName);

      exit(EXITCODE_BADARGUMENTS);
    } else if (symbolic) {
      printf1((uint64_t*) "%s: context switching during symbolic execution is unsupported\n", selfieName);

      exit(EXITCODE_BADARGUMENTS);
    } else {
      pc = pc + INSTRUCTIONSIZE;

      implementSwitch();
    }
  else
    // all system calls other than switch are handled by exception
    throwException(EXCEPTION_SYSCALL, 0);
}

void undo_ecall() {
  uint64_t a0;

  a0 = *(registers + REG_A0);

  // TODO: undo all side effects
  *(registers + REG_A0) = *(values + (tc % maxReplayLength));

  // save register a0 for redoing system call
  *(values + (tc % maxReplayLength)) = a0;
}

void backtrack_ecall() {
  if (debug_symbolic) {
    printf1((uint64_t*) "%s: backtracking ecall ", selfieName);
    printSymbolicMemory(tc);
  }

  if (*(vaddrs + tc) == 0) {
    // backtracking malloc
    if (getProgramBreak(currentContext) == *(los + tc) + *(ups + tc))
      setProgramBreak(currentContext, *(los + tc));
    else {
      printf1((uint64_t*) "%s: malloc backtracking error at ", selfieName);
      printSymbolicMemory(tc);
      printf4((uint64_t*) " with current program break %x unequal %x which is previous program break %x plus size %d\n",
        (uint64_t*) getProgramBreak(currentContext),
        (uint64_t*) (*(los + tc) + *(ups + tc)),
        (uint64_t*) *(los + tc),
        (uint64_t*) *(ups + tc));

      exit(EXITCODE_SYMBOLICEXECUTIONERROR);
    }
  } else {
    // backtracking read
    rc = rc + 1;

    // record value, lower and upper bound
    *(read_values + rc) = *(values + tc);

    *(read_los + rc) = *(los + tc);
    *(read_ups + rc) = *(ups + tc);

    storeVirtualMemory(pt, *(vaddrs + tc), *(tcs + tc));
  }

  efree();
}

// -----------------------------------------------------------------
// -------------------------- REPLAY ENGINE ------------------------
// -----------------------------------------------------------------

void recordState(uint64_t value) {
  *(pcs + (tc % maxReplayLength))    = pc;
  *(values + (tc % maxReplayLength)) = value;

  tc = tc + 1;
}

void replayTrace() {
  uint64_t traceLength;
  uint64_t tl;

  if (tc < maxReplayLength)
    traceLength = tc;
  else
    traceLength = maxReplayLength;

  record = 0;
  undo   = 1;

  tl = traceLength;

  // undo traceLength number of instructions
  while (tl > 0) {
    tc = tc - 1;

    pc = *(pcs + (tc % maxReplayLength));

    fetch();
    decode_execute();

    tl = tl - 1;
  }

  undo = 0;
  redo = 1;

  disassemble = 1;

  tl = traceLength;

  // redo traceLength number of instructions
  while (tl > 0) {
    // assert: pc == *(pcs + (tc % maxReplayLength))

    fetch();
    decode_execute();

    tc = tc + 1;
    tl = tl - 1;
  }

  disassemble = 0;

  redo   = 0;
  record = 1;
}

// -----------------------------------------------------------------
// ------------------- SYMBOLIC EXECUTION ENGINE -------------------
// -----------------------------------------------------------------

void printSymbolicMemory(uint64_t svc) {
  printf3((uint64_t*) "@%d{@%d@%x", (uint64_t*) svc, (uint64_t*) *(tcs + svc), (uint64_t*) *(pcs + svc));
  if (*(pcs + svc) >= entryPoint)
    printSourceLineNumberOfInstruction(*(pcs + svc) - entryPoint);
  if (*(vaddrs + svc) == 0) {
    printf3((uint64_t*) ";%x=%x=malloc(%d)}\n", (uint64_t*) *(values + svc), (uint64_t*) *(los + svc), (uint64_t*) *(ups + svc));
    return;
  } else if (*(vaddrs + svc) < NUMBEROFREGISTERS)
    printf2((uint64_t*) ";%s=%d", getRegisterName(*(vaddrs + svc)), (uint64_t*) *(values + svc));
  else
    printf2((uint64_t*) ";%x=%d", (uint64_t*) *(vaddrs + svc), (uint64_t*) *(values + svc));
  if (*(types + svc))
    if (*(los + svc) == *(ups + svc))
      printf1((uint64_t*) "(%d)}\n", (uint64_t*) *(los + svc));
    else
      printf2((uint64_t*) "(%d,%d)}\n", (uint64_t*) *(los + svc), (uint64_t*) *(ups + svc));
  else if (*(los + svc) == *(ups + svc))
    printf1((uint64_t*) "[%d]}\n", (uint64_t*) *(los + svc));
  else
    printf2((uint64_t*) "[%d,%d]}\n", (uint64_t*) *(los + svc), (uint64_t*) *(ups + svc));
}

uint64_t cardinality(uint64_t lo, uint64_t up) {
  // there are 2^64 values if the result is 0
  return up - lo + 1;
}

uint64_t combinedCardinality(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2) {
  uint64_t c1;
  uint64_t c2;

  c1 = cardinality(lo1, up1);
  c2 = cardinality(lo2, up2);

  if (c1 + c2 <= c1)
    // there are at least 2^64 values
    return 0;
  else if (c1 + c2 <= c2)
    // there are at least 2^64 values
    return 0;
  else
    return c1 + c2;
}

uint64_t isSymbolicValue(uint64_t type, uint64_t lo, uint64_t up) {
  if (type)
    // memory range
    return 0;
  else if (lo == up)
    // singleton interval
    return 0;
  else
    // non-singleton interval
    return 1;
}

uint64_t isSafeAddress(uint64_t vaddr, uint64_t reg) {
  if (*(reg_typ + reg)) {
    if (vaddr < *(reg_los + reg))
      // memory access below start address of mallocated block
      return 0;
    else if (vaddr - *(reg_los + reg) >= *(reg_ups + reg))
      // memory access above end address of mallocated block
      return 0;
    else
      return 1;
  } else if (*(reg_los + reg) == *(reg_ups + reg))
    return 1;
  else {
    printf2((uint64_t*) "%s: detected unsupported symbolic access of memory interval at %x", selfieName, (uint64_t*) pc);
    printSourceLineNumberOfInstruction(pc - entryPoint);
    println();

    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

uint64_t loadSymbolicMemory(uint64_t* pt, uint64_t vaddr) {
  uint64_t mrvc;

  // assert: vaddr is valid and mapped
  mrvc = loadVirtualMemory(pt, vaddr);

  if (mrvc <= tc)
    return mrvc;
  else {
    printf4((uint64_t*) "%s: detected most recent value counter %d at vaddr %x greater than current trace counter %d\n", selfieName, (uint64_t*) mrvc, (uint64_t*) vaddr, (uint64_t*) tc);

    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }
}

uint64_t isTraceSpaceAvailable() {
  return tc + 1 < maxTraceLength;
}

void ealloc() {
  tc = tc + 1;
}

void efree() {
  // assert: tc > 0
  tc = tc - 1;
}

void storeSymbolicMemory(uint64_t* pt, uint64_t vaddr, uint64_t value, uint64_t type, uint64_t lo, uint64_t up, uint64_t trb) {
  uint64_t mrvc;

  if (vaddr == 0)
    // tracking program break and size for malloc
    mrvc = 0;
  else if (vaddr < NUMBEROFREGISTERS)
    // tracking a register value for sltu
    mrvc = mrcc;
  else {
    // assert: vaddr is valid and mapped
    mrvc = loadSymbolicMemory(pt, vaddr);

    if (value == *(values + mrvc))
      if (type == *(types + mrvc))
        if (lo == *(los + mrvc))
          if (up == *(ups + mrvc))
            // prevent tracking identical updates
            return;
  }

  if (trb < mrvc) {
    // current value at vaddr does not need to be tracked,
    // just overwrite it in the trace
    *(values + mrvc) = value;

    *(types + mrvc) = type;

    *(los + mrvc) = lo;
    *(ups + mrvc) = up;

    // assert: vaddr == *(vaddrs + mrvc)

    if (debug_symbolic) {
      printf1((uint64_t*) "%s: overwriting ", selfieName);
      printSymbolicMemory(mrvc);
    }
  } else if (isTraceSpaceAvailable()) {
    // current value at vaddr is from before most recent branch,
    // track that value by creating a new trace event
    ealloc();

    *(pcs + tc) = pc;
    *(tcs + tc) = mrvc;

    *(values + tc) = value;

    *(types + tc) = type;

    *(los + tc) = lo;
    *(ups + tc) = up;

    *(vaddrs + tc) = vaddr;

    if (vaddr < NUMBEROFREGISTERS) {
      if (vaddr > 0)
        // register tracking marks most recent constraint
        mrcc = tc;
    } else
      // assert: vaddr is valid and mapped
      storeVirtualMemory(pt, vaddr, tc);

    if (debug_symbolic) {
      printf1((uint64_t*) "%s: storing ", selfieName);
      printSymbolicMemory(tc);
    }
  } else
    throwException(EXCEPTION_MAXTRACE, 0);
}

void storeConstrainedMemory(uint64_t vaddr, uint64_t lo, uint64_t up, uint64_t trb) {
  uint64_t mrvc;

  if (vaddr >= getProgramBreak(currentContext))
    if (vaddr < *(registers + REG_SP))
      // do not constrain free memory
      return;

  mrvc = loadVirtualMemory(pt, vaddr);

  if (mrvc < trb) {
    // we do not support potentially aliased constrained memory
    printf1((uint64_t*) "%s: detected potentially aliased constrained memory\n", selfieName);

    exit(EXITCODE_SYMBOLICEXECUTIONERROR);
  }

  // always track constrained memory by using tc as most recent branch
  storeSymbolicMemory(pt, vaddr, lo, 0, lo, up, tc);
}

void storeRegisterMemory(uint64_t reg, uint64_t value) {
  // always track register memory by using tc as most recent branch
  storeSymbolicMemory(pt, reg, value, 0, value, value, tc);
}

void constrainMemory(uint64_t reg, uint64_t lo, uint64_t up, uint64_t trb) {
  if (*(reg_hasco + reg)) {
    if (*(reg_hasmn + reg))
      storeConstrainedMemory(*(reg_vaddr + reg), *(reg_colos + reg) - lo, *(reg_coups + reg) - up, trb);
    else
      storeConstrainedMemory(*(reg_vaddr + reg), lo - *(reg_colos + reg), up - *(reg_coups + reg), trb);
  }
}

void setConstraint(uint64_t reg, uint64_t hasco, uint64_t vaddr, uint64_t hasmn, uint64_t colos, uint64_t coups) {
  *(reg_hasco + reg) = hasco;
  *(reg_vaddr + reg) = vaddr;
  *(reg_hasmn + reg) = hasmn;
  *(reg_colos + reg) = colos;
  *(reg_coups + reg) = coups;
}

void takeBranch(uint64_t b, uint64_t howManyMore) {
  if (howManyMore > 0) {
    // record that we need to set rd to true
    storeRegisterMemory(rd, b);

    // record frame and stack pointer
    storeRegisterMemory(REG_FP, *(registers + REG_FP));
    storeRegisterMemory(REG_SP, *(registers + REG_SP));
  } else {
    *(registers + rd) = b;

    *(reg_typ + rd) = 0;

    *(reg_los + rd) = b;
    *(reg_ups + rd) = b;

    setConstraint(rd, 0, 0, 0, 0, 0);
  }
}

void createConstraints(uint64_t lo1, uint64_t up1, uint64_t lo2, uint64_t up2, uint64_t trb, uint64_t howManyMore) {
  if (lo1 <= up1) {
    // rs1 interval is not wrapped around
    if (lo2 <= up2) {
      // both rs1 and rs2 intervals are not wrapped around
      if (up1 < lo2) {
        // rs1 interval is strictly less than rs2 interval
        constrainMemory(rs1, lo1, up1, trb);
        constrainMemory(rs2, lo2, up2, trb);

        takeBranch(1, howManyMore);
      } else if (up2 <= lo1) {
        // rs2 interval is less than or equal to rs1 interval
        constrainMemory(rs1, lo1, up1, trb);
        constrainMemory(rs2, lo2, up2, trb);

        takeBranch(0, howManyMore);
      } else if (lo2 == up2) {
        // rs2 interval is a singleton

        // construct constraint for false case
        constrainMemory(rs1, lo2, up1, trb);
        constrainMemory(rs2, lo2, up2, trb);

        // record that we need to set rd to false
        storeRegisterMemory(rd, 0);

        // record frame and stack pointer
        storeRegisterMemory(REG_FP, *(registers + REG_FP));
        storeRegisterMemory(REG_SP, *(registers + REG_SP));

        // construct constraint for true case
        constrainMemory(rs1, lo1, lo2 - 1, trb);
        constrainMemory(rs2, lo2, up2, trb);

        takeBranch(1, howManyMore);
      } else if (lo1 == up1) {
        // rs1 interval is a singleton

        // construct constraint for false case
        constrainMemory(rs1, lo1, up1, trb);
        constrainMemory(rs2, lo2, lo1, trb);

        // record that we need to set rd to false
        storeRegisterMemory(rd, 0);

        // record frame and stack pointer
        storeRegisterMemory(REG_FP, *(registers + REG_FP));
        storeRegisterMemory(REG_SP, *(registers + REG_SP));

        // construct constraint for true case
        constrainMemory(rs1, lo1, up1, trb);
        constrainMemory(rs2, lo1 + 1, up2, trb);

        takeBranch(1, howManyMore);
      } else {
        // we cannot handle non-singleton interval intersections in comparison
        printf1((uint64_t*) "%s: detected non-singleton interval intersection\n", selfieName);

        exit(EXITCODE_SYMBOLICEXECUTIONERROR);
      }
    } else {
      // rs1 interval is not wrapped around but rs2 is

      // unwrap rs2 interval and use higher portion first
      createConstraints(lo1, up1, lo2, UINT64_MAX, trb, 1);

      // then use lower portion of rs2 interval
      createConstraints(lo1, up1, 0, up2, trb, 0);
    }
  } else if (lo2 <= up2) {
    // rs2 interval is not wrapped around but rs1 is

    // unwrap rs1 interval and use higher portion first
    createConstraints(lo1, UINT64_MAX, lo2, up2, trb, 1);

    // then use lower portion of rs1 interval
    createConstraints(0, up1, lo2, up2, trb, 0);
  } else {
    // both rs1 and rs2 intervals are wrapped around

    // unwrap rs1 and rs2 intervals and use higher portions
    createConstraints(lo1, UINT64_MAX, lo2, UINT64_MAX, trb, 3);

    // use higher portion of rs1 interval and lower portion of rs2 interval
    createConstraints(lo1, UINT64_MAX, 0, up2, trb, 2);

    // use lower portions of rs1 and rs2 intervals
    createConstraints(0, up1, 0, up2, trb, 1);

    // use lower portion of rs1 interval and higher portion of rs2 interval
    createConstraints(0, up1, lo2, UINT64_MAX, trb, 0);
  }
}

uint64_t fuzzLo(uint64_t value) {
  if (fuzz >= CPUBITWIDTH)
    return 0;
  else if (value > (twoToThePowerOf(fuzz) - 1) / 2)
    return value - (twoToThePowerOf(fuzz) - 1) / 2;
  else
    return 0;
}

uint64_t fuzzUp(uint64_t value) {
  if (fuzz >= CPUBITWIDTH)
    return UINT64_MAX;
  else if (UINT64_MAX - value < twoToThePowerOf(fuzz) / 2)
    return UINT64_MAX;
  else if (value > (twoToThePowerOf(fuzz) - 1) / 2)
    return value + twoToThePowerOf(fuzz) / 2;
  else
    return twoToThePowerOf(fuzz) - 1;
}

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void printRegisterHexadecimal(uint64_t reg) {
  printf2((uint64_t*) "%s=%x", getRegisterName(reg), (uint64_t*) *(registers + reg));
}

uint64_t isSystemRegister(uint64_t reg) {
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

void printRegisterValue(uint64_t reg) {
  if (isSystemRegister(reg))
    printRegisterHexadecimal(reg);
  else
    printf3((uint64_t*) "%s=%d(%x)", getRegisterName(reg), (uint64_t*) *(registers + reg), (uint64_t*) *(registers + reg));
}

void printException(uint64_t exception, uint64_t faultingPage) {
  print((uint64_t*) *(EXCEPTIONS + exception));

  if (exception == EXCEPTION_PAGEFAULT)
    printf1((uint64_t*) " at %p", (uint64_t*) faultingPage);
}

void throwException(uint64_t exception, uint64_t faultingPage) {
  if (getException(currentContext) != EXCEPTION_NOEXCEPTION)
    if (getException(currentContext) != exception) {
      printf2((uint64_t*) "%s: context %p throws ", selfieName, currentContext);
      printException(exception, faultingPage);
      print((uint64_t*) " exception in presence of ");
      printException(getException(currentContext), getFaultingPage(currentContext));
      print((uint64_t*) " exception\n");

      exit(EXITCODE_MULTIPLEEXCEPTIONERROR);
    }

  setException(currentContext, exception);
  setFaultingPage(currentContext, faultingPage);

  trap = 1;

  if (debug_exception) {
    printf2((uint64_t*) "%s: context %p throws ", selfieName, currentContext);
    printException(exception, faultingPage);
    print((uint64_t*) " exception\n");
  }
}

void fetch() {
  // assert: isValidVirtualAddress(pc) == 1
  // assert: isVirtualAddressMapped(pt, pc) == 1

  if (pc % REGISTERSIZE == 0)
    ir = getLowWord(loadVirtualMemory(pt, pc));
  else
    ir = getHighWord(loadVirtualMemory(pt, pc - INSTRUCTIONSIZE));
}

void decode_execute() {
  opcode = getOpcode(ir);

  if (opcode == OP_IMM) {
    decodeIFormat();

    if (funct3 == F3_ADDI) {
      if (debug) {
        if (record) {
          record_lui_addi_add_sub_mul_sltu_jal_jalr();
          do_addi();
        } else if (undo)
          undo_lui_addi_add_sub_mul_divu_remu_sltu_ld_jal_jalr();
        else if (disassemble) {
          print_addi();
          if (execute) {
            print_addi_before();
            do_addi();
            print_addi_add_sub_mul_divu_remu_sltu_after();
          }
          println();
        } else if (symbolic) {
          do_addi();
          constrain_addi();
        }
      } else
        do_addi();

      return;
    }
  } else if (opcode == OP_LD) {
    decodeIFormat();

    if (funct3 == F3_LD) {
      if (debug) {
        if (record) {
          record_ld();
          do_ld();
        } else if (undo)
          undo_lui_addi_add_sub_mul_divu_remu_sltu_ld_jal_jalr();
        else if (disassemble) {
          print_ld();
          if (execute) {
            print_ld_before();
            print_ld_after(do_ld());
          }
          println();
        } else if (symbolic)
          constrain_ld();
      } else
        do_ld();

      return;
    }
  } else if (opcode == OP_SD) {
    decodeSFormat();

    if (funct3 == F3_SD) {
      if (debug) {
        if (record) {
          record_sd();
          do_sd();
        } else if (undo)
          undo_sd();
        else if (disassemble) {
          print_sd();
          if (execute) {
            print_sd_before();
            print_sd_after(do_sd());
          }
          println();
        } else if (symbolic)
          constrain_sd();
        else if (backtrack)
          backtrack_sd();
      } else
        do_sd();

      return;
    }
  } else if (opcode == OP_OP) { // could be ADD, SUB, MUL, DIVU, REMU, SLTU
    decodeRFormat();

    if (funct3 == F3_ADD) { // = F3_SUB = F3_MUL
      if (funct7 == F7_ADD) {
        if (debug) {
          if (record) {
            record_lui_addi_add_sub_mul_sltu_jal_jalr();
            do_add();
          } else if (disassemble) {
            print_add_sub_mul_divu_remu_sltu((uint64_t*) "add");
            if (execute) {
              print_add_sub_mul_divu_remu_sltu_before();
              do_add();
              print_addi_add_sub_mul_divu_remu_sltu_after();
            }
            println();
          } else if (symbolic) {
            do_add();
            constrain_add();
          }
        } else
          do_add();

        return;
      } else if (funct7 == F7_SUB) {
        if (debug) {
          if (record) {
            record_lui_addi_add_sub_mul_sltu_jal_jalr();
            do_sub();
          } else if (undo)
            undo_lui_addi_add_sub_mul_divu_remu_sltu_ld_jal_jalr();
          else if (disassemble) {
            print_add_sub_mul_divu_remu_sltu((uint64_t*) "sub");
            if (execute) {
              print_add_sub_mul_divu_remu_sltu_before();
              do_sub();
              print_addi_add_sub_mul_divu_remu_sltu_after();
            }
            println();
          } else if (symbolic) {
            do_sub();
            constrain_sub();
          }
        } else
          do_sub();

        return;
      } else if (funct7 == F7_MUL) {
        if (debug) {
          if (record) {
            record_lui_addi_add_sub_mul_sltu_jal_jalr();
            do_mul();
          } else if (undo)
            undo_lui_addi_add_sub_mul_divu_remu_sltu_ld_jal_jalr();
          else if (disassemble) {
            print_add_sub_mul_divu_remu_sltu((uint64_t*) "mul");
            if (execute) {
              print_add_sub_mul_divu_remu_sltu_before();
              do_mul();
              print_addi_add_sub_mul_divu_remu_sltu_after();
            }
            println();
          } else if (symbolic) {
            do_mul();
            constrain_mul();
          }
        } else
          do_mul();

        return;
      }
    } else if (funct3 == F3_DIVU) {
      if (funct7 == F7_DIVU) {
        if (debug) {
          if (record) {
            record_divu_remu();
            do_divu();
          } else if (undo)
            undo_lui_addi_add_sub_mul_divu_remu_sltu_ld_jal_jalr();
          else if (disassemble) {
            print_add_sub_mul_divu_remu_sltu((uint64_t*) "divu");
            if (execute) {
              print_add_sub_mul_divu_remu_sltu_before();
              do_divu();
              print_addi_add_sub_mul_divu_remu_sltu_after();
            }
            println();
          } else if (symbolic) {
            do_divu();
            constrain_divu();
          }
        } else
          do_divu();

        return;
      }
    } else if (funct3 == F3_REMU) {
      if (funct7 == F7_REMU) {
        if (debug) {
          if (record) {
            record_divu_remu();
            do_remu();
          } else if (undo)
            undo_lui_addi_add_sub_mul_divu_remu_sltu_ld_jal_jalr();
          else if (disassemble) {
            print_add_sub_mul_divu_remu_sltu((uint64_t*) "remu");
            if (execute) {
              print_add_sub_mul_divu_remu_sltu_before();
              do_remu();
              print_addi_add_sub_mul_divu_remu_sltu_after();
            }
            println();
          } else if (symbolic) {
            do_remu();
            constrain_remu();
          }
        } else
          do_remu();

        return;
      }
    } else if (funct3 == F3_SLTU) {
      if (funct7 == F7_SLTU) {
        if (debug) {
          if (record) {
            record_lui_addi_add_sub_mul_sltu_jal_jalr();
            do_sltu();
          } else if (undo)
            undo_lui_addi_add_sub_mul_divu_remu_sltu_ld_jal_jalr();
          else if (disassemble) {
            print_add_sub_mul_divu_remu_sltu((uint64_t*) "sltu");
            if (execute) {
              print_add_sub_mul_divu_remu_sltu_before();
              do_sltu();
              print_addi_add_sub_mul_divu_remu_sltu_after();
            }
            println();
          } else if (symbolic)
            constrain_sltu();
          else if (backtrack)
            backtrack_sltu();
        } else
          do_sltu();

        return;
      }
    }
  } else if (opcode == OP_BRANCH) {
    decodeBFormat();

    if (funct3 == F3_BEQ) {
      if (debug) {
        if (record) {
          record_beq();
          do_beq();
        } if (disassemble) {
          print_beq();
          if (execute) {
            print_beq_before();
            do_beq();
            print_beq_after();
          }
          println();
        } else if (symbolic)
          do_beq();
      } else
        do_beq();

      return;
    }
  } else if (opcode == OP_JAL) {
    decodeJFormat();

    if (debug) {
      if (record) {
        record_lui_addi_add_sub_mul_sltu_jal_jalr();
        do_jal();
      } else if (undo)
        undo_lui_addi_add_sub_mul_divu_remu_sltu_ld_jal_jalr();
      else if (disassemble) {
        print_jal();
        if (execute) {
          print_jal_before();
          do_jal();
          print_jal_jalr_after();
        }
        println();
      } else if (symbolic) {
        do_jal();
        constrain_jal_jalr();
      }
    } else
      do_jal();

    return;
  } else if (opcode == OP_JALR) {
    decodeIFormat();

    if (funct3 == F3_JALR) {
      if (debug) {
        if (record) {
          record_lui_addi_add_sub_mul_sltu_jal_jalr();
          do_jalr();
        } else if (undo)
          undo_lui_addi_add_sub_mul_divu_remu_sltu_ld_jal_jalr();
        else if (disassemble) {
          print_jalr();
          if (execute) {
            print_jalr_before();
            do_jalr();
            print_jal_jalr_after();
          }
          println();
        } else if (symbolic) {
          do_jalr();
          constrain_jal_jalr();
        }
      } else
        do_jalr();

      return;
    }
  } else if (opcode == OP_LUI) {
    decodeUFormat();

    if (debug) {
      if (record) {
        record_lui_addi_add_sub_mul_sltu_jal_jalr();
        do_lui();
      } else if (undo)
        undo_lui_addi_add_sub_mul_divu_remu_sltu_ld_jal_jalr();
      else if (disassemble) {
        print_lui();
        if (execute) {
          print_lui_before();
          do_lui();
          print_lui_after();
        }
        println();
      } else if (symbolic) {
        do_lui();
        constrain_lui();
      }
    } else
      do_lui();

    return;
  } else if (opcode == OP_SYSTEM) {
    decodeIFormat();

    if (funct3 == F3_ECALL) {
      if (debug) {
        if (record) {
          record_ecall();
          do_ecall();
        } else if (undo)
          undo_ecall();
        else if (disassemble) {
          print_ecall();
          if (execute) {
            print_ecall_before();
            do_ecall();
            print_ecall_after();
          }
          println();
        } else if (symbolic)
          do_ecall();
        else if (backtrack)
          backtrack_ecall();
      } else
        do_ecall();

      return;
    }
  }

  if (execute)
    throwException(EXCEPTION_UNKNOWNINSTRUCTION, 0);
  else {
    //report the error on the console
    outputFD = 1;

    printf2((uint64_t*) "%s: unknown instruction with %x opcode detected\n", selfieName, (uint64_t*) opcode);

    exit(EXITCODE_UNKNOWNINSTRUCTION);
  }
}

void interrupt() {
  if (timer != TIMEROFF) {
    timer = timer - 1;

    if (timer == 0) {
      if (getException(currentContext) == EXCEPTION_NOEXCEPTION)
        // only throw exception if no other is pending
        // TODO: handle multiple pending exceptions
        throwException(EXCEPTION_TIMER, 0);
      else
        // trigger timer in the next interrupt cycle
        timer = 1;
    }
  }
}

uint64_t* runUntilException() {
  trap = 0;

  while (trap == 0) {
    fetch();
    decode_execute();
    interrupt();
  }

  trap = 0;

  return currentContext;
}

uint64_t instructionWithMaxCounter(uint64_t* counters, uint64_t max) {
  uint64_t a;
  uint64_t n;
  uint64_t i;
  uint64_t c;

  a = -1;
  n = 0;
  i = 0;

  while (i < codeLength / INSTRUCTIONSIZE) {
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

  if (a != -1)
    return a * INSTRUCTIONSIZE;
  else
    return -1;
}

uint64_t printPerInstructionCounter(uint64_t total, uint64_t* counters, uint64_t max) {
  uint64_t a;
  uint64_t c;

  a = instructionWithMaxCounter(counters, max);

  if (a != -1) {
    c = *(counters + a / INSTRUCTIONSIZE);

    // CAUTION: we reset counter to avoid reporting it again
    *(counters + a / INSTRUCTIONSIZE) = 0;

    printf3((uint64_t*) ",%d(%.2d%%)@%x", (uint64_t*) c, (uint64_t*) fixedPointPercentage(fixedPointRatio(total, c, 4), 4), (uint64_t*) a);
    printSourceLineNumberOfInstruction(a);

    return c;
  } else {
    print((uint64_t*) ",0(0.0%)");

    return 0;
  }
}

void printPerInstructionProfile(uint64_t* message, uint64_t total, uint64_t* counters) {
  printf3((uint64_t*) "%s%s%d", selfieName, message, (uint64_t*) total);
  printPerInstructionCounter(total, counters, printPerInstructionCounter(total, counters, printPerInstructionCounter(total, counters, UINT64_MAX)));
  println();
}

void printProfile() {
  printf3((uint64_t*)
    "%s: summary: %d executed instructions and %.2dMB mapped memory\n",
    selfieName,
    (uint64_t*) getTotalNumberOfInstructions(),
    (uint64_t*) fixedPointRatio(pused(), MEGABYTE, 2));

  if (getTotalNumberOfInstructions() > 0) {
    printInstructionCounters();

    if (sourceLineNumber != (uint64_t*) 0)
      printf1((uint64_t*) "%s: profile: total,max(ratio%%)@addr(line#),2max,3max\n", selfieName);
    else
      printf1((uint64_t*) "%s: profile: total,max(ratio%%)@addr,2max,3max\n", selfieName);

    printPerInstructionProfile((uint64_t*) ": calls:   ", calls, callsPerProcedure);
    printPerInstructionProfile((uint64_t*) ": loops:   ", iterations, iterationsPerLoop);
    printPerInstructionProfile((uint64_t*) ": loads:   ", ic_ld, loadsPerInstruction);
    printPerInstructionProfile((uint64_t*) ": stores:  ", ic_sd, storesPerInstruction);
  }
}

void selfie_disassemble() {
  assemblyName = getArgument();

  if (codeLength == 0) {
    printf2((uint64_t*) "%s: nothing to disassemble to output file %s\n", selfieName, assemblyName);

    return;
  }

  // assert: assemblyName is mapped and not longer than maxFilenameLength

  assemblyFD = openWriteOnly(assemblyName);

  if (signedLessThan(assemblyFD, 0)) {
    printf2((uint64_t*) "%s: could not create assembly output file %s\n", selfieName, assemblyName);

    exit(EXITCODE_IOERROR);
  }

  outputName = assemblyName;
  outputFD   = assemblyFD;

  execute = 0;

  resetLibrary();
  resetInterpreter();

  debug       = 1;
  disassemble = 1;

  while (pc < codeLength) {
    ir = loadInstruction(pc);

    decode_execute();

    pc = pc + INSTRUCTIONSIZE;
  }

  disassemble = 0;
  debug       = 0;

  outputName = (uint64_t*) 0;
  outputFD   = 1;

  printf4((uint64_t*) "%s: %d characters of assembly with %d instructions written into %s\n", selfieName, (uint64_t*) numberOfWrittenCharacters, (uint64_t*) (codeLength / INSTRUCTIONSIZE), assemblyName);
}

// -----------------------------------------------------------------
// ---------------------------- CONTEXTS ---------------------------
// -----------------------------------------------------------------

uint64_t* allocateContext(uint64_t* parent, uint64_t* vctxt, uint64_t* in) {
  uint64_t* context;

  if (freeContexts == (uint64_t*) 0)
    context = smalloc(7 * SIZEOFUINT64STAR + 9 * SIZEOFUINT64);
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
  setRegs(context, zalloc(NUMBEROFREGISTERS * REGISTERSIZE));

  // allocate zeroed memory for page table
  // TODO: save and reuse memory for page table
  setPT(context, zalloc(VIRTUALMEMORYSIZE / PAGESIZE * REGISTERSIZE));

  // determine range of recently mapped pages
  setLoPage(context, 0);
  setMePage(context, 0);
  setHiPage(context, getPageOfVirtualAddress(VIRTUALMEMORYSIZE - REGISTERSIZE));

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

  if (debug_create)
    printf3((uint64_t*) "%s: parent context %p created child context %p\n", selfieName, parent, usedContexts);

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

  *(table + page) = frame;

  if (page <= getPageOfVirtualAddress(getProgramBreak(context) - REGISTERSIZE)) {
    // exploit spatial locality in page table caching
    if (page < getLoPage(context))
      setLoPage(context, page);
    else if (page > getMePage(context))
      setMePage(context, page);
  }

  if (debug_map) {
    printf1((uint64_t*) "%s: page ", selfieName);
    printHexadecimal(page, 4);
    printf2((uint64_t*) " mapped to frame %p in context %p\n", (uint64_t*) frame, context);
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

    setProgramBreak(context, loadVirtualMemory(parentTable, ProgramBreak(vctxt)));

    setException(context, loadVirtualMemory(parentTable, Exception(vctxt)));
    setFaultingPage(context, loadVirtualMemory(parentTable, FaultingPage(vctxt)));
    setExitCode(context, loadVirtualMemory(parentTable, ExitCode(vctxt)));

    table = (uint64_t*) loadVirtualMemory(parentTable, PT(vctxt));

    // assert: context page table is only mapped from beginning up and end down

    page = loadVirtualMemory(parentTable, LoPage(vctxt));
    me   = loadVirtualMemory(parentTable, MePage(vctxt));

    while (page <= me) {
      if (isVirtualAddressMapped(parentTable, FrameForPage(table, page))) {
        frame = loadVirtualMemory(parentTable, FrameForPage(table, page));

        mapPage(context, page, getFrameForPage(parentTable, getPageOfVirtualAddress(frame)));
      }

      page = page + 1;
    }

    storeVirtualMemory(parentTable, LoPage(vctxt), page);

    page = loadVirtualMemory(parentTable, HiPage(vctxt));

    if (isVirtualAddressMapped(parentTable, FrameForPage(table, page)))
      frame = loadVirtualMemory(parentTable, FrameForPage(table, page));
    else
      frame = 0;

    while (frame != 0) {
      mapPage(context, page, getFrameForPage(parentTable, getPageOfVirtualAddress(frame)));

      page  = page - 1;

      if (isVirtualAddressMapped(parentTable, FrameForPage(table, page)))
        frame = loadVirtualMemory(parentTable, FrameForPage(table, page));
      else
        frame = 0;
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
      print((uint64_t*) ": palloc out of physical memory\n");

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

  if (symbolic) {
    if (isTraceSpaceAvailable())
      // always track initialized memory by using tc as most recent branch
      storeSymbolicMemory(getPT(context), vaddr, data, 0, data, data, tc);
    else {
      printf1((uint64_t*) "%s: ealloc out of memory\n", selfieName);

      exit(EXITCODE_OUTOFTRACEMEMORY);
    }
  } else
    storeVirtualMemory(getPT(context), vaddr, data);
}

void up_loadBinary(uint64_t* context) {
  uint64_t baddr;

  // assert: entryPoint is multiple of PAGESIZE and REGISTERSIZE

  setPC(context, entryPoint);
  setLoPage(context, getPageOfVirtualAddress(entryPoint));
  setMePage(context, getPageOfVirtualAddress(entryPoint));
  setOriginalBreak(context, entryPoint + binaryLength);
  setProgramBreak(context, getOriginalBreak(context));

  baddr = 0;

  if (symbolic) {
    // code is never constrained...
    symbolic = 0;

    while (baddr < codeLength) {
      mapAndStore(context, entryPoint + baddr, loadData(baddr));

      baddr = baddr + REGISTERSIZE;
    }

    // ... but data is
    symbolic = 1;
  }

  while (baddr < binaryLength) {
    mapAndStore(context, entryPoint + baddr, loadData(baddr));

    baddr = baddr + REGISTERSIZE;
  }

  setName(context, binaryName);
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
    SP = up_loadString(context, (uint64_t*) *(argv + i), SP);

    // store pointer in virtual *argv
    *(vargv + i) = SP;

    i = i + 1;
  }

  // allocate memory for termination of env table
  SP = SP - REGISTERSIZE;

  // push null value to terminate env table
  mapAndStore(context, SP, 0);

  // allocate memory for termination of argv table
  SP = SP - REGISTERSIZE;

  // push null value to terminate argv table
  mapAndStore(context, SP, 0);

  // assert: i == argc

  // push argv table onto the stack
  while (i > 0) {
    // allocate memory for argv table entry
    SP = SP - REGISTERSIZE;

    i = i - 1;

    // push argv table entry
    mapAndStore(context, SP, *(vargv + i));
  }

  // allocate memory for argc
  SP = SP - REGISTERSIZE;

  // push argc
  mapAndStore(context, SP, argc);

  // store stack pointer value in stack pointer register
  *(getRegs(context) + REG_SP) = SP;

  // set bounds to register value for symbolic execution
  if (symbolic) {
    *(reg_typ + REG_SP) = 0;

    *(reg_los + REG_SP) = SP;
    *(reg_ups + REG_SP) = SP;
  }
}

uint64_t handleSystemCall(uint64_t* context) {
  uint64_t a7;

  setException(context, EXCEPTION_NOEXCEPTION);

  a7 = *(getRegs(context) + REG_A7);

  if (a7 == SYSCALL_BRK)
    implementBrk(context);
  else if (a7 == SYSCALL_READ)
    implementRead(context);
  else if (a7 == SYSCALL_WRITE)
    implementWrite(context);
  else if (a7 == SYSCALL_OPEN)
    implementOpen(context);
  else if (a7 == SYSCALL_EXIT) {
    implementExit(context);

    // TODO: exit only if all contexts have exited
    return EXIT;
  } else {
    printf2((uint64_t*) "%s: unknown system call %d\n", selfieName, (uint64_t*) a7);

    setExitCode(context, EXITCODE_UNKNOWNSYSCALL);

    return EXIT;
  }

  if (getException(context) == EXCEPTION_MAXTRACE) {
    // exiting during symbolic execution, no exit code necessary
    setException(context, EXCEPTION_NOEXCEPTION);

    return EXIT;
  } else
    return DONOTEXIT;
}

uint64_t handlePageFault(uint64_t* context) {
  setException(context, EXCEPTION_NOEXCEPTION);

  // TODO: use this table to unmap and reuse frames
  mapPage(context, getFaultingPage(context), (uint64_t) palloc());

  return DONOTEXIT;
}

uint64_t handleDivisionByZero(uint64_t* context) {
  setException(context, EXCEPTION_NOEXCEPTION);

  if (record) {
    printf1((uint64_t*) "%s: division by zero, replaying...\n", selfieName);

    replayTrace();

    setExitCode(context, EXITCODE_NOERROR);
  } else {
    printf1((uint64_t*) "%s: division by zero\n", selfieName);

    setExitCode(context, EXITCODE_DIVISIONBYZERO);
  }

  return EXIT;
}

uint64_t handleMaxTrace(uint64_t* context) {
  setException(context, EXCEPTION_NOEXCEPTION);

  setExitCode(context, EXITCODE_OUTOFTRACEMEMORY);

  return EXIT;
}

uint64_t handleTimer(uint64_t* context) {
  setException(context, EXCEPTION_NOEXCEPTION);

  return DONOTEXIT;
}

uint64_t handleException(uint64_t* context) {
  uint64_t exception;

  exception = getException(context);

  if (exception == EXCEPTION_SYSCALL)
    return handleSystemCall(context);
  else if (exception == EXCEPTION_PAGEFAULT)
    return handlePageFault(context);
  else if (exception == EXCEPTION_DIVISIONBYZERO)
    return handleDivisionByZero(context);
  else if (exception == EXCEPTION_MAXTRACE)
    return handleMaxTrace(context);
  else if (exception == EXCEPTION_TIMER)
    return handleTimer(context);
  else {
    printf2((uint64_t*) "%s: context %s throws uncaught ", selfieName, getName(context));
    printException(exception, getFaultingPage(context));
    println();

    setExitCode(context, EXITCODE_UNCAUGHTEXCEPTION);

    return EXIT;
  }
}

uint64_t mipster(uint64_t* toContext) {
  uint64_t timeout;
  uint64_t* fromContext;

  print((uint64_t*) "mipster\n");

  timeout = TIMESLICE;

  while (1) {
    fromContext = mipster_switch(toContext, timeout);

    if (getParent(fromContext) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      toContext = getParent(fromContext);

      timeout = TIMEROFF;
    } else if (handleException(fromContext) == EXIT)
      return getExitCode(fromContext);
    else {
      // TODO: scheduler should go here
      toContext = fromContext;

      timeout = TIMESLICE;
    }
  }
}

uint64_t hypster(uint64_t* toContext) {
  uint64_t* fromContext;

  print((uint64_t*) "hypster\n");

  while (1) {
    fromContext = hypster_switch(toContext, TIMESLICE);

    if (handleException(fromContext) == EXIT)
      return getExitCode(fromContext);
    else
      // TODO: scheduler should go here
      toContext = fromContext;
  }
}

uint64_t mixter(uint64_t* toContext, uint64_t mix) {
  // works with mipsters and hypsters
  uint64_t mslice;
  uint64_t timeout;
  uint64_t* fromContext;

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
      fromContext = mipster_switch(toContext, TIMESLICE);
    else
      fromContext = hypster_switch(toContext, TIMESLICE);

    if (getParent(fromContext) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      toContext = getParent(fromContext);

      timeout = TIMEROFF;
    } else if (handleException(fromContext) == EXIT)
      return getExitCode(fromContext);
    else {
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

uint64_t minmob(uint64_t* toContext) {
  uint64_t timeout;
  uint64_t* fromContext;

  timeout = TIMESLICE;

  while (1) {
    fromContext = mipster_switch(toContext, TIMESLICE);

    if (getParent(fromContext) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      toContext = getParent(fromContext);

      timeout = TIMEROFF;
    } else {
      // minster and mobster do not handle page faults
      if (getException(fromContext) == EXCEPTION_PAGEFAULT) {
        printf2((uint64_t*) "%s: context %s throws uncaught ", selfieName, getName(fromContext));
        printException(getException(fromContext), getFaultingPage(fromContext));
        println();

        return EXITCODE_UNCAUGHTEXCEPTION;
      } else if (handleException(fromContext) == EXIT)
        return getExitCode(fromContext);

      // TODO: scheduler should go here
      toContext = fromContext;

      timeout = TIMESLICE;
    }
  }
}

void mapUnmappedPages(uint64_t* context) {
  uint64_t page;

  // assert: page table is only mapped from beginning up and end down

  page = getLoPage(context);

  while (isPageMapped(getPT(context), page))
    page = page + 1;

  while (pavailable()) {
    mapPage(context, page, (uint64_t) palloc());

    page = page + 1;
  }
}

uint64_t minster(uint64_t* toContext) {
  print((uint64_t*) "minster\n");

  // virtual is like physical memory in initial context up to memory size
  // by mapping unmapped pages (for the heap) to all available page frames
  // CAUTION: consumes memory even when not accessed
  mapUnmappedPages(toContext);

  // does not handle page faults, works only until running out of mapped pages
  return minmob(toContext);
}

uint64_t mobster(uint64_t* toContext) {
  print((uint64_t*) "mobster\n");

  // does not handle page faults, relies on fancy hypsters to do that
  return minmob(toContext);
}

void backtrackTrace(uint64_t* context) {
  uint64_t savepc;

  if (debug_symbolic)
    printf3((uint64_t*) "%s: backtracking %s from exit code %d\n", selfieName, getName(context), (uint64_t*) signExtend(getExitCode(context), SYSCALL_BITWIDTH));

  symbolic = 0;

  backtrack = 1;

  while (backtrack) {
    pc = *(pcs + tc);

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

  setPC(context, pc);
}

uint64_t monster(uint64_t* toContext) {
  uint64_t b;
  uint64_t timeout;
  uint64_t* fromContext;

  print((uint64_t*) "monster\n");

  b = 0;

  timeout = TIMESLICE;

  while (1) {
    fromContext = mipster_switch(toContext, timeout);

    if (getParent(fromContext) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      toContext = getParent(fromContext);

      timeout = TIMEROFF;
    } else {
      if (handleException(fromContext) == EXIT) {
        backtrackTrace(fromContext);

        if (b == 0)
          printf1((uint64_t*) "%s: backtracking ", selfieName);
        else
          unprintInteger(b);

        b = b + 1;

        printInteger(b);

        if (pc == 0) {
          println();

          return EXITCODE_NOERROR;
        }
      }

      // TODO: scheduler should go here
      toContext = fromContext;

      timeout = TIMESLICE;
    }
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

uint64_t selfie_run(uint64_t machine) {
  uint64_t exitCode;

  if (binaryLength == 0) {
    printf1((uint64_t*) "%s: nothing to run, debug, or host\n", selfieName);

    return EXITCODE_BADARGUMENTS;
  }

  if (machine == DIPSTER) {
    debug       = 1;
    disassemble = 1;
  } else if (machine == RIPSTER) {
    debug  = 1;
    record = 1;

    initReplayEngine();
  } else if (machine == MONSTER) {
    debug    = 1;
    symbolic = 1;

    initSymbolicEngine();
  }

  if (machine == MONSTER) {
    initMemory(roundUp(maxTraceLength * SIZEOFUINT64, MEGABYTE) / MEGABYTE + 1);

    fuzz = atoi(peekArgument());
  } else
    initMemory(atoi(peekArgument()));

  execute = 1;

  resetInterpreter();
  resetMicrokernel();

  createContext(MY_CONTEXT, 0);

  up_loadBinary(currentContext);

  // pass binary name as first argument by replacing memory size
  setArgument(binaryName);

  up_loadArguments(currentContext, numberOfRemainingArguments(), remainingArguments());

  printf3((uint64_t*) "%s: selfie executing %s with %dMB physical memory on ", selfieName, binaryName, (uint64_t*) (pageFrameMemory / MEGABYTE));

  if (machine == MIPSTER)
    exitCode = mipster(currentContext);
  else if (machine == DIPSTER)
    exitCode = mipster(currentContext);
  else if (machine == RIPSTER)
    exitCode = mipster(currentContext);
  else if (machine == MONSTER)
    exitCode = monster(currentContext);
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

  execute = 0;

  printf3((uint64_t*) "%s: selfie terminating %s with exit code %d\n", selfieName, getName(currentContext), (uint64_t*) signExtend(exitCode, SYSCALL_BITWIDTH));

  printProfile();

  symbolic    = 0;
  record      = 0;
  disassemble = 0;
  debug       = 0;

  fuzz = 0;

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
  if (depth == numberOfSATVariables)
    return SAT;

  *(SATAssignment + depth) = TRUE;

  if (instanceMayBeTrue(depth)) if (babysat(depth + 1) == SAT)
    return SAT;

  *(SATAssignment + depth) = FALSE;

  if (instanceMayBeTrue(depth)) if (babysat(depth + 1) == SAT)
    return SAT;

  return UNSAT;
}

// -----------------------------------------------------------------
// ----------------------- DIMACS CNF PARSER -----------------------
// -----------------------------------------------------------------

void selfie_printDimacs() {
  uint64_t clause;
  uint64_t variable;

  printf2((uint64_t*) "p cnf %d %d\n", (uint64_t*) numberOfSATVariables, (uint64_t*) numberOfSATClauses);

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

    print((uint64_t*) "0\n");

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
      if (isCharacterNewLine())
        newLine = 1;
      else
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
      if (literal == 0) {
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

  printf2((uint64_t*) "%s: selfie loading SAT instance %s\n", selfieName, sourceName);

  // assert: sourceName is mapped and not longer than maxFilenameLength

  sourceFD = signExtend(open(sourceName, O_RDONLY, 0), SYSCALL_BITWIDTH);

  if (signedLessThan(sourceFD, 0)) {
    printf2((uint64_t*) "%s: could not open input file %s\n", selfieName, sourceName);

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

  printf4((uint64_t*) "%s: %d clauses with %d declared variables loaded from %s\n", selfieName, (uint64_t*) numberOfSATClauses, (uint64_t*) numberOfSATVariables, sourceName);

  dimacsName = sourceName;
}

void selfie_sat() {
  uint64_t variable;

  selfie_loadDimacs();

  if (dimacsName == (uint64_t*) 0) {
    printf1((uint64_t*) "%s: nothing to SAT solve\n", selfieName);

    return;
  }

  selfie_printDimacs();

  if (babysat(0) == SAT) {
    printf2((uint64_t*) "%s: %s is satisfiable with ", selfieName, dimacsName);

    variable = 0;

    while (variable < numberOfSATVariables) {
      if (*(SATAssignment + variable) == FALSE)
        printf1((uint64_t*) "-%d ", (uint64_t*) (variable + 1));
      else
        printf1((uint64_t*) "%d ", (uint64_t*) (variable + 1));

      variable = variable + 1;
    }
  } else
    printf2((uint64_t*) "%s: %s is unsatisfiable", selfieName, dimacsName);

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
  printf3((uint64_t*) "%s: usage: selfie { %s } [ %s ]\n",
    selfieName,
      (uint64_t*) "-c { source } | -o binary | -s assembly | -l binary | -sat dimacs",
      (uint64_t*) "( -m | -d | -r | -n | -y | -min | -mob ) 0-64 ...");
}

uint64_t selfie() {
  uint64_t* option;

  if (numberOfRemainingArguments() == 0)
    printUsage();
  else {
    initScanner();
    initRegister();
    initInterpreter();

    while (numberOfRemainingArguments() > 0) {
      option = getArgument();

      if (stringCompare(option, (uint64_t*) "-c"))
        selfie_compile();

      else if (numberOfRemainingArguments() == 0) {
        // remaining options have at least one argument
        printUsage();

        return EXITCODE_BADARGUMENTS;
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
      else if (stringCompare(option, (uint64_t*) "-d"))
        return selfie_run(DIPSTER);
      else if (stringCompare(option, (uint64_t*) "-r"))
        return selfie_run(RIPSTER);
      else if (stringCompare(option, (uint64_t*) "-n"))
        return selfie_run(MONSTER);
      else if (stringCompare(option, (uint64_t*) "-y"))
        return selfie_run(HYPSTER);
      else if (stringCompare(option, (uint64_t*) "-min"))
        return selfie_run(MINSTER);
      else if (stringCompare(option, (uint64_t*) "-mob"))
        return selfie_run(MOBSTER);
      else {
        printUsage();

        return EXITCODE_BADARGUMENTS;
      }
    }
  }

  return EXITCODE_NOERROR;
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  initSelfie((uint64_t) argc, (uint64_t*) argv);

  initLibrary();

  return selfie();
}