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

void exit(int code);
int read(int fd, int* buffer, int bytesToRead);
int write(int fd, int* buffer, int bytesToWrite);
int open(int* filename, int flags, int mode);
int* malloc(int size);

// -----------------------------------------------------------------
// ----------------------- LIBRARY PROCEDURES ----------------------
// -----------------------------------------------------------------

void initLibrary();
void resetLibrary();

int addWrap(int a, int b);
int subtractWrap(int a, int b);
int multiplyWrap(int a, int b);

void checkDivision(int a, int b);

int twoToThePowerOf(int p);
int leftShift(int n, int b);
int rightShift(int n, int b);

int  loadCharacter(int* s, int i);
int* storeCharacter(int* s, int i, int c);

int  stringLength(int* s);
void stringReverse(int* s);
int  stringCompare(int* s, int* t);

int  atoi(int* s);
int* itoa(int n, int* s, int b, int a, int p);

int fixedPointRatio(int a, int b);

void putCharacter(int c);

void print(int* s);
void println();

void printCharacter(int c);
void printString(int* s);
void printInteger(int n);
void printFixedPointPercentage(int a, int b);
void printFixedPointRatio(int a, int b);
void printHexadecimal(int n, int a);
void printOctal(int n, int a);
void printBinary(int n, int a);

int roundUp(int n, int m);

int* zalloc(int size);

// ------------------------ GLOBAL CONSTANTS -----------------------

int CHAR_EOF          = -1; // end of file
int CHAR_TAB          = 9;  // ASCII code 9  = tabulator
int CHAR_LF           = 10; // ASCII code 10 = line feed
int CHAR_CR           = 13; // ASCII code 13 = carriage return
int CHAR_SPACE        = ' ';
int CHAR_SEMICOLON    = ';';
int CHAR_PLUS         = '+';
int CHAR_DASH         = '-';
int CHAR_ASTERISK     = '*';
int CHAR_SLASH        = '/';
int CHAR_UNDERSCORE   = '_';
int CHAR_EQUAL        = '=';
int CHAR_LPARENTHESIS = '(';
int CHAR_RPARENTHESIS = ')';
int CHAR_LBRACE       = '{';
int CHAR_RBRACE       = '}';
int CHAR_COMMA        = ',';
int CHAR_LT           = '<';
int CHAR_GT           = '>';
int CHAR_EXCLAMATION  = '!';
int CHAR_PERCENTAGE   = '%';
int CHAR_SINGLEQUOTE  = 39; // ASCII code 39 = '
int CHAR_DOUBLEQUOTE  = '"';

int SIZEOFINT     = 4; // must be the same as WORDSIZE
int SIZEOFINTSTAR = 4; // must be the same as WORDSIZE

int* power_of_two_table;

int INT_MAX; // maximum numerical value of a signed 32-bit integer
int INT_MIN; // minimum numerical value of a signed 32-bit integer

int INT16_MAX; // maximum numerical value of a signed 16-bit integer
int INT16_MIN; // minimum numerical value of a signed 16-bit integer

int INT_OVERFLOW = 0; // indicates if an integer overflow occurred

int OVERFLOW_NO  = 0;
int OVERFLOW_YES = 1;

int maxFilenameLength = 128;

int* character_buffer; // buffer for reading and writing characters
int* integer_buffer;   // buffer for printing integers
int* filename_buffer;  // buffer for opening files
int* binary_buffer;    // buffer for binary I/O

// flags for opening read-only files
// LINUX:       0 = 0x0000 = O_RDONLY (0x0000)
// MAC:         0 = 0x0000 = O_RDONLY (0x0000)
// WINDOWS: 32768 = 0x8000 = _O_BINARY (0x8000) | _O_RDONLY (0x0000)
// since LINUX/MAC do not seem to mind about _O_BINARY set
// we use the WINDOWS flags as default
int O_RDONLY = 32768;

// flags for opening write-only files
// MAC: 1537 = 0x0601 = O_CREAT (0x0200) | O_TRUNC (0x0400) | O_WRONLY (0x0001)
int MAC_O_CREAT_TRUNC_WRONLY = 1537;

// LINUX: 577 = 0x0241 = O_CREAT (0x0040) | O_TRUNC (0x0200) | O_WRONLY (0x0001)
int LINUX_O_CREAT_TRUNC_WRONLY = 577;

// WINDOWS: 33537 = 0x8301 = _O_BINARY (0x8000) | _O_CREAT (0x0100) | _O_TRUNC (0x0200) | _O_WRONLY (0x0001)
int WINDOWS_O_BINARY_CREAT_TRUNC_WRONLY = 33537;

// flags for rw-r--r-- file permissions
// 420 = 00644 = S_IRUSR (00400) | S_IWUSR (00200) | S_IRGRP (00040) | S_IROTH (00004)
// these flags seem to be working for LINUX, MAC, and WINDOWS
int S_IRUSR_IWUSR_IRGRP_IROTH = 420;

// ------------------------ GLOBAL VARIABLES -----------------------

int numberOfWrittenCharacters = 0;

int* outputName = (int*) 0;
int  outputFD   = 1;

// ------------------------- INITIALIZATION ------------------------

void initLibrary() {
  int i;

  // powers of two table with 31 entries for 2^0 to 2^30
  // avoiding overflow for 2^31 and larger numbers with 32-bit signed integers
  power_of_two_table = malloc(31 * SIZEOFINT);

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

  INT16_MAX = twoToThePowerOf(15) - 1;
  INT16_MIN = -INT16_MAX - 1;

  // allocate and touch to make sure memory is mapped for read calls
  character_buffer  = malloc(SIZEOFINT);
  *character_buffer = 0;

  // accommodate at least 32-bit numbers for itoa, no mapping needed
  integer_buffer = malloc(33);

  // does not need to be mapped
  filename_buffer = malloc(maxFilenameLength);

  // allocate and touch to make sure memory is mapped for read calls
  binary_buffer  = malloc(SIZEOFINT);
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

void printSymbol(int symbol);
void printLineNumber(int* message, int line);

void syntaxErrorMessage(int* message);
void syntaxErrorCharacter(int character);
void syntaxErrorIdentifier(int* expected);

void getCharacter();

int isCharacterNewLine();
int isCharacterWhitespace();

int findNextCharacter();

int isCharacterLetter();
int isCharacterDigit();
int isCharacterLetterOrDigitOrUnderscore();
int isCharacterNotDoubleQuoteOrNewLineOrEOF();

int identifierStringMatch(int stringIndex);
int identifierOrKeyword();

void getSymbol();

// ------------------------ GLOBAL CONSTANTS -----------------------

int SYM_EOF          = -1; // end of file
int SYM_IDENTIFIER   = 0;  // identifier
int SYM_INTEGER      = 1;  // integer
int SYM_VOID         = 2;  // VOID
int SYM_INT          = 3;  // INT
int SYM_SEMICOLON    = 4;  // ;
int SYM_IF           = 5;  // IF
int SYM_ELSE         = 6;  // ELSE
int SYM_PLUS         = 7;  // +
int SYM_MINUS        = 8;  // -
int SYM_ASTERISK     = 9;  // *
int SYM_DIV          = 10; // /
int SYM_EQUALITY     = 11; // ==
int SYM_ASSIGN       = 12; // =
int SYM_LPARENTHESIS = 13; // (
int SYM_RPARENTHESIS = 14; // )
int SYM_LBRACE       = 15; // {
int SYM_RBRACE       = 16; // }
int SYM_WHILE        = 17; // WHILE
int SYM_RETURN       = 18; // RETURN
int SYM_COMMA        = 19; // ,
int SYM_LT           = 20; // <
int SYM_LEQ          = 21; // <=
int SYM_GT           = 22; // >
int SYM_GEQ          = 23; // >=
int SYM_NOTEQ        = 24; // !=
int SYM_MOD          = 25; // %
int SYM_CHARACTER    = 26; // character
int SYM_STRING       = 27; // string

int* SYMBOLS; // strings representing symbols

int maxIdentifierLength = 64; // maximum number of characters in an identifier
int maxIntegerLength    = 10; // maximum number of characters in an integer
int maxStringLength     = 128; // maximum number of characters in a string

// ------------------------ GLOBAL VARIABLES -----------------------

int lineNumber = 1; // current line number for error reporting

int* identifier = (int*) 0; // stores scanned identifier as string
int* integer    = (int*) 0; // stores scanned integer as string
int* string     = (int*) 0; // stores scanned string

int literal = 0; // stores numerical value of scanned integer or character

int mayBeINTMIN = 0; // allow INT_MIN if '-' was scanned before
int isINTMIN    = 0; // flag to indicate that INT_MIN was scanned

int character; // most recently read character

int numberOfReadCharacters = 0;

int symbol; // most recently recognized symbol

int numberOfIgnoredCharacters = 0;
int numberOfComments          = 0;
int numberOfScannedSymbols    = 0;

int* sourceName = (int*) 0; // name of source file
int  sourceFD   = 0;        // file descriptor of open source file

// ------------------------- INITIALIZATION ------------------------

void initScanner () {
  SYMBOLS = malloc(28 * SIZEOFINTSTAR);

  *(SYMBOLS + SYM_IDENTIFIER)   = (int) "identifier";
  *(SYMBOLS + SYM_INTEGER)      = (int) "integer";
  *(SYMBOLS + SYM_VOID)         = (int) "void";
  *(SYMBOLS + SYM_INT)          = (int) "int";
  *(SYMBOLS + SYM_SEMICOLON)    = (int) ";";
  *(SYMBOLS + SYM_IF)           = (int) "if";
  *(SYMBOLS + SYM_ELSE)         = (int) "else";
  *(SYMBOLS + SYM_PLUS)         = (int) "+";
  *(SYMBOLS + SYM_MINUS)        = (int) "-";
  *(SYMBOLS + SYM_ASTERISK)     = (int) "*";
  *(SYMBOLS + SYM_DIV)          = (int) "/";
  *(SYMBOLS + SYM_EQUALITY)     = (int) "==";
  *(SYMBOLS + SYM_ASSIGN)       = (int) "=";
  *(SYMBOLS + SYM_LPARENTHESIS) = (int) "(";
  *(SYMBOLS + SYM_RPARENTHESIS) = (int) ")";
  *(SYMBOLS + SYM_LBRACE)       = (int) "{";
  *(SYMBOLS + SYM_RBRACE)       = (int) "}";
  *(SYMBOLS + SYM_WHILE)        = (int) "while";
  *(SYMBOLS + SYM_RETURN)       = (int) "return";
  *(SYMBOLS + SYM_COMMA)        = (int) ",";
  *(SYMBOLS + SYM_LT)           = (int) "<";
  *(SYMBOLS + SYM_LEQ)          = (int) "<=";
  *(SYMBOLS + SYM_GT)           = (int) ">";
  *(SYMBOLS + SYM_GEQ)          = (int) ">=";
  *(SYMBOLS + SYM_NOTEQ)        = (int) "!=";
  *(SYMBOLS + SYM_MOD)          = (int) "%";
  *(SYMBOLS + SYM_CHARACTER)    = (int) "character";
  *(SYMBOLS + SYM_STRING)       = (int) "string";

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

void createSymbolTableEntry(int which, int* string, int line, int class, int type, int value, int address);

int* searchSymbolTable(int* entry, int* string, int class);
int* getScopedSymbolTableEntry(int* string, int class);

int isUndefinedProcedure(int* entry);
int reportUndefinedProcedures();

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

int* getNextEntry(int* entry)  { return (int*) *entry; }
int* getString(int* entry)     { return (int*) *(entry + 1); }
int  getLineNumber(int* entry) { return        *(entry + 2); }
int  getClass(int* entry)      { return        *(entry + 3); }
int  getType(int* entry)       { return        *(entry + 4); }
int  getValue(int* entry)      { return        *(entry + 5); }
int  getAddress(int* entry)    { return        *(entry + 6); }
int  getScope(int* entry)      { return        *(entry + 7); }

void setNextEntry(int* entry, int* next)    { *entry       = (int) next; }
void setString(int* entry, int* identifier) { *(entry + 1) = (int) identifier; }
void setLineNumber(int* entry, int line)    { *(entry + 2) = line; }
void setClass(int* entry, int class)        { *(entry + 3) = class; }
void setType(int* entry, int type)          { *(entry + 4) = type; }
void setValue(int* entry, int value)        { *(entry + 5) = value; }
void setAddress(int* entry, int address)    { *(entry + 6) = address; }
void setScope(int* entry, int scope)        { *(entry + 7) = scope; }

// ------------------------ GLOBAL CONSTANTS -----------------------

// classes
int VARIABLE  = 1;
int PROCEDURE = 2;
int STRING    = 3;

// types
int INT_T     = 1;
int INTSTAR_T = 2;
int VOID_T    = 3;

// symbol tables
int GLOBAL_TABLE  = 1;
int LOCAL_TABLE   = 2;
int LIBRARY_TABLE = 3;

// ------------------------ GLOBAL VARIABLES -----------------------

// table pointers
int* global_symbol_table  = (int*) 0;
int* local_symbol_table   = (int*) 0;
int* library_symbol_table = (int*) 0;

int numberOfGlobalVariables = 0;
int numberOfProcedures      = 0;
int numberOfStrings         = 0;

// ------------------------- INITIALIZATION ------------------------

void resetSymbolTables() {
  global_symbol_table  = (int*) 0;
  local_symbol_table   = (int*) 0;
  library_symbol_table = (int*) 0;

  numberOfGlobalVariables = 0;
  numberOfProcedures      = 0;
  numberOfStrings         = 0;
}

// -----------------------------------------------------------------
// ---------------------------- PARSER -----------------------------
// -----------------------------------------------------------------

void resetParser();

int isNotRbraceOrEOF();
int isExpression();
int isLiteral();
int isStarOrDivOrModulo();
int isPlusOrMinus();
int isComparison();

int lookForFactor();
int lookForStatement();
int lookForType();

void save_temporaries();
void restore_temporaries(int numberOfTemporaries);

void syntaxErrorSymbol(int expected);
void syntaxErrorUnexpected();
void printType(int type);
void typeWarning(int expected, int found);

int* getVariable(int* variable);
int  load_variable(int* variable);
void load_integer(int value);
void load_string(int* string);

int  help_call_codegen(int* entry, int* procedure);
void help_procedure_prologue(int localVariables);
void help_procedure_epilogue(int parameters);

int  gr_call(int* procedure);
int  gr_factor();
int  gr_term();
int  gr_simpleExpression();
int  gr_expression();
void gr_while();
void gr_if();
void gr_return();
void gr_statement();
int  gr_type();
void gr_variable(int offset);
int  gr_initialization(int type);
void gr_procedure(int* procedure, int type);
void gr_cstar();

// ------------------------ GLOBAL VARIABLES -----------------------

int allocatedTemporaries = 0; // number of allocated temporaries

int allocatedMemory = 0; // number of bytes for global variables and strings

int returnBranches = 0; // fixup chain for return statements

int returnType = 0; // return type of currently parsed procedure

int mainJump = 0; // address where JAL instruction to main procedure is

int numberOfCalls       = 0;
int numberOfAssignments = 0;
int numberOfWhile       = 0;
int numberOfIf          = 0;
int numberOfReturn      = 0;

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

void emitLeftShiftBy(int reg, int b);
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

void printRegister(int reg);

// ------------------------ GLOBAL CONSTANTS -----------------------

int NUMBEROFREGISTERS = 32;

int REG_ZR = 0;
int REG_AT = 1;
int REG_V0 = 2;
int REG_V1 = 3;
int REG_A0 = 4;
int REG_A1 = 5;
int REG_A2 = 6;
int REG_A3 = 7;
int REG_T0 = 8;
int REG_T1 = 9;
int REG_T2 = 10;
int REG_T3 = 11;
int REG_T4 = 12;
int REG_T5 = 13;
int REG_T6 = 14;
int REG_T7 = 15;
int REG_S0 = 16;
int REG_S1 = 17;
int REG_S2 = 18;
int REG_S3 = 19;
int REG_S4 = 20;
int REG_S5 = 21;
int REG_S6 = 22;
int REG_S7 = 23;
int REG_T8 = 24;
int REG_T9 = 25;
int REG_K0 = 26;
int REG_K1 = 27;
int REG_GP = 28;
int REG_SP = 29;
int REG_FP = 30;
int REG_RA = 31;

int* REGISTERS; // strings representing registers

// ------------------------- INITIALIZATION ------------------------

void initRegister() {
  REGISTERS = malloc(NUMBEROFREGISTERS * SIZEOFINTSTAR);

  *(REGISTERS + REG_ZR) = (int) "$zero";
  *(REGISTERS + REG_AT) = (int) "$at";
  *(REGISTERS + REG_V0) = (int) "$v0";
  *(REGISTERS + REG_V1) = (int) "$v1";
  *(REGISTERS + REG_A0) = (int) "$a0";
  *(REGISTERS + REG_A1) = (int) "$a1";
  *(REGISTERS + REG_A2) = (int) "$a2";
  *(REGISTERS + REG_A3) = (int) "$a3";
  *(REGISTERS + REG_T0) = (int) "$t0";
  *(REGISTERS + REG_T1) = (int) "$t1";
  *(REGISTERS + REG_T2) = (int) "$t2";
  *(REGISTERS + REG_T3) = (int) "$t3";
  *(REGISTERS + REG_T4) = (int) "$t4";
  *(REGISTERS + REG_T5) = (int) "$t5";
  *(REGISTERS + REG_T6) = (int) "$t6";
  *(REGISTERS + REG_T7) = (int) "$t7";
  *(REGISTERS + REG_S0) = (int) "$s0";
  *(REGISTERS + REG_S1) = (int) "$s1";
  *(REGISTERS + REG_S2) = (int) "$s2";
  *(REGISTERS + REG_S3) = (int) "$s3";
  *(REGISTERS + REG_S4) = (int) "$s4";
  *(REGISTERS + REG_S5) = (int) "$s5";
  *(REGISTERS + REG_S6) = (int) "$s6";
  *(REGISTERS + REG_S7) = (int) "$s7";
  *(REGISTERS + REG_T8) = (int) "$t8";
  *(REGISTERS + REG_T9) = (int) "$t9";
  *(REGISTERS + REG_K0) = (int) "$k0";
  *(REGISTERS + REG_K1) = (int) "$k1";
  *(REGISTERS + REG_GP) = (int) "$gp";
  *(REGISTERS + REG_SP) = (int) "$sp";
  *(REGISTERS + REG_FP) = (int) "$fp";
  *(REGISTERS + REG_RA) = (int) "$ra";
}

// -----------------------------------------------------------------
// ---------------------------- ENCODER ----------------------------
// -----------------------------------------------------------------

int encodeRFormat(int opcode, int rs, int rt, int rd, int function);
int encodeIFormat(int opcode, int rs, int rt, int immediate);
int encodeJFormat(int opcode, int instr_index);

// -----------------------------------------------------------------
// ---------------------------- DECODER ----------------------------
// -----------------------------------------------------------------

void initDecoder();

int getOpcode(int instruction);
int getRS(int instruction);
int getRT(int instruction);
int getRD(int instruction);
int getFunction(int instruction);
int getImmediate(int instruction);
int getInstrIndex(int instruction);
int signExtend(int immediate);

void decodeRFormat();
void decodeIFormat();
void decodeJFormat();

void decode();

void printOpcode(int opcode);
void printFunction(int function);

// ------------------------ GLOBAL CONSTANTS -----------------------

int OP_SPECIAL = 0;
int OP_J       = 2;
int OP_JAL     = 3;
int OP_BEQ     = 4;
int OP_ADDIU   = 9;
int OP_LW      = 35;
int OP_SW      = 43;

int* OPCODES; // strings representing MIPS opcodes

int FCT_NOP     = 0;
int FCT_JR      = 8;
int FCT_SYSCALL = 12;
int FCT_MFHI    = 16;
int FCT_MFLO    = 18;
int FCT_MULTU   = 25;
int FCT_DIVU    = 27;
int FCT_ADDU    = 33;
int FCT_SUBU    = 35;
int FCT_SLT     = 42;

int* FUNCTIONS; // strings representing MIPS functions

// ------------------------ GLOBAL VARIABLES -----------------------

int opcode      = 0;
int rs          = 0;
int rt          = 0;
int rd          = 0;
int immediate   = 0;
int function    = 0;
int instr_index = 0;

// ------------------------- INITIALIZATION ------------------------

void initDecoder() {
  OPCODES = malloc(44 * SIZEOFINTSTAR);

  *(OPCODES + OP_SPECIAL) = (int) "nop";
  *(OPCODES + OP_J)       = (int) "j";
  *(OPCODES + OP_JAL)     = (int) "jal";
  *(OPCODES + OP_BEQ)     = (int) "beq";
  *(OPCODES + OP_ADDIU)   = (int) "addiu";
  *(OPCODES + OP_LW)      = (int) "lw";
  *(OPCODES + OP_SW)      = (int) "sw";

  FUNCTIONS = malloc(43 * SIZEOFINTSTAR);

  *(FUNCTIONS + FCT_NOP)     = (int) "nop";
  *(FUNCTIONS + FCT_JR)      = (int) "jr";
  *(FUNCTIONS + FCT_SYSCALL) = (int) "syscall";
  *(FUNCTIONS + FCT_MFHI)    = (int) "mfhi";
  *(FUNCTIONS + FCT_MFLO)    = (int) "mflo";
  *(FUNCTIONS + FCT_MULTU)   = (int) "multu";
  *(FUNCTIONS + FCT_DIVU)    = (int) "divu";
  *(FUNCTIONS + FCT_ADDU)    = (int) "addu";
  *(FUNCTIONS + FCT_SUBU)    = (int) "subu";
  *(FUNCTIONS + FCT_SLT)     = (int) "slt";
}

// -----------------------------------------------------------------
// ----------------------------- CODE ------------------------------
// -----------------------------------------------------------------

int  loadBinary(int baddr);
void storeBinary(int baddr, int instruction);

void emitInstruction(int instruction);
void emitRFormat(int opcode, int rs, int rt, int rd, int function);
void emitIFormat(int opcode, int rs, int rt, int immediate);
void emitJFormat(int opcode, int instr_index);

void fixup_relative(int fromAddress);
void fixup_absolute(int fromAddress, int toAddress);
void fixlink_absolute(int fromAddress, int toAddress);

int copyStringToBinary(int* s, int a);

void emitGlobalsStrings();

int openWriteOnly(int* name);

void selfie_output();

int* touch(int* memory, int length);

void selfie_load();

// ------------------------ GLOBAL CONSTANTS -----------------------

int maxBinaryLength = 262144; // 256KB

// ------------------------ GLOBAL VARIABLES -----------------------

int* binary = (int*) 0; // binary of emitted instructions

int binaryLength = 0; // length of binary in bytes incl. globals & strings

int codeLength = 0; // length of code portion of binary in bytes

int* binaryName = (int*) 0; // file name of binary

int* sourceLineNumber = (int*) 0; // source line number per emitted instruction

int* assemblyName = (int*) 0; // name of assembly file
int  assemblyFD   = 0;        // file descriptor of open assembly file

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emitExit();
void implementExit(int* context);

void emitRead();
void implementRead(int* context);

void emitWrite();
void implementWrite(int* context);

void emitOpen();
int  down_loadString(int* table, int vaddr, int* s);
void implementOpen(int* context);

void emitMalloc();
int implementMalloc(int* context);

// ------------------------ GLOBAL CONSTANTS -----------------------

int debug_read   = 0;
int debug_write  = 0;
int debug_open   = 0;

int debug_malloc = 0;

int SYSCALL_EXIT   = 4001;
int SYSCALL_READ   = 4003;
int SYSCALL_WRITE  = 4004;
int SYSCALL_OPEN   = 4005;

int SYSCALL_MALLOC = 4045;

// -----------------------------------------------------------------
// ----------------------- HYPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emitSwitch();
void doSwitch(int* toContext, int timeout);
void implementSwitch();
int* mipster_switch(int* toContext, int timeout);

// ------------------------ GLOBAL CONSTANTS -----------------------

int SYSCALL_SWITCH = 4901;

int debug_switch = 0;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void initMemory(int megabytes);

int  loadPhysicalMemory(int* paddr);
void storePhysicalMemory(int* paddr, int data);

int FrameForPage(int* table, int page);
int getFrameForPage(int* table, int page);
int isPageMapped(int* table, int page);

int isValidVirtualAddress(int vaddr);
int getPageOfVirtualAddress(int vaddr);
int isVirtualAddressMapped(int* table, int vaddr);

int* tlb(int* table, int vaddr);

int  loadVirtualMemory(int* table, int vaddr);
void storeVirtualMemory(int* table, int vaddr, int data);

// ------------------------ GLOBAL CONSTANTS -----------------------

int debug_tlb = 0;

// we use the unit [number of words] to prevent overflow problems in calculations
int MEGABYTE = 1048576;         // 1024 * 1024       one megabyte in [number of Bytes]
int MEGABYTEINWORDS = 262144;   // 1024 * 1024 / 4   one megabyte in [number of words]

int HIGHESTMEMORYADDRESS = -4;  // highest word aligned 32bit address in two's complement

int WORDSIZE = 4;               // must be the same as SIZEOFINT and SIZEOFINTSTAR

int PAGESIZE = 4096;            // we use standard 4KB pages [number of bytes] 
                                // (=> 12 pagebits: 2^12 == 4096)
int PAGESIZEINWORDS = 1024;     // page size in words [number of words]

int NUMBEROFPAGES = 1048576;    // 2^32 / PAGESIZE   maximum amount of pages in virtual memory.

// ------------------------ GLOBAL VARIABLES -----------------------

int pageFrameMemory = 0; // size of memory for frames [number of words]

// ------------------------- INITIALIZATION ------------------------

void initMemory(int megabytes) {
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

int debug_overflow = 1;

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void initInterpreter();
void resetInterpreter();

void printException(int exception, int faultingPage);
void throwException(int exception, int faultingPage);

void fetch();
void execute();
void interrupt();

int* runUntilException();

int addressWithMaxCounter(int* counters, int max);

int  printCounters(int total, int* counters, int max);
void printProfile(int* message, int total, int* counters);

void selfie_disassemble();

// ------------------------ GLOBAL CONSTANTS -----------------------

int EXCEPTION_NOEXCEPTION        = 0;
int EXCEPTION_PAGEFAULT          = 1;
int EXCEPTION_SYSCALL            = 2;
int EXCEPTION_TIMER              = 3;
int EXCEPTION_INVALIDADDRESS     = 4;
int EXCEPTION_UNKNOWNINSTRUCTION = 5;

int* EXCEPTIONS; // strings representing exceptions

int debug_exception = 0;

// number of instructions from context switch to timer interrupt
// CAUTION: avoid interrupting any kernel activities, keep TIMESLICE large
// TODO: implement proper interrupt controller to turn interrupts on and off
int TIMESLICE = 10000000;

int TIMEROFF = -1;

// ------------------------ GLOBAL VARIABLES -----------------------

int interpret = 0; // flag for executing or disassembling code

int debug = 0; // flag for logging code execution

// hardware thread state

int pc = 0; // program counter
int ir = 0; // instruction register

int* registers = (int*) 0; // general-purpose registers

int loReg = 0; // lo register for multiplication/division
int hiReg = 0; // hi register for multiplication/division

int* pt = (int*) 0; // page table

// core state

int timer = -1; // counter for timer interrupt

int trap = 0; // flag for creating a trap

int  calls           = 0;        // total number of executed procedure calls
int* callsPerAddress = (int*) 0; // number of executed calls of each procedure

int  loops           = 0;        // total number of executed loop iterations
int* loopsPerAddress = (int*) 0; // number of executed iterations of each loop

int  loads           = 0;        // total number of executed memory loads
int* loadsPerAddress = (int*) 0; // number of executed loads per load operation

int  stores           = 0;        // total number of executed memory stores
int* storesPerAddress = (int*) 0; // number of executed stores per store operation

// ------------------------- INITIALIZATION ------------------------

void initInterpreter() {
  EXCEPTIONS = malloc(6 * SIZEOFINTSTAR);

  *(EXCEPTIONS + EXCEPTION_NOEXCEPTION)        = (int) "no exception";
  *(EXCEPTIONS + EXCEPTION_PAGEFAULT)          = (int) "page fault";
  *(EXCEPTIONS + EXCEPTION_SYSCALL)            = (int) "syscall";
  *(EXCEPTIONS + EXCEPTION_TIMER)              = (int) "timer interrupt";
  *(EXCEPTIONS + EXCEPTION_INVALIDADDRESS)     = (int) "invalid address";
  *(EXCEPTIONS + EXCEPTION_UNKNOWNINSTRUCTION) = (int) "unknown instruction";
}

void resetInterpreter() {
  pc = 0;
  ir = 0;

  registers = (int*) 0;

  loReg = 0;
  hiReg = 0;

  pt = (int*) 0;

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

int* allocateContext(int* parent, int* vctxt, int* in);

int* findContext(int* parent, int* vctxt, int* in);

void freeContext(int* context);
int* deleteContext(int* context, int* from);

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

int nextContext(int* context)    { return (int) context; }
int prevContext(int* context)    { return (int) (context + 1); }
int PC(int* context)             { return (int) (context + 2); }
int Regs(int* context)           { return (int) (context + 3); }
int LoReg(int* context)          { return (int) (context + 4); }
int HiReg(int* context)          { return (int) (context + 5); }
int PT(int* context)             { return (int) (context + 6); }
int LoPage(int* context)         { return (int) (context + 7); }
int MePage(int* context)         { return (int) (context + 8); }
int HiPage(int* context)         { return (int) (context + 9); }
int ProgramBreak(int* context)   { return (int) (context + 10); }
int Exception(int* context)      { return (int) (context + 11); }
int FaultingPage(int* context)   { return (int) (context + 12); }
int ExitCode(int* context)       { return (int) (context + 13); }
int Parent(int* context)         { return (int) (context + 14); }
int VirtualContext(int* context) { return (int) (context + 15); }
int Name(int* context)           { return (int) (context + 16); }

int* getNextContext(int* context)    { return (int*) *context; }
int* getPrevContext(int* context)    { return (int*) *(context + 1); }
int  getPC(int* context)             { return        *(context + 2); }
int* getRegs(int* context)           { return (int*) *(context + 3); }
int  getLoReg(int* context)          { return        *(context + 4); }
int  getHiReg(int* context)          { return        *(context + 5); }
int* getPT(int* context)             { return (int*) *(context + 6); }
int  getLoPage(int* context)         { return        *(context + 7); }
int  getMePage(int* context)         { return        *(context + 8); }
int  getHiPage(int* context)         { return        *(context + 9); }
int  getProgramBreak(int* context)   { return        *(context + 10); }
int  getException(int* context)      { return        *(context + 11); }
int  getFaultingPage(int* context)   { return        *(context + 12); }
int  getExitCode(int* context)       { return        *(context + 13); }
int* getParent(int* context)         { return (int*) *(context + 14); }
int* getVirtualContext(int* context) { return (int*) *(context + 15); }
int* getName(int* context)           { return (int*) *(context + 16); }

void setNextContext(int* context, int* next) { *context       = (int) next; }
void setPrevContext(int* context, int* prev) { *(context + 1) = (int) prev; }
void setPC(int* context, int pc)             { *(context + 2) = pc; }
void setRegs(int* context, int* regs)        { *(context + 3) = (int) regs; }
void setLoReg(int* context, int loReg)       { *(context + 4) = loReg; }
void setHiReg(int* context, int hiReg)       { *(context + 5) = hiReg; }
void setPT(int* context, int* pt)            { *(context + 6) = (int) pt; }
void setLoPage(int* context, int loPage)     { *(context + 7) = loPage; }
void setMePage(int* context, int mePage)     { *(context + 8) = mePage; }
void setHiPage(int* context, int hiPage)     { *(context + 9) = hiPage; }
void setProgramBreak(int* context, int brk)  { *(context + 10) = brk; }
void setException(int* context, int exception) { *(context + 11) = exception; }
void setFaultingPage(int* context, int page) { *(context + 12) = page; }
void setExitCode(int* context, int code)     { *(context + 13) = code; }
void setParent(int* context, int* parent) { *(context + 14) = (int) parent; }
void setVirtualContext(int* context, int* vctxt) { *(context + 15) = (int) vctxt; }
void setName(int* context, int* name) { *(context + 16) = (int) name; }

// -----------------------------------------------------------------
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

void resetMicrokernel();

int* createContext(int* parent, int* vctxt);

int* cacheContext(int* vctxt);

void saveContext(int* context);

void mapPage(int* context, int page, int frame);

void restoreContext(int* context);

// ------------------------ GLOBAL CONSTANTS -----------------------

int debug_create = 0;
int debug_map    = 0;

// ------------------------ GLOBAL VARIABLES -----------------------

int* currentContext = (int*) 0; // context currently running

int* usedContexts = (int*) 0; // doubly-linked list of used contexts
int* freeContexts = (int*) 0; // singly-linked list of free contexts

// ------------------------- INITIALIZATION ------------------------

void resetMicrokernel() {
  currentContext = (int*) 0;

  while (usedContexts != (int*) 0)
    usedContexts = deleteContext(usedContexts, usedContexts);
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

int pavailable();
int pused();

int* palloc();
void pfree(int* frame);

void mapAndStore(int* context, int vaddr, int data);

void up_loadBinary(int* context);

int  up_loadString(int* context, int* s, int SP);
void up_loadArguments(int* context, int argc, int* argv);

void mapUnmappedPages(int* context);

int isBootLevelZero();

int handleSystemCalls(int* context);

int mipster(int* toContext);
int minster(int* toContext);
int mobster(int* toContext);
int hypster(int* toContext);
int mixter(int* toContext, int mix);

int selfie_run(int machine);

// ------------------------ GLOBAL CONSTANTS -----------------------

int* MY_CONTEXT = (int*) 0;

int DONOTEXIT = 0;
int EXIT = 1;

int EXITCODE_NOERROR = 0;
int EXITCODE_IOERROR = -1;
int EXITCODE_SCANNERERROR = -2;
int EXITCODE_PARSERERROR = -3;
int EXITCODE_COMPILERERROR = -4;
int EXITCODE_OUTOFVIRTUALMEMORY = -5;
int EXITCODE_OUTOFPHYSICALMEMORY = -6;
int EXITCODE_UNKNOWNSYSCALL = -7;
int EXITCODE_UNCAUGHTEXCEPTION = -8;

int MINSTER = 1;
int MIPSTER = 2;
int MOBSTER = 3;

int HYPSTER = 4;

// ------------------------ GLOBAL VARIABLES -----------------------

int nextPageFrame = 0;        // [number of words]

int usedPageFrameMemory = 0;  // [number of words]
int freePageFrameMemory = 0;  // [number of words]

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------   T H E O R E M  P R O V E R    ----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// -------------------------- SAT Solver ---------------------------
// -----------------------------------------------------------------

int FALSE = 0;
int TRUE  = 1;

int UNSAT = 0;
int SAT   = 1;

int* dimacsName = (int*) 0;

int numberOfSATVariables = 0;

 // numberOfSATVariables
int* SATAssignment = (int*) 0;

int numberOfSATClauses = 0;

// numberOfSATClauses * 2 * numberOfSATVariables
int* SATInstance = (int*) 0;

int clauseMayBeTrue(int* clauseAddress, int depth);
int instanceMayBeTrue(int depth);

int babysat(int depth);

// -----------------------------------------------------------------
// ----------------------- DIMACS CNF PARSER -----------------------
// -----------------------------------------------------------------

void selfie_printDimacs();

void dimacs_findNextCharacter(int newLine);
void dimacs_getSymbol();
void dimacs_word(int* word);
int  dimacs_number();
void dimacs_getClause(int clause);
void dimacs_getInstance();

void selfie_loadDimacs();

void selfie_sat();

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

void initSelfie(int argc, int* argv);

int numberOfRemainingArguments();
int* remainingArguments();

int* peekArgument();
int* getArgument();
void setArgument(int* argv);

void printUsage();

// ------------------------ GLOBAL VARIABLES -----------------------

int selfie_argc = 0;
int* selfie_argv = (int*) 0;

int* selfieName = (int*) 0;

// ------------------------- INITIALIZATION ------------------------

void initSelfie(int argc, int* argv) {
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

int addWrap(int a, int b) {
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

int subtractWrap(int a, int b) {
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

int multiplyWrap(int a, int b) {
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

void checkDivision(int a, int b) {
  INT_OVERFLOW = OVERFLOW_NO;

  if (b == 0)
    INT_OVERFLOW = OVERFLOW_YES;
  else if (a == INT_MIN)
    if (b == -1)
      INT_OVERFLOW = OVERFLOW_YES;
}

int twoToThePowerOf(int p) {
  // assert: 0 <= p < 31
  return *(power_of_two_table + p);
}

int leftShift(int n, int b) {
  int t;

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

int rightShift(int n, int b) {
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

int loadCharacter(int* s, int i) {
  // assert: i >= 0
  int a;

  // a is the index of the word where the to-be-loaded i-th character in s is
  a = i / SIZEOFINT;

  // shift to-be-loaded character to the left resetting all bits to the left
  // then shift to-be-loaded character all the way to the right and return
  return rightShift(leftShift(*(s + a), ((SIZEOFINT - 1) - (i % SIZEOFINT)) * 8), (SIZEOFINT - 1) * 8);
}

int* storeCharacter(int* s, int i, int c) {
  // assert: i >= 0, all characters are 7-bit
  int a;

  // a is the index of the word where the with c
  // to-be-overwritten i-th character in s is
  a = i / SIZEOFINT;

  // subtract the to-be-overwritten character resetting its bits in s
  // then add c setting its bits at the i-th position in s
  *(s + a) = (*(s + a) - leftShift(loadCharacter(s, i), (i % SIZEOFINT) * 8)) + leftShift(c, (i % SIZEOFINT) * 8);

  return s;
}

int stringLength(int* s) {
  int i;

  i = 0;

  while (loadCharacter(s, i) != 0)
    i = i + 1;

  return i;
}

void stringReverse(int* s) {
  int i;
  int j;
  int tmp;

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

int stringCompare(int* s, int* t) {
  int i;

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

int atoi(int* s) {
  int i;
  int n;
  int c;

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

int* itoa(int n, int* s, int b, int a, int p) {
  // assert: b in {2,4,8,10,16}

  int i;
  int sign;
  int msb;

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

int fixedPointRatio(int a, int b) {
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

int fixedPointPercentage(int r) {
  if (r != 0)
    // 1000000 = 10000 (for 100.00%) * 100 (for 2 fractional digits of r)
    return 1000000 / r;
  else
    return 0;
}

void putCharacter(int c) {
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
      print((int*) ": could not write character to output file ");
      print(outputName);
      println();
    }

    exit(EXITCODE_IOERROR);
  }
}

void print(int* s) {
  int i;

  if (s == (int*) 0)
    print((int*) "NULL");
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

void printCharacter(int c) {
  putCharacter(CHAR_SINGLEQUOTE);

  if (c == CHAR_EOF)
    print((int*) "end of file");
  else if (c == CHAR_TAB)
    print((int*) "tabulator");
  else if (c == CHAR_LF)
    print((int*) "line feed");
  else if (c == CHAR_CR)
    print((int*) "carriage return");
  else
    putCharacter(c);

  putCharacter(CHAR_SINGLEQUOTE);
}

void printString(int* s) {
  putCharacter(CHAR_DOUBLEQUOTE);

  print(s);

  putCharacter(CHAR_DOUBLEQUOTE);
}

void printInteger(int n) {
  print(itoa(n, integer_buffer, 10, 0, 0));
}

void printFixedPointPercentage(int a, int b) {
  print(itoa(fixedPointPercentage(fixedPointRatio(a, b)), integer_buffer, 10, 0, 2));
}

void printFixedPointRatio(int a, int b) {
  print(itoa(fixedPointRatio(a, b), integer_buffer, 10, 0, 2));
}

void printHexadecimal(int n, int a) {
  print(itoa(n, integer_buffer, 16, a, 0));
}

void printOctal(int n, int a) {
  print(itoa(n, integer_buffer, 8, a, 0));
}

void printBinary(int n, int a) {
  print(itoa(n, integer_buffer, 2, a, 0));
}

int roundUp(int n, int m) {
  if (n % m == 0)
    return n;
  else if (n >= 0)
    return n + m - n % m;
  else
    return n - n % m;
}

int* zalloc(int size) {
  // this procedure is only executed at boot level zero
  // zalloc allocates size bytes rounded up to word size
  // and then zeroes that memory, similar to calloc, but
  // called zalloc to avoid redeclaring calloc
  int* memory;
  int  i;

  size = roundUp(size, WORDSIZE);

  memory = malloc(size);

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

void printSymbol(int symbol) {
  putCharacter(CHAR_DOUBLEQUOTE);

  if (symbol == SYM_EOF)
    print((int*) "end of file");
  else
    print((int*) *(SYMBOLS + symbol));

  putCharacter(CHAR_DOUBLEQUOTE);
}

void printLineNumber(int* message, int line) {
  print(selfieName);
  print((int*) ": ");
  print(message);
  print((int*) " in ");
  print(sourceName);
  print((int*) " in line ");
  printInteger(line);
  print((int*) ": ");
}

void syntaxErrorMessage(int* message) {
  printLineNumber((int*) "error", lineNumber);

  print(message);

  println();
}

void syntaxErrorCharacter(int expected) {
  printLineNumber((int*) "error", lineNumber);

  printCharacter(expected);
  print((int*) " expected but ");

  printCharacter(character);
  print((int*) " found");

  println();
}

void syntaxErrorIdentifier(int* expected) {
  printLineNumber((int*) "error", lineNumber);

  print(expected);
  print((int*) " expected but ");

  print(identifier);
  print((int*) " found");

  println();
}

void getCharacter() {
  int numberOfReadBytes;

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
    print((int*) ": could not read character from input file ");
    print(sourceName);
    println();

    exit(EXITCODE_IOERROR);
  }
}

int isCharacterNewLine() {
  if (character == CHAR_LF)
    return 1;
  else if (character == CHAR_CR)
    return 1;
  else
    return 0;
}

int isCharacterWhitespace() {
  if (character == CHAR_SPACE)
    return 1;
  else if (character == CHAR_TAB)
    return 1;
  else
    return isCharacterNewLine();
}

int findNextCharacter() {
  int inComment;

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

int isCharacterLetter() {
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

int isCharacterDigit() {
  // ASCII codes for digits are in a contiguous interval
  if (character >= '0')
    if (character <= '9')
      return 1;
    else
      return 0;
  else
    return 0;
}

int isCharacterLetterOrDigitOrUnderscore() {
  if (isCharacterLetter())
    return 1;
  else if (isCharacterDigit())
    return 1;
  else if (character == CHAR_UNDERSCORE)
    return 1;
  else
    return 0;
}

int isCharacterNotDoubleQuoteOrNewLineOrEOF() {
  if (character == CHAR_DOUBLEQUOTE)
    return 0;
  else if (isCharacterNewLine())
    return 0;
  else if (character == CHAR_EOF)
    return 0;
  else
    return 1;
}

int identifierStringMatch(int keyword) {
  return stringCompare(identifier, (int*) *(SYMBOLS + keyword));
}

int identifierOrKeyword() {
  if (identifierStringMatch(SYM_WHILE))
    return SYM_WHILE;
  if (identifierStringMatch(SYM_IF))
    return SYM_IF;
  if (identifierStringMatch(SYM_INT))
    return SYM_INT;
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
  int i;

  // reset previously scanned symbol
  symbol = SYM_EOF;

  if (findNextCharacter() != CHAR_EOF) {
    if (symbol != SYM_DIV) {
      // '/' may have already been recognized
      // while looking for whitespace and "//"
      if (isCharacterLetter()) {
        // accommodate identifier and null for termination
        identifier = malloc(maxIdentifierLength + 1);

        i = 0;

        while (isCharacterLetterOrDigitOrUnderscore()) {
          if (i >= maxIdentifierLength) {
            syntaxErrorMessage((int*) "identifier too long");

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
        integer = malloc(maxIntegerLength + 1);

        i = 0;

        while (isCharacterDigit()) {
          if (i >= maxIntegerLength) {
            syntaxErrorMessage((int*) "integer out of bound");

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
              syntaxErrorMessage((int*) "integer out of bound");

              exit(EXITCODE_SCANNERERROR);
            }
          } else {
            syntaxErrorMessage((int*) "integer out of bound");

            exit(EXITCODE_SCANNERERROR);
          }
        }

        symbol = SYM_INTEGER;

      } else if (character == CHAR_SINGLEQUOTE) {
        getCharacter();

        literal = 0;

        if (character == CHAR_EOF) {
          syntaxErrorMessage((int*) "reached end of file looking for a character literal");

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
            syntaxErrorMessage((int*) "string too long");

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
        printLineNumber((int*) "error", lineNumber);
        print((int*) "found unknown character ");
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

void createSymbolTableEntry(int whichTable, int* string, int line, int class, int type, int value, int address) {
  int* newEntry;

  newEntry = malloc(2 * SIZEOFINTSTAR + 6 * SIZEOFINT);

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

int* searchSymbolTable(int* entry, int* string, int class) {
  while (entry != (int*) 0) {
    if (stringCompare(string, getString(entry)))
      if (class == getClass(entry))
        return entry;

    // keep looking
    entry = getNextEntry(entry);
  }

  return (int*) 0;
}

int* getScopedSymbolTableEntry(int* string, int class) {
  int* entry;

  if (class == VARIABLE)
    // local variables override global variables
    entry = searchSymbolTable(local_symbol_table, string, VARIABLE);
  else if (class == PROCEDURE)
    // library procedures override declared or defined procedures
    entry = searchSymbolTable(library_symbol_table, string, PROCEDURE);
  else
    entry = (int*) 0;

  if (entry == (int*) 0)
    return searchSymbolTable(global_symbol_table, string, class);
  else
    return entry;
}

int isUndefinedProcedure(int* entry) {
  int* libraryEntry;

  if (getClass(entry) == PROCEDURE) {
    // library procedures override declared or defined procedures
    libraryEntry = searchSymbolTable(library_symbol_table, getString(entry), PROCEDURE);

    if (libraryEntry != (int*) 0)
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

int reportUndefinedProcedures() {
  int undefined;
  int* entry;

  undefined = 0;

  entry = global_symbol_table;

  while (entry != (int*) 0) {
    if (isUndefinedProcedure(entry)) {
      undefined = 1;

      printLineNumber((int*) "error", getLineNumber(entry));
      print((int*) "procedure ");
      print(getString(entry));
      print((int*) " undefined");
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

int isNotRbraceOrEOF() {
  if (symbol == SYM_RBRACE)
    return 0;
  else if (symbol == SYM_EOF)
    return 0;
  else
    return 1;
}

int isExpression() {
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

int isLiteral() {
  if (symbol == SYM_INTEGER)
    return 1;
  else if (symbol == SYM_CHARACTER)
    return 1;
  else
    return 0;
}

int isStarOrDivOrModulo() {
  if (symbol == SYM_ASTERISK)
    return 1;
  else if (symbol == SYM_DIV)
    return 1;
  else if (symbol == SYM_MOD)
    return 1;
  else
    return 0;
}

int isPlusOrMinus() {
  if (symbol == SYM_MINUS)
    return 1;
  else if (symbol == SYM_PLUS)
    return 1;
  else
    return 0;
}

int isComparison() {
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

int lookForFactor() {
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

int lookForStatement() {
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

int lookForType() {
  if (symbol == SYM_INT)
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
    syntaxErrorMessage((int*) "out of registers");

    exit(EXITCODE_COMPILERERROR);
  }
}

int currentTemporary() {
  if (allocatedTemporaries > 0)
    return allocatedTemporaries + REG_A3;
  else {
    syntaxErrorMessage((int*) "illegal register access");

    exit(EXITCODE_COMPILERERROR);
  }
}

int previousTemporary() {
  if (allocatedTemporaries > 1)
    return currentTemporary() - 1;
  else {
    syntaxErrorMessage((int*) "illegal register access");

    exit(EXITCODE_COMPILERERROR);
  }
}

int nextTemporary() {
  if (allocatedTemporaries < REG_T7 - REG_A3)
    return currentTemporary() + 1;
  else {
    syntaxErrorMessage((int*) "out of registers");

    exit(EXITCODE_COMPILERERROR);
  }
}

void tfree(int numberOfTemporaries) {
  allocatedTemporaries = allocatedTemporaries - numberOfTemporaries;

  if (allocatedTemporaries < 0) {
    syntaxErrorMessage((int*) "illegal register deallocation");

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

void restore_temporaries(int numberOfTemporaries) {
  while (allocatedTemporaries < numberOfTemporaries) {
    talloc();

    // restore temporary from stack
    emitIFormat(OP_LW, REG_SP, currentTemporary(), 0);
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);
  }
}

void syntaxErrorSymbol(int expected) {
  printLineNumber((int*) "error", lineNumber);

  printSymbol(expected);
  print((int*) " expected but ");

  printSymbol(symbol);
  print((int*) " found");

  println();
}

void syntaxErrorUnexpected() {
  printLineNumber((int*) "error", lineNumber);

  print((int*) "unexpected symbol ");
  printSymbol(symbol);
  print((int*) " found");

  println();
}

void printType(int type) {
  if (type == INT_T)
    print((int*) "int");
  else if (type == INTSTAR_T)
    print((int*) "int*");
  else if (type == VOID_T)
    print((int*) "void");
  else
    print((int*) "unknown");
}

void typeWarning(int expected, int found) {
  printLineNumber((int*) "warning", lineNumber);

  print((int*) "type mismatch, ");

  printType(expected);

  print((int*) " expected but ");

  printType(found);

  print((int*) " found");

  println();
}

int* getVariable(int* variable) {
  int* entry;

  entry = getScopedSymbolTableEntry(variable, VARIABLE);

  if (entry == (int*) 0) {
    printLineNumber((int*) "error", lineNumber);
    print(variable);
    print((int*) " undeclared");
    println();

    exit(EXITCODE_PARSERERROR);
  }

  return entry;
}

int load_variable(int* variable) {
  int* entry;

  entry = getVariable(variable);

  talloc();

  emitIFormat(OP_LW, getScope(entry), currentTemporary(), getAddress(entry));

  return getType(entry);
}

void load_integer(int value) {
  int isNegative;

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

void load_string(int* string) {
  int length;

  length = stringLength(string) + 1;

  allocatedMemory = allocatedMemory + roundUp(length, WORDSIZE);

  createSymbolTableEntry(GLOBAL_TABLE, string, lineNumber, STRING, INTSTAR_T, 0, -allocatedMemory);

  talloc();

  emitIFormat(OP_ADDIU, REG_GP, currentTemporary(), -allocatedMemory);
}

int help_call_codegen(int* entry, int* procedure) {
  int type;

  if (entry == (int*) 0) {
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

void help_procedure_prologue(int localVariables) {
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

void help_procedure_epilogue(int parameters) {
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

int gr_call(int* procedure) {
  int* entry;
  int numberOfTemporaries;
  int type;

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

int gr_factor() {
  int hasCast;
  int cast;
  int type;

  int* variableOrProcedureName;

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

    // cast: "(" "int" [ "*" ] ")"
    if (symbol == SYM_INT) {
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

int gr_term() {
  int ltype;
  int operatorSymbol;
  int rtype;

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

int gr_simpleExpression() {
  int sign;
  int ltype;
  int operatorSymbol;
  int rtype;

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
          syntaxErrorMessage((int*) "(int*) + (int*) is undefined");
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
          emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_SUBU);
          emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), SIZEOFINT);
          emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), 0, FCT_DIVU);
          emitRFormat(OP_SPECIAL, 0, 0, previousTemporary(), FCT_MFLO);

          ltype = INT_T;
        }
      } else if (rtype == INTSTAR_T)
        // INT_T - INTSTAR_T
        syntaxErrorMessage((int*) "(int) - (int*) is undefined");
      else
        // INT_T - INT_T
        emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_SUBU);
    }

    tfree(1);
  }

  // assert: allocatedTemporaries == n + 1

  return ltype;
}

int gr_expression() {
  int ltype;
  int operatorSymbol;
  int rtype;

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
  int brBackToWhile;
  int brForwardToEnd;

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
  int brForwardToElseOrEnd;
  int brForwardToEnd;

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
  int type;

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
  int ltype;
  int rtype;
  int* variableOrProcedureName;
  int* entry;

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

int gr_type() {
  int type;

  type = INT_T;

  if (symbol == SYM_INT) {
    getSymbol();

    if (symbol == SYM_ASTERISK) {
      type = INTSTAR_T;

      getSymbol();
    }
  } else
    syntaxErrorSymbol(SYM_INT);

  return type;
}

void gr_variable(int offset) {
  int type;

  type = gr_type();

  if (symbol == SYM_IDENTIFIER) {
    // TODO: check if identifier has already been declared
    createSymbolTableEntry(LOCAL_TABLE, identifier, lineNumber, VARIABLE, type, 0, offset);

    getSymbol();
  } else {
    syntaxErrorSymbol(SYM_IDENTIFIER);

    createSymbolTableEntry(LOCAL_TABLE, (int*) "missing variable name", lineNumber, VARIABLE, type, 0, offset);
  }
}

int gr_initialization(int type) {
  int initialValue;
  int hasCast;
  int cast;
  int sign;

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

void gr_procedure(int* procedure, int type) {
  int isUndefined;
  int numberOfParameters;
  int parameters;
  int localVariables;
  int* entry;

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
    if (entry == (int*) 0)
      // procedure never called nor declared nor defined
      createSymbolTableEntry(GLOBAL_TABLE, procedure, lineNumber, PROCEDURE, type, 0, 0);
    else if (getType(entry) != type)
      // procedure already called, declared, or even defined
      // check return type but otherwise ignore
      typeWarning(getType(entry), type);

    getSymbol();

  } else if (symbol == SYM_LBRACE) {
    // this is a procedure definition
    if (entry == (int*) 0)
      // procedure never called nor declared nor defined
      createSymbolTableEntry(GLOBAL_TABLE, procedure, lineNumber, PROCEDURE, type, 0, binaryLength);
    else {
      // procedure already called or declared or defined
      if (getAddress(entry) != 0) {
        // procedure already called or defined
        if (getOpcode(loadBinary(getAddress(entry))) == OP_JAL) {
          // procedure already called but not defined
          fixlink_absolute(getAddress(entry), binaryLength);

          if (stringCompare(procedure, (int*) "main"))
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
        printLineNumber((int*) "warning", lineNumber);
        print((int*) "redefinition of procedure ");
        print(procedure);
        print((int*) " ignored");
        println();
      }
    }

    getSymbol();

    localVariables = 0;

    while (symbol == SYM_INT) {
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

  local_symbol_table = (int*) 0;

  // assert: allocatedTemporaries == 0
}

void gr_cstar() {
  int type;
  int* variableOrProcedureName;
  int currentLineNumber;
  int initialValue;
  int* entry;

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

          if (entry == (int*) 0) {
            allocatedMemory = allocatedMemory + WORDSIZE;

            createSymbolTableEntry(GLOBAL_TABLE, variableOrProcedureName, currentLineNumber, VARIABLE, type, initialValue, -allocatedMemory);
          } else {
            // global variable already declared or defined
            printLineNumber((int*) "warning", currentLineNumber);
            print((int*) "redefinition of global variable ");
            print(variableOrProcedureName);
            print((int*) " ignored");
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

void emitLeftShiftBy(int reg, int b) {
  // assert: 0 <= b < 15

  // load multiplication factor less than 2^15 to avoid sign extension
  emitIFormat(OP_ADDIU, REG_ZR, nextTemporary(), twoToThePowerOf(b));
  emitRFormat(OP_SPECIAL, reg, nextTemporary(), 0, FCT_MULTU);
  emitRFormat(OP_SPECIAL, 0, 0, reg, FCT_MFLO);
}

void emitMainEntry() {
  int i;

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

  createSymbolTableEntry(GLOBAL_TABLE, (int*) "main", 0, PROCEDURE, INT_T, 0, mainJump);

  // jump and link to main, will return here only if there is no exit call
  emitJFormat(OP_JAL, 0);

  // we exit with exit code in return register pushed onto the stack
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, -WORDSIZE);
  emitIFormat(OP_SW, REG_SP, REG_V0, 0);

  // no need to reset return register here
}

void bootstrapCode() {
  int savedBinaryLength;

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
  int link;
  int numberOfSourceFiles;

  // link until next console option
  link = 1;

  numberOfSourceFiles = 0;

  sourceName = (int*) "library";

  binaryName = sourceName;

  // allocate memory for storing binary
  binary       = malloc(maxBinaryLength);
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
      print((int*) ": this is selfie compiling ");
      print(sourceName);
      print((int*) " with starc");
      println();

      // assert: sourceName is mapped and not longer than maxFilenameLength

      sourceFD = open(sourceName, O_RDONLY, 0);

      if (sourceFD < 0) {
        print(selfieName);
        print((int*) ": could not open input file ");
        print(sourceName);
        println();

        exit(EXITCODE_IOERROR);
      }

      resetScanner();
      resetParser();

      // compile
      gr_cstar();

      print(selfieName);
      print((int*) ": ");
      printInteger(numberOfReadCharacters);
      print((int*) " characters read in ");
      printInteger(lineNumber - 1);
      print((int*) " lines and ");
      printInteger(numberOfComments);
      print((int*) " comments");
      println();

      print(selfieName);
      print((int*) ": with ");
      printInteger(numberOfReadCharacters - numberOfIgnoredCharacters);
      print((int*) "(");
      printFixedPointPercentage(numberOfReadCharacters, numberOfReadCharacters - numberOfIgnoredCharacters);
      print((int*) "%) characters in ");
      printInteger(numberOfScannedSymbols);
      print((int*) " actual symbols");
      println();

      print(selfieName);
      print((int*) ": ");
      printInteger(numberOfGlobalVariables);
      print((int*) " global variables, ");
      printInteger(numberOfProcedures);
      print((int*) " procedures, ");
      printInteger(numberOfStrings);
      print((int*) " string literals");
      println();

      print(selfieName);
      print((int*) ": ");
      printInteger(numberOfCalls);
      print((int*) " calls, ");
      printInteger(numberOfAssignments);
      print((int*) " assignments, ");
      printInteger(numberOfWhile);
      print((int*) " while, ");
      printInteger(numberOfIf);
      print((int*) " if, ");
      printInteger(numberOfReturn);
      print((int*) " return");
      println();
    }
  }

  if (numberOfSourceFiles == 0) {
    print(selfieName);
    print((int*) ": nothing to compile, only library generated");
    println();
  }

  codeLength = binaryLength;

  emitGlobalsStrings();

  bootstrapCode();

  print(selfieName);
  print((int*) ": ");
  printInteger(binaryLength + WORDSIZE);
  print((int*) " bytes generated with ");
  printInteger(codeLength / WORDSIZE);
  print((int*) " instructions and ");
  printInteger(binaryLength - codeLength + WORDSIZE);
  print((int*) " bytes of data");
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

void printRegister(int reg) {
  print((int*) *(REGISTERS + reg));
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
int encodeRFormat(int opcode, int rs, int rt, int rd, int function) {
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
int encodeIFormat(int opcode, int rs, int rt, int immediate) {
  // assert: 0 <= opcode < 2^6
  // assert: 0 <= rs < 2^5
  // assert: 0 <= rt < 2^5
  // assert: -2^15 <= immediate < 2^15
  if (immediate < 0)
    // convert from 32-bit to 16-bit two's complement
    immediate = immediate + twoToThePowerOf(16);

  return leftShift(leftShift(leftShift(opcode, 5) + rs, 5) + rt, 16) + immediate;
}

// --------------------------------------------------------------
// 32 bit
//
// +------+--------------------------+
// |opcode|       instr_index        |
// +------+--------------------------+
//    6                26
int encodeJFormat(int opcode, int instr_index) {
  // assert: 0 <= opcode < 2^6
  // assert: 0 <= instr_index < 2^26
  return leftShift(opcode, 26) + instr_index;
}

// -----------------------------------------------------------------
// ---------------------------- DECODER ----------------------------
// -----------------------------------------------------------------

int getOpcode(int instruction) {
  return rightShift(instruction, 26);
}

int getRS(int instruction) {
  return rightShift(leftShift(instruction, 6), 27);
}

int getRT(int instruction) {
  return rightShift(leftShift(instruction, 11), 27);
}

int getRD(int instruction) {
  return rightShift(leftShift(instruction, 16), 27);
}

int getFunction(int instruction) {
  return rightShift(leftShift(instruction, 26), 26);
}

int getImmediate(int instruction) {
  return rightShift(leftShift(instruction, 16), 16);
}

int getInstrIndex(int instruction) {
  return rightShift(leftShift(instruction, 6), 6);
}

int signExtend(int immediate) {
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

void printOpcode(int opcode) {
  print((int*) *(OPCODES + opcode));
}

void printFunction(int function) {
  print((int*) *(FUNCTIONS + function));
}

// -----------------------------------------------------------------
// ----------------------------- CODE ------------------------------
// -----------------------------------------------------------------

int loadBinary(int baddr) {
  return *(binary + baddr / WORDSIZE);
}

void storeBinary(int baddr, int instruction) {
  if (baddr >= maxBinaryLength) {
    syntaxErrorMessage((int*) "maximum binary length exceeded");

    exit(EXITCODE_COMPILERERROR);
  }

  *(binary + baddr / WORDSIZE) = instruction;
}

void emitInstruction(int instruction) {
  storeBinary(binaryLength, instruction);

  if (*(sourceLineNumber + binaryLength / WORDSIZE) == 0)
    *(sourceLineNumber + binaryLength / WORDSIZE) = lineNumber;

  binaryLength = binaryLength + WORDSIZE;
}

void emitRFormat(int opcode, int rs, int rt, int rd, int function) {
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

void emitIFormat(int opcode, int rs, int rt, int immediate) {
  emitInstruction(encodeIFormat(opcode, rs, rt, immediate));

  if (opcode == OP_BEQ)
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_NOP); // delay slot
}

void emitJFormat(int opcode, int instr_index) {
  emitInstruction(encodeJFormat(opcode, instr_index));

  emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_NOP); // delay slot
}

void fixup_relative(int fromAddress) {
  int instruction;

  instruction = loadBinary(fromAddress);

  storeBinary(fromAddress,
    encodeIFormat(getOpcode(instruction),
      getRS(instruction),
      getRT(instruction),
      (binaryLength - fromAddress - WORDSIZE) / WORDSIZE));
}

void fixup_absolute(int fromAddress, int toAddress) {
  storeBinary(fromAddress,
    encodeJFormat(getOpcode(loadBinary(fromAddress)), toAddress / WORDSIZE));
}

void fixlink_absolute(int fromAddress, int toAddress) {
  int previousAddress;

  while (fromAddress != 0) {
    previousAddress = getInstrIndex(loadBinary(fromAddress)) * WORDSIZE;

    fixup_absolute(fromAddress, toAddress);

    fromAddress = previousAddress;
  }
}

int copyStringToBinary(int* s, int baddr) {
  int next;

  next = baddr + roundUp(stringLength(s) + 1, WORDSIZE);

  while (baddr < next) {
    storeBinary(baddr, *s);

    s = s + 1;

    baddr = baddr + WORDSIZE;
  }

  return next;
}

void emitGlobalsStrings() {
  int* entry;

  entry = global_symbol_table;

  // assert: n = binaryLength

  // allocate space for global variables and copy strings
  while ((int) entry != 0) {
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

int openWriteOnly(int* name) {
  // we try opening write-only files using platform-specific flags
  // to make selfie platform-independent, this may nevertheless
  // not always work and require intervention
  int fd;

  // try Mac flags
  fd = open(name, MAC_O_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH);

  if (fd < 0) {
    // try Linux flags
    fd = open(name, LINUX_O_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH);

    if (fd < 0)
      // try Windows flags
      fd = open(name, WINDOWS_O_BINARY_CREAT_TRUNC_WRONLY, S_IRUSR_IWUSR_IRGRP_IROTH);
  }

  return fd;
}

void selfie_output() {
  int fd;

  binaryName = getArgument();

  if (binaryLength == 0) {
    print(selfieName);
    print((int*) ": nothing to emit to output file ");
    print(binaryName);
    println();

    return;
  }

  // assert: binaryName is mapped and not longer than maxFilenameLength

  fd = openWriteOnly(binaryName);

  if (fd < 0) {
    print(selfieName);
    print((int*) ": could not create binary output file ");
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
  print((int*) ": ");
  printInteger(binaryLength + WORDSIZE);
  print((int*) " bytes with ");
  printInteger(codeLength / WORDSIZE);
  print((int*) " instructions and ");
  printInteger(binaryLength - codeLength + WORDSIZE);
  print((int*) " bytes of data written into ");
  print(binaryName);
  println();
}

int* touch(int* memory, int length) {
  int* m;
  int n;

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
  int fd;
  int numberOfReadBytes;

  binaryName = getArgument();

  // assert: binaryName is mapped and not longer than maxFilenameLength

  fd = open(binaryName, O_RDONLY, 0);

  if (fd < 0) {
    print(selfieName);
    print((int*) ": could not open input file ");
    print(binaryName);
    println();

    exit(EXITCODE_IOERROR);
  }

  // make sure binary is mapped
  binary = touch(malloc(maxBinaryLength), maxBinaryLength);

  binaryLength = 0;
  codeLength   = 0;

  // no source line numbers in binaries
  sourceLineNumber = (int*) 0;

  // assert: binary_buffer is mapped

  // read code length first
  numberOfReadBytes = read(fd, binary_buffer, WORDSIZE);

  if (numberOfReadBytes == WORDSIZE) {
    codeLength = *binary_buffer;

    if (codeLength <= maxBinaryLength) {
      // assert: binary is mapped

      // now read binary including global variables and strings
      numberOfReadBytes = read(fd, binary, maxBinaryLength);

      if (numberOfReadBytes > 0) {
        binaryLength = numberOfReadBytes;

        // check if we are really at EOF
        if (read(fd, binary_buffer, WORDSIZE) == 0) {
          print(selfieName);
          print((int*) ": ");
          printInteger(binaryLength + WORDSIZE);
          print((int*) " bytes with ");
          printInteger(codeLength / WORDSIZE);
          print((int*) " instructions and ");
          printInteger(binaryLength - codeLength + WORDSIZE);
          print((int*) " bytes of data loaded from ");
          print(binaryName);
          println();

          return;
        }
      }
    }
  }

  print(selfieName);
  print((int*) ": failed to load code from input file ");
  print(binaryName);
  println();

  exit(EXITCODE_IOERROR);
}

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emitExit() {
  createSymbolTableEntry(LIBRARY_TABLE, (int*) "exit", 0, PROCEDURE, VOID_T, 0, binaryLength);

  // load argument for exit
  emitIFormat(OP_LW, REG_SP, REG_A0, 0); // exit code

  // remove the argument from the stack
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

  // load the correct syscall number and invoke syscall
  emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_EXIT);
  emitRFormat(0, 0, 0, 0, FCT_SYSCALL);

  // never returns here
}

void implementExit(int* context) {
  setExitCode(context, *(getRegs(context)+REG_A0));

  print(selfieName);
  print((int*) ": ");
  print(getName(context));
  print((int*) " exiting with exit code ");
  printInteger(getExitCode(context));
  print((int*) " and ");
  printFixedPointRatio(getProgramBreak(context) - maxBinaryLength, MEGABYTE);
  print((int*) "MB of mallocated memory");
  println();
}

void emitRead() {
  createSymbolTableEntry(LIBRARY_TABLE, (int*) "read", 0, PROCEDURE, INT_T, 0, binaryLength);

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

void implementRead(int* context) {
  int size;
  int vaddr;
  int fd;
  int readTotal;
  int bytesToRead;
  int* buffer;
  int actuallyRead;
  int failed;

  // assert: read buffer is mapped

  size  = *(getRegs(context)+REG_A2);
  vaddr = *(getRegs(context)+REG_A1);
  fd    = *(getRegs(context)+REG_A0);

  if (debug_read) {
    print(selfieName);
    print((int*) ": trying to read ");
    printInteger(size);
    print((int*) " bytes from file with descriptor ");
    printInteger(fd);
    print((int*) " into buffer at virtual address ");
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
          if (actuallyRead > 0)
            readTotal = readTotal + actuallyRead;

          size = 0;
        }
      } else {
        failed = 1;

        size = 0;

        if (debug_read) {
          print(selfieName);
          print((int*) ": reading into virtual address ");
          printHexadecimal(vaddr, 8);
          print((int*) " failed because the address is unmapped");
          println();
        }
      }
    } else {
      failed = 1;

      size = 0;

      if (debug_read) {
        print(selfieName);
        print((int*) ": reading into virtual address ");
        printHexadecimal(vaddr, 8);
        print((int*) " failed because the address is invalid");
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
    print((int*) ": actually read ");
    printInteger(readTotal);
    print((int*) " bytes from file with descriptor ");
    printInteger(fd);
    println();
  }
}

void emitWrite() {
  createSymbolTableEntry(LIBRARY_TABLE, (int*) "write", 0, PROCEDURE, INT_T, 0, binaryLength);

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

void implementWrite(int* context) {
  int size;
  int vaddr;
  int fd;
  int writtenTotal;
  int bytesToWrite;
  int* buffer;
  int actuallyWritten;
  int failed;

  // assert: write buffer is mapped

  size  = *(getRegs(context)+REG_A2);
  vaddr = *(getRegs(context)+REG_A1);
  fd    = *(getRegs(context)+REG_A0);

  if (debug_write) {
    print(selfieName);
    print((int*) ": trying to write ");
    printInteger(size);
    print((int*) " bytes from buffer at virtual address ");
    printHexadecimal(vaddr, 8);
    print((int*) " into file with descriptor ");
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
          if (actuallyWritten > 0)
            writtenTotal = writtenTotal + actuallyWritten;

          size = 0;
        }
      } else {
        failed = 1;

        size = 0;

        if (debug_write) {
          print(selfieName);
          print((int*) ": writing into virtual address ");
          printHexadecimal(vaddr, 8);
          print((int*) " failed because the address is unmapped");
          println();
        }
      }
    } else {
      failed = 1;

      size = 0;

      if (debug_write) {
        print(selfieName);
        print((int*) ": writing into virtual address ");
        printHexadecimal(vaddr, 8);
        print((int*) " failed because the address is invalid");
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
    print((int*) ": actually wrote ");
    printInteger(writtenTotal);
    print((int*) " bytes into file with descriptor ");
    printInteger(fd);
    println();
  }
}

void emitOpen() {
  createSymbolTableEntry(LIBRARY_TABLE, (int*) "open", 0, PROCEDURE, INT_T, 0, binaryLength);

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

int down_loadString(int* table, int vaddr, int* s) {
  int i;
  int* paddr;

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
          print((int*) ": opening file with name at virtual address ");
          printHexadecimal(vaddr, 8);
          print((int*) " failed because the address is unmapped");
          println();
        }
      }
    } else {
      if (debug_open) {
        print(selfieName);
        print((int*) ": opening file with name at virtual address ");
        printHexadecimal(vaddr, 8);
        print((int*) " failed because the address is invalid");
        println();
      }
    }
  }

  return 0;
}

void implementOpen(int* context) {
  int mode;
  int flags;
  int vaddr;
  int fd;

  mode  = *(getRegs(context)+REG_A2);
  flags = *(getRegs(context)+REG_A1);
  vaddr = *(getRegs(context)+REG_A0);

  if (down_loadString(getPT(context), vaddr, filename_buffer)) {
    fd = open(filename_buffer, flags, mode);

    *(getRegs(context)+REG_V0) = fd;

    if (debug_open) {
      print(selfieName);
      print((int*) ": opened file ");
      printString(filename_buffer);
      print((int*) " with flags ");
      printHexadecimal(flags, 0);
      print((int*) " and mode ");
      printOctal(mode, 0);
      print((int*) " returning file descriptor ");
      printInteger(fd);
      println();
    }
  } else {
    *(getRegs(context)+REG_V0) = -1;

    if (debug_open) {
      print(selfieName);
      print((int*) ": opening file with name at virtual address ");
      printHexadecimal(vaddr, 8);
      print((int*) " failed because the name is too long");
      println();
    }
  }
}

void emitMalloc() {
  createSymbolTableEntry(LIBRARY_TABLE, (int*) "malloc", 0, PROCEDURE, INTSTAR_T, 0, binaryLength);

  // on boot levels higher than zero, zalloc falls back to malloc
  // assuming that page frames are zeroed on boot level zero
  createSymbolTableEntry(LIBRARY_TABLE, (int*) "zalloc", 0, PROCEDURE, INTSTAR_T, 0, binaryLength);

  emitIFormat(OP_LW, REG_SP, REG_A0, 0); // size
  emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

  emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_MALLOC);
  emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

  emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

int implementMalloc(int* context) {
  int size;
  int bump;
  int stackptr;
  int available;
  int temp;

  if (debug_malloc) {
    print(selfieName);
    print((int*) ": trying to malloc ");
    printInteger(*(getRegs(context)+REG_A0));
    print((int*) " bytes");
    println();
  }

  size = roundUp(*(getRegs(context)+REG_A0), WORDSIZE);

  bump = getProgramBreak(context);

  stackptr = *(getRegs(context)+REG_SP);

  temp = INT_OVERFLOW;

  available = subtractWrap(stackptr, bump);

  if (available < 0)
    available = INT_MAX;

  if (size > available) {
    setExitCode(context, EXITCODE_OUTOFVIRTUALMEMORY);

    return EXIT;
  } else {
    *(getRegs(context)+REG_V0) = bump;

    setProgramBreak(context, addWrap(bump, size));

    INT_OVERFLOW = temp;

    if (debug_malloc) {
      print(selfieName);
      print((int*) ": actually mallocating ");
      printInteger(size);
      print((int*) " bytes at virtual address ");
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
  createSymbolTableEntry(LIBRARY_TABLE, (int*) "hypster_switch", 0, PROCEDURE, INTSTAR_T, 0, binaryLength);

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

void doSwitch(int* toContext, int timeout) {
  int* fromContext;

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
    *(registers+REG_V1) = (int) getVirtualContext(fromContext);
  else
    *(registers+REG_V1) = (int) fromContext;

  currentContext = toContext;

  timer = timeout;

  if (debug_switch) {
    print(selfieName);
    print((int*) ": switched from context ");
    printHexadecimal((int) fromContext, 8);
    print((int*) " to context ");
    printHexadecimal((int) toContext, 8);
    if (timeout >= 0) {
      print((int*) " to execute ");
      printInteger(timeout);
      print((int*) " instructions");
    }
    println();
  }
}

void implementSwitch() {
  saveContext(currentContext);

  // cache context on my boot level before switching
  doSwitch(cacheContext((int*) *(registers+REG_A0)), *(registers+REG_A1));
}

int* mipster_switch(int* toContext, int timeout) {
  doSwitch(toContext, timeout);

  runUntilException();

  saveContext(currentContext);

  return currentContext;
}

int* hypster_switch(int* toContext, int timeout) {
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

int loadPhysicalMemory(int* paddr) {
  return *paddr;
}

void storePhysicalMemory(int* paddr, int data) {
  *paddr = data;
}

int FrameForPage(int* table, int page) {
  return (int) (table + page);
}

int getFrameForPage(int* table, int page) {
  return *(table + page);
}

int isPageMapped(int* table, int page) {
  if (getFrameForPage(table, page) != 0)
    return 1;
  else
    return 0;
}

int isValidVirtualAddress(int vaddr) {
  // memory must be word-addressed for lack of byte-sized data type
  return vaddr % WORDSIZE == 0;
}

int getPageOfVirtualAddress(int vaddr) {
  if (vaddr < 0)
    return (vaddr - INT_MIN) / PAGESIZE + NUMBEROFPAGES / 2;

  return vaddr / PAGESIZE;
}

int isVirtualAddressMapped(int* table, int vaddr) {
  // assert: isValidVirtualAddress(vaddr) == 1

  return isPageMapped(table, getPageOfVirtualAddress(vaddr));
}

int* tlb(int* table, int vaddr) {
  int page;
  int frame;
  int paddr;

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
    print((int*) ": tlb access:");
    println();
    print((int*) " vaddr: ");
    printBinary(vaddr, 32);
    println();
    print((int*) " page:  ");
    if (page < NUMBEROFPAGES / 2)
      printBinary(page * PAGESIZE, 32);
    else
      printBinary(INT_MIN + (page - NUMBEROFPAGES / 2) * PAGESIZE, 32);
    printBinary(page * PAGESIZE, 32);
    println();
    print((int*) " frame: ");
    printBinary(frame, 32);
    println();
    print((int*) " paddr: ");
    printBinary(paddr, 32);
    println();
  }

  return (int*) paddr;
}

int loadVirtualMemory(int* table, int vaddr) {
  // assert: isValidVirtualAddress(vaddr) == 1
  // assert: isVirtualAddressMapped(table, vaddr) == 1

  return loadPhysicalMemory(tlb(table, vaddr));
}

void storeVirtualMemory(int* table, int vaddr, int data) {
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
  int s;
  int t;
  int d;
  int n;

  if (interpret) {
    s = *(registers+rs);
    t = *(registers+rt);
    d = *(registers+rd);

    n = addWrap(s, t);
  }

  if (debug) {
    printFunction(function);
    print((int*) " ");
    printRegister(rd);
    print((int*) ",");
    printRegister(rs);
    print((int*) ",");
    printRegister(rt);
    if (interpret) {
      print((int*) ": ");
      printRegister(rd);
      print((int*) "=");
      printInteger(d);
      print((int*) ",");
      printRegister(rs);
      print((int*) "=");
      printInteger(s);
      print((int*) ",");
      printRegister(rt);
      print((int*) "=");
      printInteger(t);
      print((int*) " -> ");
      printRegister(rd);
      print((int*) "=");
      printInteger(n);
    }
    println();
  }

  if (interpret) {
    *(registers+rd) = n;

    pc = pc + WORDSIZE;

    if (debug_overflow)
      if (INT_OVERFLOW == OVERFLOW_YES) {
        print((int*) "overflow: ");
        printInteger(s);
        print((int*) " + ");
        printInteger(t);
        print((int*) " ~ ");
        printInteger(n);
        println();
      }
  }
}

void fct_subu() {
  int s;
  int t;
  int d;
  int n;

  if (interpret) {
    s = *(registers+rs);
    t = *(registers+rt);
    d = *(registers+rd);

    n = subtractWrap(s, t);
  }

  if (debug) {
    printFunction(function);
    print((int*) " ");
    printRegister(rd);
    print((int*) ",");
    printRegister(rs);
    print((int*) ",");
    printRegister(rt);
    if (interpret) {
      print((int*) ": ");
      printRegister(rd);
      print((int*) "=");
      printInteger(d);
      print((int*) ",");
      printRegister(rs);
      print((int*) "=");
      printInteger(s);
      print((int*) ",");
      printRegister(rt);
      print((int*) "=");
      printInteger(t);
      print((int*) " -> ");
      printRegister(rd);
      print((int*) "=");
      printInteger(n);
    }
    println();
  }

  if (interpret) {
    *(registers+rd) = n;

    pc = pc + WORDSIZE;

    if (debug_overflow)
      if (INT_OVERFLOW == OVERFLOW_YES) {
        print((int*) "overflow: ");
        printInteger(s);
        print((int*) " - ");
        printInteger(t);
        print((int*) " ~ ");
        printInteger(n);
        println();
      }
  }
}

void fct_multu() {
  int s;
  int t;
  int n;

  if (interpret) {
    s = *(registers+rs);
    t = *(registers+rt);

    n = multiplyWrap(s, t);
  }

  if (debug) {
    printFunction(function);
    print((int*) " ");
    printRegister(rs);
    print((int*) ",");
    printRegister(rt);
    if (interpret) {
      print((int*) ": ");
      printRegister(rs);
      print((int*) "=");
      printInteger(s);
      print((int*) ",");
      printRegister(rt);
      print((int*) "=");
      printInteger(t);
      print((int*) ",$lo=");
      printInteger(loReg);
      print((int*) " -> $lo=");
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
        print((int*) "overflow: ");
        printInteger(s);
        print((int*) " * ");
        printInteger(t);
        print((int*) " ~ ");
        printInteger(n);
        println();
      }
  }
}

void fct_divu() {
  int s;
  int t;
  int l;
  int h;

  if (interpret) {
    s = *(registers+rs);
    t = *(registers+rt);

    checkDivision(s, t);

    if (debug_overflow)
      if (INT_OVERFLOW == OVERFLOW_YES) {
        if (t == 0)
          print((int*) "division-by-zero error: ");
        else
          print((int*) "signed integer error: ");
        printInteger(s);
        print((int*) " / ");
        printInteger(t);
        println();
      }

    // this will fail if t == 0 or (s == INT_MIN and t == -1)
    l = s / t;
    h = s % t;
  }

  if (debug) {
    printFunction(function);
    print((int*) " ");
    printRegister(rs);
    print((int*) ",");
    printRegister(rt);
    if (interpret) {
      print((int*) ": ");
      printRegister(rs);
      print((int*) "=");
      printInteger(s);
      print((int*) ",");
      printRegister(rt);
      print((int*) "=");
      printInteger(t);
      print((int*) ",$lo=");
      printInteger(loReg);
      print((int*) ",$hi=");
      printInteger(hiReg);
      print((int*) " -> $lo=");
      printInteger(l);
      print((int*) ",$hi=");
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
    print((int*) " ");
    printRegister(rd);
    if (interpret) {
      print((int*) ":");
      printRegister(rd);
      print((int*) "=");
      printInteger(*(registers+rd));
      print((int*) ",$hi=");
      printInteger(hiReg);
    }
  }

  if (interpret) {
    *(registers+rd) = hiReg;

    pc = pc + WORDSIZE;
  }

  if (debug) {
    if (interpret) {
      print((int*) " -> ");
      printRegister(rd);
      print((int*) "=");
      printInteger(*(registers+rd));
    }
    println();
  }
}

void fct_mflo() {
  if (debug) {
    printFunction(function);
    print((int*) " ");
    printRegister(rd);
    if (interpret) {
      print((int*) ": ");
      printRegister(rd);
      print((int*) "=");
      printInteger(*(registers+rd));
      print((int*) ",$lo=");
      printInteger(loReg);
    }
  }

  if (interpret) {
    *(registers+rd) = loReg;

    pc = pc + WORDSIZE;
  }

  if (debug) {
    if (interpret) {
      print((int*) " -> ");
      printRegister(rd);
      print((int*) "=");
      printInteger(*(registers+rd));
    }
    println();
  }
}

void fct_slt() {
  if (debug) {
    printFunction(function);
    print((int*) " ");
    printRegister(rd);
    print((int*) ",");
    printRegister(rs);
    print((int*) ",");
    printRegister(rt);
    if (interpret) {
      print((int*) ": ");
      printRegister(rs);
      print((int*) "=");
      printInteger(*(registers+rs));
      print((int*) ",");
      printRegister(rt);
      print((int*) "=");
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
      print((int*) " -> ");
      printRegister(rd);
      print((int*) "=");
      printInteger(*(registers+rd));
    }
    println();
  }
}

void fct_jr() {
  if (debug) {
    printFunction(function);
    print((int*) " ");
    printRegister(rs);
    if (interpret) {
      print((int*) ": ");
      printRegister(rs);
      print((int*) "=");
      printHexadecimal(*(registers+rs), 0);
    }
  }

  if (interpret)
    pc = *(registers+rs);

  if (debug) {
    if (interpret) {
      print((int*) " -> $pc=");
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
    print((int*) " ");
    printRegister(rt);
    print((int*) ",");
    printRegister(rs);
    print((int*) ",");
    printInteger(signExtend(immediate));
    if (interpret) {
      print((int*) ": ");
      printRegister(rt);
      print((int*) "=");
      printInteger(*(registers+rt));
      print((int*) ",");
      printRegister(rs);
      print((int*) "=");
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
      print((int*) " -> ");
      printRegister(rt);
      print((int*) "=");
      printInteger(*(registers+rt));
    }
    println();
  }
}

void op_lw() {
  int vaddr;

  if (debug) {
    printOpcode(opcode);
    print((int*) " ");
    printRegister(rt);
    print((int*) ",");
    printInteger(signExtend(immediate));
    print((int*) "(");
    printRegister(rs);
    print((int*) ")");
    if (interpret) {
      print((int*) ": ");
      printRegister(rt);
      print((int*) "=");
      printInteger(*(registers+rt));
      print((int*) ",");
      printRegister(rs);
      print((int*) "=");
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
      print((int*) " -> ");
      printRegister(rt);
      print((int*) "=");
      printInteger(*(registers+rt));
      print((int*) "=memory[");
      printHexadecimal(vaddr, 0);
      print((int*) "]");
    }
    println();
  }
}

void op_sw() {
  int vaddr;

  if (debug) {
    printOpcode(opcode);
    print((int*) " ");
    printRegister(rt);
    print((int*) ",");
    printInteger(signExtend(immediate));
    print((int*) "(");
    printRegister(rs);
    print((int*) ")");
    if (interpret) {
      print((int*) ": ");
      printRegister(rt);
      print((int*) "=");
      printInteger(*(registers+rt));
      print((int*) ",");
      printRegister(rs);
      print((int*) "=");
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
      print((int*) " -> memory[");
      printHexadecimal(vaddr, 0);
      print((int*) "]=");
      printInteger(*(registers+rt));
      print((int*) "=");
      printRegister(rt);
    }
    println();
  }
}

void op_beq() {
  if (debug) {
    printOpcode(opcode);
    print((int*) " ");
    printRegister(rs);
    print((int*) ",");
    printRegister(rt);
    print((int*) ",");
    printInteger(signExtend(immediate));
    print((int*) "[");
    printHexadecimal(pc + WORDSIZE + signExtend(immediate) * WORDSIZE, 0);
    print((int*) "]");
    if (interpret) {
      print((int*) ": ");
      printRegister(rs);
      print((int*) "=");
      printInteger(*(registers+rs));
      print((int*) ",");
      printRegister(rt);
      print((int*) "=");
      printInteger(*(registers+rt));
    }
  }

  if (interpret) {
    pc = pc + WORDSIZE;

    if (*(registers+rs) == *(registers+rt)) {
      pc = pc + signExtend(immediate) * WORDSIZE;

      if (signExtend(immediate) < 0) {
        // keep track of number of loop iterations
        loops = loops + 1;

        *(loopsPerAddress + pc / WORDSIZE) = *(loopsPerAddress + pc / WORDSIZE) + 1;
      }

      // TODO: execute delay slot
    }
  }

  if (debug) {
    if (interpret) {
      print((int*) " -> $pc=");
      printHexadecimal(pc, 0);
    }
    println();
  }
}

void op_jal() {
  if (debug) {
    printOpcode(opcode);
    print((int*) " ");
    printHexadecimal(instr_index, 0);
    print((int*) "[");
    printHexadecimal(instr_index * WORDSIZE, 0);
    print((int*) "]");
    if (interpret) {
      print((int*) ": ");
      printRegister(REG_RA);
      print((int*) "=");
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
      print((int*) " -> ");
      printRegister(REG_RA);
      print((int*) "=");
      printHexadecimal(*(registers+REG_RA), 0);
      print((int*) ",$pc=");
      printHexadecimal(pc, 0);
    }
    println();
  }
}

void op_j() {
  if (debug) {
    printOpcode(opcode);
    print((int*) " ");
    printHexadecimal(instr_index, 0);
    print((int*) "[");
    printHexadecimal(instr_index * WORDSIZE, 0);
    print((int*) "]");
  }

  if (interpret) {
    pc = instr_index * WORDSIZE;

    // TODO: execute delay slot
  }

  if (debug) {
    if (interpret) {
      print((int*) ": -> $pc=");
      printHexadecimal(pc, 0);
    }
    println();
  }
}

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void printException(int exception, int faultingPage) {
  print((int*) *(EXCEPTIONS + exception));

  if (exception == EXCEPTION_PAGEFAULT) {
    print((int*) " at ");
    printHexadecimal(faultingPage, 8);
  }
}

void throwException(int exception, int faultingPage) {
  setException(currentContext, exception);
  setFaultingPage(currentContext, faultingPage);

  trap = 1;

  if (debug_exception) {
    print(selfieName);
    print((int*) ": context ");
    printHexadecimal((int) currentContext, 8);
    print((int*) " throws ");
    printException(exception, faultingPage);
    print((int*) " exception");
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
      print((int*) ": $pc=");
    }
    printHexadecimal(pc, 0);
    if (sourceLineNumber != (int*) 0) {
      print((int*) "(~");
      printInteger(*(sourceLineNumber + pc / WORDSIZE));
      print((int*) ")");
    }
    print((int*) ": ");
    printHexadecimal(ir, 8);
    print((int*) ": ");
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

int* runUntilException() {
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

int addressWithMaxCounter(int* counters, int max) {
  int a;
  int n;
  int i;
  int c;

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

int printCounters(int total, int* counters, int max) {
  int a;

  a = addressWithMaxCounter(counters, max);

  printInteger(*(counters + a / WORDSIZE));

  print((int*) "(");
  printFixedPointPercentage(total, *(counters + a / WORDSIZE));
  print((int*) "%)");

  if (*(counters + a / WORDSIZE) != 0) {
    print((int*) "@");
    printHexadecimal(a, 0);
    if (sourceLineNumber != (int*) 0) {
      print((int*) "(~");
      printInteger(*(sourceLineNumber + a / WORDSIZE));
      print((int*) ")");
    }
  }

  return a;
}

void printProfile(int* message, int total, int* counters) {
  int a;

  if (total > 0) {
    print(selfieName);
    print(message);
    printInteger(total);
    print((int*) ",");
    a = printCounters(total, counters, INT_MAX); // max counter
    print((int*) ",");
    a = printCounters(total, counters, *(counters + a / WORDSIZE)); // 2nd max
    print((int*) ",");
    a = printCounters(total, counters, *(counters + a / WORDSIZE)); // 3rd max
    println();
  }
}

void selfie_disassemble() {
  assemblyName = getArgument();

  if (codeLength == 0) {
    print(selfieName);
    print((int*) ": nothing to disassemble to output file ");
    print(assemblyName);
    println();

    return;
  }

  // assert: assemblyName is mapped and not longer than maxFilenameLength

  assemblyFD = openWriteOnly(assemblyName);

  if (assemblyFD < 0) {
    print(selfieName);
    print((int*) ": could not create assembly output file ");
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

  outputName = (int*) 0;
  outputFD   = 1;

  print(selfieName);
  print((int*) ": ");
  printInteger(numberOfWrittenCharacters);
  print((int*) " characters of assembly with ");
  printInteger(codeLength / WORDSIZE);
  print((int*) " instructions written into ");
  print(assemblyName);
  println();
}

// -----------------------------------------------------------------
// ---------------------------- CONTEXTS ---------------------------
// -----------------------------------------------------------------

int* allocateContext(int* parent, int* vctxt, int* in) {
  int* context;

  if (freeContexts == (int*) 0)
    context = malloc(6 * SIZEOFINTSTAR + 11 * SIZEOFINT);
  else {
    context = freeContexts;

    freeContexts = getNextContext(freeContexts);
  }

  setNextContext(context, in);
  setPrevContext(context, (int*) 0);

  if (in != (int*) 0)
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

  setName(context, (int*) 0);

  return context;
}

int* findContext(int* parent, int* vctxt, int* in) {
  int* context;

  context = in;

  while (context != (int*) 0) {
    if (getParent(context) == parent)
      if (getVirtualContext(context) == vctxt)
        return context;

    context = getNextContext(context);
  }

  return (int*) 0;
}

void freeContext(int* context) {
  setNextContext(context, freeContexts);

  freeContexts = context;
}

int* deleteContext(int* context, int* from) {
  if (getNextContext(context) != (int*) 0)
    setPrevContext(getNextContext(context), getPrevContext(context));

  if (getPrevContext(context) != (int*) 0) {
    setNextContext(getPrevContext(context), getNextContext(context));
    setPrevContext(context, (int*) 0);
  } else
    from = getNextContext(context);

  freeContext(context);

  return from;
}

// -----------------------------------------------------------------
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

int* createContext(int* parent, int* vctxt) {
  // TODO: check if context already exists
  usedContexts = allocateContext(parent, vctxt, usedContexts);

  if (currentContext == (int*) 0)
    currentContext = usedContexts;

  if (debug_create) {
    print(selfieName);
    print((int*) ": parent context ");
    printHexadecimal((int) parent, 8);
    print((int*) " created child context ");
    printHexadecimal((int) usedContexts, 8);
    println();
  }

  return usedContexts;
}

int* cacheContext(int* vctxt) {
  int* context;

  // find cached context on my boot level
  context = findContext(currentContext, vctxt, usedContexts);

  if (context == (int*) 0)
    // create cached context on my boot level
    context = createContext(currentContext, vctxt);

  return context;
}

void saveContext(int* context) {
  int* parentTable;
  int* vctxt;
  int r;
  int* regs;
  int* vregs;

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

    vregs = (int*) loadVirtualMemory(parentTable, Regs(vctxt));

    while (r < NUMBEROFREGISTERS) {
      storeVirtualMemory(parentTable, (int) (vregs + r), *(regs + r));

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

void mapPage(int* context, int page, int frame) {
  int* table;

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
    print((int*) ": page ");
    printHexadecimal(page, 4);
    print((int*) " mapped to frame ");
    printHexadecimal(frame, 8);
    print((int*) " in context ");
    printHexadecimal((int) context, 8);
    println();
  }
}

void restoreContext(int* context) {
  int* parentTable;
  int* vctxt;
  int r;
  int* regs;
  int* vregs;
  int* table;
  int page;
  int me;
  int frame;

  if (getParent(context) != MY_CONTEXT) {
    parentTable = getPT(getParent(context));

    vctxt = getVirtualContext(context);

    setPC(context, loadVirtualMemory(parentTable, PC(vctxt)));

    r = 0;

    regs = getRegs(context);

    vregs = (int*) loadVirtualMemory(parentTable, Regs(vctxt));

    while (r < NUMBEROFREGISTERS) {
      *(regs + r) = loadVirtualMemory(parentTable, (int) (vregs + r));

      r = r + 1;
    }

    setLoReg(context, loadVirtualMemory(parentTable, LoReg(vctxt)));
    setHiReg(context, loadVirtualMemory(parentTable, HiReg(vctxt)));
    setProgramBreak(context, loadVirtualMemory(parentTable, ProgramBreak(vctxt)));

    setException(context, loadVirtualMemory(parentTable, Exception(vctxt)));
    setFaultingPage(context, loadVirtualMemory(parentTable, FaultingPage(vctxt)));
    setExitCode(context, loadVirtualMemory(parentTable, ExitCode(vctxt)));

    table = (int*) loadVirtualMemory(parentTable, PT(vctxt));

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

int pavailable() {
  if (freePageFrameMemory > 0)
    return 1;
  else if (usedPageFrameMemory + MEGABYTEINWORDS <= pageFrameMemory)
    return 1;
  else
    return 0;
}

int pused() {
  return usedPageFrameMemory - freePageFrameMemory;
}

int* palloc() {
  // CAUTION: on boot level zero palloc may return frame addresses < 0
  int block;
  int frame;

  // assert: pageFrameMemory is equal to or a multiple of MEGABYTEINWORDS
  // assert: PAGESIZEINWORDS is a factor of MEGABYTEINWORDS strictly less than MEGABYTEINWORDS

  if (freePageFrameMemory == 0) {
    freePageFrameMemory = MEGABYTEINWORDS;

    if (usedPageFrameMemory + freePageFrameMemory <= pageFrameMemory) {
      // on boot level zero allocate zeroed memory
      block = (int) zalloc(freePageFrameMemory * WORDSIZE);

      usedPageFrameMemory = usedPageFrameMemory + freePageFrameMemory;

      // page frames must be page-aligned to work as page table index
      nextPageFrame = roundUp(block, PAGESIZE) / WORDSIZE;

      if (nextPageFrame > block)
        // losing one page frame to fragmentation
        freePageFrameMemory = freePageFrameMemory - PAGESIZEINWORDS;
    } else {
      print(selfieName);
      print((int*) ": palloc out of physical memory");
      println();

      exit(EXITCODE_OUTOFPHYSICALMEMORY);
    }
  }

  // frame[number of bytes] = nextPageFrame[number of words] * WORDSIZE
  frame = nextPageFrame * WORDSIZE;

  nextPageFrame = nextPageFrame + PAGESIZEINWORDS;

  freePageFrameMemory = freePageFrameMemory - PAGESIZEINWORDS;

  // strictly, touching is only necessary on boot levels higher than zero
  return touch((int*) frame, PAGESIZE);
}

void pfree(int* frame) {
  // TODO: implement free list of page frames
}

void mapAndStore(int* context, int vaddr, int data) {
  // assert: isValidVirtualAddress(vaddr) == 1

  if (isVirtualAddressMapped(getPT(context), vaddr) == 0)
    mapPage(context, getPageOfVirtualAddress(vaddr), (int) palloc());

  storeVirtualMemory(getPT(context), vaddr, data);
}

void up_loadBinary(int* context) {
  int vaddr;

  setName(context, binaryName);

  // binaries start at lowest virtual address
  vaddr = 0;

  while (vaddr < binaryLength) {
    mapAndStore(context, vaddr, loadBinary(vaddr));

    vaddr = vaddr + WORDSIZE;
  }
}

int up_loadString(int* context, int* s, int SP) {
  int bytes;
  int i;

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

void up_loadArguments(int* context, int argc, int* argv) {
  int SP;
  int vargv;
  int i_argc;
  int i_vargv;

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
    SP = up_loadString(context, (int*) *argv, SP);

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

void mapUnmappedPages(int* context) {
  int page;

  // assert: page table is only mapped from beginning up and end down

  page = 0;

  while (isPageMapped(getPT(context), page))
    page = page + 1;

  while (pavailable()) {
    mapPage(context, page, (int) palloc());

    page = page + 1;
  }
}

int isBootLevelZero() {
  // in C99 malloc(0) returns either a null pointer or a unique pointer. 
  // (see http://pubs.opengroup.org/onlinepubs/9699919799/)
  // selfie's malloc implementation, on the other hand, 
  // returns the same not null address, if malloc(0) is called consecutively.
  int firstMalloc;
  int secondMalloc;

  firstMalloc = (int) malloc(0);
  secondMalloc = (int) malloc(0);

  if (firstMalloc == 0)
    return 1;
  if (firstMalloc != secondMalloc)
    return 1;

  // it is selfie's malloc, so it can not be boot level zero.
  return 0;
}

int handleSystemCalls(int* context) {
  int v0;

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
      print((int*) ": unknown system call ");
      printInteger(v0);
      println();

      setExitCode(context, EXITCODE_UNKNOWNSYSCALL);

      return EXIT;
    }
  } else if (getException(context) != EXCEPTION_TIMER) {
    print(selfieName);
    print((int*) ": context ");
    print(getName(context));
    print((int*) " throws uncaught ");
    printException(getException(context), getFaultingPage(context));
    println();

    setExitCode(context, EXITCODE_UNCAUGHTEXCEPTION);

    return EXIT;
  }

  return DONOTEXIT;
}

int mipster(int* toContext) {
  int timeout;
  int* fromContext;

  print((int*) "mipster");
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
        mapPage(fromContext, getFaultingPage(fromContext), (int) palloc());
      else if (handleSystemCalls(fromContext) == EXIT)
        return getExitCode(fromContext);

      setException(fromContext, EXCEPTION_NOEXCEPTION);

      toContext = fromContext;

      timeout = TIMESLICE;
    }
  }
}

int minster(int* toContext) {
  int timeout;
  int* fromContext;

  print((int*) "minster");
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

int mobster(int* toContext) {
  int timeout;
  int* fromContext;

  print((int*) "mobster");
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

int hypster(int* toContext) {
  int* fromContext;

  print((int*) "hypster");
  println();

  while (1) {
    fromContext = hypster_switch(toContext, TIMESLICE);

    if (getException(fromContext) == EXCEPTION_PAGEFAULT)
      // TODO: use this table to unmap and reuse frames
      mapPage(fromContext, getFaultingPage(fromContext), (int) palloc());
    else if (handleSystemCalls(fromContext) == EXIT)
      return getExitCode(fromContext);

    setException(fromContext, EXCEPTION_NOEXCEPTION);

    toContext = fromContext;
  }
}

int mixter(int* toContext, int mix) {
  // works with mipsters and hypsters
  int mslice;
  int timeout;
  int* fromContext;

  print((int*) "mixter (");
  printInteger(mix);
  print((int*) "% mipster/");
  printInteger(100 - mix);
  print((int*) "% hypster)");
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
        mapPage(fromContext, getFaultingPage(fromContext), (int) palloc());
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

int selfie_run(int machine) {
  int exitCode;

  if (binaryLength == 0) {
    print(selfieName);
    print((int*) ": nothing to run, debug, or host");
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
  print((int*) ": this is selfie executing ");
  print(binaryName);
  print((int*) " with ");
  printInteger(pageFrameMemory / MEGABYTEINWORDS);
  print((int*) "MB of physical memory on ");

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
  print((int*) ": this is selfie terminating ");
  print(getName(currentContext));
  print((int*) " with exit code ");
  printInteger(exitCode);
  print((int*) " and ");
  printFixedPointRatio(pused(), MEGABYTEINWORDS);
  print((int*) "MB of mapped memory");
  println();

  if (calls > 0) {
    print(selfieName);
    if (sourceLineNumber != (int*) 0)
      print((int*) ": profile: total,max(ratio%)@addr(line#),2max(ratio%)@addr(line#),3max(ratio%)@addr(line#)");
    else
      print((int*) ": profile: total,max(ratio%)@addr,2max(ratio%)@addr,3max(ratio%)@addr");
    println();
    printProfile((int*) ": calls: ", calls, callsPerAddress);
    printProfile((int*) ": loops: ", loops, loopsPerAddress);
    printProfile((int*) ": loads: ", loads, loadsPerAddress);
    printProfile((int*) ": stores: ", stores, storesPerAddress);
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

int clauseMayBeTrue(int* clauseAddress, int depth) {
  int variable;

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

int instanceMayBeTrue(int depth) {
  int clause;

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

int babysat(int depth) {
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
  int clause;
  int variable;

  print((int*) "p cnf ");
  printInteger(numberOfSATVariables);
  print((int*) " ");
  printInteger(numberOfSATClauses);
  println();

  clause = 0;

  while (clause < numberOfSATClauses) {
    variable = 0;

    while (variable < numberOfSATVariables) {
      if (*(SATInstance + clause * 2 * numberOfSATVariables + 2 * variable) == TRUE) {
        printInteger(variable + 1);
        print((int*) " ");
      } else if (*(SATInstance + clause * 2 * numberOfSATVariables + 2 * variable + 1) == TRUE) {
        printInteger(-(variable + 1));
        print((int*) " ");
      }

      variable = variable + 1;
    }

    print((int*) "0");
    println();

    clause = clause + 1;
  }
}

void dimacs_findNextCharacter(int newLine) {
  int inComment;

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

void dimacs_word(int* word) {
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

int dimacs_number() {
  int number;

  if (symbol == SYM_INTEGER) {
    number = literal;

    dimacs_getSymbol();

    return number;
  } else
    syntaxErrorSymbol(SYM_INTEGER);

  exit(EXITCODE_PARSERERROR);
}

void dimacs_getClause(int clause) {
  int not;

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
        syntaxErrorMessage((int*) "clause exceeds declared number of variables");

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
  int clauses;

  clauses = 0;

  while (clauses < numberOfSATClauses)
    if (symbol != SYM_EOF) {
      dimacs_getClause(clauses);

      clauses = clauses + 1;
    } else {
      syntaxErrorMessage((int*) "instance has fewer clauses than declared");

      exit(EXITCODE_PARSERERROR);
    }

  if (symbol != SYM_EOF) {
    syntaxErrorMessage((int*) "instance has more clauses than declared");

    exit(EXITCODE_PARSERERROR);
  }
}

void selfie_loadDimacs() {
  sourceName = getArgument();

  print(selfieName);
  print((int*) ": this is selfie loading SAT instance ");
  print(sourceName);
  println();

  // assert: sourceName is mapped and not longer than maxFilenameLength

  sourceFD = open(sourceName, O_RDONLY, 0);

  if (sourceFD < 0) {
    print(selfieName);
    print((int*) ": could not open input file ");
    print(sourceName);
    println();

    exit(EXITCODE_IOERROR);
  }

  resetScanner();

  // ignore all comments before problem
  dimacs_findNextCharacter(1);

  dimacs_getSymbol();

  dimacs_word((int*) "p");
  dimacs_word((int*) "cnf");

  numberOfSATVariables = dimacs_number();

  SATAssignment = (int*) malloc(numberOfSATVariables * WORDSIZE);

  numberOfSATClauses = dimacs_number();

  SATInstance = (int*) malloc(numberOfSATClauses * 2 * numberOfSATVariables * WORDSIZE);

  dimacs_getInstance();

  print(selfieName);
  print((int*) ": ");
  printInteger(numberOfSATClauses);
  print((int*) " clauses with ");
  printInteger(numberOfSATVariables);
  print((int*) " declared variables loaded from ");
  print(sourceName);
  println();

  dimacsName = sourceName;
}

void selfie_sat() {
  int variable;

  selfie_loadDimacs();

  if (dimacsName == (int*) 0) {
    print(selfieName);
    print((int*) ": nothing to SAT solve");
    println();

    return;
  }

  selfie_printDimacs();

  if (babysat(0) == SAT) {
    print(selfieName);
    print((int*) ": ");
    print(dimacsName);
    print((int*) " is satisfiable with ");

    variable = 0;

    while (variable < numberOfSATVariables) {
      if (*(SATAssignment + variable) == FALSE)
        print((int*) "-");

      printInteger(variable + 1);
      print((int*) " ");

      variable = variable + 1;
    }
  } else {
    print(selfieName);
    print((int*) ": ");
    print(dimacsName);
    print((int*) " is unsatisfiable");
  }

  println();
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

int numberOfRemainingArguments() {
  return selfie_argc;
}

int* remainingArguments() {
  return selfie_argv;
}

int* peekArgument() {
  if (numberOfRemainingArguments() > 0)
    return (int*) *selfie_argv;
  else
    return (int*) 0;
}

int* getArgument() {
  int* argument;

  argument = peekArgument();

  if (numberOfRemainingArguments() > 0) {
    selfie_argc = selfie_argc - 1;
    selfie_argv = selfie_argv + 1;
  }

  return argument;
}

void setArgument(int* argv) {
  *selfie_argv = (int) argv;
}

void printUsage() {
  print(selfieName);
  print((int*) ": usage: ");
  print((int*) "selfie { -c { source } | -o binary | -s assembly | -l binary | -sat dimacs } ");
  print((int*) "[ ( -m | -d | -y | -min | -mob ) size ... ]");
  println();
}

int selfie() {
  int* option;

  if (numberOfRemainingArguments() == 0)
    printUsage();
  else {
    initScanner();
    initRegister();
    initDecoder();
    initInterpreter();

    while (numberOfRemainingArguments() > 0) {
      option = getArgument();

      if (stringCompare(option, (int*) "-c"))
        selfie_compile();
      else if (numberOfRemainingArguments() == 0) {
        // remaining options have at least one argument
        printUsage();

        return -1;
      } else if (stringCompare(option, (int*) "-o"))
        selfie_output();
      else if (stringCompare(option, (int*) "-s"))
        selfie_disassemble();
      else if (stringCompare(option, (int*) "-l"))
        selfie_load();
      else if (stringCompare(option, (int*) "-sat"))
        selfie_sat();
      else if (stringCompare(option, (int*) "-m"))
        return selfie_run(MIPSTER);
      else if (stringCompare(option, (int*) "-d")) {
        debug = 1;

        return selfie_run(MIPSTER);
      } else if (stringCompare(option, (int*) "-y"))
        return selfie_run(HYPSTER);
      else if (stringCompare(option, (int*) "-min"))
        return selfie_run(MINSTER);
      else if (stringCompare(option, (int*) "-mob"))
        return selfie_run(MOBSTER);
      else {
        printUsage();

        return -1;
      }
    }
  }

  return 0;
}

int main(int argc, int* argv) {
  initSelfie(argc, (int*) argv);

  initLibrary();

  return selfie();
}