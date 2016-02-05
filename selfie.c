// Copyright (c) 2015-2016, the Selfie Project authors. All rights reserved.
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
// Selfie is a fully self-referential 6k-line C implementation of:
//
// 1. a self-compiling compiler called cstarc that compiles
//    a tiny but powerful subset of C called C Star (C*) to
//    a tiny but powerful subset of MIPS32 called MIPSter,
// 2. a self-executing emulator called mipster that executes
//    MIPSter code including itself when compiled with cstarc,
// 3. a self-hosting hypervisor called hypster which is based on
//    a tiny microkernel implemented in mipster and provides
//    MIPSter virtual machines that can host all of selfie,
//    that is, cstarc, mipster, and hypster itself, and
// 4. a tiny C* library called libcstar utilized by selfie.
//
// Selfie is kept minimal for simplicity and implemented in a single file.
// There is neither a linker nor an assembler. However, there is a simple
// profiler and disassembler and even a simple debugger as well as minimal
// operating system support in the form of MIPS32 o32 system calls built
// into the emulator.
//
// C* is a tiny Turing-complete subset of C that includes dereferencing
// (the * operator) but excludes data structures, bitwise and Boolean
// operators, and many other features. There are only signed 32-bit
// integers and pointers as well as character and string literals.
// This choice turns out to be helpful for students to understand the
// true role of composite data structures such as arrays and records.
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

int *selfieName = (int*) 0;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     L I B R A R Y     ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------- LIBRARY FUNCTIONS -----------------------
// -----------------------------------------------------------------

void initLibrary();

int twoToThePowerOf(int p);
int leftShift(int n, int b);
int rightShift(int n, int b);

int  loadCharacter(int *s, int i);
int* storeCharacter(int *s, int i, int c);

int  stringLength(int *s);
void stringReverse(int *s);
int  stringCompare(int *s, int *t);

int  atoi(int *s);
int* itoa(int n, int *s, int b, int a, int p);

void putCharacter(int character);

void print(int *s);
void println();

void printCharacter(int character);
void printString(int *s);

int roundUp(int n, int m);

int* malloc(int size);
void exit(int code);

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
int CHAR_HASH         = '#';
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

int *power_of_two_table;

int INT_MAX; // maximum numerical value of an integer
int INT_MIN; // minimum numerical value of an integer

int maxFilenameLength = 128;

int *character_buffer; // buffer for reading and writing characters
int *string_buffer;    // buffer for string output
int *filename_buffer;  // buffer for filenames
int *io_buffer;        // buffer for binary I/O

// 0 = O_RDONLY (0x0000)
int O_RDONLY = 0;

// 577 = 0x0241 = O_CREAT (0x0040) | O_WRONLY (0x0001) | O_TRUNC (0x0200)
int O_CREAT_WRONLY_TRUNC = 577; // flags for opening write-only files

// 420 = 00644 = S_IRUSR (00400) | S_IWUSR (00200) | S_IRGRP (00040) | S_IROTH (00004)
int S_IRUSR_IWUSR_IRGRP_IROTH = 420; // flags for rw-r--r-- file permissions

// ------------------------ GLOBAL VARIABLES -----------------------

int *outputName = (int*) 0;
int outputFD    = 1;

// ------------------------- INITIALIZATION ------------------------

void initLibrary() {
    int i;

    power_of_two_table = malloc(31 * SIZEOFINT);

    *power_of_two_table = 1; // 2^0

    i = 1;

    while (i < 31) {
        *(power_of_two_table + i) = *(power_of_two_table + (i - 1)) * 2;

        i = i + 1;
    }

    // computing INT_MAX and INT_MIN without overflows
    INT_MAX = (twoToThePowerOf(30) - 1) * 2 + 1;
    INT_MIN = -INT_MAX - 1;

    // allocate and touch to make sure memory is mapped for read calls
    character_buffer  = malloc(1);
    *character_buffer = 0;

    // accommodate at least 32-bit numbers for itoa, no mapping needed
    string_buffer = malloc(33);

    // does not need to be mapped
    filename_buffer = malloc(maxFilenameLength);

    // allocate and touch to make sure memory is mapped for read calls
    io_buffer  = malloc(SIZEOFINT);
    *io_buffer = 0;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     C O M P I L E R   ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- SCANNER ----------------------------
// -----------------------------------------------------------------

void initScanner();
void resetScanner();

void printSymbol(int symbol);
void printLineNumber(int* message, int line);

void syntaxErrorMessage(int *message);
void syntaxErrorCharacter(int character);

void getCharacter();

int isCharacterWhitespace();
int findNextCharacter();
int isCharacterLetter();
int isCharacterDigit();
int isCharacterLetterOrDigitOrUnderscore();
int isNotDoubleQuoteOrEOF();
int identifierStringMatch(int stringIndex);
int identifierOrKeyword();

int getSymbol();

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

int *SYMBOLS; // array of strings representing symbols

int maxIdentifierLength = 64; // maximum number of characters in an identifier
int maxIntegerLength    = 10; // maximum number of characters in an integer
int maxStringLength     = 128; // maximum number of characters in a string

// ------------------------ GLOBAL VARIABLES -----------------------

int lineNumber = 1; // current Line Number for error reporting

int *identifier = (int*) 0; // stores scanned identifier as string
int *integer    = (int*) 0; // stores scanned integer as string
int *string     = (int*) 0; // stores scanned string

int literal = 0; // stores numerical value of scanned integer or character

int initialValue = 0; // stores initial value of variable definitions

int mayBeINTMIN = 0; // support INT_MIN
int isINTMIN    = 0;

int character; // most recently read character
int symbol;    // most recently recognized symbol

int *sourceName = (int*) 0; // name of source file
int sourceFD    = 0;        // file descriptor of open source file

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

    getCharacter();
    getSymbol();
}

// -----------------------------------------------------------------
// ------------------------- SYMBOL TABLE --------------------------
// -----------------------------------------------------------------

void resetSymbolTables();

void createSymbolTableEntry(int which, int *string, int line, int class, int type, int value, int address);
int* searchSymbolTable(int *entry, int *string, int class);
int* getSymbolTableEntry(int *string, int class);

int isUndefinedProcedure(int *entry);
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

int* getNextEntry(int *entry) { return (int*) *entry; }
int* getString(int *entry)    { return (int*) *(entry + 1); }
int  getLineNumber(int *entry) { return *(entry + 2); }
int  getClass(int *entry)      { return *(entry + 3); }
int  getType(int *entry)       { return *(entry + 4); }
int  getValue(int *entry)      { return *(entry + 5); }
int  getAddress(int *entry)    { return *(entry + 6); }
int  getScope(int *entry)      { return *(entry + 7); }

void setNextEntry(int *entry, int *next)    { *entry       = (int) next; }
void setString(int *entry, int *identifier) { *(entry + 1) = (int) identifier; }
void setLineNumber(int *entry, int line)    { *(entry + 2) = line; }
void setClass(int *entry, int class)        { *(entry + 3) = class; }
void setType(int *entry, int type)          { *(entry + 4) = type; }
void setValue(int *entry, int value)        { *(entry + 5) = value; }
void setAddress(int *entry, int address)    { *(entry + 6) = address; }
void setScope(int *entry, int scope)        { *(entry + 7) = scope; }

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
int *global_symbol_table  = (int*) 0;
int *local_symbol_table   = (int*) 0;
int *library_symbol_table = (int*) 0;

// ------------------------- INITIALIZATION ------------------------

void resetSymbolTables() {
    global_symbol_table  = (int*) 0;
    local_symbol_table   = (int*) 0;
    library_symbol_table = (int*) 0;
}

// -----------------------------------------------------------------
// ---------------------------- PARSER -----------------------------
// -----------------------------------------------------------------

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
int* putType(int type);
void typeWarning(int expected, int found);

int* getVariable(int *variable);
int  load_variable(int *variable);
void load_integer(int value);
void load_string(int *string);

int  help_call_codegen(int *entry, int *procedure);
void help_procedure_prologue(int localVariables);
void help_procedure_epilogue(int parameters);

int  gr_call(int *procedure);
int  gr_factor();
int  gr_term();
int  gr_simpleExpression();
int  gr_expression();
void gr_while();
void gr_if();
void gr_return(int returnType);
void gr_statement();
int  gr_type();
void gr_variable(int offset);
void gr_initialization(int *name, int offset, int type);
void gr_procedure(int *procedure, int returnType);
void gr_cstar();

// ------------------------ GLOBAL VARIABLES -----------------------

int allocatedTemporaries = 0; // number of allocated temporaries

int allocatedMemory = 0; // number of bytes for global variables and strings

int returnBranches  = 0; // fixup chain for return statements

int *currentProcedureName = (int*) 0; // name of currently parsed procedure

// -----------------------------------------------------------------
// ---------------------- MACHINE CODE LIBRARY ---------------------
// -----------------------------------------------------------------

void emitLeftShiftBy(int b);
void emitMainEntry();
void fixRegisterInitialization();

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

int *REGISTERS; // array of strings representing registers

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

int getOpcode(int instruction);
int getRS(int instruction);
int getRT(int instruction);
int getRD(int instruction);
int getFunction(int instruction);
int getImmediate(int instruction);
int getInstrIndex(int instruction);
int signExtend(int immediate);

// -----------------------------------------------------------------
// ---------------------------- DECODER ----------------------------
// -----------------------------------------------------------------

void initDecoder();

void printOpcode(int opcode);
void printFunction(int function);

void decode();
void decodeRFormat();
void decodeIFormat();
void decodeJFormat();

// ------------------------ GLOBAL CONSTANTS -----------------------

int OP_SPECIAL = 0;
int OP_J       = 2;
int OP_JAL     = 3;
int OP_BEQ     = 4;
int OP_BNE     = 5;
int OP_ADDIU   = 9;
int OP_LW      = 35;
int OP_SW      = 43;
    
int *OPCODES; // array of strings representing MIPS opcodes

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

int *FUNCTIONS; // array of strings representing MIPS functions

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
    *(OPCODES + OP_BNE)     = (int) "bne";
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

void storeInstruction(int baddr, int instruction);

void emitInstruction(int instruction);
void emitRFormat(int opcode, int rs, int rt, int rd, int function);
void emitIFormat(int opcode, int rs, int rt, int immediate);
void emitJFormat(int opcode, int instr_index);

void fixup_relative(int fromAddress);
void fixup_absolute(int fromAddress, int toAddress);
void fixlink_absolute(int fromAddress, int toAddress);

int copyStringToBinary(int *s, int a);

void emitGlobalsStrings();

void selfie_emit();

int* touch(int *memory, int length);

void selfie_load();

// ------------------------ GLOBAL CONSTANTS -----------------------

int maxBinaryLength = 131072; // 128KB

// ------------------------ GLOBAL VARIABLES -----------------------

int *binary = (int*) 0; // binary of emitted instructions

int binaryLength = 0; // length of binary in bytes incl. globals & strings

int codeLength = 0; // length of code portion of binary in bytes

int *binaryName = (int*) 0; // file name of binary

int *sourceLineNumber = (int*) 0; // source line number per emitted instruction

int *assemblyName = (int*) 0; // name of assembly file
int assemblyFD    = 0;        // file descriptor of open assembly file

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void emitExit();
void implementExit();

void emitRead();
void implementRead();

void emitWrite();
void implementWrite();

void emitOpen();
int  down_loadString(int *table, int vaddr, int *s);
void implementOpen();

void emitMalloc();
void implementMalloc();

void emitPutchar();

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

void emitID();
void implementID();

int selfie_ID();

void emitCreate();
int  doCreate(int parentID);
void implementCreate();

int selfie_create();

void emitSwitch();
int  doSwitch(int toID);
void implementSwitch();
int  mipster_switch(int toID);

int selfie_switch(int toID);

void emitStatus();
void implementStatus();

int selfie_status();

void emitDelete();
void doDelete(int ID);
void implementDelete();

void selfie_delete(int ID);

void emitMap();
void doMap(int ID, int page, int frame);
void implementMap();

void selfie_map(int ID, int page, int frame);

// ------------------------ GLOBAL CONSTANTS -----------------------

int debug_create = 0;
int debug_switch = 0;
int debug_status = 0;
int debug_delete = 0;
int debug_map    = 0;

int SYSCALL_ID     = 4901;
int SYSCALL_CREATE = 4902;
int SYSCALL_SWITCH = 4903;
int SYSCALL_STATUS = 4904;
int SYSCALL_DELETE = 4905;
int SYSCALL_MAP    = 4906;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     E M U L A T O R   ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void initMemory(int bytes);

int  loadPhysicalMemory(int *paddr);
void storePhysicalMemory(int *paddr, int data);

int isValidVirtualAddress(int vaddr);

int getFrameForPage(int *table, int page);

int isVirtualAddressMapped(int *table, int vaddr);

int* tlb(int *table, int vaddr);

int  loadVirtualMemory(int *table, int vaddr);
void storeVirtualMemory(int *table, int vaddr, int data);

void mapAndStoreVirtualMemory(int *table, int vaddr, int data);

// ------------------------ GLOBAL CONSTANTS -----------------------

int debug_tlb = 0;

int MEGABYTE = 1048576;

int VIRTUALMEMORYSIZE = 67108864; // 64MB of virtual memory

int WORDSIZE = 4; // must be the same as SIZEOFINT and SIZEOFINTSTAR

int PAGESIZE = 4096; // we use standard 4KB pages
int PAGEBITS = 12;   // 2^12 == 4096

// ------------------------ GLOBAL VARIABLES -----------------------

int frameMemorySize = 0; // size of memory for frames in bytes

// ------------------------- INITIALIZATION ------------------------

void initMemory(int bytes) {
    if (bytes < 0)
        frameMemorySize = 64 * MEGABYTE;
    else if (bytes > 1024 * MEGABYTE)
        frameMemorySize = 1024 * MEGABYTE;
    else
        frameMemorySize = bytes;
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

void fct_syscall();
void fct_nop();
void op_jal();
void op_j();
void op_beq();
void op_bne();
void op_addiu();
void fct_jr();
void fct_mfhi();
void fct_mflo();
void fct_multu();
void fct_divu();
void fct_addu();
void fct_subu();
void op_lw();
void fct_slt();
void op_sw();

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void initInterpreter();
void resetInterpreter();

void printException(int exception);

int encodeException(int exception, int parameter);
int decodeExceptionNumber(int status);
int decodeExceptionParameter(int status);

void printStatus(int status);

void throwException(int exception, int parameter);

void fetch();
void execute();
void interrupt();

void runUntilException();
void runUntilExit();

int  up_loadString(int *table, int *s, int SP);
void up_loadArguments(int *table, int argc, int *argv);
void up_loadBinary(int *table);

int addressWithMaxCounter(int *counters, int max);
int fixedPointRatio(int a, int b);

int  printCounters(int total, int *counters, int max);
void printProfile(int *message, int total, int *counters);

void selfie_disassemble(int argc, int *argv);
void selfie_run(int argc, int *argv);

// ------------------------ GLOBAL CONSTANTS -----------------------

int EXCEPTION_NOEXCEPTION        = 0;
int EXCEPTION_UNKNOWNINSTRUCTION = 1;
int EXCEPTION_UNKNOWNSYSCALL     = 2;
int EXCEPTION_ADDRESSERROR       = 3;
int EXCEPTION_HEAPOVERFLOW       = 4;
int EXCEPTION_EXIT               = 5;
int EXCEPTION_INTERRUPT          = 6;
int EXCEPTION_PAGEFAULT          = 7;

int *EXCEPTIONS; // array of strings representing exceptions

int debug_exception = 0;

// number of instructions from context switch to timer interrupt
// CAUTION: avoid interrupting any kernel activities, keep TIMESLICE large
// TODO: implement proper interrupt controller to turn interrupts on and off
int TIMESLICE = 10000000;

// ------------------------ GLOBAL VARIABLES -----------------------

int *registers = (int*) 0; // general purpose registers

int pc = 0; // program counter
int ir = 0; // instruction record

int reg_hi = 0; // hi register for multiplication/division
int reg_lo = 0; // lo register for multiplication/division

int *pt = (int*) 0; // page table

int brk = 0; // break between code, data, and heap

int trap = 0; // flag for creating a trap

int status = 0; // machine status including faulting address

int cycles = 0; // cycle counter where one cycle is equal to one instruction

int timer = 0; // counter for timer interrupt

int mipster = 0; // flag for forcing to use mipster rather than hypster

int interpret = 0; // flag for executing or disassembling code

int debug = 0; // flag for logging code execution

int calls            = 0;        // total number of executed procedure calls
int *callsPerAddress = (int*) 0; // number of executed calls of each procedure

int loops            = 0;        // total number of executed loop iterations
int *loopsPerAddress = (int*) 0; // number of executed iterations of each loop

int loads            = 0;        // total number of executed memory loads
int *loadsPerAddress = (int*) 0; // number of executed loads per load operation

int stores            = 0;        // total number of executed memory stores
int *storesPerAddress = (int*) 0; // number of executed stores per store operation

// ------------------------- INITIALIZATION ------------------------

void initInterpreter() {
    EXCEPTIONS = malloc(8 * SIZEOFINTSTAR);

    *(EXCEPTIONS + EXCEPTION_NOEXCEPTION)        = (int) "no exception";
    *(EXCEPTIONS + EXCEPTION_UNKNOWNINSTRUCTION) = (int) "unknown instruction";
    *(EXCEPTIONS + EXCEPTION_UNKNOWNSYSCALL)     = (int) "unknown syscall";
    *(EXCEPTIONS + EXCEPTION_ADDRESSERROR)       = (int) "address error";
    *(EXCEPTIONS + EXCEPTION_HEAPOVERFLOW)       = (int) "heap overflow";
    *(EXCEPTIONS + EXCEPTION_EXIT)               = (int) "exit";
    *(EXCEPTIONS + EXCEPTION_INTERRUPT)          = (int) "timer interrupt";
    *(EXCEPTIONS + EXCEPTION_PAGEFAULT)          = (int) "page fault";
}

void resetInterpreter() {
    registers = (int*) 0;

    pc = 0;
    ir = 0;

    reg_hi = 0;
    reg_lo = 0;

    pt = (int*) 0;

    brk = maxBinaryLength;

    trap = 0;

    status = 0;

    cycles = 0;

    timer = TIMESLICE;

    if (interpret) {
        calls           = 0;
        callsPerAddress = malloc(maxBinaryLength);

        loops           = 0;
        loopsPerAddress = malloc(maxBinaryLength);

        loads           = 0;
        loadsPerAddress = malloc(maxBinaryLength);

        stores           = 0;
        storesPerAddress = malloc(maxBinaryLength);
    }
}

// -----------------------------------------------------------------
// ---------------------------- CONTEXTS ---------------------------
// -----------------------------------------------------------------

int createID(int seed);

int* allocateContext(int ID, int parentID);
int* createContext(int ID, int parentID, int *in);

int* findContext(int ID, int *in);

void switchContext(int *from, int *to);

void freeContext(int *context);
int* deleteContext(int *context, int *from);

void mapPage(int *table, int page, int frame);

// context struct:
// +---+--------+
// | 0 | next   | pointer to next context
// | 1 | prev   | pointer to previous context
// | 2 | id     | unique identifier
// | 3 | pc     | program counter
// | 4 | regs   | pointer to general purpose registers
// | 5 | reg_hi | hi register
// | 6 | reg_lo | lo register
// | 7 | pt     | pointer to page table
// | 8 | brk    | break between code, data, and heap
// | 9 | parent | ID of context that created this context
// +---+--------+

int* getNextContext(int *context) { return (int*) *context; }
int* getPrevContext(int *context) { return (int*) *(context + 1); }
int  getID(int *context)          { return        *(context + 2); }
int  getPC(int *context)          { return        *(context + 3); }
int* getRegs(int *context)        { return (int*) *(context + 4); }
int  getRegHi(int *context)       { return        *(context + 5); }
int  getRegLo(int *context)       { return        *(context + 6); }
int* getPT(int *context)          { return (int*) *(context + 7); }
int  getBreak(int *context)       { return        *(context + 8); }
int  getParent(int *context)      { return        *(context + 9); }

void setNextContext(int *context, int *next) { *context       = (int) next; }
void setPrevContext(int *context, int *prev) { *(context + 1) = (int) prev; }
void setID(int *context, int id)             { *(context + 2) = id; }
void setPC(int *context, int pc)             { *(context + 3) = pc; }
void setRegs(int *context, int *regs)        { *(context + 4) = (int) regs; }
void setRegHi(int *context, int reg_hi)      { *(context + 5) = reg_hi; }
void setRegLo(int *context, int reg_lo)      { *(context + 6) = reg_lo; }
void setPT(int *context, int *pt)            { *(context + 7) = (int) pt; }
void setBreak(int *context, int brk)         { *(context + 8) = brk; }
void setParent(int *context, int id)         { *(context + 9) = id; }

// -----------------------------------------------------------------
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

void resetMicrokernel();

// ------------------------ GLOBAL CONSTANTS -----------------------

int NO_ID = -1;

// ------------------------ GLOBAL VARIABLES -----------------------

int bumpID; // counter for generating unique context IDs

int *currentContext  = (int*) 0; // context currently running

int *activeContexts = (int*) 0; // doubly-linked list of active contexts
int *freeContexts   = (int*) 0; // singly-linked list of free contexts

// ------------------------- INITIALIZATION ------------------------

void resetMicrokernel() {
    bumpID = NO_ID;

    currentContext = (int*) 0;

    while (activeContexts != (int*) 0)
        activeContexts = deleteContext(activeContexts, activeContexts);
}

// -----------------------------------------------------------------
// --------------------------- HYPSTER -----------------------------
// -----------------------------------------------------------------

int  palloc();
void pfree(int frame);

void down_mapPageTable(int *context);

void boot(int argc, int *argv);

// ------------------------ GLOBAL VARIABLES -----------------------

int initID = 0;

int *readyContexts = (int*) 0;

int *initContext = (int*) 0;

int usedMemory = 0;

int nextPageFrame = 0;
int freePageFrame = 0;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     L I B R A R Y     ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------- LIBRARY FUNCTIONS -----------------------
// -----------------------------------------------------------------

int twoToThePowerOf(int p) {
    // assert: 0 <= p < 31
    return *(power_of_two_table + p);
}

int leftShift(int n, int b) {
    // assert: b >= 0;

    if (b > 30)
        return 0;
    else
        return n * twoToThePowerOf(b);
}

int rightShift(int n, int b) {
    // assert: b >= 0

    if (b > 30)
        return 0;
    else if (n >= 0)
        return n / twoToThePowerOf(b);
    else
        // works even if n == INT_MIN:
        // shift right n with msb reset and then restore msb
        return ((n + 1) + INT_MAX) / twoToThePowerOf(b) +
            (INT_MAX / twoToThePowerOf(b) + 1);
}

int loadCharacter(int *s, int i) {
    // assert: i >= 0
    int a;

    a = i / SIZEOFINT;

    return rightShift(leftShift(*(s + a), ((SIZEOFINT - 1) - (i % SIZEOFINT)) * 8), (SIZEOFINT - 1) * 8);
}

int* storeCharacter(int *s, int i, int c) {
    // assert: i >= 0, all characters are 7-bit
    int a;

    a = i / SIZEOFINT;

    *(s + a) = (*(s + a) - leftShift(loadCharacter(s, i), (i % SIZEOFINT) * 8)) + leftShift(c, (i % SIZEOFINT) * 8);
    
    return s;
}

int stringLength(int *s) {
    int i;

    i = 0;

    while (loadCharacter(s, i) != 0)
        i = i + 1;

    return i;
}

void stringReverse(int *s) {
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

int stringCompare(int *s, int *t) {
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

int atoi(int *s) {
    int i;
    int n;
    int c;

    i = 0;

    n = 0;

    c = loadCharacter(s, i);

    while (c != 0) {
        c = c - '0';

        if (c < 0)
            return -1;
        else if (c > 9)
            return -1;

        n = n * 10 + c;
        
        i = i + 1;

        c = loadCharacter(s, i);

        if (n < 0) {
            if (n != INT_MIN)
                return -1;
            else if (c != 0)
                return -1;
        }
    }

    return n;
}

int* itoa(int n, int *s, int b, int a, int p) {
    // assert: b in {2,4,8,10,16}

    int i;
    int sign;
    int msb;

    i = 0;

    sign = 0;

    msb = 0;

    if (n == 0) {
        storeCharacter(s, 0, '0');

        i = 1;
    } else if (n < 0) {
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

                i = i + 1;
                p = 0;
            }

        if (n % b > 9)
            storeCharacter(s, i, n % b - 10 + 'A');
        else
            storeCharacter(s, i, n % b + '0');

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

        storeCharacter(s, i, '.');     // set point
        storeCharacter(s, i + 1, '0'); // leading 0

        i = i + 2;
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
            storeCharacter(s, i, '0');     // octal numbers start with 00
            storeCharacter(s, i + 1, '0');

            i = i + 2;
        } else if (b == 16) {
            storeCharacter(s, i, 'x');     // hexadecimal numbers start with 0x
            storeCharacter(s, i + 1, '0');

            i = i + 2;
        }
    }
    
    storeCharacter(s, i, 0); // null terminated string

    stringReverse(s);

    return s;
}

void putCharacter(int character) {
    if (outputFD == 1)
        putchar(character);
    else {
        *character_buffer = character;

        // assert: character_buffer is mapped

        if (write(outputFD, character_buffer, 1) != 1) {
            outputFD = 1;

            print(selfieName);
            print((int*) ": could not write character to output file ");
            print(outputName);
            println();

            exit(-1);
        }
    }
}

void print(int *s) {
    int i;

    i = 0;

    while (loadCharacter(s, i) != 0) {
        putCharacter(loadCharacter(s, i));

        i = i + 1;
    }
}

void println() {
    putCharacter(CHAR_LF);
}

void printCharacter(int character) {
    putCharacter(CHAR_SINGLEQUOTE);

    if (character == CHAR_EOF)
        print((int*) "end of file");
    else if (character == CHAR_TAB)
        print((int*) "tabulator");
    else if (character == CHAR_LF)
        print((int*) "line feed");
    else if (character == CHAR_CR)
        print((int*) "carriage return");
    else
        putCharacter(character);

    putCharacter(CHAR_SINGLEQUOTE);
}

void printString(int *s) {
    putCharacter(CHAR_DOUBLEQUOTE);

    print(s);
    
    putCharacter(CHAR_DOUBLEQUOTE);
}

int roundUp(int n, int m) {
    if (n % m == 0)
        return n;
    else if (n >= 0)
        return n + m - n % m;
    else
        return n - n % m;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     C O M P I L E R   ---------------------
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
    print(itoa(line, string_buffer, 10, 0, 0));
    print((int*) ": ");
}

void syntaxErrorMessage(int *message) {
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

void getCharacter() {
    int numberOfReadBytes;

    // assert: character_buffer is mapped

    numberOfReadBytes = read(sourceFD, character_buffer, 1);

    if (numberOfReadBytes == 1)
        character = *character_buffer;
    else if (numberOfReadBytes == 0)
        character = CHAR_EOF;
    else {
        print(selfieName);
        print((int*) ": could not read character from input file ");
        print(sourceName);
        println();

        exit(-1);
    }
}

int isCharacterWhitespace() {
    if (character == CHAR_SPACE)
        return 1;
    else if (character == CHAR_TAB)
        return 1;
    else if (character == CHAR_LF)
        return 1;
    else if (character == CHAR_CR)
        return 1;
    else
        return 0;
}

int findNextCharacter() {
    int inComment;

    inComment = 0;

    while (1) {
        if (inComment) {
            getCharacter();

            if (character == CHAR_LF)
                inComment = 0;
            else if (character == CHAR_CR)
                inComment = 0;
            else if (character == CHAR_EOF)
                return character;

        } else if (isCharacterWhitespace()) {
            if (character == CHAR_LF)
                lineNumber = lineNumber + 1;
            else if (character == CHAR_CR)
                lineNumber = lineNumber + 1;

            getCharacter();

        } else if (character == CHAR_HASH) {
            getCharacter();

            inComment = 1;

        } else if (character == CHAR_SLASH) {
            getCharacter();

            if (character == CHAR_SLASH)
                inComment = 1;
            else {
                symbol = SYM_DIV;
                return character;
            }

        } else
            return character;
    }
}

int isCharacterLetter() {
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

int isNotDoubleQuoteOrEOF() {
    if (character == CHAR_DOUBLEQUOTE)
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

int getSymbol() {
    int i;

    symbol = SYM_EOF;

    if (findNextCharacter() == CHAR_EOF)
        return SYM_EOF;
    else if (symbol == SYM_DIV)
        // check here because / was recognized instead of //
        return SYM_DIV;

    if (isCharacterLetter()) {
        identifier = malloc(maxIdentifierLength + 1);

        i = 0;

        while (isCharacterLetterOrDigitOrUnderscore()) {
            if (i >= maxIdentifierLength) {
                syntaxErrorMessage((int*) "identifier too long");

                exit(-1);
            }

            storeCharacter(identifier, i, character);

            i = i + 1;

            getCharacter();
        }

        storeCharacter(identifier, i, 0); // null terminated string

        symbol = identifierOrKeyword();

    } else if (isCharacterDigit()) {
        integer = malloc(maxIntegerLength + 1);

        i = 0;

        while (isCharacterDigit()) {
            if (i >= maxIntegerLength) {
                syntaxErrorMessage((int*) "integer out of bound");
                
                exit(-1);
            }

            storeCharacter(integer, i, character);

            i = i + 1;
            
            getCharacter();
        }

        storeCharacter(integer, i, 0); // null terminated string

        literal = atoi(integer);

        if (literal < 0) {
            if (literal == INT_MIN) {
                if (mayBeINTMIN)
                    isINTMIN = 1;
                else {
                    syntaxErrorMessage((int*) "integer out of bound");
                    
                    exit(-1);
                }
            } else {
                syntaxErrorMessage((int*) "integer out of bound");
                
                exit(-1);
            }
        }

        symbol = SYM_INTEGER;

    } else if (character == CHAR_SINGLEQUOTE) {
        getCharacter();

        literal = 0;

        if (character == CHAR_EOF) {
            syntaxErrorMessage((int*) "reached end of file looking for a character literal");

            exit(-1);
        } else
            literal = character;

        getCharacter();

        if (character == CHAR_SINGLEQUOTE)
            getCharacter();
        else if (character == CHAR_EOF) {
            syntaxErrorCharacter(CHAR_SINGLEQUOTE);

            exit(-1);
        } else
            syntaxErrorCharacter(CHAR_SINGLEQUOTE);

        symbol = SYM_CHARACTER;

    } else if (character == CHAR_DOUBLEQUOTE) {
        getCharacter();

        string = malloc(maxStringLength + 1);

        i = 0;

        while (isNotDoubleQuoteOrEOF()) {
            if (i >= maxStringLength) {
                syntaxErrorMessage((int*) "string too long");
                
                exit(-1);
            }

            storeCharacter(string, i, character);

            i = i + 1;
            
            getCharacter();
        }

        if (character == CHAR_DOUBLEQUOTE)
            getCharacter();
        else {
            syntaxErrorCharacter(CHAR_DOUBLEQUOTE);

            exit(-1);
        }

        storeCharacter(string, i, 0); // null terminated string

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

        exit(-1);
    }

    return symbol;
}

// -----------------------------------------------------------------
// ------------------------- SYMBOL TABLE --------------------------
// -----------------------------------------------------------------

void createSymbolTableEntry(int whichTable, int *string, int line, int class, int type, int value, int address) {
    int *newEntry;

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

int* searchSymbolTable(int *entry, int *string, int class) {
    while (entry != (int*) 0) {
        if (stringCompare(string, getString(entry)))
            if (class == getClass(entry))
                return entry;
        
        // keep looking
        entry = getNextEntry(entry);
    }

    return (int*) 0;
}

int* getSymbolTableEntry(int *string, int class) {
    int *entry;

    if (class == VARIABLE) {
        // local variables override global variables
        entry = searchSymbolTable(local_symbol_table, string, class);

        if (entry != (int*) 0)
            return entry;
    }
    
    return searchSymbolTable(global_symbol_table, string, class);
}

int isUndefinedProcedure(int *entry) {
    int *libraryEntry;

    if (getClass(entry) == PROCEDURE) {
        // library procedures override regular procedures for bootstrapping
        libraryEntry = searchSymbolTable(library_symbol_table, getString(entry), PROCEDURE);

        if (libraryEntry != (int*) 0)
            entry = libraryEntry;

        if (getAddress(entry) == 0)
            return 1;
        else if (getOpcode(loadBinary(getAddress(entry))) == OP_JAL)
            return 1;
    }
    
    return 0;
}

int reportUndefinedProcedures() {
    int undefined;
    int *entry;

    undefined = 0;

    entry = global_symbol_table;

    while (entry != (int*) 0) {
        if (isUndefinedProcedure(entry)) {
            undefined = 1;

            printLineNumber((int*) "error", getLineNumber(entry));
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
    else if(symbol == SYM_EOF)
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

        exit(-1);
    }
}

int currentTemporary() {
    if (allocatedTemporaries > 0)
        return allocatedTemporaries + REG_A3;
    else {
        syntaxErrorMessage((int*) "illegal register access");

        exit(-1);
    }
}

int previousTemporary() {
    if (allocatedTemporaries > 1)
        return currentTemporary() - 1;
    else {
        syntaxErrorMessage((int*) "illegal register access");

        exit(-1);
    }
}

int nextTemporary() {
    if (allocatedTemporaries < REG_T7 - REG_A3)
        return currentTemporary() + 1;
    else {
        syntaxErrorMessage((int*) "out of registers");

        exit(-1);
    }
}

void tfree(int numberOfTemporaries) {
    allocatedTemporaries = allocatedTemporaries - numberOfTemporaries;

    if (allocatedTemporaries < 0) {
        syntaxErrorMessage((int*) "illegal register deallocation");

        exit(-1);
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

int* putType(int type) {
    if (type == INT_T)
        return (int*) "int";
    else if (type == INTSTAR_T)
        return (int*) "int*";
    else if (type == VOID_T)
        return (int*) "void";
    else
        return (int*) "unknown";
}

void typeWarning(int expected, int found) {
    printLineNumber((int*) "warning", lineNumber);

    print((int*) "type mismatch, ");

    print(putType(expected));

    print((int*) " expected but ");

    print(putType(found));

    print((int*) " found");

    println();
}

int* getVariable(int *variable) {
    int *entry;

    entry = getSymbolTableEntry(variable, VARIABLE);

    if (entry == (int*) 0) {
        printLineNumber((int*) "error", lineNumber);
        print(variable);
        print((int*) " undeclared");
        println();

        exit(-1);
    }

    return entry;
}

int load_variable(int *variable) {
    int *entry;

    entry = getVariable(variable);

    talloc();

    emitIFormat(OP_LW, getScope(entry), currentTemporary(), getAddress(entry));

    return getType(entry);
}

void load_integer(int value) {
    // assert: value >= 0 or value == INT_MIN

    talloc();

    if (value >= 0) {
        if (value < twoToThePowerOf(15))
            // ADDIU can only load numbers < 2^15 without sign extension
            emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), value);
        else if (value < twoToThePowerOf(28)) {
            // load 14 msbs of a 28-bit number first
            emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), rightShift(value, 14));

            // shift left by 14 bits
            emitLeftShiftBy(14);

            // and finally add 14 lsbs
            emitIFormat(OP_ADDIU, currentTemporary(), currentTemporary(), rightShift(leftShift(value, 18), 18));
        } else {
            // load 14 msbs of a 31-bit number first
            emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), rightShift(value, 17));

            emitLeftShiftBy(14);

            // then add the next 14 msbs
            emitIFormat(OP_ADDIU, currentTemporary(), currentTemporary(), rightShift(leftShift(value, 15), 18));

            emitLeftShiftBy(3);

            // and finally add the remaining 3 lsbs
            emitIFormat(OP_ADDIU, currentTemporary(), currentTemporary(), rightShift(leftShift(value, 29), 29));
        }
    } else {
        // load largest positive 16-bit number with a single bit set: 2^14
        emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), twoToThePowerOf(14));

        // and then multiply 2^14 by 2^14*2^3 to get to 2^31 == INT_MIN
        emitLeftShiftBy(14);
        emitLeftShiftBy(3);
    }
}

void load_string(int *string) {
    int length;

    length = stringLength(string) + 1;

    allocatedMemory = allocatedMemory + roundUp(length, WORDSIZE);

    createSymbolTableEntry(GLOBAL_TABLE, string, lineNumber, STRING, INTSTAR_T, 0, -allocatedMemory);

    talloc();

    emitIFormat(OP_ADDIU, REG_GP, currentTemporary(), -allocatedMemory);
}

int help_call_codegen(int *entry, int *procedure) {
    int type;

    if (entry == (int*) 0) {
        // CASE 1: function call, no definition, no declaration.
        createSymbolTableEntry(GLOBAL_TABLE, procedure, lineNumber, PROCEDURE, INT_T, 0, binaryLength);

        emitJFormat(OP_JAL, 0);

        type = INT_T; //assume default return type 'int'

    } else {
        type = getType(entry);

        if (getAddress(entry) == 0) {
            // CASE 2: function call, no definition, but declared.
            setAddress(entry, binaryLength);

            emitJFormat(OP_JAL, 0);
        } else if (getOpcode(loadBinary(getAddress(entry))) == OP_JAL) {
            // CASE 3: function call, no declaration
            emitJFormat(OP_JAL, getAddress(entry) / WORDSIZE);

            setAddress(entry, binaryLength - 2 * WORDSIZE);
        } else
            // CASE 4: function defined, use the address
            emitJFormat(OP_JAL, getAddress(entry) / WORDSIZE);
    }

    return type;
}

void help_procedure_prologue(int localVariables) {
    // allocate space for return address
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, -WORDSIZE);

    // save return address
    emitIFormat(OP_SW, REG_SP, REG_RA, 0);

    // allocate space for caller's frame pointer
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, -WORDSIZE);

    // save caller's frame pointer
    emitIFormat(OP_SW, REG_SP, REG_FP, 0);

    // set callee's frame pointer
    emitIFormat(OP_ADDIU, REG_SP, REG_FP, 0);

    // allocate space for callee's local variables
    if (localVariables != 0)
        emitIFormat(OP_ADDIU, REG_SP, REG_SP, -localVariables * WORDSIZE);
}

void help_procedure_epilogue(int parameters) {
    // deallocate space for callee's frame pointer and local variables
    emitIFormat(OP_ADDIU, REG_FP, REG_SP, 0);

    // restore caller's frame pointer
    emitIFormat(OP_LW, REG_SP, REG_FP, 0);

    // deallocate space for caller's frame pointer
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

    // restore return address
    emitIFormat(OP_LW, REG_SP, REG_RA, 0);

    // deallocate space for return address and parameters
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, (parameters + 1) * WORDSIZE);

    // return
    emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

int gr_call(int *procedure) {
    int *entry;
    int numberOfTemporaries;
    int type;

    // assert: n = allocatedTemporaries

    // library procedures override regular procedures for bootstrapping
    entry = searchSymbolTable(library_symbol_table, procedure, PROCEDURE);

    if (entry == (int*) 0)
        entry = getSymbolTableEntry(procedure, PROCEDURE);

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

    // assert: allocatedTemporaries == n
    return type;
}

int gr_factor() {
    int hasCast;
    int cast;
    int type;

    int *variableOrProcedureName;

    // assert: n = allocatedTemporaries

    hasCast = 0;

    type = INT_T;

    while (lookForFactor()) {
        syntaxErrorUnexpected();

        if (symbol == SYM_EOF)
            exit(-1);
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

            // function call: identifier "(" ... ")"
            type = gr_call(variableOrProcedureName);

            talloc();

            emitIFormat(OP_ADDIU, REG_V0, currentTemporary(), 0);
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
                    // pointer arithmetic: factor of 2^2 of integer operand
                    emitLeftShiftBy(2);
            } else if (rtype == INTSTAR_T)
                typeWarning(ltype, rtype);

            emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_ADDU);

        } else if (operatorSymbol == SYM_MINUS) {
            if (ltype != rtype)
                typeWarning(ltype, rtype);

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
            // subtract, if result = 0 then 1, else 0
            emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_SUBU);

            tfree(1);

            emitIFormat(OP_BEQ, REG_ZR, currentTemporary(), 4);
            emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), 0);
            emitIFormat(OP_BEQ, REG_ZR, currentTemporary(), 2);
            emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), 1);

        } else if (operatorSymbol == SYM_NOTEQ) {
            // subtract, if result = 0 then 0, else 1
            emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_SUBU);

            tfree(1);

            emitIFormat(OP_BNE, REG_ZR, currentTemporary(), 4);
            emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), 0);
            emitIFormat(OP_BEQ, REG_ZR, currentTemporary(), 2);
            emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), 1);

        } else if (operatorSymbol == SYM_LT) {
            // set to 1 if a < b, else 0
            emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_SLT);

            tfree(1);

        } else if (operatorSymbol == SYM_GT) {
            // set to 1 if b < a, else 0
            emitRFormat(OP_SPECIAL, currentTemporary(), previousTemporary(), previousTemporary(), FCT_SLT);

            tfree(1);

        } else if (operatorSymbol == SYM_LEQ) {
            // if b < a set 0, else 1
            emitRFormat(OP_SPECIAL, currentTemporary(), previousTemporary(), previousTemporary(), FCT_SLT);

            tfree(1);

            emitIFormat(OP_BNE, REG_ZR, currentTemporary(), 4);
            emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), 1);
            emitIFormat(OP_BEQ, REG_ZR, REG_ZR, 2);
            emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), 0);

        } else if (operatorSymbol == SYM_GEQ) {
            // if a < b set 0, else 1
            emitRFormat(OP_SPECIAL, previousTemporary(), currentTemporary(), previousTemporary(), FCT_SLT);

            tfree(1);

            emitIFormat(OP_BNE, REG_ZR, currentTemporary(), 4);
            emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), 1);
            emitIFormat(OP_BEQ, REG_ZR, REG_ZR, 2);
            emitIFormat(OP_ADDIU, REG_ZR, currentTemporary(), 0);
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

                        exit(-1);
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
        // now we have our address for the conditional jump from above
        fixup_relative(brForwardToEnd);

    // assert: allocatedTemporaries == 0
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

            // if the "if" case is not true, we jump to "else" (if provided)
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

                        exit(-1);
                    }
                }
                // only one statement without {}
                else
                    gr_statement();

                //optional: else
                if (symbol == SYM_ELSE) {
                    getSymbol();

                    // if the "if" case was true, we jump to the end
                    brForwardToEnd = binaryLength;
                    emitIFormat(OP_BEQ, REG_ZR, REG_ZR, 0);

                    // if the "if" case was not true, we jump here
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

                            exit(-1);
                        }

                    // only one statement without {}
                    } else
                        gr_statement();

                    // if the "if" case was true, we jump here
                    fixup_relative(brForwardToEnd);
                } else
                    // if the "if" case was not true, we jump here
                    fixup_relative(brForwardToElseOrEnd);
            } else
                syntaxErrorSymbol(SYM_RPARENTHESIS);
        } else
            syntaxErrorSymbol(SYM_LPARENTHESIS);
    } else
        syntaxErrorSymbol(SYM_IF);

    // assert: allocatedTemporaries == 0
}

void gr_return(int returnType) {
    int type;

    // assert: allocatedTemporaries == 0

    if (symbol == SYM_RETURN)
        getSymbol();
    else
        syntaxErrorSymbol(SYM_RETURN);

    // optional: expression
    if (symbol != SYM_SEMICOLON) {
        type = gr_expression();

        if (returnType == VOID_T)
            typeWarning(type, returnType);
        else if (type != returnType)
            typeWarning(returnType, type);

        // save value of expression in return register
        emitRFormat(OP_SPECIAL, REG_ZR, currentTemporary(), REG_V0, FCT_ADDU);
        
        tfree(1);
    }

    // unconditional branch to procedure epilogue
    // maintain fixup chain for later fixup
    emitJFormat(OP_J, returnBranches / WORDSIZE);

    // new head of fixup chain
    // offest is two words rather than one because of delay slot NOP
    returnBranches = binaryLength - 2 * WORDSIZE;

    // assert: allocatedTemporaries == 0
}

void gr_statement() {
    int ltype;
    int rtype;
    int *variableOrProcedureName;
    int *entry;

    // assert: allocatedTemporaries == 0;

    while (lookForStatement()) {
        syntaxErrorUnexpected();

        if (symbol == SYM_EOF)
            exit(-1);
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
            } else
                syntaxErrorSymbol(SYM_ASSIGN);

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
                } else
                    syntaxErrorSymbol(SYM_ASSIGN);

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

        // call
        if (symbol == SYM_LPARENTHESIS) {
            getSymbol();

            gr_call(variableOrProcedureName);

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
        entry = getSymbolTableEntry(currentProcedureName, PROCEDURE);

        gr_return(getType(entry));

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
        createSymbolTableEntry(LOCAL_TABLE, identifier, lineNumber, VARIABLE, type, 0, offset);

        getSymbol();
    } else {
        syntaxErrorSymbol(SYM_IDENTIFIER);

        createSymbolTableEntry(LOCAL_TABLE, (int*) "missing variable name", lineNumber, VARIABLE, type, 0, offset);
    }
}

void gr_initialization(int *name, int offset, int type) {
    int actualLineNumber;
    int hasCast;
    int cast;
    int sign;

    actualLineNumber = lineNumber;

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

    createSymbolTableEntry(GLOBAL_TABLE, name, actualLineNumber, VARIABLE, type, initialValue, offset);
}

void gr_procedure(int *procedure, int returnType) {
    int numberOfParameters;
    int parameters;
    int localVariables;
    int functionStart;
    int *entry;

    currentProcedureName = procedure;

    numberOfParameters = 0;

    // ( variable , variable ) ;
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
                entry      = getNextEntry(entry);
            }

            if (symbol == SYM_RPARENTHESIS)
                getSymbol();
            else
                syntaxErrorSymbol(SYM_RPARENTHESIS);
        } else
            getSymbol();
    } else
        syntaxErrorSymbol(SYM_LPARENTHESIS);

    if (symbol == SYM_SEMICOLON) {
        entry = getSymbolTableEntry(currentProcedureName, PROCEDURE);

        if (entry == (int*) 0)
            createSymbolTableEntry(GLOBAL_TABLE, currentProcedureName, lineNumber, PROCEDURE, returnType, 0, 0);

        getSymbol();

    // ( variable, variable ) { variable; variable; statement }
    } else if (symbol == SYM_LBRACE) {
        functionStart = binaryLength;
        
        entry = getSymbolTableEntry(currentProcedureName, PROCEDURE);

        if (entry == (int*) 0)
            createSymbolTableEntry(GLOBAL_TABLE, currentProcedureName, lineNumber, PROCEDURE, returnType, 0, binaryLength);
        else {
            if (getAddress(entry) != 0) {
                if (getOpcode(loadBinary(getAddress(entry))) == OP_JAL)
                    fixlink_absolute(getAddress(entry), functionStart);
                else {
                    printLineNumber((int*) "error", lineNumber);
                    print((int*) "multiple definitions of ");
                    print(currentProcedureName);
                    println();
                }
            }

            setLineNumber(entry, lineNumber);
            setAddress(entry, functionStart);

            if (getType(entry) != returnType)
                typeWarning(getType(entry), returnType);

            setType(entry, returnType);
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

        while (isNotRbraceOrEOF())
            gr_statement();

        if (symbol == SYM_RBRACE)
            getSymbol();
        else {
            syntaxErrorSymbol(SYM_RBRACE);

            exit(-1);
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
    int *variableOrProcedureName;

    while (symbol != SYM_EOF) {
        while (lookForType()) {
            syntaxErrorUnexpected();

            if (symbol == SYM_EOF)
                exit(-1);
            else
                getSymbol();
        }

        // void identifier procedure
        if (symbol == SYM_VOID) {
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

                // type identifier "(" procedure declaration or definition
                if (symbol == SYM_LPARENTHESIS)
                    gr_procedure(variableOrProcedureName, type);
                else {
                    allocatedMemory = allocatedMemory + WORDSIZE;

                    // type identifier ";" global variable declaration
                    if (symbol == SYM_SEMICOLON) {
                        createSymbolTableEntry(GLOBAL_TABLE, variableOrProcedureName, lineNumber, VARIABLE, type, 0, -allocatedMemory);

                        getSymbol();

                    // type identifier "=" global variable definition
                    } else
                        gr_initialization(variableOrProcedureName, -allocatedMemory, type);
                }
            } else
                syntaxErrorSymbol(SYM_IDENTIFIER);
        }
    }
}

// -----------------------------------------------------------------
// ------------------------ MACHINE CODE LIBRARY -------------------
// -----------------------------------------------------------------

void emitLeftShiftBy(int b) {
    // assert: 0 <= b < 15

    // load multiplication factor less than 2^15 to avoid sign extension
    emitIFormat(OP_ADDIU, REG_ZR, nextTemporary(), twoToThePowerOf(b));
    emitRFormat(OP_SPECIAL, currentTemporary(), nextTemporary(), 0, FCT_MULTU);
    emitRFormat(OP_SPECIAL, 0, 0, currentTemporary(), FCT_MFLO);
}

void emitMainEntry() {
    int i;

    // the instruction at address zero cannot be fixed up
    // we therefore need at least one not-to-be-fixed-up instruction here

    // we generate NOPs to accommodate GP and SP register
    // initialization code that overwrites the NOPs later
    // when binaryLength is known

    i = 0;
    
    // 8 NOPs per register is enough for initialization
    // since we load positive integers < 2^28 which take
    // no more than 8 instructions each, see load_integer
    while (i < 16) {
        emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_NOP);

        i = i + 1;
    }

    createSymbolTableEntry(GLOBAL_TABLE, (int*) "main", 0, PROCEDURE, INT_T, 0, binaryLength);

    // jump and link to main, will return here only if there is no exit call
    emitJFormat(OP_JAL, 0);

    // we exit cleanly with error code 0 pushed onto the stack
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, -WORDSIZE);
    emitIFormat(OP_SW, REG_SP, REG_ZR, 0);
}

void fixRegisterInitialization() {
    int savedBinaryLength;

    savedBinaryLength = binaryLength;

    binaryLength = 0;

    // assert: allocatedTemporaries == 0

    // assert: 0 <= savedBinaryLength < 2^28 (see load_integer)

    load_integer(savedBinaryLength);

    // load binaryLength into GP register
    emitIFormat(OP_ADDIU, currentTemporary(), REG_GP, 0);

    tfree(1);

    // assert: allocatedTemporaries == 0

    // assert: 0 <= VIRTUALMEMORYSIZE - WORDSIZE < 2^28 (see load_integer)

    // initial stack pointer is stored at highest virtual address
    load_integer(VIRTUALMEMORYSIZE - WORDSIZE);

    // load initial stack pointer into SP register
    emitIFormat(OP_LW, currentTemporary(), REG_SP, 0);

    tfree(1);

    // assert: allocatedTemporaries == 0

    binaryLength = savedBinaryLength;
}

// -----------------------------------------------------------------
// --------------------------- COMPILER ----------------------------
// -----------------------------------------------------------------

void selfie_compile() {
    print(selfieName);
    print((int*) ": this is selfie's cstarc compiling ");
    print(sourceName);
    println();

    // assert: sourceName is mapped and not longer than maxFilenameLength

    sourceFD = open(sourceName, O_RDONLY, 0);

    if (sourceFD < 0) {
        print(selfieName);
        print((int*) ": could not open input file ");
        print(sourceName);
        println();

        exit(-1);
    }

    // reset scanner
    resetScanner();

    // reset symbol tables
    resetSymbolTables();

    // allocate space for storing binary
    binary       = malloc(maxBinaryLength);
    binaryLength = 0;

    // reset code length
    codeLength = 0;

    // allocate space for storing source code line numbers
    sourceLineNumber = malloc(maxBinaryLength);

    // jump to main
    emitMainEntry();

    // library:
    // exit must be first to exit main
    // if exit call in main is missing
    emitExit();
    emitRead();
    emitWrite();
    emitOpen();
    emitMalloc();
    emitPutchar();

    emitID();
    emitCreate();
    emitSwitch();
    emitStatus();
    emitDelete();
    emitMap();

    // parser
    gr_cstar();

    // set code length
    codeLength = binaryLength;

    // emit global variables and strings
    emitGlobalsStrings();

    // fix register initialization code
    fixRegisterInitialization();

    if (reportUndefinedProcedures())
        exit(-1);
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
// |opcode|  rs |  rt |  rd |00000|fction|
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
// |opcode|  rs |  rt |    immediate   |
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

// -----------------------------------------------------------------
// ---------------------------- DECODER ----------------------------
// -----------------------------------------------------------------

void printOpcode(int opcode) {
    print((int*) *(OPCODES + opcode));
}

void printFunction(int function) {
    print((int*) *(FUNCTIONS + function));
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

// --------------------------------------------------------------
// 32 bit
//
// +------+-----+-----+-----+-----+------+
// |opcode|  rs |  rt |  rd |00000|fction|
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
// |opcode|  rs |  rt |    immediate   |
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

// -----------------------------------------------------------------
// ----------------------------- CODE ------------------------------
// -----------------------------------------------------------------

int loadBinary(int baddr) {
    return *(binary + baddr / WORDSIZE);
}

void storeBinary(int baddr, int instruction) {
    *(binary + baddr / WORDSIZE) = instruction;
}

void storeInstruction(int baddr, int instruction) {
    if (*(sourceLineNumber + baddr / WORDSIZE) == 0)
        *(sourceLineNumber + baddr / WORDSIZE) = lineNumber;

    storeBinary(baddr, instruction);
}

void emitInstruction(int instruction) {
    if (binaryLength >= maxBinaryLength) {
        syntaxErrorMessage((int*) "exceeded maximum binary length");
        exit(-1);
    } else {
        storeInstruction(binaryLength, instruction);
        
        binaryLength = binaryLength + WORDSIZE;
    }
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
    else if (opcode == OP_BNE)
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

int copyStringToBinary(int *s, int baddr) {
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
    int *entry;

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

void selfie_emit() {
    int fd;
    
    // assert: binaryName is mapped and not longer than maxFilenameLength

    fd = open(binaryName, O_CREAT_WRONLY_TRUNC, S_IRUSR_IWUSR_IRGRP_IROTH);

    if (fd < 0) {
        print(selfieName);
        print((int*) ": could not create output file ");
        print(binaryName);
        println();

        exit(-1);
    }

    print(selfieName);
    print((int*) ": writing code into output file ");
    print(binaryName);
    println();

    *io_buffer = codeLength;

    // assert: io_buffer is mapped

    // first write code length
    write(fd, io_buffer, WORDSIZE);

    // assert: binary is mapped

    // then write binary
    write(fd, binary, binaryLength);
}

int* touch(int *memory, int length) {
    int *m;
    int n;

    m = memory;

    if (length > 0)
        // touch memory at beginning
        n = *m;

    while (length > PAGESIZE) {
        length = length - PAGESIZE;

        m = m + PAGESIZE / WORDSIZE;

        // touch every following page
        n = *m;
    }

    if (length > 0) {
        m = m + (length - 1) / WORDSIZE;

        // touch at end
        n = *m;
    }

    return memory;
}

void selfie_load() {
    int fd;
    int numberOfReadBytes;

    // assert: binaryName is mapped and not longer than maxFilenameLength

    fd = open(binaryName, O_RDONLY, 0);

    if (fd < 0) {
        print(selfieName);
        print((int*) ": could not open input file ");
        print(binaryName);
        println();

        exit(-1);
    }

    // make sure binary is mapped
    binary = touch(malloc(maxBinaryLength), maxBinaryLength);

    binaryLength = 0;
    codeLength   = 0;

    // no source line numbers in binaries
    sourceLineNumber = (int*) 0;

    print(selfieName);
    print((int*) ": loading code from input file ");
    print(binaryName);
    println();

    // assert: io_buffer is mapped

    // read code length first
    numberOfReadBytes = read(fd, io_buffer, WORDSIZE);

    if (numberOfReadBytes == WORDSIZE) {
        codeLength = *io_buffer;
        
        if (codeLength <= maxBinaryLength) {
            // assert: binary is mapped

            // now read binary including global variables and strings
            numberOfReadBytes = read(fd, binary, maxBinaryLength);

            if (numberOfReadBytes > 0) {
                binaryLength = numberOfReadBytes;

                // check if we are really at EOF
                if (read(fd, io_buffer, WORDSIZE) == 0)
                    return;
            }
        }
    }
    
    print(selfieName);
    print((int*) ": failed to load code from input file ");
    print(binaryName);
    println();

    exit(-1);
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

void implementExit() {
    throwException(EXCEPTION_EXIT, *(registers+REG_A0)); // exit code

    print(binaryName);
    print((int*) ": exiting with error code ");
    print(itoa(*(registers+REG_A0), string_buffer, 10, 0, 0));
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

void implementRead() {
    int size;
    int vaddr;
    int fd;
    int readTotal;
    int bytesToRead;
    int *buffer;
    int actuallyRead;
    int failed;

    // assert: read buffer is mapped

    size  = *(registers+REG_A2);
    vaddr = *(registers+REG_A1);
    fd    = *(registers+REG_A0);

    if (debug_read) {
        print(binaryName);
        print((int*) ": trying to read ");
        print(itoa(size, string_buffer, 10, 0, 0));
        print((int*) " bytes from file with descriptor ");
        print(itoa(fd, string_buffer, 10, 0, 0));
        print((int*) " into buffer at virtual address ");
        print(itoa(vaddr, string_buffer, 16, 8, 0));
        println();
    }

    readTotal   = 0;
    bytesToRead = WORDSIZE;

    failed = 0;

    while (size > 0) {
        if (isValidVirtualAddress(vaddr)) {
            if (isVirtualAddressMapped(pt, vaddr)) {
                buffer = tlb(pt, vaddr);

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
                    print(binaryName);
                    print((int*) ": reading into virtual address ");
                    print(itoa(vaddr, string_buffer, 16, 8, 0));
                    print((int*) " failed because the address is unmapped");
                    println();
                }
            }
        } else {
            failed = 1;

            size = 0;

            if (debug_read) {
                print(binaryName);
                print((int*) ": reading into virtual address ");
                print(itoa(vaddr, string_buffer, 16, 8, 0));
                print((int*) " failed because the address is invalid");
                println();
            }
        }
    }

    if (failed == 0)
        *(registers+REG_V0) = readTotal;
    else
        *(registers+REG_V0) = -1;

    if (debug_read) {
        print(binaryName);
        print((int*) ": actually read ");
        print(itoa(readTotal, string_buffer, 10, 0, 0));
        print((int*) " bytes from file with descriptor ");
        print(itoa(fd, string_buffer, 10, 0, 0));
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

void implementWrite() {
    int size;
    int vaddr;
    int fd;
    int writtenTotal;
    int bytesToWrite;
    int *buffer;
    int actuallyWritten;
    int failed;

    // assert: write buffer is mapped

    size  = *(registers+REG_A2);
    vaddr = *(registers+REG_A1);
    fd    = *(registers+REG_A0);

    if (debug_write) {
        print(binaryName);
        print((int*) ": trying to write ");
        print(itoa(size, string_buffer, 10, 0, 0));
        print((int*) " bytes from buffer at virtual address ");
        print(itoa(vaddr, string_buffer, 16, 8, 0));
        print((int*) " into file with descriptor ");
        print(itoa(fd, string_buffer, 10, 0, 0));
        println();
    }

    writtenTotal = 0;
    bytesToWrite = WORDSIZE;

    failed = 0;

    while (size > 0) {
        if (isValidVirtualAddress(vaddr)) {
            if (isVirtualAddressMapped(pt, vaddr)) {
                buffer = tlb(pt, vaddr);
        
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
                    print(binaryName);
                    print((int*) ": writing into virtual address ");
                    print(itoa(vaddr, string_buffer, 16, 8, 0));
                    print((int*) " failed because the address is unmapped");
                    println();
                }
            }
        } else {
            failed = 1;

            size = 0;

            if (debug_write) {
                print(binaryName);
                print((int*) ": writing into virtual address ");
                print(itoa(vaddr, string_buffer, 16, 8, 0));
                print((int*) " failed because the address is invalid");
                println();
            }
        }
    }

    if (failed == 0)
        *(registers+REG_V0) = writtenTotal;
    else
        *(registers+REG_V0) = -1;

    if (debug_write) {
        print(binaryName);
        print((int*) ": actually wrote ");
        print(itoa(writtenTotal, string_buffer, 10, 0, 0));
        print((int*) " bytes into file with descriptor ");
        print(itoa(fd, string_buffer, 10, 0, 0));
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

int down_loadString(int *table, int vaddr, int *s) {
    int i;
    int *paddr;

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
                    print(binaryName);
                    print((int*) ": opening file with name at virtual address ");
                    print(itoa(vaddr, string_buffer, 16, 8, 0));
                    print((int*) " failed because the address is unmapped");
                    println();
                }
            }
        } else {
            if (debug_open) {
                print(binaryName);
                print((int*) ": opening file with name at virtual address ");
                print(itoa(vaddr, string_buffer, 16, 8, 0));
                print((int*) " failed because the address is invalid");
                println();
            }
        }
    }

    return 0;
}

void implementOpen() {
    int mode;
    int flags;
    int vaddr;
    int fd;

    mode  = *(registers+REG_A2);
    flags = *(registers+REG_A1);
    vaddr = *(registers+REG_A0);

    if (down_loadString(pt, vaddr, filename_buffer)) {
        fd = open(filename_buffer, flags, mode);

        *(registers+REG_V0) = fd;

        if (debug_open) {
            print(binaryName);
            print((int*) ": opened file ");
            printString(filename_buffer);
            print((int*) " with flags ");
            print(itoa(flags, string_buffer, 16, 0, 0));
            print((int*) " and mode ");
            print(itoa(mode, string_buffer, 8, 0, 0));
            print((int*) " returning file descriptor ");
            print(itoa(fd, string_buffer, 10, 0, 0));
            println();
        }
    } else {
        *(registers+REG_V0) = -1;

        if (debug_open) {
            print(binaryName);
            print((int*) ": opening file with name at virtual address ");
            print(itoa(vaddr, string_buffer, 16, 8, 0));
            print((int*) " failed because the name is too long");
            println();
        }
    }
}

void emitMalloc() {
    createSymbolTableEntry(LIBRARY_TABLE, (int*) "malloc", 0, PROCEDURE, INTSTAR_T, 0, binaryLength);

    emitIFormat(OP_LW, REG_SP, REG_A0, 0); // size
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

    emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_MALLOC);
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

    emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

void implementMalloc() {
    int size;
    int bump;

    if (debug_malloc) {
        print(binaryName);
        print((int*) ": trying to malloc ");
        print(itoa(*(registers+REG_A0), string_buffer, 10, 0, 0));
        print((int*) " bytes");
        println();
    }

    size = roundUp(*(registers+REG_A0), WORDSIZE);

    bump = brk;

    if (bump + size >= *(registers+REG_SP))
        throwException(EXCEPTION_HEAPOVERFLOW, 0);
    else {
        *(registers+REG_V0) = bump;

        brk = bump + size;

        if (debug_malloc) {
            print(binaryName);
            print((int*) ": actually mallocating ");
            print(itoa(size, string_buffer, 10, 0, 0));
            print((int*) " bytes at virtual address ");
            print(itoa(bump, string_buffer, 16, 8, 0));
            println();
        }
    }
}

void emitPutchar() {
    createSymbolTableEntry(LIBRARY_TABLE, (int*) "putchar", 0, PROCEDURE, INT_T, 0, binaryLength);

    emitIFormat(OP_ADDIU, REG_ZR, REG_A2, WORDSIZE); // write one word

    emitIFormat(OP_ADDIU, REG_SP, REG_A1, 0); // pointer to character
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

    emitIFormat(OP_ADDIU, REG_ZR, REG_A0, 1); // stdout file descriptor

    emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_WRITE);
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

    emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

// -----------------------------------------------------------------
// ----------------------- HYPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------


void emitID() {
    createSymbolTableEntry(LIBRARY_TABLE, (int*) "hypster_ID", 0, PROCEDURE, INT_T, 0, binaryLength);

    emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_ID);
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

    emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

void implementID() {
    // this procedure is executed at boot levels higher than zero
    *(registers+REG_V0) = getID(currentContext);
}

int hypster_ID() {
    // this procedure is only executed at boot level zero
    return NO_ID;
}

int selfie_ID() {
    if (mipster)
        return NO_ID;
    else
        return hypster_ID();
}

void emitCreate() {
    createSymbolTableEntry(LIBRARY_TABLE, (int*) "hypster_create", 0, PROCEDURE, INT_T, 0, binaryLength);

    emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_CREATE);
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

    emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

int doCreate(int parentID) {
    if (bumpID < INT_MAX) {
        bumpID = createID(bumpID);

        activeContexts = createContext(bumpID, parentID, activeContexts);

        if (currentContext == (int*) 0)
            currentContext = activeContexts;

        if (debug_create) {
            print(binaryName);
            print((int*) ": selfie_create context ");
            print(itoa(bumpID, string_buffer, 10, 0, 0));
            println();
        }

        return bumpID;
    } else {
        print(binaryName);
        print((int*) ": selfie_create failed");
        println();

        exit(-1);
    }
}

void implementCreate() {
    // this procedure is executed at boot levels higher than zero
    *(registers+REG_V0) = doCreate(getID(currentContext));
}

int hypster_create() {
    // this procedure is only executed at boot level zero
    return doCreate(selfie_ID());
}

int selfie_create() {
    if (mipster)
        return doCreate(selfie_ID());
    else
        return hypster_create();
}

void emitSwitch() {
    createSymbolTableEntry(LIBRARY_TABLE, (int*) "hypster_switch", 0, PROCEDURE, INT_T, 0, binaryLength);

    emitIFormat(OP_LW, REG_SP, REG_A0, 0); // ID of context to which we switch
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

    emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_SWITCH);
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

    // save ID of context from which we are switching here in return register
    emitRFormat(OP_SPECIAL, REG_ZR, REG_V1, REG_V0, FCT_ADDU);

    emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

int doSwitch(int toID) {
    int fromID;
    int *toContext;

    fromID = getID(currentContext);

    toContext = findContext(toID, activeContexts);

    if (toContext != (int*) 0) {
        switchContext(currentContext, toContext);

        currentContext = toContext;

        if (debug_switch) {
            print(binaryName);
            print((int*) ": selfie_switch from context ");
            print(itoa(fromID, string_buffer, 10, 0, 0));
            print((int*) " to context ");
            print(itoa(toID, string_buffer, 10, 0, 0));
            println();
        }
    } else if (debug_switch) {
        print(binaryName);
        print((int*) ": selfie_switch context ");
        print(itoa(toID, string_buffer, 10, 0, 0));
        print((int*) " not found");
        println();
    }

    return fromID;
}

void implementSwitch() {
    // this procedure is executed at boot levels higher than zero
    *(registers+REG_V1) = doSwitch(*(registers+REG_A0));
}

int mipster_switch(int toID) {
    *(registers+REG_V1) = doSwitch(toID);

    runUntilException();

    return getID(currentContext);
}

int hypster_switch(int toID) {
    // this procedure is only executed at boot level zero
    return mipster_switch(toID);
}

int selfie_switch(int toID) {
    if (mipster)
        return mipster_switch(toID);
    else
        return hypster_switch(toID);
}

void emitStatus() {
    createSymbolTableEntry(LIBRARY_TABLE, (int*) "hypster_status", 0, PROCEDURE, INT_T, 0, binaryLength);

    emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_STATUS);
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

    emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

int doStatus() {
    int savedStatus;

    savedStatus = status;

    status = 0;

    if (debug_status) {
        print(binaryName);
        print((int*) ": selfie_status ");
        printStatus(savedStatus);
        println();
    }

    return savedStatus;
}

void implementStatus() {
    // this procedure is executed at boot levels higher than zero
    *(registers+REG_V0) = doStatus();
}

int hypster_status() {
    // this procedure is only executed at boot level zero
    return doStatus();
}

int selfie_status() {
    if (mipster)
        return doStatus();
    else
        return hypster_status();
}

void emitDelete() {
    createSymbolTableEntry(LIBRARY_TABLE, (int*) "hypster_delete", 0, PROCEDURE, VOID_T, 0, binaryLength);

    emitIFormat(OP_LW, REG_SP, REG_A0, 0); // context ID
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

    emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_DELETE);
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

    emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

void doDelete(int ID) {
    int *context;

    context = findContext(ID, activeContexts);

    if (context != (int*) 0) {
        activeContexts = deleteContext(context, activeContexts);

        if (debug_delete) {
            print(binaryName);
            print((int*) ": selfie_delete context ");
            print(itoa(ID, string_buffer, 10, 0, 0));
            println();
        }
    } else if (debug_delete) {
        print(binaryName);
        print((int*) ": selfie_delete context ");
        print(itoa(ID, string_buffer, 10, 0, 0));
        print((int*) " not found");
        println();
    }
}

void implementDelete() {
    // this procedure is executed at boot levels higher than zero
    doDelete(*(registers+REG_A0));
}

void hypster_delete(int ID) {
    // this procedure is only executed at boot level zero
    doDelete(ID);
}

void selfie_delete(int ID) {
    if (mipster)
        doDelete(ID);
    else
        hypster_delete(ID);
}

void emitMap() {
    createSymbolTableEntry(LIBRARY_TABLE, (int*) "hypster_map", 0, PROCEDURE, VOID_T, 0, binaryLength);

    emitIFormat(OP_LW, REG_SP, REG_A2, 0); // frame
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

    emitIFormat(OP_LW, REG_SP, REG_A1, 0); // page
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

    emitIFormat(OP_LW, REG_SP, REG_A0, 0); // context ID
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, WORDSIZE);

    emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_MAP);
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

    emitRFormat(OP_SPECIAL, REG_RA, 0, 0, FCT_JR);
}

void doMap(int ID, int page, int frame) {
    int *mapContext;
    int *parentContext;

    mapContext = findContext(ID, activeContexts);

    if (mapContext != (int*) 0) {
        if (getParent(mapContext) != NO_ID) {
            parentContext = findContext(getParent(mapContext), activeContexts);

            if (parentContext != (int*) 0)
                frame = getFrameForPage(getPT(parentContext), frame / PAGESIZE);
            else if (debug_map) {
                print(binaryName);
                print((int*) ": selfie_map parent context ");
                print(itoa(getParent(mapContext), string_buffer, 10, 0, 0));
                print((int*) " of context ");
                print(itoa(ID, string_buffer, 10, 0, 0));
                print((int*) " not found");
                println();
            }
        }

        mapPage(getPT(mapContext), page, frame);

        if (debug_map) {
            print(binaryName);
            print((int*) ": selfie_map page ");
            print(itoa(page, string_buffer, 16, 4, 0));
            print((int*) " to frame ");
            print(itoa(frame, string_buffer, 16, 8, 0));
            print((int*) " for context ");
            print(itoa(ID, string_buffer, 10, 0, 0));
            println();
        }
    } else if (debug_map) {
        print(binaryName);
        print((int*) ": selfie_map context ");
        print(itoa(ID, string_buffer, 10, 0, 0));
        print((int*) " not found");
        println();
    }
}

void implementMap() {
    // this procedure is executed at boot levels higher than zero
    doMap(*(registers+REG_A0), *(registers+REG_A1), *(registers+REG_A2));
}

void hypster_map(int ID, int page, int frame) {
    // this procedure is only executed at boot level zero
    doMap(ID, page, frame);
}

void selfie_map(int ID, int page, int frame) {
    if (mipster)
        doMap(ID, page, frame);
    else
        hypster_map(ID, page, frame);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     E M U L A T O R   ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

int loadPhysicalMemory(int *paddr) {
    return *paddr;
}

void storePhysicalMemory(int *paddr, int data) {
    *paddr = data;
}

int isValidVirtualAddress(int vaddr) {
    if (vaddr >= 0)
        if (vaddr < VIRTUALMEMORYSIZE)
            // memory must be word-addressed for lack of byte-sized data type
            if (vaddr % WORDSIZE == 0)
                return 1;
    
    return 0;
}

int getFrameForPage(int *table, int page) {
    return *(table + page);
}

int isVirtualAddressMapped(int *table, int vaddr) {
    // assert: isValidVirtualAddress(vaddr) == 1
    
    if (getFrameForPage(table, vaddr / PAGESIZE) != 0)
        return 1;
    else
        return 0;
}

int* tlb(int *table, int vaddr) {
    int page;
    int frame;
    int paddr;

    // assert: isValidVirtualAddress(vaddr) == 1
    // assert: isVirtualAddressMapped(table, vaddr) == 1

    page = vaddr / PAGESIZE;

    frame = getFrameForPage(table, page);

    paddr = (vaddr - page * PAGESIZE) + frame;

    if (debug_tlb) {
        print(binaryName);
        print((int*) ": tlb access:");
        println();
        print((int*) " vaddr: ");
        print(itoa(vaddr, string_buffer, 2, 32, 0));
        println();
        print((int*) " page:  ");
        print(itoa(page * PAGESIZE, string_buffer, 2, 32, 0));
        println();
        print((int*) " frame: ");
        print(itoa(frame, string_buffer, 2, 32, 0));
        println();
        print((int*) " paddr: ");
        print(itoa(paddr, string_buffer, 2, 32, 0));
        println();
    }

    return (int*) paddr;
}

int loadVirtualMemory(int *table, int vaddr) {
    // assert: isValidVirtualAddress(vaddr) == 1
    // assert: isVirtualAddressMapped(table, vaddr) == 1

    return loadPhysicalMemory(tlb(table, vaddr));
}

void storeVirtualMemory(int *table, int vaddr, int data) {
    // assert: isValidVirtualAddress(vaddr) == 1
    // assert: isVirtualAddressMapped(table, vaddr) == 1

    storePhysicalMemory(tlb(table, vaddr), data);
}

void mapAndStoreVirtualMemory(int *table, int vaddr, int data) {
    // assert: isValidVirtualAddress(vaddr) == 1

    if (isVirtualAddressMapped(table, vaddr) == 0)
        mapPage(table, vaddr / PAGESIZE, palloc());
    
    storeVirtualMemory(table, vaddr, data);
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

void fct_syscall() {
    if (debug) {
        printFunction(function);
        println();
    }

    if (interpret) {
        pc = pc + WORDSIZE;

        if (*(registers+REG_V0) == SYSCALL_EXIT)
            implementExit();
        else if (*(registers+REG_V0) == SYSCALL_READ)
            implementRead();
        else if (*(registers+REG_V0) == SYSCALL_WRITE)
            implementWrite();
        else if (*(registers+REG_V0) == SYSCALL_OPEN)
            implementOpen();
        else if (*(registers+REG_V0) == SYSCALL_MALLOC)
            implementMalloc();
        else if (*(registers+REG_V0) == SYSCALL_ID)
            implementID();
        else if (*(registers+REG_V0) == SYSCALL_CREATE)
            implementCreate();
        else if (*(registers+REG_V0) == SYSCALL_SWITCH)
            implementSwitch();
        else if (*(registers+REG_V0) == SYSCALL_STATUS)
            implementStatus();
        else if (*(registers+REG_V0) == SYSCALL_DELETE)
            implementDelete();
        else if (*(registers+REG_V0) == SYSCALL_MAP)
            implementMap();
        else {
            pc = pc - WORDSIZE;

            throwException(EXCEPTION_UNKNOWNSYSCALL, 0);
        }
    }
}

void fct_nop() {
    if (debug) {
        printFunction(function);
        println();
    }

    if (interpret)
        pc = pc + WORDSIZE;
}

void op_jal() {
    if (debug) {
        printOpcode(opcode);
        print((int*) " ");
        print(itoa(instr_index, string_buffer, 16, 0, 0));
        print((int*) "[");
        print(itoa(instr_index * WORDSIZE, string_buffer, 16, 0, 0));
        print((int*) "]");
        if (interpret) {
            print((int*) ": ");
            printRegister(REG_RA);
            print((int*) "=");
            print(itoa(*(registers+REG_RA), string_buffer, 16, 0, 0));
        }
    }

    if (interpret) {
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
            print(itoa(*(registers+REG_RA), string_buffer, 16, 0, 0));
            print((int*) ",$pc=");
            print(itoa(pc, string_buffer, 16, 0, 0));
        }
        println();
    }
}

void op_j() {
    if (debug) {
        printOpcode(opcode);
        print((int*) " ");
        print(itoa(instr_index, string_buffer, 16, 0, 0));
        print((int*) "[");
        print(itoa(instr_index * WORDSIZE, string_buffer, 16, 0, 0));
        print((int*) "]");
    }

    if (interpret) {
        pc = instr_index * WORDSIZE;

        // TODO: execute delay slot
    }

    if (debug) {
        if (interpret) {
            print((int*) ": -> $pc=");
            print(itoa(pc, string_buffer, 16, 0, 0));
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
        print(itoa(signExtend(immediate), string_buffer, 10, 0, 0));
        print((int*) "[");
        print(itoa(pc + WORDSIZE + signExtend(immediate) * WORDSIZE, string_buffer, 16, 0, 0));
        print((int*) "]");
        if (interpret) {
            print((int*) ": ");
            printRegister(rs);
            print((int*) "=");
            print(itoa(*(registers+rs), string_buffer, 10, 0, 0));
            print((int*) ",");
            printRegister(rt);
            print((int*) "=");
            print(itoa(*(registers+rt), string_buffer, 10, 0, 0));
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
            print(itoa(pc, string_buffer, 16, 0, 0));
        }
        println();
    }
}

void op_bne() {
    if (debug) {
        printOpcode(opcode);
        print((int*) " ");
        printRegister(rs);
        print((int*) ",");
        printRegister(rt);
        print((int*) ",");
        print(itoa(signExtend(immediate), string_buffer, 10, 0, 0));
        print((int*) "[");
        print(itoa(pc + WORDSIZE + signExtend(immediate) * WORDSIZE, string_buffer, 16, 0, 0));
        print((int*) "]");
        if (interpret) {
            print((int*) ": ");
            printRegister(rs);
            print((int*) "=");
            print(itoa(*(registers+rs), string_buffer, 10, 0, 0));
            print((int*) ",");
            printRegister(rt);
            print((int*) "=");
            print(itoa(*(registers+rt), string_buffer, 10, 0, 0));
        }
    }

    if (interpret) {
        pc = pc + WORDSIZE;

        if (*(registers+rs) != *(registers+rt)) {
            pc = pc + signExtend(immediate) * WORDSIZE;

            // TODO: execute delay slot
        }
    }

    if (debug) {
        if (interpret) {
            print((int*) " -> $pc=");
            print(itoa(pc, string_buffer, 16, 0, 0));
        }
        println();
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
        print(itoa(signExtend(immediate), string_buffer, 10, 0, 0));
        if (interpret) {
            print((int*) ": ");
            printRegister(rt);
            print((int*) "=");
            print(itoa(*(registers+rt), string_buffer, 10, 0, 0));
            print((int*) ",");
            printRegister(rs);
            print((int*) "=");
            print(itoa(*(registers+rs), string_buffer, 10, 0, 0));
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
            print(itoa(*(registers+rt), string_buffer, 10, 0, 0));
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
            print(itoa(*(registers+rs), string_buffer, 16, 0, 0));
        }
    }

    if (interpret)
        pc = *(registers+rs);

    if (debug) {
        if (interpret) {
            print((int*) " -> $pc=");
            print(itoa(pc, string_buffer, 16, 0, 0));
        }
        println();
    }
}

void fct_mfhi() {
    if (debug) {
        printFunction(function);
        print((int*) " ");
        printRegister(rd);
        if (interpret) {
            print((int*) ": ");
            printRegister(rd);
            print((int*) "=");
            print(itoa(*(registers+rd), string_buffer, 10, 0, 0));
            print((int*) ",$hi=");
            print(itoa(reg_hi, string_buffer, 10, 0, 0));
        }
    }

    if (interpret) {
        *(registers+rd) = reg_hi;

        pc = pc + WORDSIZE;
    }

    if (debug) {
        if (interpret) {
            print((int*) " -> ");
            printRegister(rd);
            print((int*) "=");
            print(itoa(*(registers+rd), string_buffer, 10, 0, 0));
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
            print(itoa(*(registers+rd), string_buffer, 10, 0, 0));
            print((int*) ",$lo=");
            print(itoa(reg_lo, string_buffer, 10, 0, 0));
        }
    }

    if (interpret) {
        *(registers+rd) = reg_lo;

        pc = pc + WORDSIZE;
    }

    if (debug) {
        if (interpret) {
            print((int*) " -> ");
            printRegister(rd);
            print((int*) "=");
            print(itoa(*(registers+rd), string_buffer, 10, 0, 0));
        }
        println();
    }
}

void fct_multu() {
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
            print(itoa(*(registers+rs), string_buffer, 10, 0, 0));
            print((int*) ",");
            printRegister(rt);
            print((int*) "=");
            print(itoa(*(registers+rt), string_buffer, 10, 0, 0));
            print((int*) ",$lo=");
            print(itoa(reg_lo, string_buffer, 10, 0, 0));
        }
    }

    if (interpret) {
        // TODO: 64-bit resolution currently not supported
        reg_lo = *(registers+rs) * *(registers+rt);

        pc = pc + WORDSIZE;
    }

    if (debug) {
        if (interpret) {
            print((int*) " -> $lo=");
            print(itoa(reg_lo, string_buffer, 10, 0, 0));
        }
        println();
    }
}

void fct_divu() {
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
            print(itoa(*(registers+rs), string_buffer, 10, 0, 0));
            print((int*) ",");
            printRegister(rt);
            print((int*) "=");
            print(itoa(*(registers+rt), string_buffer, 10, 0, 0));
            print((int*) ",$lo=");
            print(itoa(reg_lo, string_buffer, 10, 0, 0));
            print((int*) ",$hi=");
            print(itoa(reg_hi, string_buffer, 10, 0, 0));
        }
    }

    if (interpret) {
        reg_lo = *(registers+rs) / *(registers+rt);
        reg_hi = *(registers+rs) % *(registers+rt);

        pc = pc + WORDSIZE;
    }

    if (debug) {
        if (interpret) {
            print((int*) " -> $lo=");
            print(itoa(reg_lo, string_buffer, 10, 0, 0));
            print((int*) ",$hi=");
            print(itoa(reg_hi, string_buffer, 10, 0, 0));
        }
        println();
    }
}

void fct_addu() {
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
            print(itoa(*(registers+rd), string_buffer, 10, 0, 0));
            print((int*) ",");
            printRegister(rs);
            print((int*) "=");
            print(itoa(*(registers+rs), string_buffer, 10, 0, 0));
            print((int*) ",");
            printRegister(rt);
            print((int*) "=");
            print(itoa(*(registers+rt), string_buffer, 10, 0, 0));
        }
    }

    if (interpret) {
        *(registers+rd) = *(registers+rs) + *(registers+rt);

        pc = pc + WORDSIZE;
    }

    if (debug) {
        if (interpret) {
            print((int*) " -> ");
            printRegister(rd);
            print((int*) "=");
            print(itoa(*(registers+rd), string_buffer, 10, 0, 0));
        }
        println();
    }
}

void fct_subu() {
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
            print(itoa(*(registers+rd), string_buffer, 10, 0, 0));
            print((int*) ",");
            printRegister(rs);
            print((int*) "=");
            print(itoa(*(registers+rs), string_buffer, 10, 0, 0));
            print((int*) ",");
            printRegister(rt);
            print((int*) "=");
            print(itoa(*(registers+rt), string_buffer, 10, 0, 0));
        }
    }

    if (interpret) {
        *(registers+rd) = *(registers+rs) - *(registers+rt);

        pc = pc + WORDSIZE;
    }

    if (debug) {
        if (interpret) {
            print((int*) " -> ");
            printRegister(rd);
            print((int*) "=");
            print(itoa(*(registers+rd), string_buffer, 10, 0, 0));
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
        print(itoa(signExtend(immediate), string_buffer, 10, 0, 0));
        print((int*) "(");
        printRegister(rs);
        print((int*) ")");
        if (interpret) {
            print((int*) ": ");
            printRegister(rt);
            print((int*) "=");
            print(itoa(*(registers+rt), string_buffer, 10, 0, 0));
            print((int*) ",");
            printRegister(rs);
            print((int*) "=");
            print(itoa(*(registers+rs), string_buffer, 16, 0, 0));
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
                throwException(EXCEPTION_PAGEFAULT, vaddr);
        } else
            throwException(EXCEPTION_ADDRESSERROR, vaddr);
    }

    if (debug) {
        if (interpret) {
            print((int*) " -> ");
            printRegister(rt);
            print((int*) "=");
            print(itoa(*(registers+rt), string_buffer, 10, 0, 0));
            print((int*) "=memory[vaddr=");
            print(itoa(vaddr, string_buffer, 16, 8, 0));
            print((int*) "]");
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
            print(itoa(*(registers+rs), string_buffer, 10, 0, 0));
            print((int*) ",");
            printRegister(rt);
            print((int*) "=");
            print(itoa(*(registers+rt), string_buffer, 10, 0, 0));
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
            print(itoa(*(registers+rd), string_buffer, 10, 0, 0));
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
        print(itoa(signExtend(immediate), string_buffer, 10, 0, 0));
        print((int*) "(");
        printRegister(rs);
        print((int*) ")");
        if (interpret) {
            print((int*) ": ");
            printRegister(rt);
            print((int*) "=");
            print(itoa(*(registers+rt), string_buffer, 10, 0, 0));
            print((int*) ",");
            printRegister(rs);
            print((int*) "=");
            print(itoa(*(registers+rs), string_buffer, 16, 0, 0));
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
                throwException(EXCEPTION_PAGEFAULT, vaddr);
        } else
            throwException(EXCEPTION_ADDRESSERROR, vaddr);
    }

    if (debug) {
        if (interpret) {
            print((int*) " -> memory[vaddr=");
            print(itoa(vaddr, string_buffer, 16, 8, 0));
            print((int*) "]=");
            print(itoa(*(registers+rt), string_buffer, 10, 0, 0));
            print((int*) "=");
            printRegister(rt);
        }
        println();
    }
}

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void printException(int exception) {
    print((int*) *(EXCEPTIONS + exception));
}

int encodeException(int exception, int parameter) {
    // assert: 0 <= exception < 2^16
    // assert: -2^15 <= parameter < 2^15

    if (parameter < 0)
        // convert from 32-bit to 16-bit two's complement
        parameter = parameter + twoToThePowerOf(16);

    return leftShift(exception, 16) + parameter;
}

int decodeExceptionNumber(int status) {
    return rightShift(status, 16);
}

int decodeExceptionParameter(int status) {
    return signExtend(rightShift(leftShift(status, 16), 16));
}

void printStatus(int status) {
    int exception;
    int parameter;

    exception = decodeExceptionNumber(status);
    parameter = decodeExceptionParameter(status);

    printException(exception);
    print((int*) " with parameter ");
    print(itoa(parameter, string_buffer, 16, 4, 0));
}

void throwException(int exception, int parameter) {
    if (exception == EXCEPTION_PAGEFAULT)
        status = encodeException(exception, parameter / PAGESIZE);
    else
        status = encodeException(exception, parameter);

    trap = 1;

    if (debug_exception) {
        print(binaryName);
        print((int*) ": context ");
        print(itoa(getID(currentContext), string_buffer, 10, 0, 0));
        print((int*) " ");
        printStatus(status);
        if (exception == EXCEPTION_PAGEFAULT) {
            print((int*) " [virtual address=");
            print(itoa(parameter, string_buffer, 16, 8, 0));
            print((int*) "]");
        }
        println();
    }
}

void fetch() {
    // assert: isValidVirtualAddress(pc) == 1
    // assert: isVirtualAddressMapped(pt, pc) == 1

    ir = loadVirtualMemory(pt, pc);
}

void execute() {
    if (debug)
        if (sourceLineNumber != (int*) 0) {
            print(binaryName);
            print((int*) ": ");
        }

    if (interpret)
        if (debug)
            print((int*) "$pc=");

    if (debug) {
        print(itoa(pc, string_buffer, 16, 8, 0));
        if (sourceLineNumber != (int*) 0) {
            print((int*) "(~");
            print(itoa(*(sourceLineNumber + pc / WORDSIZE), string_buffer, 10, 0, 0));
            print((int*) ")");
        }
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
    else if (opcode == OP_BNE)
        op_bne();
    else if (opcode == OP_JAL)
        op_jal();
    else if (opcode == OP_J)
        op_j();
    else
        throwException(EXCEPTION_UNKNOWNINSTRUCTION, 0);

    if (interpret == 0) {
        if (pc == codeLength - WORDSIZE)
            throwException(EXCEPTION_EXIT, 0);
        else
            pc = pc + WORDSIZE;
    }
}

void interrupt() {
    cycles = cycles + 1;

    if (timer > 0)
        if (cycles == timer) {
            cycles = 0;

            if (status == 0)
                // only throw exception if no other is pending
                // TODO: handle multiple pending exceptions
                throwException(EXCEPTION_INTERRUPT, 0);
        }
}

void runUntilException() {
    trap = 0;

    while (trap == 0) {
        fetch();
        decode();
        execute();
        interrupt();
    }

    trap = 0;
}

void runUntilExit() {
    int toID;
    int fromID;
    int *fromContext;
    int savedStatus;
    int exceptionNumber;
    int exceptionParameter;
    int frame;

    toID = initID;

    while (1) {
        fromID = selfie_switch(toID);

        fromContext = findContext(fromID, readyContexts);

        if (fromContext == (int*) 0) {
            // assert: context with fromID must be in activeContexts
            fromContext = findContext(fromID, activeContexts);

            // switch to parent which is in charge of handling exceptions
            toID = getParent(fromContext);
        } else {
            // we are the parent in charge of handling exceptions
            savedStatus = selfie_status();

            exceptionNumber    = decodeExceptionNumber(savedStatus);
            exceptionParameter = decodeExceptionParameter(savedStatus);

            if (exceptionNumber == EXCEPTION_EXIT)
                // TODO: only return if all contexts have exited
                return;
            else if (exceptionNumber == EXCEPTION_PAGEFAULT) {
                frame = palloc();

                // TODO: use this table to unmap and reuse frames
                mapPage(getPT(fromContext), exceptionParameter, frame);

                // page table on microkernel boot level
                selfie_map(fromID, exceptionParameter, frame);
            }
        
            // TODO: scheduler should go here
            toID = fromID;
        }
    }
}

int up_loadString(int *table, int *s, int SP) {
    int bytes;
    int i;

    bytes = roundUp(stringLength(s) + 1, WORDSIZE);

    // allocate space for storing string
    SP = SP - bytes;

    i = 0;

    while (i < bytes) {
        mapAndStoreVirtualMemory(table, SP + i, *s);

        s = s + 1;

        i = i + WORDSIZE;
    }

    return SP;
}

void up_loadArguments(int *table, int argc, int *argv) {
    int SP;
    int vargv;
    int i_argc;
    int i_vargv;

    // arguments are pushed onto stack which starts at highest virtual address
    SP = VIRTUALMEMORYSIZE - WORDSIZE;

    // allocate space for storing stack pointer later
    SP = SP - WORDSIZE;

    // allocate space for storing *argv array
    SP = SP - argc * WORDSIZE;

    // assert: argc > 0
    vargv = SP + WORDSIZE;

    i_vargv = vargv;
    i_argc  = argc;

    while (i_argc > 0) {
        SP = up_loadString(table, (int*) *argv, SP);

        // store pointer to string in virtual *argv
        mapAndStoreVirtualMemory(table, i_vargv, SP);

        argv = argv + 1;

        i_vargv = i_vargv + WORDSIZE;

        i_argc = i_argc - 1;
    }

    // allocate space for one word on the stack
    SP = SP - WORDSIZE;

    // push argc
    mapAndStoreVirtualMemory(table, SP, argc);

    // allocate space for one word on the stack
    SP = SP - WORDSIZE;

    // push virtual argv
    mapAndStoreVirtualMemory(table, SP, vargv);

    // store stack pointer at highest virtual address for binary to retrieve
    mapAndStoreVirtualMemory(table, VIRTUALMEMORYSIZE - WORDSIZE, SP);
}

void up_loadBinary(int *table) {
    int vaddr;

    // binaries start at lowest virtual address
    vaddr = 0;

    while (vaddr < binaryLength) {
        mapAndStoreVirtualMemory(table, vaddr, loadBinary(vaddr));

        vaddr = vaddr + WORDSIZE;
    }
}

int addressWithMaxCounter(int *counters, int max) {
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

int fixedPointRatio(int a, int b) {
    // assert: a >= b
    int r;

    // compute fixed point ratio r with 2 fractional digits
    
    r = 0;
    
    // multiply a/b with 100 but avoid overflow

    if (a <= INT_MAX / 100) {
        if (b != 0)
            r = a * 100 / b;
    } else if (a <= INT_MAX / 10) {
        if (b / 10 != 0)
            r = a * 10 / (b / 10);
    } else {
        if (b / 100 != 0)
            r = a / (b / 100);
    }

    // compute a/b in percent
    // 1000000 = 10000 (for 100.00%) * 100 (for 2 fractional digits of r)

    if (r != 0)
        return 1000000 / r;
    else
        return 0;
}

int printCounters(int total, int *counters, int max) {
    int a;

    a = addressWithMaxCounter(counters, max);

    print(itoa(*(counters + a / WORDSIZE), string_buffer, 10, 0, 0));
    
    print((int*) "(");
    print(itoa(fixedPointRatio(total, *(counters + a / WORDSIZE)), string_buffer, 10, 0, 2));
    print((int*) "%)");
    
    if (*(counters + a / WORDSIZE) != 0) {
        print((int*) "@");
        print(itoa(a, string_buffer, 16, 8, 0));
        if (sourceLineNumber != (int*) 0) {
            print((int*) "(~");
            print(itoa(*(sourceLineNumber + a / WORDSIZE), string_buffer, 10, 0, 0));
            print((int*) ")");
        }
    }

    return a;
}

void printProfile(int *message, int total, int *counters) {
    int a;

    if (total > 0) {
        print(selfieName);
        print(message);
        print(itoa(total, string_buffer, 10, 0, 0));
        print((int*) ",");
        a = printCounters(total, counters, INT_MAX); // max counter
        print((int*) ",");
        a = printCounters(total, counters, *(counters + a / WORDSIZE)); // 2nd max
        print((int*) ",");
        a = printCounters(total, counters, *(counters + a / WORDSIZE)); // 3rd max
        println();
    }
}

void selfie_disassemble(int argc, int *argv) {
    // assert: assemblyName is mapped and not longer than maxFilenameLength

    assemblyFD = open(assemblyName, O_CREAT_WRONLY_TRUNC, S_IRUSR_IWUSR_IRGRP_IROTH);

    if (assemblyFD < 0) {
        print(selfieName);
        print((int*) ": could not create assembly output file ");
        print(assemblyName);
        println();

        exit(-1);
    }

    print(selfieName);
    print((int*) ": writing assembly into output file ");
    print(assemblyName);
    println();

    outputName = assemblyName;
    outputFD   = assemblyFD;

    mipster = 1;
    debug   = 1;
    
    // argc and argv are not needed here
    boot(argc, argv);

    mipster = 0;
    debug   = 0;

    outputName = (int*) 0;
    outputFD   = 1;
}

void selfie_run(int argc, int *argv) {
    print(selfieName);
    print((int*) ": this is selfie's ");
    if (mipster) print((int*) "mipster"); else print((int*) "hypster");
    print((int*) " executing ");
    print(binaryName);
    print((int*) " with ");
    print(itoa(frameMemorySize / 1024 / 1024, string_buffer, 10, 0, 0));
    print((int*) "MB of memory");
    println();

    interpret = 1;

    boot(argc, argv);

    interpret = 0;

    print(selfieName);
    print((int*) ": this is selfie's ");
    if (mipster) print((int*) "mipster"); else print((int*) "hypster");
    print((int*) " terminating ");
    print(binaryName);
    println();

    if (mipster) {
        print(selfieName);
        print((int*) ": profile: total,max(ratio%)@addr(line#),2max(ratio%)@addr(line#),3max(ratio%)@addr(line#)");
        println();
        printProfile((int*) ": calls: ", calls, callsPerAddress);
        printProfile((int*) ": loops: ", loops, loopsPerAddress);
        printProfile((int*) ": loads: ", loads, loadsPerAddress);
        printProfile((int*) ": stores: ", stores, storesPerAddress);
    }
}

// -----------------------------------------------------------------
// ---------------------------- CONTEXTS ---------------------------
// -----------------------------------------------------------------

int createID(int seed) {
    // assert: seed < INT_MAX
    return seed + 1;
}

int* allocateContext(int ID, int parentID) {
    int *context;
    
    if (freeContexts == (int*) 0)
        context = malloc(4 * SIZEOFINTSTAR + 6 * SIZEOFINT);
    else {
        context = freeContexts;

        freeContexts = getNextContext(freeContexts);
    }

    setNextContext(context, (int*) 0);
    setPrevContext(context, (int*) 0);

    setID(context, ID);

    setPC(context, 0);

    // allocate memory for general purpose registers
    // TODO: reuse memory
    setRegs(context, malloc(NUMBEROFREGISTERS * WORDSIZE));

    setRegHi(context, 0);
    setRegLo(context, 0);

    // allocate memory for page table
    // TODO: save and reuse memory for page table
    setPT(context, malloc(VIRTUALMEMORYSIZE / PAGESIZE * WORDSIZE));

    // heap starts where it is safe to start
    setBreak(context, maxBinaryLength);

    setParent(context, parentID);

    return context;
}

int* createContext(int ID, int parentID, int *in) {
    int *context;

    context = allocateContext(ID, parentID);

    setNextContext(context, in);
    
    if (in != (int*) 0)
        setPrevContext(in, context);

    return context;
}

int* findContext(int ID, int *in) {
    int *context;

    context = in;

    while (context != (int*) 0) {
        if (getID(context) == ID)
            return context;

        context = getNextContext(context);
    }

    return (int*) 0;
}

void switchContext(int *from, int *to) {
    // save machine state
    setPC(from, pc);
    setRegHi(from, reg_hi);
    setRegLo(from, reg_lo);
    setBreak(from, brk);

    // restore machine state
    pc        = getPC(to);
    registers = getRegs(to);
    reg_hi    = getRegHi(to);
    reg_lo    = getRegLo(to);
    pt        = getPT(to);
    brk       = getBreak(to);
}

void freeContext(int *context) {
    setNextContext(context, freeContexts);

    freeContexts = context;
}

int* deleteContext(int *context, int *from) {
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

void mapPage(int *table, int page, int frame) {
    // assert: 0 <= page < VIRTUALMEMORYSIZE / PAGESIZE
    *(table + page) = frame;
}

// -----------------------------------------------------------------
// --------------------------- HYPSTER -----------------------------
// -----------------------------------------------------------------

int palloc() {
    // CAUTION: on boot level zero palloc may return frame addresses < 0
    int block;
    int frame;

    // assert: frameMemorySize is equal to or a multiple of MEGABYTE
    // assert: PAGESIZE is a factor of MEGABYTE strictly less than MEGABYTE

    if (freePageFrame == 0) {
        freePageFrame = MEGABYTE;

        if (usedMemory + freePageFrame <= frameMemorySize) {
            block = (int) malloc(freePageFrame);

            usedMemory = usedMemory + freePageFrame;

            // page frames must be page-aligned to work as page table index
            nextPageFrame = roundUp(block, PAGESIZE);

            if (nextPageFrame > block)
                freePageFrame = freePageFrame - PAGESIZE;
        } else {
            print(selfieName);
            print((int*) ": palloc out of physical memory");
            println();

            exit(-1);
        }
    }

    frame = nextPageFrame;

    nextPageFrame = nextPageFrame + PAGESIZE;
    freePageFrame = freePageFrame - PAGESIZE;

    // strictly, touching is only necessary on boot levels higher than zero
    touch((int*) frame, PAGESIZE);

    return frame;
}

void pfree(int frame) {
    // TODO: implement free list of page frames
}

void down_mapPageTable(int *context) {
    int page;

    // assert: context page table is only mapped from beginning up and end down

    page = 0;

    while (getFrameForPage(getPT(context), page) != 0) {
        selfie_map(getID(context), page, getFrameForPage(getPT(context), page));

        page = page + 1;
    }

    page = (VIRTUALMEMORYSIZE - WORDSIZE) / PAGESIZE;

    while (getFrameForPage(getPT(context), page) != 0) {
        selfie_map(getID(context), page, getFrameForPage(getPT(context), page));

        page = page - 1;
    }
}

void boot(int argc, int *argv) {
    // resetting is only necessary for mipster to run
    resetInterpreter();
    resetMicrokernel();

    // create initial context on microkernel boot level
    initID = selfie_create();

    // create duplicate of the initial context on this boot level
    readyContexts = createContext(initID, selfie_ID(), readyContexts);

    initContext = readyContexts;

    up_loadBinary(getPT(initContext));

    up_loadArguments(getPT(initContext), argc, argv);

    // set up page table of initial context
    down_mapPageTable(initContext);

    runUntilExit();
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

int selfie(int argc, int* argv) {
    if (argc < 2)
        return -1;
    else {
        while (argc >= 2) {
            if (stringCompare((int*) *argv, (int*) "-c")) {
                sourceName = (int*) *(argv+1);
                binaryName = sourceName;

                argc = argc - 2;
                argv = argv + 2;

                selfie_compile();
            } else if (stringCompare((int*) *argv, (int*) "-o")) {
                binaryName = (int*) *(argv+1);

                argc = argc - 2;
                argv = argv + 2;

                if (binaryLength > 0)
                    selfie_emit();
                else {                    
                    print(selfieName);
                    print((int*) ": nothing to emit to output file ");
                    print(binaryName);
                    println();
                }
            } else if (stringCompare((int*) *argv, (int*) "-s")) {
                assemblyName = (int*) *(argv+1);

                argc = argc - 2;
                argv = argv + 2;

                if (binaryLength > 0) {
                    initMemory(MEGABYTE);

                    selfie_disassemble(argc, argv);
                } else {
                    print(selfieName);
                    print((int*) ": nothing to disassemble to output file ");
                    print(assemblyName);
                    println();
                }
            } else if (stringCompare((int*) *argv, (int*) "-l")) {
                binaryName = (int*) *(argv+1);

                argc = argc - 2;
                argv = argv + 2;

                selfie_load();
            } else if (stringCompare((int*) *argv, (int*) "-m")) {
                initMemory(atoi((int*) *(argv+1)) * MEGABYTE);

                argc = argc - 1;
                argv = argv + 1;

                // pass binaryName as first argument replacing size
                *argv = (int) binaryName;

                if (binaryLength > 0) {
                    mipster = 1;

                    selfie_run(argc, argv);

                    mipster = 0;
                } else {
                    print(selfieName);
                    print((int*) ": nothing to run");
                    println();

                    exit(-1);
                }

                return 0;
            } else if (stringCompare((int*) *argv, (int*) "-d")) {
                initMemory(atoi((int*) *(argv+1)) * MEGABYTE);

                argc = argc - 1;
                argv = argv + 1;

                // pass binaryName as first argument replacing size
                *argv = (int) binaryName;

                if (binaryLength > 0) {
                    mipster = 1;
                    debug   = 1;

                    selfie_run(argc, argv);

                    mipster = 0;
                    debug   = 0;
                } else {
                    print(selfieName);
                    print((int*) ": nothing to debug");
                    println();

                    exit(-1);
                }

                return 0;
            } else if (stringCompare((int*) *argv, (int*) "-y")) {
                initMemory(atoi((int*) *(argv+1)) * MEGABYTE);

                argc = argc - 1;
                argv = argv + 1;

                // pass binaryName as first argument replacing size
                *argv = (int) binaryName;

                if (binaryLength > 0)
                    selfie_run(argc, argv);
                else {
                    print(selfieName);
                    print((int*) ": nothing to run");
                    println();

                    exit(-1);
                }

                return 0;
            } else
                return -1;
        }
    }

    return 0;
}

int main(int argc, int *argv) {
    initLibrary();

    initScanner();
    
    initRegister();
    initDecoder();
    
    initInterpreter();

    selfieName = (int*) *argv;

    argc = argc - 1;
    argv = argv + 1;

    if (selfie(argc, (int*) argv) != 0) {
        print(selfieName);
        print((int*) ": usage: selfie { -c source | -o binary | -s assembly | -l binary } [ -m size ... | -d size ... | -y size ... ] ");
        println();
    }
}