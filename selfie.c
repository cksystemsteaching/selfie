// Copyright (c) 2015, the Selfie Project authors. All rights reserved.
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
// Selfie is a fully self-referential 4k-line C implementation of:
//
// 1. a self-compiling compiler called cstarc that compiles
//    a tiny but powerful subset of C called C Star (C*) to
//    a tiny but powerful subset of MIPS32 called MIPSter,
// 2. a self-executing emulator called mipster that executes
//    MIPSter code including itself when compiled with cstarc, and
// 3. a tiny C* library called libcstar utilized by cstarc and mipster.
//
// Selfie is kept minimal for simplicity and implemented in a single file.
// There is no linker, assembler, or debugger. However, there is minimal
// operating system support in the form of MIPS32 o32 system calls built
// into the emulator. Selfie is meant to be extended in numerous ways.
//
// C* is a tiny Turing-complete subset of C that includes dereferencing
// (the * operator) but excludes data structures, Boolean expressions, and
// many other features. There are only signed 32-bit integers and pointers,
// and character constants for constructing word-aligned strings manually.
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
// helps exposing the self-referential nature of that challenge.
//
// Selfie is the result of many years of teaching systems engineering.
// The design of the compiler is inspired by the Oberon compiler of
// Professor Niklaus Wirth from ETH Zurich.

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

int  stringLength(int *s);
void reverseString(int *s);
int  stringCompare(int *s, int *t);
int  atoi(int *s);
int* itoa(int n, int *s, int b, int a);
void print(int *s);
void assignString(int *s, int c0, int c1, int c2, int c3, int c4,
    int c5, int c6, int c7, int c8, int c9,
    int c10, int c11, int c12, int c13, int c14,
    int c15, int c16, int c17, int c18, int c19);
int* createString(int c0, int c1, int c2, int c3, int c4,
    int c5, int c6, int c7, int c8, int c9,
    int c10, int c11, int c12, int c13, int c14,
    int c15, int c16, int c17, int c18, int c19);
void printString(int c0, int c1, int c2, int c3, int c4,
    int c5, int c6, int c7, int c8, int c9,
    int c10, int c11, int c12, int c13, int c14,
    int c15, int c16, int c17, int c18, int c19);
void memset(int *a, int size, int v);

void exit(int code);
int* malloc(int size);

// ------------------------ GLOBAL CONSTANTS -----------------------

int *power_of_two_table;

int INT_MAX; // maximum numerical value of an integer
int INT_MIN; // minimum numerical value of an integer

int CHAR_TAB;
int CHAR_LF;
int CHAR_CR;

int *string_buffer;

// ------------------------- INITIALIZATION ------------------------

void initLibrary() {
    int i;

    power_of_two_table = malloc(31*4);

    *power_of_two_table = 1; // 2^0

    i = 1;

    while (i < 31) {
        *(power_of_two_table + i) = *(power_of_two_table + (i - 1)) * 2;

        i = i + 1;
    }

    // computing INT_MAX and INT_MIN without overflows
    INT_MAX = (twoToThePowerOf(30) - 1) * 2 + 1;
    INT_MIN = -INT_MAX - 1;

    CHAR_TAB = 9;  // ASCII code 9  = tabulator
    CHAR_LF  = 10; // ASCII code 10 = linefeed
    CHAR_CR  = 13; // ASCII code 13 = carriage return

    string_buffer = malloc(33*4);
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

int findNextCharacter();
int isCharacterWhitespace();
int isCharacterLetterOrDigitOrUnderscore();
int isCharacterDigit();
int isCharacterLetter();
int identifierStringMatch(int stringIndex);
int identifierOrKeyword();
int getSymbol();

void syntaxWarn(int errCode);
void syntaxError(int errCode);

// ------------------------ GLOBAL CONSTANTS -----------------------

int SYM_EOF;            // end of file
int SYM_IDENTIFIER;     // identifier
int SYM_INTEGER;        // a number
int SYM_VOID;           // VOID
int SYM_INT;            // INT
int SYM_SEMICOLON;      // ;
int SYM_IF;             // IF
int SYM_ELSE;           // ELSE
int SYM_PLUS;           // +
int SYM_MINUS;          // -
int SYM_ASTERISK;       // *
int SYM_DIV;            // /
int SYM_EQUAL;          // ==
int SYM_ASSIGN;         // =
int SYM_LPARENTHESIS;   // (
int SYM_RPARENTHESIS;   // )
int SYM_LBRACE;         // {
int SYM_RBRACE;         // }
int SYM_WHILE;          // WHILE
int SYM_RETURN;         // RETURN
int SYM_COMMA;          // ,
int SYM_LT;             // <
int SYM_LEQ;            // <=
int SYM_GT;             // >
int SYM_GEQ;            // >=
int SYM_NOTEQ;          // !=
int SYM_MOD;            // %
int SYM_CHARACTER;      // char value

int maxIdentifierLength; // maximum number of characters in an identifier
int maxIntegerLength;    // maximum number of characters in an integer

// Error-Token declaration
int ERR_EOF;
int ERR_UNKNOWN;
int ERR_EXPRESSION;
int ERR_TYPE;
int ERR_IDENTIFIER_OR_LPARENTHESIS;
int ERR_IDENTIFIER;
int ERR_ASSIGN;
int ERR_IDENTIFIER_OR_ASSIGN;
int ERR_IDENT_OR_CONST_OR_EXP;
int ERR_LBRACE_OR_SEMICOLON;
int ERR_PROCEDURE_OR_VARIABLE;
int ERR_UNDECLARED_VARIABLE;
int ERR_TYPE_MISMATCH;
int ERR_WRONG_RETURNTYPE;
int ERR_MAXCODELENGTH;
int ERR_MAXIDENTIFIERLENGTH;
int ERR_WRAPAROUND;
int ERR_STATEMENT;
int ERR_FILE_NOT_FOUND;
int ERR_ILLEGAL_DEREF;
int ERR_IDENTIFIER_OR_INTEGER;

// strings for better error messages
int *error;
int *warning;
int *errNewline;
int *errLine;
int *errSymbol;
int *stringArray;

// ------------------------ GLOBAL VARIABLES -----------------------

int lineNumber; // Current Line Number for error reporting
int character;   // most recently read character
int symbol;      // most recently recognized symbol

int *identifier; // stores scanned identifier
int *integer;    // stores scanned integer as string

int ivalue; // stores numerical value of scanned integer string

int mayBeINTMINConstant; // support INT_MIN constant

// ------------------------- INITIALIZATION ------------------------

void initScanner () {
    SYM_EOF              = -1;  // end of file
    SYM_IDENTIFIER       = 0;   // identifier
    SYM_INTEGER          = 1;   // a number
    SYM_VOID             = 2;   // VOID
    SYM_INT              = 3;   // INT
    SYM_SEMICOLON        = 4;   // ;
    SYM_IF               = 5;   // IF
    SYM_ELSE             = 6;   // ELSE
    SYM_PLUS             = 7;   // +
    SYM_MINUS            = 8;   // -
    SYM_ASTERISK         = 9;   // *
    SYM_DIV              = 10;  // /
    SYM_EQUAL            = 11;  // ==
    SYM_ASSIGN           = 12;  // =
    SYM_LPARENTHESIS     = 13;  // (
    SYM_RPARENTHESIS     = 14;  // )
    SYM_LBRACE           = 15;  // {
    SYM_RBRACE           = 16;  // }
    SYM_WHILE            = 17;  // WHILE
    SYM_RETURN           = 18;  // RETURN
    SYM_COMMA            = 19;  // ,
    SYM_LT               = 20;  // <
    SYM_LEQ              = 21;  // <=
    SYM_GT               = 22;  // >
    SYM_GEQ              = 23;  // >=
    SYM_NOTEQ            = 24;  // !=
    SYM_MOD              = 25;  // %
    SYM_CHARACTER        = 26;  // character value

    maxIdentifierLength = 64;
    maxIntegerLength    = 10;

    ERR_EOF                        = 40;    //keep this b/c -1 is no valid array index
    ERR_UNKNOWN                    = 41;
    ERR_EXPRESSION                 = 42;
    ERR_TYPE                       = 43;
    ERR_IDENTIFIER_OR_LPARENTHESIS = 44;
    ERR_IDENTIFIER                 = 45;
    ERR_ASSIGN                     = 46;
    ERR_IDENTIFIER_OR_ASSIGN       = 47;
    ERR_IDENT_OR_CONST_OR_EXP      = 48;
    ERR_LBRACE_OR_SEMICOLON        = 49;
    ERR_PROCEDURE_OR_VARIABLE      = 50;
    ERR_UNDECLARED_VARIABLE        = 51;
    ERR_TYPE_MISMATCH              = 52;
    ERR_WRONG_RETURNTYPE           = 53;
    ERR_MAXCODELENGTH              = 54;
    ERR_MAXIDENTIFIERLENGTH        = 55;
    ERR_WRAPAROUND                 = 56;
    ERR_STATEMENT                  = 57;
    ERR_FILE_NOT_FOUND             = 58;
    ERR_ILLEGAL_DEREF              = 59;
    ERR_IDENTIFIER_OR_INTEGER      = 60;

    // ------------ "ERROR: " ------------
    error = createString('E','R','R','O','R',':',' ',0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ "WARNING: " ------------
    warning = createString('W','A','R','N','I','N','G',':',' ',0,0,0,0,0,0,0,0,0,0,0);

    // ------------ "/n" ------------
    errNewline = createString(10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ ", line " ------------
    errLine = createString(',',' ','l','i','n','e',' ',0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ ", current symbol: " ------------
    errSymbol = createString(',',' ','c','u','r','r','e','n','t',' ','s','y','m','b','o','l',':',' ',0,0);

    // -------------------- ERROR TOKENS --------------------

    stringArray = (int*)malloc(4*70);

    // ------------ "unknown" ------------
    *(stringArray + ERR_UNKNOWN) = (int)createString('u','n','k','n','o','w','n',0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ "expression" ------------
    *(stringArray + ERR_EXPRESSION) = (int)createString('e','x','p','r','e','s','s','i','o','n',0,0,0,0,0,0,0,0,0,0);

    // ------------ "while" ------------
    *(stringArray + SYM_WHILE) = (int)createString('w','h','i','l','e',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ "if" ------------
    *(stringArray + SYM_IF) = (int)createString('i','f',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ "return" ------------
    *(stringArray + SYM_RETURN) = (int)createString('r','e','t','u','r','n',0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ "type" ------------
    *(stringArray + ERR_TYPE) = (int)createString('t','y','p','e',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ "(" ------------
    *(stringArray + SYM_LPARENTHESIS) = (int)createString('(',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ ")" ------------
    *(stringArray + SYM_RPARENTHESIS) = (int)createString(')',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ "{" ------------
    *(stringArray + SYM_LBRACE) = (int)createString('{',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ "}" ------------
    *(stringArray + SYM_RBRACE) = (int)createString('}',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ ";" ------------
    *(stringArray + SYM_SEMICOLON) = (int)createString(';',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ "ident or (" ------------
    *(stringArray + ERR_IDENTIFIER_OR_LPARENTHESIS) = (int)createString('i','d','e','n','t',' ','o','r',' ','(',0,0,0,0,0,0,0,0,0,0);

    // ------------ "identifier" ------------
    *(stringArray + ERR_IDENTIFIER) = (int)createString('i','d','e','n','t','i','f','i','e','r',0,0,0,0,0,0,0,0,0,0);

    // ------------ "assign" ------------
    *(stringArray + ERR_ASSIGN) = (int)createString('a','s','s','i','g','n',0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ "ident or assign" ------------
    *(stringArray + ERR_IDENTIFIER_OR_ASSIGN) = (int)createString('i','d','e','n','t',' ','o','r',' ','a','s','s','i','g','n',0,0,0,0,0);

    // ------------ "ident, const or exp" ------------
    *(stringArray + ERR_IDENT_OR_CONST_OR_EXP) = (int)createString('i','d','e','n','t',',',' ','c','o','n','s','t',' ','o','r',' ','e','x','p',0);

    // ------------ "( or ;" ------------
    *(stringArray + ERR_LBRACE_OR_SEMICOLON) = (int)createString('(',' ','o','r',' ',';',0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ "procedure or var"------------
    *(stringArray + ERR_PROCEDURE_OR_VARIABLE) = (int)createString('p','r','o','c','e','d','u','r','e',' ','o','r',' ','v','a','r',0,0,0,0);

    // ------------ "eof" ------------
    *(stringArray + ERR_EOF) = (int)createString('e','o','f',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ "undeclared var"------------
    *(stringArray + ERR_UNDECLARED_VARIABLE) = (int)createString('u','n','d','e','c','l','a','r','e','d',' ','v','a','r',0,0,0,0,0,0);

    // ------------ "type mismatch" ------------
    *(stringArray + ERR_TYPE_MISMATCH) = (int)createString('t','y','p','e',' ','m','i','s','m','a','t','c','h',0,0,0,0,0,0,0);

    // ------------ "wrong return type" ------------
    *(stringArray + ERR_WRONG_RETURNTYPE) = (int)createString('w','r','o','n','g',' ','r','e','t','u','r','n',' ','t','y','p','e',0,0,0);

    // ------------ "statement" ------------
    *(stringArray + ERR_STATEMENT) = (int)createString('s','t','a','t','e','m','e','n','t',0,0,0,0,0,0,0,0,0,0,0);

    // ------------ "wraparound" ------------
    *(stringArray + ERR_WRAPAROUND) = (int)createString('w','r','a','p','a','r','o','u','n','d',0,0,0,0,0,0,0,0,0,0);

    // ------------ "maxcodelength" ------------
    *(stringArray + ERR_MAXCODELENGTH) = (int)createString('m','a','x','c','o','d','e','l','e','n','g','t','h',0,0,0,0,0,0,0);

    // ------------ "maxidentlength" ------------
    *(stringArray + ERR_MAXIDENTIFIERLENGTH) = (int)createString('m','a','x','i','d','e','n','t','l','e','n','g','t','h',0,0,0,0,0,0);

    // ------------ "file not found" ------------
    *(stringArray + ERR_FILE_NOT_FOUND) = (int)createString('f','i','l','e',' ','n','o','t',' ','f','o','u','n','d',0,0,0,0,0,0);

    // ------------ "else" ------------
    *(stringArray + SYM_ELSE) = (int)createString('e','l','s','e',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ "void" ------------
    *(stringArray + SYM_VOID) = (int)createString('v','o','i','d',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    // ------------ "int" ------------
    *(stringArray + SYM_INT) = (int)createString('i','n','t',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    lineNumber = 1;
    character  = getchar();
    symbol     = -1;

    identifier  = 0;
    integer     = 0;

    ivalue = 0;

    mayBeINTMINConstant = 0;
}

// -----------------------------------------------------------------
// ------------------------- SYMBOL TABLE --------------------------
// -----------------------------------------------------------------

void initSymbolTable();

void createSymbolTableEntry(int which_symbol_table, int *ident, int data, int class, int type);
int  *getSymbolTableEntry(int *ident, int *symbol_table);

int  *getNext(int *entry);
int  *getIdentifier(int *entry);
int  getData(int *entry);
int  getClass(int *entry);
int  getType(int *entry);
int  getRegister(int *entry);

void setNext(int *entry, int *next);
void setIdentifier(int *entry, int *identifier);
void setData(int *entry, int data);
void setClass(int *entry, int class);
void setType(int *entry, int type);
void setRegister(int *entry, int reg);

// ------------------------ GLOBAL CONSTANTS -----------------------

// classes
int UNKNOWN;  // 0
int CONSTANT; // 1
int VARIABLE; // 2
int FUNCTION; // 3

// types
int INT_T;     // 1
int INTSTAR_T; // 2
int VOID_T;    // 3

// symbol tables
int GLOBAL_TABLE;
int LOCAL_TABLE;

// ------------------------ GLOBAL VARIABLES -----------------------

// table pointer
int *global_symbol_table;
int *local_symbol_table;

// ------------------------- INITIALIZATION ------------------------

void initSymbolTable() {
    // classes
    UNKNOWN  = 0;
    CONSTANT = 1;
    VARIABLE = 2;
    FUNCTION = 3;

    // types
    INT_T     = 1;
    INTSTAR_T = 2;
    VOID_T    = 3;

    // symbol tables
    GLOBAL_TABLE = 1;
    LOCAL_TABLE  = 2;

    // table pointer
    global_symbol_table = 0;
    local_symbol_table  = 0;
}

// -----------------------------------------------------------------
// ---------------------------- PARSER -----------------------------
// -----------------------------------------------------------------

void initParser();

int isNotRbraceOrEOF();
int isVariableOrProcedure();
int isExpression();
int isPlusOrMinus();
int isStarOrDivOrModulo();

int waitForStatement();
int waitForVariable();
int waitForFactor();

void save_registers();
void restore_registers(int numberOfRegisters);

int* getVariable(int *variable);
int  load_variable(int *variable);
void load_integer();

int  help_call_codegen(int *entry, int *procedure);
void help_procedure_prologue(int localVariables);
void help_procedure_epilogue(int parameters, int functionStart, int functionType);

int  gr_call(int *procedure);
int  gr_factor();
int  gr_term();
int  gr_simpleExpression();
int  gr_expression();
void gr_while();
void gr_if();
void gr_return(int returnType);
void gr_statement();
int  gr_variable();
void gr_procedure(int *procedure, int returnType);
void gr_cstar();

// ------------------------ GLOBAL CONSTANTS -----------------------

int maxCodeLength;

// ------------------------ GLOBAL VARIABLES -----------------------

int allocatedRegisters;       // number of allocated registers
int allocatedGlobalVariables; // number of global variables

int  codeLength;
int  returnBranches;
int *currentFuncName; // holds the name of currently parsed function

// ------------------------- INITIALIZATION ------------------------

void
initParser() {
    // set maximum code length for emitting code
    maxCodeLength = 32000;

    allocatedRegisters       = 0;
    allocatedGlobalVariables = 0;

    codeLength = 0;
    returnBranches = 0;
    currentFuncName = 0;
}

// -----------------------------------------------------------------
// ---------------------- MACHINE CODE LIBRARY ---------------------
// -----------------------------------------------------------------

void emitLeftShiftBy(int b);
void emitMainEntry();

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- REGISTER ---------------------------
// -----------------------------------------------------------------

// ------------------------ GLOBAL CONSTANTS -----------------------

int REG_ZR;
int REG_V0;
int REG_A0;
int REG_A1;
int REG_A2;
int REG_A3;
int REG_RR;
int REG_K1;
int REG_GP;
int REG_SP;
int REG_FP;
int REG_LINK;

// ------------------------- INITIALIZATION ------------------------

void initRegister() {
    REG_ZR   = 0;
    REG_V0   = 2;
    REG_A0   = 4;
    REG_A1   = 5;
    REG_A2   = 6;
    REG_A3   = 7;
    REG_RR   = 26;
    REG_K1   = 27;
    REG_GP   = 28;
    REG_SP   = 29;
    REG_FP   = 30;
    REG_LINK = 31;
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

void decode();
void decodeRFormat();
void decodeIFormat();
void decodeJFormat();

// ------------------------ GLOBAL CONSTANTS -----------------------

int OP_SPECIAL;
int FCT_SYSCALL;
int FCT_MFHI;
int FCT_MFLO;
int FCT_MULTU;
int FCT_DIVU;
int OP_ADDIU;
int FCT_ADDU;
int FCT_SUBU;
int OP_LW;
int OP_SW;
int OP_BEQ;
int OP_BNE;
int FCT_SLT;
int FCT_NOP;
int FCT_JR;
int OP_JAL;
int OP_J;
int FCT_TEQ;

// ------------------------ GLOBAL VARIABLES -----------------------

int opcode;
int rs;
int rt;
int rd;
int immediate;
int function;
int instr_index;

// ------------------------- INITIALIZATION ------------------------

void initDecoder() {
    OP_SPECIAL  = 0;
    FCT_NOP     = 0;
    OP_JAL      = 3;
    OP_J        = 2;
    OP_BEQ      = 4;
    OP_BNE      = 5;
    OP_ADDIU    = 9;
    FCT_JR      = 8;
    FCT_SYSCALL = 12;
    FCT_MFHI    = 16;
    FCT_MFLO    = 18;
    FCT_MULTU   = 25;
    FCT_DIVU    = 27;
    FCT_ADDU    = 33;
    FCT_SUBU    = 35;
    OP_LW       = 35;
    FCT_SLT     = 42;
    OP_SW       = 43;
    FCT_TEQ     = 52;

    opcode      = 0;
    rs          = 0;
    rt          = 0;
    rd          = 0;
    immediate   = 0;
    function    = 0;
    instr_index = 0;
}

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void allocateMachineMemory(int size);

// ------------------------ GLOBAL VARIABLES -----------------------

int *memory; // machine memory

// -----------------------------------------------------------------
// ---------------------------- BINARY -----------------------------
// -----------------------------------------------------------------

void emitInstruction(int instruction);
void emitRFormat(int opcode, int rs, int rt, int rd, int function);
void emitIFormat(int opcode, int rs, int rt, int immediate);
void emitJFormat(int opcode, int instr_index);

void fixup_relative(int fromAddress);
void fixup_absolute(int fromAddress, int toAddress);
void fixlink_absolute(int fromAddress, int toAddress);

void emitBinary();
int  loadBinary(int *filename);

// -----------------------------------------------------------------
// --------------------------- SYSCALLS ----------------------------
// -----------------------------------------------------------------

void initSyscalls();

void emitExit();
void syscall_exit();

void syscall_read();
void emitRead();

void syscall_write();
void emitWrite();

void syscall_open();
void emitOpen();

void syscall_malloc();
void emitMalloc();

void syscall_getchar();
void emitGetchar();

void emitPutchar();

// ------------------------ GLOBAL CONSTANTS -----------------------

int SYSCALL_EXIT;
int SYSCALL_READ;
int SYSCALL_WRITE;
int SYSCALL_OPEN;
int SYSCALL_MALLOC;
int SYSCALL_GETCHAR;

// ------------------------- INITIALIZATION ------------------------

void initSyscalls() {
    SYSCALL_EXIT    = 4001;
    SYSCALL_READ    = 4003;
    SYSCALL_WRITE   = 4004;
    SYSCALL_OPEN    = 4005;
    SYSCALL_MALLOC  = 5001;
    SYSCALL_GETCHAR = 5002;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     E M U L A T O R   ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

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
void op_lui();
void fct_mfhi();
void fct_mflo();
void fct_multu();
void fct_divu();
void fct_addu();
void fct_subu();
void op_lw();
void fct_slt();
void op_sw();
void op_teq();

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void initInterpreter();

void exception_handler(int enumber);

int addressTranslation(int vaddr);

void pre_debug();
void post_debug();

void fetch();
void execute();
void run();

void debug_boot(int memorySize);
int* parse_args(int argc, int *argv, int *cstar_argv);
void up_push(int value);
int  up_malloc(int size);
int  up_copyCString(int *s);
void up_copyArguments(int argc, int *argv);

int main_emulator(int argc, int *argv, int *cstar_argv);

// ------------------------ GLOBAL CONSTANTS -----------------------

int *register_strings; // static strings for register names
int *op_strings;       // static strings for debug_disassemble
int *fct_strings;

int debug_registers;
int debug_syscalls;
int debug_load;
int debug_disassemble;

int EXCEPTION_SIGNAL;
int EXCEPTION_ADDRESSERROR;
int EXCEPTION_UNKNOWNINSTRUCTION;
int EXCEPTION_HEAPOVERFLOW;
int EXCEPTION_UNKNOWNSYSCALL;
int EXCEPTION_UNKNOWNFUNCTION;

// ------------------------ GLOBAL VARIABLES -----------------------

int *registers; // general purpose registers

int pc; // program counter
int ir; // instruction record

int reg_hi; // hi register for multiplication/division
int reg_lo; // lo register for multiplication/division

// ------------------------- INITIALIZATION ------------------------

void initInterpreter() {
    register_strings = (int*)malloc(4*32);
    op_strings       = (int*)malloc(4*64);
    fct_strings      = (int*)malloc(4*64);

    *(register_strings + 0)  = (int)createString('z','e','r','o',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 1)  = (int)createString('a','t',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 2)  = (int)createString('v','0',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 3)  = (int)createString('v','1',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 4)  = (int)createString('a','0',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 5)  = (int)createString('a','1',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 6)  = (int)createString('a','2',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 7)  = (int)createString('a','3',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 8)  = (int)createString('t','0',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 9)  = (int)createString('t','1',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 10) = (int)createString('t','2',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 11) = (int)createString('t','3',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 12) = (int)createString('t','4',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 13) = (int)createString('t','5',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 14) = (int)createString('t','6',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 15) = (int)createString('t','7',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 16) = (int)createString('s','0',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 17) = (int)createString('s','1',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 18) = (int)createString('s','2',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 19) = (int)createString('s','3',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 20) = (int)createString('s','4',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 21) = (int)createString('s','5',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 22) = (int)createString('s','6',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 23) = (int)createString('s','7',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 24) = (int)createString('t','8',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 25) = (int)createString('t','9',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 26) = (int)createString('k','0',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 27) = (int)createString('k','1',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 28) = (int)createString('g','p',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 29) = (int)createString('s','p',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 30) = (int)createString('f','p',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(register_strings + 31) = (int)createString('r','a',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    *(fct_strings + 0) = (int)createString('n','o','p',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(fct_strings + 8) = (int)createString('j','r',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(fct_strings + 12) = (int)createString('s','y','s','c','a','l','l',0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(fct_strings + 16) = (int)createString('m','f','h','i',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(fct_strings + 18) = (int)createString('m','f','l','o',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(fct_strings + 25) = (int)createString('m','u','l','t','u',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(fct_strings + 27) = (int)createString('d','i','v','u',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(fct_strings + 33) = (int)createString('a','d','d','u',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(fct_strings + 35) = (int)createString('s','u','b','u',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(fct_strings + 42) =  (int)createString('s','l','t',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(fct_strings + 52) =  (int)createString('t','e','q',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    *(op_strings + 0) = (int)createString('n','o','p',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(op_strings + 3) = (int)createString('j','a','l',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(op_strings + 2) = (int)createString('j',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(op_strings + 4) = (int)createString('b','e','q',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(op_strings + 5) = (int)createString('b','n','e',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(op_strings + 9) = (int)createString('a','d','d','i','u',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(op_strings + 15) = (int)createString('l','u','i',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(op_strings + 35) = (int)createString('l','w',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
    *(op_strings + 43) =  (int)createString('s','w',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    debug_registers   = 0;
    debug_syscalls    = 0;
    debug_load        = 0;
    debug_disassemble = 0;

    EXCEPTION_SIGNAL             = 1;
    EXCEPTION_ADDRESSERROR       = 2;
    EXCEPTION_UNKNOWNINSTRUCTION = 3;
    EXCEPTION_HEAPOVERFLOW       = 4;
    EXCEPTION_UNKNOWNSYSCALL     = 5;
    EXCEPTION_UNKNOWNFUNCTION    = 6;

    registers = (int*)malloc(32*4);

    pc = 0;
    ir = 0;

    reg_hi = 0;
    reg_lo = 0;
}

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
        // works even if n == INT_MIN
        return ((n + 1) + INT_MAX) / twoToThePowerOf(b) +
            (INT_MAX / twoToThePowerOf(b) + 1);
}

int stringLength(int *s) {
    int i;

    i = 0;

    while (*(s+i) != 0)
        i = i + 1;

    return i;
}

void reverseString(int *s) {
    int tmp;
    int i;
    int j;

    i = 0;
    j = stringLength(s) - 1;

    while (i < j) {
        tmp = *(s+i);
        *(s+i) = *(s+j);
        *(s+j) = tmp;
        i = i + 1;
        j = j - 1;
    }
}

int stringCompare(int* s, int* t) {
    while (1)
        if (*s == 0)
            if (*t == 0)
                return 1;
            else
                return 0;
        else if (*s == *t) {
            s = s + 1;
            t = t + 1;
        } else
            return 0;
}

int atoi(int* s) {
    int n;

    n = 0;

    while (*s != 0) {
        n = n * 10 + *s - '0';
        s = s + 1;
    }

    return n;
}

int* itoa(int n, int *s, int b, int a) {
    // assert: b in {2,4,8,10,16}

    int i;
    int sign;

    i = 0;

    sign = 0;

    if (n == 0) {
        *s = '0';

        i = 1;
    } else if (n < 0) {
        sign = 1;

        if (b == 10) {
            if (n == INT_MIN) {
                *s = '8'; // rightmost decimal digit of 32-bit INT_MIN

                n = -(n / 10);
                i = i + 1;
            } else
                n = -n;
        } else {
            if (n == INT_MIN) {
                *s = '0'; // rightmost non-decimal digit of INT_MIN

                n = (rightShift(INT_MIN, 1) / b) * 2;
                i = i + 1;
            } else
                n = rightShift(leftShift(n, 1), 1);
        }
    }

    while (n != 0) {
        *(s+i) = n % b;

        if (*(s+i) > 9)
            *(s+i) = *(s+i) - 10 + 'A';
        else
            *(s+i) = *(s+i) + '0';

        n = n / b;
        i = i + 1;

        if (i == 1) {
            if (sign) {
                if (b != 10)
                    n = n + (rightShift(INT_MIN, 1) / b) * 2;
            }
        }
    }

    if (b != 10) {
        while (i < a) {
            *(s+i) = '0'; // align with zeros

            i = i + 1;
        }
    } else if (sign) {
        *(s+i) = '-';

        i = i + 1;
    }

    *(s+i) = 0; // null terminated string

    reverseString(s);

    return s;
}

void print(int *s) {
    while (*s != 0) {
        putchar(*s);
        s = s + 1;
    }
}

void assignString(int *s, int c0, int c1, int c2, int c3, int c4,
        int c5, int c6, int c7, int c8, int c9,
        int c10, int c11, int c12, int c13, int c14,
        int c15, int c16, int c17, int c18, int c19) {

    *(s+0) = c0; *(s+1) = c1; *(s+2) = c2; *(s+3) = c3; *(s+4) = c4;
    *(s+5) = c5; *(s+6) = c6; *(s+7) = c7; *(s+8) = c8; *(s+9) = c9;
    *(s+10) = c10; *(s+11) = c11; *(s+12) = c12; *(s+13) = c13; *(s+14) = c14;
    *(s+15) = c15; *(s+16) = c16; *(s+17) = c17; *(s+18) = c18; *(s+19) = c19;
    *(s+20) = 0;
}

int* createString(int c0, int c1, int c2, int c3, int c4,
        int c5, int c6, int c7, int c8, int c9,
        int c10, int c11, int c12, int c13, int c14,
        int c15, int c16, int c17, int c18, int c19) {
    int* s;

    s = (int*)malloc(21*4);
    assignString(s, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9,
                 c10, c11, c12, c13, c14, c15, c16, c17, c18, c19);
    return s;
}

void printString(int c0, int c1, int c2, int c3, int c4,
        int c5, int c6, int c7, int c8, int c9,
        int c10, int c11, int c12, int c13, int c14,
        int c15, int c16, int c17, int c18, int c19) {

    assignString(string_buffer, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9,
                 c10, c11, c12, c13, c14, c15, c16, c17, c18, c19);

    print(string_buffer);
}

void memset(int *a, int size, int v) {
    while (size > 0) {
        size = size - 1;
        *(a+size) = v;
    }
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     C O M P I L E R   ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- SCANNER ----------------------------
// -----------------------------------------------------------------

int findNextCharacter() {
    int inComment;

    inComment = 0;

    while (1) {
        if (inComment) {
            character = getchar();

            if (character == CHAR_LF)
                inComment = 0;
            else if (character == CHAR_CR)
                inComment = 0;
            else if (character == SYM_EOF)
                return character;

        } else if (isCharacterWhitespace()) {
            if (character == CHAR_LF)
                lineNumber = lineNumber + 1;
            else if (character == CHAR_CR)
                lineNumber = lineNumber + 1;

            character = getchar();

        } else if (character == '#') {
            character = getchar();
            inComment = 1;

        } else if (character == '/') {
            character = getchar();
            if (character == '/')
                inComment = 1;
            else {
                symbol = SYM_DIV;
                return character;
            }

        } else
            return character;
    }
}

int isCharacterWhitespace() {
    if (character == ' ')
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

int isCharacterLetterOrDigitOrUnderscore() {
    if (isCharacterLetter())
        return 1;
    else if(isCharacterDigit())
        return 1;
    else if(character == '_')
        return 1;
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

int identifierStringMatch(int stringIndex) {
    return stringCompare(identifier, (int*)(*(stringArray + stringIndex)));
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

    if (findNextCharacter() == SYM_EOF)
        return SYM_EOF;
    else if (symbol == SYM_DIV)
        // check here because / was recognized instead of //
        return SYM_DIV;

    if (isCharacterLetter()) {
        identifier = (int*)malloc((maxIdentifierLength+1) * 4);
        i = 0;

        while (isCharacterLetterOrDigitOrUnderscore()) {
            if (i+1 > maxIdentifierLength) {
                syntaxError(ERR_MAXIDENTIFIERLENGTH); // identifier too long
                exit(-1);
            }
            *(identifier+i) = character;
            i = i + 1;
            character = getchar();
        }

        *(identifier+i) = 0; // null terminated string
        symbol = identifierOrKeyword();

    } else if (isCharacterDigit()) {
        integer = (int*)malloc((maxIntegerLength+1) * 4);
        i = 0;

        while (isCharacterDigit()) {
            if (i+1 > maxIntegerLength) {
                syntaxError(ERR_WRAPAROUND); // integer too long
                exit(-1);
            }
            *(integer+i) = character;
            i = i + 1;
            character = getchar();
        }

        *(integer+i) = 0; // null terminated string
        ivalue = atoi(integer);

        if (ivalue < 0) {
            if (ivalue == INT_MIN) {
                if (mayBeINTMINConstant == 0) {
                    syntaxError(ERR_WRAPAROUND);
                    exit(-1);
                }
            } else {
                syntaxError(ERR_WRAPAROUND);
                exit(-1);
            }
        }

        symbol = SYM_INTEGER;

    } else if (character == ';') {
        character = getchar();
        symbol = SYM_SEMICOLON;

    } else if (character == '+') {
        character = getchar();
        symbol = SYM_PLUS;

    } else if (character == '-') {
        character = getchar();
        symbol = SYM_MINUS;

    } else if (character == '*') {
        character = getchar();
        symbol = SYM_ASTERISK;

    } else if (character == '=') {
        character = getchar();
        if (character == '=') {
            character = getchar();
            symbol = SYM_EQUAL;
        } else
            symbol = SYM_ASSIGN;

    } else if (character == '(') {
        character = getchar();
        symbol = SYM_LPARENTHESIS;

    } else if (character == ')') {
        character = getchar();
        symbol = SYM_RPARENTHESIS;

    } else if (character == '{') {
        character = getchar();
        symbol = SYM_LBRACE;

    } else if (character == '}') {
        character = getchar();
        symbol = SYM_RBRACE;

    } else if (character == ',') {
        character = getchar();
        symbol = SYM_COMMA;

    } else if (character == '<') {
        character = getchar();
        if (character == '=') {
            character = getchar();
            symbol = SYM_LEQ;
        } else
            symbol = SYM_LT;

    } else if (character == '>') {
        character = getchar();
        if (character == '=') {
            character = getchar();
            symbol = SYM_GEQ;
        } else
            symbol = SYM_GT;

    } else if (character == '!') {
        character = getchar();
        if (character == '=') {
            character = getchar();
            symbol = SYM_NOTEQ;
        } else
            syntaxError(ERR_UNKNOWN);

    } else if (character == '%') {
        character = getchar();
        symbol = SYM_MOD;

    } else if (character == 39) {     // '
        character = getchar();
        ivalue    = character;        // any ascii character
        character = getchar();
        if (character == 39) {        // '
            character = getchar();
            symbol    = SYM_CHARACTER;
        } else
            syntaxError(ERR_UNKNOWN);
    } else {
        syntaxError(ERR_UNKNOWN);
        exit(-1); // unknown character
    }

    return symbol;
}

void syntaxWarn(int errCode) {
    int *numberBuffer;

    numberBuffer = (int*)malloc(4*10);

    print(warning);

    print((int*)(*(stringArray+errCode)));

    print(errLine);
    print(itoa(lineNumber, numberBuffer, 10, 0));

    print(errSymbol);
    print(itoa(symbol, numberBuffer, 10, 0));

    print(errNewline);
}

void syntaxError(int errCode) {
    int *numberBuffer;

    numberBuffer = (int*)malloc(4*10);

    print(error);

    print((int*)(*(stringArray+errCode)));

    print(errLine);
    print(itoa(lineNumber, numberBuffer, 10, 0));

    print(errSymbol);
    print(itoa(symbol, numberBuffer, 10, 0));

    print(errNewline);

    getSymbol();
}

// -----------------------------------------------------------------
// ------------------------- SYMBOL TABLE --------------------------
// -----------------------------------------------------------------

void createSymbolTableEntry(int which_symbol_table, int *ident, int data, int class, int type) {
    int* newEntry;

    // symbolTable:
    // +----+------------+
    // |  0 | ptr to next|
    // |  1 | identifier |
    // |  2 | data       |  VARIABLE: offset/FUNCTION: code address
    // |  3 | class      |
    // |  4 | type       |
    // |  5 | register   |
    // +----+------------+

    newEntry = (int*)malloc(6 * 4);

    // store pointer to identifier
    // cast only works if size of int and int* is equivalent
    setIdentifier(newEntry, ident);
    setData(newEntry, data);
    setClass(newEntry, class);
    setType(newEntry, type);

    // create entry at head of symbol table
    // cast only works if size of int and int* is equivalent
    if (which_symbol_table == GLOBAL_TABLE) {
        setRegister(newEntry, REG_GP);
        setNext(newEntry, global_symbol_table);
        global_symbol_table = newEntry;
    } else {
        setRegister(newEntry, REG_FP);
        setNext(newEntry, local_symbol_table);
        local_symbol_table = newEntry;
    }
}

int* getSymbolTableEntry(int *ident, int *symbol_table) {
    while ((int)symbol_table != 0) {
        if (stringCompare(ident, getIdentifier(symbol_table)))
            return symbol_table;
        else
            // keep looking
            // cast only works if size of int and int* is equivalent
            symbol_table = getNext(symbol_table);
    }

    return 0;
}

int* getNext(int *entry) {
    return (int*) *entry;
}

int* getIdentifier(int *entry) {
    return (int*) *(entry + 1);
}

int getData(int *entry) {
    return *(entry + 2);
}

int getClass(int *entry) {
    return *(entry + 3);
}

int getType(int *entry) {
    return *(entry + 4);
}

int getRegister(int *entry) {
    return *(entry + 5);
}

void setNext(int *entry, int *next) {
    *entry = (int) next;
}

void setIdentifier(int *entry, int *identifier) {
    *(entry + 1) = (int) identifier;
}

void setData(int *entry, int data) {
    *(entry + 2) = data;
}

void setClass(int *entry, int class) {
    *(entry + 3) = class;
}

void setType(int *entry, int type) {
    *(entry + 4) = type;
}

void setRegister(int *entry, int reg) {
    *(entry + 5) = reg;
}

// -----------------------------------------------------------------
// ---------------------------- PARSER -----------------------------
// -----------------------------------------------------------------

int isNotRbraceOrEOF() {
    if (symbol == SYM_EOF)
        return 0;
    else if(symbol == SYM_RBRACE)
        return 0;
    else
        return 1;
}

int isVariableOrProcedure() {
    if (symbol == SYM_INT)
        return 1;
    else if (symbol == SYM_VOID)
        return 1;
    else
        return 0;
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
    else if (symbol == SYM_CHARACTER)
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

int waitForStatement() {
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

int waitForVariable() {
    if (symbol == SYM_INT)
        return 0;
    else if (symbol == SYM_EOF)
        return 0;
    else
        return 1;
}

int waitForFactor() {
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
    else if (symbol == SYM_EOF)
        return 0;
    else
        return 1;
}

void save_registers() {
    while (allocatedRegisters > 0) {
        emitIFormat(OP_ADDIU, REG_SP, REG_SP, -4);
        emitIFormat(OP_SW, REG_SP, allocatedRegisters, 0);

        allocatedRegisters = allocatedRegisters - 1;
    }
}

void restore_registers(int numberOfRegisters) {

    while (allocatedRegisters < numberOfRegisters) {
        allocatedRegisters = allocatedRegisters + 1;

        emitIFormat(OP_LW, REG_SP, allocatedRegisters, 0);
        emitIFormat(OP_ADDIU, REG_SP, REG_SP, 4);
    }
}

int* getVariable(int *variable) {
    int* entry;

    entry = getSymbolTableEntry(variable, local_symbol_table);

    if ((int)entry == 0) {
        entry = getSymbolTableEntry(variable, global_symbol_table);

        if ((int)entry == 0)
            syntaxError(ERR_UNDECLARED_VARIABLE);
    }

    return entry;
}

int load_variable(int *variable) {
    int *entry;

    entry = getVariable(variable);

    allocatedRegisters = allocatedRegisters + 1;

    emitIFormat(OP_LW, getRegister(entry), allocatedRegisters, getData(entry));

    return getType(entry);
}

void load_integer() {
    // assert: ivalue >= 0 or ivalue == INT_MIN

    allocatedRegisters = allocatedRegisters + 1;

    if (ivalue >= 0) {
        mayBeINTMINConstant = 0;

        if (ivalue < twoToThePowerOf(15))
            // ADDIU can only load numbers < 2^15 without sign extension
            emitIFormat(OP_ADDIU, REG_ZR, allocatedRegisters, ivalue);
        else if (ivalue < twoToThePowerOf(28)) {
            // load 14 msbs of a 28-bit number first
            emitIFormat(OP_ADDIU, REG_ZR, allocatedRegisters, rightShift(ivalue, 14));

            // shift left by 14 bits
            emitLeftShiftBy(14);

            // and finally add 14 lsbs
            emitIFormat(OP_ADDIU, allocatedRegisters, allocatedRegisters, rightShift(leftShift(ivalue, 18), 18));
        } else {
            // load 14 msbs of a 31-bit number first
            emitIFormat(OP_ADDIU, REG_ZR, allocatedRegisters, rightShift(ivalue, 17));

            emitLeftShiftBy(14);

            // then add the next 14 msbs
            emitIFormat(OP_ADDIU, allocatedRegisters, allocatedRegisters, rightShift(leftShift(ivalue, 15), 18));

            emitLeftShiftBy(3);

            // and finally add the remaining 3 lsbs
            emitIFormat(OP_ADDIU, allocatedRegisters, allocatedRegisters, rightShift(leftShift(ivalue, 29), 29));
        }
    } else {
        // load largest positive 16-bit number with a single bit set: 2^14
        emitIFormat(OP_ADDIU, REG_ZR, allocatedRegisters, twoToThePowerOf(14));

        // and then multiply 2^14 by 2^14*2^3 to get to 2^31 == INT_MIN
        emitLeftShiftBy(14);
        emitLeftShiftBy(3);
    }

    getSymbol();
}

int help_call_codegen(int *entry, int *procedure) {
    int type;

    type = UNKNOWN;

    if ((int)entry == 0) {
        // CASE 1: function call, no definition, no declaration.
        createSymbolTableEntry(GLOBAL_TABLE, procedure, codeLength, FUNCTION, INT_T);
        emitJFormat(OP_JAL, 0);
        type = INT_T; //assume default return type 'int'

    } else {
        type = getType(entry);

        if (getData(entry) == 0) {
            // CASE 2: function call, no definition, but declared.
            setData(entry, codeLength);
            emitJFormat(OP_JAL, 0);
        } else if (getOpcode(*(memory + getData(entry))) == OP_JAL) {
            // CASE 3: function call, no declaration
            emitJFormat(OP_JAL, getData(entry));
            setData(entry, codeLength - 2);
        } else
            // CASE 4: function defined, use the address
            emitJFormat(OP_JAL, getData(entry));
    }

    return type;
}

void help_procedure_prologue(int localVariables) {
    // save return address
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, -4);
    emitIFormat(OP_SW, REG_SP, REG_LINK, 0);

    // save caller's frame
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, -4);
    emitIFormat(OP_SW, REG_SP, REG_FP, 0);

    // allocate callee's frame
    emitIFormat(OP_ADDIU, REG_SP, REG_FP, 0);

    // allocate callee's local variables
    if (localVariables != 0) {
        emitIFormat(OP_ADDIU, REG_SP, REG_SP, localVariables * (-4));
    }
}

void help_procedure_epilogue(int parameters, int functionStart, int functionType) {
    // deallocate callee's frame and local variables
    emitIFormat(OP_ADDIU, REG_FP, REG_SP, 0);

    // restore caller's frame
    emitIFormat(OP_LW, REG_SP, REG_FP, 0);
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, 4);

    // restore return address and deallocate parameters
    emitIFormat(OP_LW, REG_SP, REG_LINK, 0);
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, ((parameters+1)*4));

    // return
    emitRFormat(OP_SPECIAL, REG_LINK, 0, 0, FCT_JR);
}

int gr_call(int *procedure) {
    int *entry;
    int numberOfRegisters;
    int type;

    // assert: n = allocatedRegisters

    entry = getSymbolTableEntry(procedure, global_symbol_table);

    numberOfRegisters = allocatedRegisters;

    save_registers();

    // assert: allocatedRegisters == 0

    if (isExpression()) {
        gr_expression();

        // TODO: check if types/number of params is correct.
        // PSH first parameter onto stack
        emitIFormat(OP_ADDIU, REG_SP, REG_SP, -4);
        emitIFormat(OP_SW, REG_SP, allocatedRegisters, 0);
        allocatedRegisters = allocatedRegisters - 1;

        while (symbol == SYM_COMMA) {
            getSymbol();
            gr_expression();

            // PSH more parameters onto stack
            emitIFormat(OP_ADDIU, REG_SP, REG_SP, -4);
            emitIFormat(OP_SW, REG_SP, allocatedRegisters, 0);
            allocatedRegisters = allocatedRegisters - 1;
        }
        if (symbol == SYM_RPARENTHESIS) {
            getSymbol();
            type = help_call_codegen(entry, procedure);
        } else {
            syntaxWarn(SYM_RPARENTHESIS);
            type = INT_T;
        }
    } else if (symbol == SYM_RPARENTHESIS) {
        getSymbol();
        type = help_call_codegen(entry, procedure);
    } else {
        syntaxWarn(ERR_EXPRESSION);
        type = INT_T;
    }

    // assert: allocatedRegisters == 0

    restore_registers(numberOfRegisters);

    // assert: allocatedRegisters == n
    return type;
}

int gr_factor() {
    int cast;
    int type;
    int *variableOrProcedureName;

    // assert: n = allocatedRegisters

    cast = 0; // turn off cast by default

    while (waitForFactor())
        syntaxError(ERR_IDENT_OR_CONST_OR_EXP);

    // optional cast: [ cast ]
    if (symbol == SYM_LPARENTHESIS) {
        getSymbol();

        mayBeINTMINConstant = 0;

        // (int)
        if (symbol == SYM_INT) {
            getSymbol();

            cast = INT_T;

            // (int*)
            if (symbol == SYM_ASTERISK) {
                getSymbol();

                cast = INTSTAR_T;
            }

            if (symbol == SYM_RPARENTHESIS)
                getSymbol();
            else
                syntaxWarn(SYM_RPARENTHESIS);

        // Not a cast: "(" expression ")"
        } else {
            type = gr_expression();

            if (symbol == SYM_RPARENTHESIS)
                getSymbol();
            else
                syntaxWarn(SYM_RPARENTHESIS);

            // assert: allocatedRegisters == n + 1

            return type;
        }
    }

    // dereference?
    if (symbol == SYM_ASTERISK) {
        getSymbol();

        mayBeINTMINConstant = 0;

        // ["*"] identifier
        if (symbol == SYM_IDENTIFIER) {
            type = load_variable(identifier);

            getSymbol();

        // * "(" simpleExpression ")"
        } else if (symbol == SYM_LPARENTHESIS) {
            getSymbol();

            type = gr_expression();

            if (symbol == SYM_RPARENTHESIS)
                getSymbol();
            else
                syntaxWarn(SYM_RPARENTHESIS);
        } else
            syntaxError(ERR_IDENTIFIER_OR_LPARENTHESIS);

        // dereference
        emitIFormat(OP_LW, allocatedRegisters, allocatedRegisters, 0);

        if (cast == 0) {
            if (type != INTSTAR_T)
                syntaxWarn(ERR_ILLEGAL_DEREF);

            type = INT_T;
        }

    // identifier?
    } else if (symbol == SYM_IDENTIFIER) {
        variableOrProcedureName = identifier;

        getSymbol();

        mayBeINTMINConstant = 0;

        if (symbol == SYM_LPARENTHESIS) {
            getSymbol();

            // function call:  identifier "(" ... ")" ...
            type = gr_call(variableOrProcedureName);

            allocatedRegisters = allocatedRegisters + 1;

            emitIFormat(OP_ADDIU, REG_RR, allocatedRegisters, 0);
        } else
            // else.. it is just an 'identifier'
            type = load_variable(variableOrProcedureName);

    // integer?
    } else if (symbol == SYM_INTEGER) {
        load_integer();
        type = INT_T;

    // character?
    } else if (symbol == SYM_CHARACTER) {
        mayBeINTMINConstant = 0;

        allocatedRegisters = allocatedRegisters + 1;

        emitIFormat(OP_ADDIU, REG_ZR, allocatedRegisters, ivalue);

        getSymbol();
        type = INT_T;

    //  "(" expression ")"
    } else if (symbol == SYM_LPARENTHESIS) {
        mayBeINTMINConstant = 0;
        getSymbol();
        type = gr_expression();

        if (symbol == SYM_RPARENTHESIS)
            getSymbol();
        else
            syntaxWarn(SYM_RPARENTHESIS);
    }

    // assert: allocatedRegisters == n + 1

    if (cast == 0)
        return type;
    else
        return cast;
}

int gr_term() {
    int ltype;
    int rtype;

    // assert: n = allocatedRegisters

    ltype = gr_factor();

    // assert: allocatedRegisters == n + 1

    // * / or % ?
    while (isStarOrDivOrModulo()) {
        if (symbol == SYM_ASTERISK) {
            // assert: allocatedRegisters == n + 2
            getSymbol();
            rtype = gr_factor();


            if (ltype == rtype) {
                emitRFormat(OP_SPECIAL, allocatedRegisters-1, allocatedRegisters, 0, FCT_MULTU);
                emitRFormat(OP_SPECIAL, 0, 0, allocatedRegisters-1, FCT_MFLO);

                allocatedRegisters = allocatedRegisters - 1;
            } else
                syntaxError(ERR_TYPE_MISMATCH);

        } else if (symbol == SYM_DIV) {
            getSymbol();
            rtype = gr_factor();


            if (ltype == rtype) {
                emitRFormat(OP_SPECIAL, allocatedRegisters-1, allocatedRegisters, 0, FCT_DIVU);
                emitRFormat(OP_SPECIAL, 0, 0, allocatedRegisters-1, FCT_MFLO);

                allocatedRegisters = allocatedRegisters - 1;
            }  else
                syntaxError(ERR_TYPE_MISMATCH);

        } else if (symbol == SYM_MOD) {
            getSymbol();
            rtype = gr_factor();

            if (ltype == rtype) {
                emitRFormat(OP_SPECIAL, allocatedRegisters-1, allocatedRegisters, 0, FCT_DIVU);
                emitRFormat(OP_SPECIAL, 0, 0, allocatedRegisters-1, FCT_MFHI);

                allocatedRegisters = allocatedRegisters - 1;
            } else
                syntaxError(ERR_TYPE_MISMATCH);
        }
    }

    // assert: allocatedRegisters == n + 1

    return ltype;
}

int gr_simpleExpression() {
    int sign;
    int ltype;
    int rtype;
    int operatorSymbol;

    // assert: n = allocatedRegisters

    // optional: -
    if (symbol == SYM_MINUS) {
        sign = 1;
        mayBeINTMINConstant = 1;
        getSymbol();
    } else
        sign = 0;

    ltype = gr_term();

    // assert: allocatedRegisters == n + 1

    if (sign == 1) {
        if (mayBeINTMINConstant)
            // avoids 0-INT_MIN overflow when bootstrapping
            // even though 0-INT_MIN == INT_MIN
            mayBeINTMINConstant = 0;
        else
            emitRFormat(OP_SPECIAL, REG_ZR, allocatedRegisters, allocatedRegisters, FCT_SUBU);
    }

    // + or -?
    while (isPlusOrMinus()) {
        operatorSymbol = symbol;
        getSymbol();

        rtype = gr_term();

        // assert: allocatedRegisters == n + 2

        if (operatorSymbol == SYM_PLUS) {
            if (ltype == rtype) { // base case, normal arithmetic
                emitRFormat(OP_SPECIAL, allocatedRegisters-1, allocatedRegisters, allocatedRegisters-1, FCT_ADDU);
            } else if (ltype == INTSTAR_T) {
                if (rtype == INT_T) {
                    // pointer arithmetic requires factor of 2^2
                    emitLeftShiftBy(2);
                    emitRFormat(OP_SPECIAL, allocatedRegisters-1, allocatedRegisters, allocatedRegisters-1, FCT_ADDU);
                } else {
                    syntaxError(ERR_TYPE_MISMATCH);
                }
            } else if (rtype == INTSTAR_T) {
                if (ltype == INT_T) {
                    // pointer arithmetic requires factor of 2^2
                    emitLeftShiftBy(2);
                    emitRFormat(OP_SPECIAL, allocatedRegisters-1, allocatedRegisters, allocatedRegisters-1, FCT_ADDU);
                } else
                    syntaxError(ERR_TYPE_MISMATCH);
            }
        } else {
            if (ltype == rtype)
                emitRFormat(OP_SPECIAL, allocatedRegisters-1, allocatedRegisters, allocatedRegisters-1, FCT_SUBU);
            else
                syntaxError(ERR_TYPE_MISMATCH);
        }

        allocatedRegisters = allocatedRegisters - 1;
    }

    // assert: allocatedRegisters == n + 1

    return ltype;
}

int gr_expression() {
    int ltype;
    int rtype;

    // assert: n = allocatedRegisters

    ltype = gr_simpleExpression(); // type of left element

    // assert: allocatedRegisters == n + 1

    //optional: ==, !=, <, >, <=, >= simpleExpression
    if (symbol == SYM_EQUAL) {
        getSymbol();
        rtype = gr_simpleExpression();

        // assert: allocatedRegisters == n + 2

        if (ltype == rtype) {
            // subtract, if result = 0 then 1, else 0
            emitRFormat(OP_SPECIAL, allocatedRegisters-1, allocatedRegisters, allocatedRegisters-1, FCT_SUBU);

            allocatedRegisters = allocatedRegisters - 1;

            emitIFormat(OP_BEQ, REG_ZR, allocatedRegisters, 4);
            emitIFormat(OP_ADDIU, REG_ZR, allocatedRegisters, 0);
            emitIFormat(OP_BEQ, REG_ZR, allocatedRegisters, 2);
            emitIFormat(OP_ADDIU, REG_ZR, allocatedRegisters, 1);
        } else
            syntaxError(ERR_TYPE_MISMATCH);

    } else if (symbol == SYM_NOTEQ) {
        getSymbol();
        rtype = gr_simpleExpression();

        // assert: allocatedRegisters == n + 2

        if (ltype == rtype) {
            // subtract, if result = 0 then 0, else 1
            emitRFormat(OP_SPECIAL, allocatedRegisters-1, allocatedRegisters, allocatedRegisters-1, FCT_SUBU);

            allocatedRegisters = allocatedRegisters - 1;

            emitIFormat(OP_BNE, REG_ZR, allocatedRegisters, 4);
            emitIFormat(OP_ADDIU, REG_ZR, allocatedRegisters, 0);
            emitIFormat(OP_BEQ, REG_ZR, allocatedRegisters, 2);
            emitIFormat(OP_ADDIU, REG_ZR, allocatedRegisters, 1);
        } else
            syntaxError(ERR_TYPE_MISMATCH);

    } else if (symbol == SYM_LT) {
        getSymbol();
        rtype = gr_simpleExpression();

        // assert: allocatedRegisters == n + 2

        if (ltype == rtype) {
            // set to 1 if a < b, else 0
            emitRFormat(OP_SPECIAL, allocatedRegisters-1, allocatedRegisters, allocatedRegisters-1, FCT_SLT);

            allocatedRegisters = allocatedRegisters - 1;
        } else
            syntaxError(ERR_TYPE_MISMATCH);

    } else if (symbol == SYM_GT) {
        getSymbol();
        rtype = gr_simpleExpression();

        // assert: allocatedRegisters == n + 2

        if (ltype == rtype) {
            // set to 1 if b < a, else 0
            emitRFormat(OP_SPECIAL, allocatedRegisters, allocatedRegisters-1, allocatedRegisters-1, FCT_SLT);

            allocatedRegisters = allocatedRegisters - 1;
        } else
            syntaxError(ERR_TYPE_MISMATCH);

    } else if (symbol == SYM_LEQ) {
        getSymbol();
        rtype = gr_simpleExpression();

        // assert: allocatedRegisters == n + 2

        if (ltype == rtype) {
            // if b < a set 0, else 1
            emitRFormat(OP_SPECIAL, allocatedRegisters, allocatedRegisters-1, allocatedRegisters-1, FCT_SLT);

            allocatedRegisters = allocatedRegisters - 1;

            emitIFormat(OP_BNE, REG_ZR, allocatedRegisters, 4);
            emitIFormat(OP_ADDIU, REG_ZR, allocatedRegisters, 1);
            emitIFormat(OP_BEQ, REG_ZR, REG_ZR, 2);
            emitIFormat(OP_ADDIU, REG_ZR, allocatedRegisters, 0);
        } else
            syntaxError(ERR_TYPE_MISMATCH);

    } else if (symbol == SYM_GEQ) {
        getSymbol();
        rtype = gr_simpleExpression();

        // assert: allocatedRegisters == n + 2

        if (ltype == rtype) {
            // if a < b set 0, else 1
            emitRFormat(OP_SPECIAL, allocatedRegisters-1, allocatedRegisters, allocatedRegisters-1, FCT_SLT);

            allocatedRegisters = allocatedRegisters - 1;

            emitIFormat(OP_BNE, REG_ZR, allocatedRegisters, 4);
            emitIFormat(OP_ADDIU, REG_ZR, allocatedRegisters, 1);
            emitIFormat(OP_BEQ, REG_ZR, REG_ZR, 2);
            emitIFormat(OP_ADDIU, REG_ZR, allocatedRegisters, 0);
        } else
            syntaxError(ERR_TYPE_MISMATCH);
    }

    // assert: allocatedRegisters == n + 1

    return ltype;
}

void
gr_while() {
    int brBackToWhile;
    int brForwardToEnd;

    // assert: allocatedRegisters == 0

    brBackToWhile = codeLength;

    // while ( expression )
    if (symbol == SYM_WHILE) {
        getSymbol();
        if (symbol == SYM_LPARENTHESIS) {
            getSymbol();
            gr_expression();

            //don't know where to branch, fixup later
            brForwardToEnd = codeLength;
            emitIFormat(OP_BEQ, REG_ZR, allocatedRegisters, 0);
            allocatedRegisters = allocatedRegisters - 1;

            if (symbol == SYM_RPARENTHESIS) {
                getSymbol();
                // zero or more statements: { statement }
                if (symbol == SYM_LBRACE) {
                    getSymbol();
                    while (isNotRbraceOrEOF())
                        gr_statement();

                    if (symbol == SYM_RBRACE)
                        getSymbol();
                    else
                        syntaxWarn(SYM_RBRACE);
                }
                // only one statement without {}
                else
                    gr_statement();
            } else
                syntaxError(SYM_RPARENTHESIS);
        } else
            syntaxError(SYM_LPARENTHESIS);
    } else
        syntaxError(SYM_WHILE);

    // unconditional branch to beginning of while
    emitIFormat(OP_BEQ, 0, 0, brBackToWhile - codeLength - 1);

    // first instr after loop comes here, now we have
    // our address for the conditional jump from above
    fixup_relative(brForwardToEnd);

    // assert: allocatedRegisters == 0
}

void gr_if() {
    int brForwardToElseOrEnd;
    int brForwardToEnd;

    // assert: allocatedRegisters == 0

    // if ( expression )
    if (symbol == SYM_IF) {
        getSymbol();
        if (symbol == SYM_LPARENTHESIS) {
            getSymbol();
            gr_expression();

            // if the "if" case is not true, we jump to "else" (if provided)
            brForwardToElseOrEnd = codeLength;
            emitIFormat(OP_BEQ, REG_ZR, allocatedRegisters, 0);
            allocatedRegisters = allocatedRegisters - 1;

            if (symbol == SYM_RPARENTHESIS) {
                getSymbol();
                // zero or more statements: { statement }
                if (symbol == SYM_LBRACE) {
                    getSymbol();

                    while (isNotRbraceOrEOF())
                        gr_statement();

                    if (symbol == SYM_RBRACE)
                        getSymbol();
                    else
                        syntaxWarn(SYM_RBRACE);
                }
                // only one statement without {}
                else
                    gr_statement();

                //optional: else
                if (symbol == SYM_ELSE) {
                    getSymbol();

                    // if the "if" case was true, we jump to the end
                    brForwardToEnd = codeLength;
                    emitIFormat(OP_BEQ, 0, 0, 0);

                    // if the "if" case was not true, we jump here
                    fixup_relative(brForwardToElseOrEnd);

                    // zero or more statements: { statement }
                    if (symbol == SYM_LBRACE) {
                        getSymbol();
                        while (isNotRbraceOrEOF())
                            gr_statement();

                        if (symbol == SYM_RBRACE)
                            getSymbol();
                        else
                            syntaxWarn(SYM_RBRACE);
                    // only one statement without {}
                    } else
                        gr_statement();

                    // if the "if" case was true, we jump here
                    fixup_relative(brForwardToEnd);
                } else
                    // if the "if" case was not true, we jump here
                    fixup_relative(brForwardToElseOrEnd);
            } else
                syntaxError(SYM_RPARENTHESIS);
        } else
            syntaxError(SYM_LPARENTHESIS);
    } else
        syntaxError(SYM_IF);

    // assert: allocatedRegisters == 0
}

void gr_return(int returnType) {
    // assert: allocatedRegisters == 0

    // keyword return
    if (symbol == SYM_RETURN)
        getSymbol();
    else
        syntaxError(SYM_RETURN);

    // optional: expression
    if (symbol != SYM_SEMICOLON) {
        if (returnType != VOID_T) {
            // TODO check for other wrong types, too
            gr_expression();

            // save value of expression in return register
            emitRFormat(OP_SPECIAL, REG_ZR, allocatedRegisters, REG_RR, FCT_ADDU);
            allocatedRegisters = allocatedRegisters - 1;
        } else
            syntaxError(ERR_WRONG_RETURNTYPE);
    }

    // unconditional branch to procedure epilogue
    // maintain fixup chain for later fixup
    emitJFormat(OP_J, returnBranches);

    // new head of fixup chain
    returnBranches = codeLength-2;

    // assert: allocatedRegisters == 0
}

void gr_statement() {
    int *variableOrProcedureName;
    int *entry;

    // assert: allocatedRegisters == 0;

    while (waitForStatement())
        syntaxError(ERR_STATEMENT);

    // ["*"]
    if (symbol == SYM_ASTERISK) {
        getSymbol();
        // ["*"] identifier
        if (symbol == SYM_IDENTIFIER) {
            load_variable(identifier);
            getSymbol();

            // ["*"] identifier "="
            if (symbol == SYM_ASSIGN) {
                getSymbol();

                gr_expression();

                emitIFormat(OP_SW, allocatedRegisters-1, allocatedRegisters, 0);
                allocatedRegisters = allocatedRegisters - 2;
            } else
                syntaxError(ERR_ASSIGN);

            if (symbol == SYM_SEMICOLON)
                getSymbol();
            else
                syntaxWarn(SYM_SEMICOLON);

        // "*" "(" identifier [ "+" integer ]
        } else if (symbol == SYM_LPARENTHESIS) {
            getSymbol();
            if (symbol == SYM_IDENTIFIER) {
                load_variable(identifier);

                getSymbol();

                if (symbol == SYM_PLUS) {
                    getSymbol();
                    if (symbol == SYM_IDENTIFIER) {
                        load_variable(identifier);

                        getSymbol();
                    } else if (symbol == SYM_INTEGER)
                        load_integer();
                    else
                        syntaxError(ERR_IDENTIFIER_OR_INTEGER);

                    // pointer arithmetic requires factor of 2^2
                    emitLeftShiftBy(2);
                    emitRFormat(OP_SPECIAL, allocatedRegisters-1, allocatedRegisters, allocatedRegisters-1, FCT_ADDU);

                    allocatedRegisters = allocatedRegisters - 1;
                }

                if (symbol == SYM_RPARENTHESIS) {
                    getSymbol();

                    // "*" "(" identifier ["+" integer] ")" ="
                    if (symbol == SYM_ASSIGN) {
                        getSymbol();

                        gr_expression();

                        emitIFormat(OP_SW, allocatedRegisters-1, allocatedRegisters, 0);

                        allocatedRegisters = allocatedRegisters - 2;
                    } else
                        syntaxError(ERR_ASSIGN);

                    if (symbol == SYM_SEMICOLON)
                        getSymbol();
                    else
                        syntaxWarn(SYM_SEMICOLON);
                } else
                    syntaxWarn(SYM_RPARENTHESIS);
            } else
                syntaxError(ERR_IDENTIFIER);
        } else
            syntaxError(SYM_LPARENTHESIS);
    }

    // identifier = [ "*" ] identifier "=" expression ";" |
    // identifier = call ";"
    // call;
    else if (symbol == SYM_IDENTIFIER) {
        variableOrProcedureName = identifier;

        getSymbol();

        // call ";"
        if (symbol == SYM_LPARENTHESIS) {
            getSymbol();

            gr_call(variableOrProcedureName);

            if (symbol == SYM_SEMICOLON)
                getSymbol();
            else
                syntaxWarn(SYM_SEMICOLON);

        // identifier = expression ";"
        } else if (symbol == SYM_ASSIGN) {
            entry = getVariable(variableOrProcedureName);
            getSymbol();
            gr_expression();

            emitIFormat(OP_SW, getRegister(entry), allocatedRegisters, getData(entry));

            allocatedRegisters = allocatedRegisters - 1;

            if (symbol == SYM_SEMICOLON)
                getSymbol();
            else
                syntaxError(SYM_SEMICOLON);
        } else
            syntaxError(ERR_IDENTIFIER_OR_ASSIGN);
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
        entry = getSymbolTableEntry(currentFuncName, global_symbol_table);

        gr_return(getType(entry));

        if (symbol == SYM_SEMICOLON)
            getSymbol();
        else
            syntaxWarn(SYM_SEMICOLON);
    }
}

int gr_variable() {
    int type;

    while (waitForVariable())
        syntaxError(ERR_TYPE);

    type = UNKNOWN;

    if (symbol == SYM_INT) {
        type = INT_T;

        getSymbol();

        if (symbol == SYM_ASTERISK) {
            type = INTSTAR_T;

            getSymbol();
        }

        if (symbol != SYM_IDENTIFIER)
            syntaxError(ERR_IDENTIFIER);
    } else
        syntaxError(ERR_EOF);

    return type;
}

void gr_procedure(int *procedure, int returnType) {
    int parameters;
    int oparam;
    int offset;
    int localVariables;
    int type;
    int functionStart;
    int *entry;

    currentFuncName = procedure;

    oparam = 0;

    // ( variable , variable ) ;
    if (symbol == SYM_LPARENTHESIS) {
        getSymbol();

        parameters = 0;

        if (symbol != SYM_RPARENTHESIS) {
            type = gr_variable();

            createSymbolTableEntry(LOCAL_TABLE, identifier, 0, VARIABLE, type);

            getSymbol();

            parameters = 1;

            while (symbol == SYM_COMMA) {
                getSymbol();

                type = gr_variable();

                createSymbolTableEntry(LOCAL_TABLE, identifier, 0, VARIABLE, type);

                getSymbol();

                parameters = parameters + 1;
            }

            oparam = parameters;
            entry = local_symbol_table;
            offset = 8;                  // skip fp and link
            while (parameters > 0) {
                setData(entry, offset);
                parameters = parameters - 1;
                offset     = offset + 4;
                entry      = getNext(entry);
            }

            if (symbol == SYM_RPARENTHESIS)
                getSymbol();
            else
                syntaxWarn(SYM_RPARENTHESIS);
        } else
            getSymbol();
    } else
        syntaxError(SYM_LPARENTHESIS);

    if (symbol == SYM_SEMICOLON) {
        entry = getSymbolTableEntry(currentFuncName, global_symbol_table);

        if ((int)entry == 0)
            createSymbolTableEntry(GLOBAL_TABLE, currentFuncName, 0, FUNCTION, returnType);

        getSymbol();

    // ( variable, variable ) { variable; variable; statement }
    } else if (symbol == SYM_LBRACE) {
        functionStart = codeLength;
        getSymbol();
        localVariables = 0;

        entry = getSymbolTableEntry(currentFuncName, global_symbol_table);

        if ((int)entry == 0) {
            createSymbolTableEntry(GLOBAL_TABLE, currentFuncName, codeLength, FUNCTION, returnType);
        } else {
            if (getData(entry) != 0)
                if (getOpcode(*(memory + getData(entry))) == OP_JAL)
                    fixlink_absolute(getData(entry), functionStart);

            // TODO: overwrites previous definitions
            setData(entry, functionStart);

            // TODO: check type of declaration and definition
            setType(entry, returnType);
        }

        while (symbol == SYM_INT) {
            type = gr_variable();

            localVariables = localVariables + 1;

            createSymbolTableEntry(LOCAL_TABLE, identifier, -4 * localVariables, VARIABLE, type);

            getSymbol();

            if (symbol == SYM_SEMICOLON)
                getSymbol();
            else
                syntaxWarn(SYM_SEMICOLON);
        }

        help_procedure_prologue(localVariables);

        // create a fixup chain for return statements
        returnBranches = 0;

        while (isNotRbraceOrEOF())
            gr_statement();

        if (symbol == SYM_RBRACE)
            getSymbol();
        else
            syntaxWarn(SYM_RBRACE);

        fixlink_absolute(returnBranches, codeLength);

        returnBranches = 0;

        help_procedure_epilogue(oparam, functionStart, returnType);

    } else
        syntaxError(ERR_LBRACE_OR_SEMICOLON);

    local_symbol_table = 0;

    // assert: allocatedRegisters == 0
}

void gr_cstar() {
    int offset;
    int type;
    int *variableOrProcedureName;

    type = UNKNOWN;

    while (isVariableOrProcedure()) {
        // type identifier
        if (symbol == SYM_INT) {
            type = INT_T;

            getSymbol();

            if (symbol == SYM_ASTERISK) {
                type = INTSTAR_T;
                getSymbol();
            }

            if (symbol == SYM_IDENTIFIER) {
                variableOrProcedureName = identifier;

                getSymbol();

                // type identifier, this means it is a global variable
                if (symbol == SYM_SEMICOLON) {
                    getSymbol();

                    offset = allocatedGlobalVariables * (-4);

                    createSymbolTableEntry(GLOBAL_TABLE, variableOrProcedureName, offset, VARIABLE, type);

                    allocatedGlobalVariables = allocatedGlobalVariables + 1;
                }
                // type identifier procedure
                else
                    gr_procedure(variableOrProcedureName, type);
            } else
                syntaxError(ERR_IDENTIFIER);

        // void identifier procedure
        } else if (symbol == SYM_VOID) {
            type = VOID_T;
            getSymbol();

            if (symbol == SYM_IDENTIFIER) {
                variableOrProcedureName = identifier;

                getSymbol();

                gr_procedure(variableOrProcedureName, type);
            }
        } else
            syntaxError(ERR_PROCEDURE_OR_VARIABLE);
    }

    // when we leave while, we don't expect any more
    // code to come, but if it does, it's a syntax error
    if (symbol != SYM_EOF) {
        syntaxError(ERR_EOF);
        exit(-1);
    }
}

// -----------------------------------------------------------------
// ------------------------ MACHINE CODE LIBRARY -------------------
// -----------------------------------------------------------------

void emitLeftShiftBy(int b) {
    // assert: 0 <= b < 15

    // load multiplication factor less than 2^15 to avoid sign extension
    emitIFormat(OP_ADDIU, REG_ZR, allocatedRegisters+1, twoToThePowerOf(b));
    emitRFormat(OP_SPECIAL, allocatedRegisters, allocatedRegisters+1, 0, FCT_MULTU);
    emitRFormat(OP_SPECIAL, 0, 0, allocatedRegisters, FCT_MFLO);
}

void emitMainEntry() {
    int *label;

    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_NOP); // null page

    // "main": entry point
    label = (int*)createString('m','a','i','n',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    createSymbolTableEntry(GLOBAL_TABLE, label, codeLength, FUNCTION, INT_T);

    emitJFormat(OP_JAL, 0);
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

int main_compiler() {
    initScanner();
    initSymbolTable();
    initParser();

    allocateMachineMemory(maxCodeLength*4);

    getSymbol();

    emitMainEntry();

    // Library functions:
    emitExit();      // first library function because this marks
                     // also 'default'-exit when programmer hasn't
                     // inserted exit() call in main
    emitRead();
    emitWrite();
    emitOpen();
    emitMalloc();
    emitGetchar();
    emitPutchar();

    gr_cstar();     // invoke compiler
    emitBinary();

    exit(0);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

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
    // assert: 0 <= immediate < 2^26
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
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void allocateMachineMemory(int size) {
    memory = (int*)malloc(size);
}

// -----------------------------------------------------------------
// ---------------------------- BINARY -----------------------------
// -----------------------------------------------------------------

void emitInstruction(int instruction) {
    if (codeLength >= maxCodeLength) {
        syntaxError(ERR_MAXCODELENGTH);
        exit(-1);
    } else {
        *(memory + codeLength) = instruction;
        codeLength = codeLength + 1;
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
    *(memory + fromAddress) = encodeIFormat(
        getOpcode(*(memory + fromAddress)),
        getRS(*(memory + fromAddress)),
        getRT(*(memory + fromAddress)),
        codeLength - fromAddress - 1);
}

void fixup_absolute(int fromAddress, int toAddress) {
    *(memory + fromAddress) =
        encodeJFormat(getOpcode(*(memory + fromAddress)), toAddress);
}

void fixlink_absolute(int fromAddress, int toAddress) {
    int previousAddress;

    while (fromAddress != 0) {
        previousAddress = getInstrIndex(*(memory + fromAddress));
        fixup_absolute(fromAddress, toAddress);
        fromAddress = previousAddress;
    }
}

void emitBinary() {
    int i;
    int *filename;
    int fd;

    i = 0;

    // put global variables as 0 at end of codearray
    while (i < allocatedGlobalVariables) {
        *(memory + codeLength) = 0;

        codeLength = codeLength + 1;

        i = i + 1;
    }

    filename = (int*)malloc(4*4);
    *filename = 7632239; //filename: out

    // assumption: file with name "out" exists prior to execution of compiler
    fd = open(filename, 1); // 1 = O_WRONLY

    if (fd < 0) {
        syntaxError(ERR_FILE_NOT_FOUND);
        exit(-1);
    }

    // The mipster_sycall 4004 writes the code array into a binary called 'out'.
    // The syscall uses the 'write' system call of the underlying operating
    // system and the compiler (gcc/x86).  The write system call of our Linux uses
    // Little Endian byte ordering.
    write(fd, memory, codeLength*4);
}

int loadBinary(int *filename) {
    int fd;
    int i;
    int ret;

    fd = open(filename, 0);

    if (fd < 0)
        exit(-1);

    i = 0;

    ret = 4;

    while (ret == 4) {
        ret = read(fd, memory + i, 4);

        if (debug_load) {
            memset(string_buffer, 33, 0);
            print(itoa(i * 4, string_buffer, 16, 4));
            putchar(' ');
            putchar('#');
            putchar(' ');
            memset(string_buffer, 33, 0);
            print(itoa(*(memory+i), string_buffer, 16, 8));
            putchar(CHAR_LF);
        }

        i = i + 1;
    }

    // Return global pointer and bump pointer for malloc
    return i * 4;
}

// -----------------------------------------------------------------
// --------------------------- SYSCALLS ----------------------------
// -----------------------------------------------------------------

void emitExit() {
    int *label;

    // "exit"
    label = createString('e','x','i','t',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    createSymbolTableEntry(GLOBAL_TABLE, label, codeLength, FUNCTION, INT_T);

    emitIFormat(OP_ADDIU, REG_ZR, REG_A3, 0);
    emitIFormat(OP_ADDIU, REG_ZR, REG_A2, 0);
    emitIFormat(OP_ADDIU, REG_ZR, REG_A1, 0);

    emitIFormat(OP_LW, REG_SP, REG_A0, 0); // exit code
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, 4);

    emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_EXIT);
    emitRFormat(0, 0, 0, 0, FCT_SYSCALL);
}

void syscall_exit() {
    int exitCode;

    exitCode = *(registers+REG_A0);

    printString('[','O','S',']',' ','T', 'e', 'r','m','i','n','a','t','e','d',' ','w','i','t','h');
    putchar(' ');

    *(registers+REG_V0) = exitCode;

    print(itoa(exitCode, string_buffer, 10, 0));
    putchar(CHAR_LF);

    exit(0);
}

void emitRead() {
    int *label;

    // "read"
    label = createString('r','e','a','d',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    createSymbolTableEntry(GLOBAL_TABLE, label, codeLength, FUNCTION, INT_T);

    emitIFormat(OP_ADDIU, REG_ZR, REG_A3, 0);

    emitIFormat(OP_LW, REG_SP, REG_A2, 0); // count
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, 4);

    emitIFormat(OP_LW, REG_SP, REG_A1, 0); // *buffer
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, 4);

    emitIFormat(OP_LW, REG_SP, REG_A0, 0); // fd
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, 4);

    emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_READ);
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

    emitIFormat(OP_ADDIU, REG_V0, REG_RR, 0);

    emitRFormat(OP_SPECIAL, REG_LINK, 0, 0, FCT_JR);
}

void syscall_read() {
    int count;
    int address;
    int fd;
    int *buffer;
    int size;

    count   = *(registers+REG_A2);
    address = *(registers+REG_A1) / 4;
    fd      = *(registers+REG_A0);

    buffer = memory + address;

    size = read(fd, buffer, count);

    *(registers+REG_V0) = size;

    if (debug_syscalls) {
        printString('[','O','S',']',' ','c', 'a', 'l','l',' ','r','e','a','d',' ',CHAR_TAB,0,0,0,0);

        print(itoa(fd, string_buffer, 10, 0));
        putchar(' ');
        memset(string_buffer, 33, 0);
        print(itoa((int)buffer, string_buffer, 16, 8));
        putchar(' ');
        print(itoa(size, string_buffer, 10, 0));
        putchar(CHAR_LF);
    }
}

void emitWrite() {
    int *label;

    // "write"
    label = createString('w','r','i','t','e',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    createSymbolTableEntry(GLOBAL_TABLE, label, codeLength, FUNCTION, INT_T);

    emitIFormat(OP_ADDIU, REG_ZR, REG_A3, 0);

    emitIFormat(OP_LW, REG_SP, REG_A2, 0); // size
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, 4);

    emitIFormat(OP_LW, REG_SP, REG_A1, 0); // *buffer
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, 4);

    emitIFormat(OP_LW, REG_SP, REG_A0, 0); // fd
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, 4);

    emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_WRITE);
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

    emitIFormat(OP_ADDIU, REG_V0, REG_RR, 0);

    emitRFormat(OP_SPECIAL, REG_LINK, 0, 0, FCT_JR);
}

void syscall_write() {
    int size;
    int address;
    int fd;
    int *buffer;

    size    = *(registers+REG_A2);
    address = *(registers+REG_A1) / 4;
    fd      = *(registers+REG_A0);

    buffer = memory + address;

    size = write(fd, buffer, size);

    *(registers+REG_V0) = size;

    if (debug_syscalls)
        printString('[','O','S',']',' ','c', 'a', 'l','l',' ','w','r','i','t','e',CHAR_LF,0,0,0,0);
}

void emitOpen() {
    int *label;

    // "open"
    label = createString('o','p','e','n',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    createSymbolTableEntry(GLOBAL_TABLE, label, codeLength, FUNCTION, INT_T);

    emitIFormat(OP_ADDIU, REG_ZR, REG_A3, 0);
    emitIFormat(OP_ADDIU, REG_ZR, REG_A2, 0);

    emitIFormat(OP_LW, REG_SP, REG_A1, 0); // flags
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, 4);

    emitIFormat(OP_LW, REG_SP, REG_A0, 0); // filename
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, 4);

    emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_OPEN);
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

    emitIFormat(OP_ADDIU, REG_V0, REG_RR, 0);

    emitRFormat(OP_SPECIAL, REG_LINK, 0, 0, FCT_JR);
}

void syscall_open() {
    int flags;
    int address;
    int *filename;
    int fd;

    flags   = *(registers+REG_A1);
    address = *(registers+REG_A0) / 4;

    filename = memory + address;

    fd = open(filename, flags);

    *(registers+REG_V0) = fd;

    if (debug_syscalls) {
        printString('[','O','S',']',' ','c', 'a', 'l','l',' ','o','p','e','n',' ',CHAR_TAB,0,0,0,0);

        print(itoa(fd, string_buffer, 10, 0));
        putchar(CHAR_LF);
    }
}

void emitMalloc() {
    int *label;

    // "malloc"
    label = createString('m','a','l','l','o','c',0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    createSymbolTableEntry(GLOBAL_TABLE, label, codeLength, FUNCTION, INTSTAR_T);

    emitIFormat(OP_ADDIU, REG_ZR, REG_A3, 0);
    emitIFormat(OP_ADDIU, REG_ZR, REG_A2, 0);
    emitIFormat(OP_ADDIU, REG_ZR, REG_A1, 0);

    // load argument for malloc (size)
    emitIFormat(OP_LW, REG_SP, REG_A0, 0);

    // remove the argument from the stack
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, 4);

    // load the correct syscall number and invoke syscall
    emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_MALLOC);
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

    // put return value into return register
    emitIFormat(OP_ADDIU, REG_V0, REG_RR, 0);

    // jump back to caller
    emitRFormat(OP_SPECIAL, REG_LINK, 0, 0, FCT_JR);
}

void syscall_malloc() {
    int size;
    int bump;

    size = *(registers+REG_A0);

    if (size % 4 != 0)
        size = size + (4 - size % 4);

    bump = *(registers+REG_K1);

    if (bump + size >= *(registers+REG_SP))
        exception_handler(EXCEPTION_HEAPOVERFLOW);

    *(registers+REG_K1) = bump + size;
    *(registers+REG_V0) = bump;

    if (debug_syscalls)
        printString('[','O','S',']',' ','c', 'a', 'l','l',' ','m','a','l','l','o','c',CHAR_LF,0,0,0);
}

void emitGetchar() {
    int *label;

    // "getchar"
    label = createString('g','e','t','c','h','a','r',0,0,0,0,0,0,0,0,0,0,0,0,0);

    createSymbolTableEntry(GLOBAL_TABLE, label, codeLength, FUNCTION, INT_T);

    emitIFormat(OP_ADDIU, REG_ZR, REG_A3, 0);
    emitIFormat(OP_ADDIU, REG_ZR, REG_A2, 0);
    emitIFormat(OP_ADDIU, REG_ZR, REG_A1, 0);
    emitIFormat(OP_ADDIU, REG_ZR, REG_A0, 0);

    emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_GETCHAR);
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

    emitIFormat(OP_ADDIU, REG_V0, REG_RR, 0);

    emitRFormat(OP_SPECIAL, REG_LINK, 0, 0, FCT_JR);
}

void syscall_getchar() {
    *(registers+REG_V0) = getchar();

    if (debug_syscalls)
        printString('[','O','S',']',' ','c', 'a', 'l','l',' ','g','e','t','c','h','a','r',CHAR_LF,0,0);
}

void emitPutchar() {
    int *label;

    // "putchar"
    label = createString('p','u','t','c','h','a','r',0,0,0,0,0,0,0,0,0,0,0,0,0);

    createSymbolTableEntry(GLOBAL_TABLE, label, codeLength, FUNCTION, INT_T);

    emitIFormat(OP_ADDIU, REG_ZR, REG_A3, 0);

    emitIFormat(OP_ADDIU, REG_ZR, REG_A2, 4); // write one integer, 4 bytes

    emitIFormat(OP_ADDIU, REG_SP, REG_A1, 0); // pointer to character
    emitIFormat(OP_ADDIU, REG_SP, REG_SP, 4);

    emitIFormat(OP_ADDIU, REG_ZR, REG_A0, 1); // stdout file descriptor

    emitIFormat(OP_ADDIU, REG_ZR, REG_V0, SYSCALL_WRITE);
    emitRFormat(OP_SPECIAL, 0, 0, 0, FCT_SYSCALL);

    emitRFormat(OP_SPECIAL, REG_LINK, 0, 0, FCT_JR);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     E M U L A T O R   ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

void fct_syscall() {
    if (debug_disassemble) {
        print((int*)(*(fct_strings+function)));
        putchar(CHAR_LF);
    }

    if (*(registers+REG_V0) == SYSCALL_EXIT) {
        syscall_exit();
    } else if (*(registers+REG_V0) == SYSCALL_READ) {
        syscall_read();
    } else if (*(registers+REG_V0) == SYSCALL_WRITE) {
        syscall_write();
    } else if (*(registers+REG_V0) == SYSCALL_OPEN) {
        syscall_open();
    } else if (*(registers+REG_V0) == SYSCALL_MALLOC) {
        syscall_malloc();
    } else if (*(registers+REG_V0) == SYSCALL_GETCHAR) {
        syscall_getchar();
    } else {
        exception_handler(EXCEPTION_UNKNOWNSYSCALL);
    }

    pc = pc + 1;
}

void fct_nop() {
    pc = pc + 1;

    if (debug_disassemble) {
        print((int*)(*(fct_strings+function)));
        putchar(CHAR_LF);
    }
}

void op_jal() {
    *(registers+REG_LINK) = pc * 4 + 8;

    pc = instr_index;

    // TODO: execute delay slot

    if (debug_disassemble) {
        print((int*)(*(op_strings+opcode)));

        putchar(' ');
        memset(string_buffer, 33, 0);
        print(itoa(instr_index, string_buffer, 16, 8));
        putchar(CHAR_LF);
    }
}

void op_j() {
    pc = instr_index;

    // TODO: execute delay slot

    if (debug_disassemble) {
        print((int*)(*(op_strings+opcode)));

        putchar(' ');
        memset(string_buffer, 33, 0);
        print(itoa(instr_index, string_buffer, 16, 8));
        putchar(CHAR_LF);
    }
}

void op_beq() {
    pc = pc + 1;

    if (*(registers+rs) == *(registers+rt)) {
        pc = pc + signExtend(immediate);
        // TODO: execute delay slot
    }

    if (debug_disassemble) {
        print((int*)(*(op_strings+opcode)));

        putchar(' ');
        print((int*)(*(register_strings+rs)));
        putchar(',');
        print((int*)(*(register_strings+rt)));
        putchar(',');
        print(itoa(signExtend(immediate), string_buffer, 10, 0));

        putchar(CHAR_LF);
    }
}

void op_bne() {
    pc = pc + 1;

    if (*(registers+rs) != *(registers+rt)) {
        pc = pc + signExtend(immediate);
        // TODO: execute delay slot
    }

    if (debug_disassemble) {
        print((int*)(*(op_strings+opcode)));

        putchar(' ');
        print((int*)(*(register_strings+rs)));
        putchar(',');
        print((int*)(*(register_strings+rt)));
        putchar(',');
        print(itoa(signExtend(immediate), string_buffer, 10, 0));

        putchar(CHAR_LF);
    }
}

void op_addiu() {
    *(registers+rt) = *(registers+rs) + signExtend(immediate);

    // TODO: check for overflow

    pc = pc + 1;

    if (debug_disassemble) {
        print((int*)(*(op_strings+opcode)));

        putchar(' ');
        print((int*)(*(register_strings+rt)));
        putchar(',');
        print((int*)(*(register_strings+rs)));
        putchar(',');
        print(itoa(signExtend(immediate), string_buffer, 10, 0));

        putchar(CHAR_LF);
    }
}

void fct_jr() {
    pc = *(registers+rs) / 4;

    if (debug_disassemble) {
        print((int*)(*(fct_strings+function)));

        putchar(' ');
        print((int*)(*(register_strings+rs)));

        putchar(CHAR_LF);
    }
}

void op_lui() {
    *(registers+rt) = leftShift(immediate, 16);

    pc = pc + 1;

    if (debug_disassemble) {
        print((int*)(*(op_strings+opcode)));

        putchar(' ');

        print((int*)(*(register_strings+rt)));
        putchar(',');
        print(itoa(signExtend(immediate), string_buffer, 10, 0));

        putchar(CHAR_LF);
    }
}

void fct_mfhi() {
    *(registers+rd) = reg_hi;

    pc = pc + 1;

    if (debug_disassemble) {
        print((int*)(*(fct_strings+function)));

        putchar(' ');
        print((int*)(*(register_strings+rd)));

        putchar(CHAR_LF);
    }
}

void fct_mflo() {
    *(registers+rd) = reg_lo;

    pc = pc + 1;

    if (debug_disassemble) {
        print((int*)(*(fct_strings+function)));

        putchar(' ');
        print((int*)(*(register_strings+rd)));

        putchar(CHAR_LF);
    }
}

void fct_multu() {
    // TODO: 64-bit resolution currently not supported
    reg_lo = *(registers+rs) * *(registers+rt);

    pc = pc + 1;

    if (debug_disassemble) {
        print((int*)(*(fct_strings+function)));

        putchar(' ');
        print((int*)(*(register_strings+rs)));
        putchar(',');
        print((int*)(*(register_strings+rt)));

        putchar(CHAR_LF);
    }
}

void fct_divu() {
    reg_lo = *(registers+rs) / *(registers+rt);
    reg_hi = *(registers+rs) % *(registers+rt);

    pc = pc + 1;

    if (debug_disassemble) {
        print((int*)(*(fct_strings+function)));

        putchar(' ');
        print((int*)(*(register_strings+rs)));
        putchar(',');
        print((int*)(*(register_strings+rt)));

        putchar(CHAR_LF);
    }
}

void fct_addu() {
    *(registers+rd) = *(registers+rs) + *(registers+rt);

    pc = pc + 1;

    if (debug_disassemble) {
        print((int*)(*(fct_strings+function)));

        putchar(' ');
        print((int*)(*(register_strings+rd)));
        putchar(',');
        print((int*)(*(register_strings+rs)));
        putchar(',');
        print((int*)(*(register_strings+rt)));
        putchar(CHAR_LF);
    }
}

void fct_subu() {
    *(registers+rd) = *(registers+rs) - *(registers+rt);

    pc = pc + 1;

    if (debug_disassemble) {
        print((int*)(*(fct_strings+function)));

        putchar(' ');
        print((int*)(*(register_strings+rd)));
        putchar(',');
        print((int*)(*(register_strings+rs)));
        putchar(',');
        print((int*)(*(register_strings+rt)));
        putchar(CHAR_LF);

    }
}

void op_lw() {
    int vaddr;
    int paddr;

    vaddr = *(registers+rs) + signExtend(immediate);

    paddr = addressTranslation(vaddr) / 4;

    *(registers+rt) = *(memory+paddr);

    pc = pc + 1;

    if (debug_disassemble) {
        print((int*)(*(op_strings+opcode)));

        putchar(' ');
        print((int*)(*(register_strings+rt)));
        putchar(',');
        print(itoa(signExtend(immediate), string_buffer, 10, 0));

        putchar('(');
        print((int*)(*(register_strings+rs)));
        putchar(')');

        putchar(CHAR_LF);
    }
}

void fct_slt() {
    if (*(registers+rs) < *(registers+rt))
        *(registers+rd) = 1;
    else
        *(registers+rd) = 0;

    pc = pc + 1;

    if (debug_disassemble) {
        print((int*)(*(fct_strings+function)));

        putchar(' ');
        print((int*)(*(register_strings+rd)));
        putchar(',');
        print((int*)(*(register_strings+rs)));
        putchar(',');
        print((int*)(*(register_strings+rt)));

        putchar(CHAR_LF);
    }
}

void op_sw() {
    int vaddr;
    int paddr;
    int tmp;

    vaddr = *(registers+rs) + signExtend(immediate);

    paddr = addressTranslation(vaddr) / 4;

    *(memory+paddr) = *(registers+rt);

    pc = pc + 1;

    if (debug_disassemble) {
        print((int*)(*(op_strings+opcode)));

        putchar(' ');
        print((int*)(*(register_strings+rt)));
        putchar(',');
        print(itoa(signExtend(immediate), string_buffer, 10, 0));

        putchar('(');
        print((int*)(*(register_strings+rs)));
        putchar(')');

        putchar(CHAR_LF);
    }
}

void fct_teq() {
    if (*(registers+rs) == *(registers+rt))
        exception_handler(EXCEPTION_SIGNAL);

    pc = pc + 1;

    if (debug_disassemble) {
        print((int*)*(fct_strings+function));

        putchar(' ');
        print((int*)(*(register_strings+rs)));
        putchar(',');
        print((int*)(*(register_strings+rt)));

        putchar(CHAR_LF);
    }
}

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void exception_handler(int enumber) {
    if (enumber == EXCEPTION_SIGNAL) {
        exit(EXCEPTION_SIGNAL);
    } else if (enumber == EXCEPTION_ADDRESSERROR) {
        exit(EXCEPTION_ADDRESSERROR);
    } else if (enumber == EXCEPTION_UNKNOWNINSTRUCTION) {
        exit(EXCEPTION_UNKNOWNINSTRUCTION);
    } else if (enumber == EXCEPTION_HEAPOVERFLOW) {
        exit(EXCEPTION_HEAPOVERFLOW);
    } else if (enumber == EXCEPTION_UNKNOWNSYSCALL) {
        exit(EXCEPTION_UNKNOWNSYSCALL);
    } else if (enumber == EXCEPTION_UNKNOWNFUNCTION) {
        exit(EXCEPTION_UNKNOWNFUNCTION);
    }
}

int addressTranslation(int vaddr) {
    if (vaddr % 4 != 0)
        exception_handler(EXCEPTION_ADDRESSERROR);

    return vaddr;
}

void pre_debug() {
    if (debug_disassemble) {
        memset(string_buffer, 33, 0);           // print current PC
        print(itoa(4 * pc, string_buffer, 16, 4));
        putchar(CHAR_TAB);
    }
}

void post_debug() {
    int i;
    if (debug_registers) {
        i = 0;

        while (i < 32) {
            if (*(registers+i) != 0) {
                print((int*)*(register_strings+i));
                putchar(CHAR_TAB);
                memset(string_buffer, 33, 0);
                print(itoa(*(registers+i), string_buffer, 16, 8));

                putchar(CHAR_LF);
            }
            i = i + 1;
        }
        putchar(CHAR_LF);
    }
}

void fetch() {
    ir = *(memory+pc);
}

void execute() {
    if (opcode == OP_SPECIAL) {
        if (function == FCT_NOP) {
            fct_nop();
        } else if (function == FCT_ADDU) {
            fct_addu();
        } else if (function == FCT_SUBU) {
            fct_subu();
        } else if (function == FCT_MULTU) {
            fct_multu();
        } else if (function == FCT_DIVU) {
            fct_divu();
        } else if (function == FCT_MFHI) {
            fct_mfhi();
        } else if (function == FCT_MFLO) {
            fct_mflo();
        } else if (function == FCT_SLT) {
            fct_slt();
        } else if (function == FCT_JR) {
            fct_jr();
        } else if (function == FCT_SYSCALL) {
            fct_syscall();
        } else if (function == FCT_TEQ) {
            fct_teq();
        } else {
            exception_handler(EXCEPTION_UNKNOWNINSTRUCTION);
        }
    } else if (opcode == OP_ADDIU) {
        op_addiu();
    } else if (opcode == OP_LW) {
        op_lw();
    } else if (opcode == OP_SW) {
        op_sw();
    } else if (opcode == OP_BEQ) {
        op_beq();
    } else if (opcode == OP_BNE) {
        op_bne();
    } else if (opcode == OP_JAL) {
        op_jal();
    } else if (opcode == OP_J) {
        op_j();
    } else {
        exception_handler(EXCEPTION_UNKNOWNINSTRUCTION);
    }
}

void run() {

    while (1) {
        fetch();
        decode();
        pre_debug();
        execute();
        post_debug();
    }
}

void debug_boot(int memorySize) {
    printString('m','e','m',' ',0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);

    print(itoa(memorySize/1024/1024*4, string_buffer, 10, 0));

    printString('M','B',CHAR_LF,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0);
}

int* parse_args(int argc, int *argv, int *cstar_argv) {
    // assert: ./selfie -m size executable {-m size executable}
    int memorySize;

    memorySize = atoi((int*)*(cstar_argv+2)) * 1024 * 1024 / 4;

    allocateMachineMemory(memorySize*4);

    // initialize stack pointer
    *(registers+REG_SP) = (memorySize - 1) * 4;

    debug_boot(memorySize);

    // return executable file name
    return (int*)*(argv+3);
}

void up_push(int value) {
    int address;

    // allocate space for one value on the stack
    *(registers+REG_SP) = *(registers+REG_SP) - 4;

    // compute address
    address = *(registers+REG_SP) / 4;

    // store value
    *(memory + address) = value;
}

int up_malloc(int size) {
    *(registers+REG_A0) = size;

    syscall_malloc();

    return *(registers+REG_V0);
}

int CStringLength(int* s) {
    int l;

    l = 0;

    while (rightShift(leftShift(*s, 24 - (l % 4) * 8), 24) != 0) {
        l = l + 1;

        if (l % 4 == 0)
            s = s + 1;
    }

    return l;
}

int up_copyCString(int *s) {
    int l;
    int r;
    int a;

    l = CStringLength(s);

    r = up_malloc(l+1);

    a = r / 4;

    while (a * 4 < r + l + 1) {
        *(memory + a) = *s;

        s = s + 1;
        a = a + 1;
    }

    return r;
}

void up_copyArguments(int argc, int *argv) {
    int c_argv;
    
    up_push(argc);

    c_argv = up_malloc(argc*4);

    up_push(c_argv);

    c_argv = c_argv / 4;

    while (argc > 0) {
        *(memory + c_argv) = up_copyCString((int*)*argv);

        c_argv = c_argv + 1;
        argv = argv + 1;

        argc = argc - 1;
    }
}

int main_emulator(int argc, int *argv, int *cstar_argv) {
    initInterpreter();

    *(registers+REG_GP) = loadBinary(parse_args(argc, argv, cstar_argv));

    *(registers+REG_K1) = *(registers+REG_GP);

    up_copyArguments(argc-3, argv+3);

    run();

    exit(0);
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

int* copyC2CStarString(int* s) {
    int l;
    int *r;
    int i;

    l = CStringLength(s);

    r = malloc((l + 1) * 4);

    i = 0;

    while (i <= l) {
        *(r+i) = rightShift(leftShift(*s, 24 - (i % 4) * 8), 24);

        i = i + 1;

        if (i % 4 == 0)
            s = s + 1;
    }

    return r;
}

int* copyC2CStarArguments(int argc, int *argv) {
    int *cstar_argv;
    int *cursor;

    cstar_argv = malloc(argc * 4);

    cursor = cstar_argv;

    while (argc > 0) {
        *cursor = (int)copyC2CStarString((int*)*argv);

        argv = argv + 1;
        cursor = cursor + 1;
        argc = argc - 1;
    }

    return cstar_argv;
}

int main(int argc, int *argv) {
    int *cstar_argv;
    int *firstParameter;

    initLibrary();

    initRegister();
    initDecoder();
    initSyscalls();

    cstar_argv = copyC2CStarArguments(argc, argv);

    if (argc > 1) {
        firstParameter = (int*) (*(cstar_argv+1));

        if (*firstParameter == '-') {
            if (*(firstParameter+1) == 'c')
                main_compiler();
            else if (*(firstParameter+1) == 'm') {
                if (argc > 3)
                    main_emulator(argc, argv, cstar_argv);
                else
                    exit(-1);
            }
            else {
                exit(-1);
            }
        } else {
            exit(-1);
        }
    } else
        // default: compiler
        main_compiler();
}
