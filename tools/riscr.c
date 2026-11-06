/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

Riscr implements RISC-R, the reversible variant of RISC-U, with
selfie as library. RISC-R keeps the 14 RISC-U instructions and their
encodings but changes what they mean such that every instruction is
a bijection on the machine state. Riscr executes RISC-R binaries,
which are RISC-U binaries with bit 8 of e_flags set, forward and,
without any trace, backward. See riscr.md for the instruction set
and projects/reversible.md for the development plan.

The emulator reuses mipster's loader, memory, contexts, and decoder,
and replaces mipster's execution with RISC-R semantics: a reverse
flag selects the direction, and instruction_address() and
continue_at() hide it from the instructions. Files are part of the
machine state: system calls exchange words with tapes that remember
what was read and written.

Options in addition to selfie's options:

-t binary translates the loaded RISC-U binary into a RISC-R binary
in Bennett mode and writes it to binary (milestone M2),
-m 0-4096 ... runs a RISC-R binary forward until it exits,
-rev 0-4096 ... runs it forward and then all instructions but the
exit system call backward.

Selfie's own mipster refuses RISC-R binaries.
*/

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     L I B R A R Y     ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------- EXCLUSIVE OR --------------------------
// -----------------------------------------------------------------

void     init_xor_table();
uint64_t bitwise_xor(uint64_t a, uint64_t b);

// ------------------------ GLOBAL VARIABLES -----------------------

char* xor_table = (char*) 0; // 256x256 table of byte-wise exclusive ors, see init_xor_table()

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------    C O M P I L E R    ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// -------------------------- TRANSLATOR ---------------------------
// -----------------------------------------------------------------

// Bennett mode (milestone M2): translate RISC-U binaries into RISC-R
// binaries. Every value a RISC-U instruction overwrites is exchanged
// onto a history stack, every branch target gets a come-from, and a
// flag pushed at every join records which way control arrived, see
// projects/reversible.md. The translated program uses six registers
// that starc never uses.

uint64_t selfie_translate();

void translation_error(uint64_t i, char* message);
uint64_t is_reserved_register(uint64_t reg);

void put_instruction(uint64_t instruction);
void put_lui(uint64_t reg, uint64_t immediate);
void put_addi(uint64_t reg, uint64_t rs, uint64_t immediate);
void put_op(uint64_t instruction_id, uint64_t reg, uint64_t rs, uint64_t rt);
void put_add(uint64_t reg, uint64_t rs, uint64_t rt);
void put_sub(uint64_t reg, uint64_t rs, uint64_t rt);
void put_ld(uint64_t reg, uint64_t rs, uint64_t immediate);
void put_beq(uint64_t rs, uint64_t rt, uint64_t immediate);
void put_jal(uint64_t reg, uint64_t immediate);
void put_jalr(uint64_t reg, uint64_t rs, uint64_t immediate);
void put_ecall();
void put_push(uint64_t reg);
void put_pop(uint64_t reg);
void put_source(uint64_t reg);

void     decode_source(uint64_t i);
uint64_t origin_target(uint64_t i);
uint64_t syscall_number(uint64_t i);

void load_source();
void classify_source(uint64_t i);
void analyze_source();

void put_prologue();
void put_trailer();
void put_prefix(uint64_t i);
void put_origin(uint64_t i);
void put_syscall(uint64_t i);
void put_body(uint64_t i);

void layout_translation();
void emit_translation();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t REG_HP  = 18; // s2: history pointer, next free slot
uint64_t REG_FL  = 19; // s3: flag, 1 on a taken transfer, 0 otherwise
uint64_t REG_ONE = 20; // s4: constant 1, the flag's partner in come-froms
uint64_t REG_BRK = 21; // s5: current program break, what RISC-U brk(0) returns
uint64_t REG_X   = 22; // s6: scratch, zero between translated instructions
uint64_t REG_Y   = 23; // s7: scratch, zero between translated instructions

uint64_t HISTORY_GIGABYTES = 3; // size of the history stack at the start of the heap

// kinds of translated instructions
uint64_t TK_COPY      = 0;  // emitted as is
uint64_t TK_INPLACE   = 1;  // rd += f(rs) with rd a source, no history
uint64_t TK_PUSHOP    = 2;  // push rd, then compute into the zeroed rd
uint64_t TK_SCRATCH   = 3;  // compute into scratch, exchange through the history slot
uint64_t TK_LOAD      = 4;  // copy a memory word into rd
uint64_t TK_LOADSAME  = 5;  // the same with rd == rs1
uint64_t TK_STORE     = 6;  // push the memory word, copy rs2 into it
uint64_t TK_BEQ       = 7;  // conditional branch to a join
uint64_t TK_JALZ      = 8;  // unconditional jump to a join
uint64_t TK_CALL      = 9;  // jal ra
uint64_t TK_RET       = 10; // jalr zero,0(ra)
uint64_t TK_ECALL     = 11; // system call

uint64_t ORIGIN_NONE      = 0;
uint64_t ORIGIN_BEQ       = 1;
uint64_t ORIGIN_JALZ      = 2;
uint64_t ORIGIN_SYNTHETIC = 3; // falling into a procedure entry becomes a jump

uint64_t NONE = -1;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* source_code = (uint64_t*) 0; // RISC-U instructions, one per word
uint64_t  number_of_source_instructions = 0;

// decoded source instructions, see decode_source
uint64_t* source_is  = (uint64_t*) 0;
uint64_t* source_rd  = (uint64_t*) 0;
uint64_t* source_rs1 = (uint64_t*) 0;
uint64_t* source_rs2 = (uint64_t*) 0;
uint64_t* source_imm = (uint64_t*) 0;

uint64_t* body_length = (uint64_t*) 0; // per source instruction: bytes of its translation

uint64_t* kind        = (uint64_t*) 0; // TK_* per source instruction
uint64_t* target_of   = (uint64_t*) 0; // source index of branch target or callee, or NONE
uint64_t* origin_kind = (uint64_t*) 0; // ORIGIN_* per source instruction

uint64_t* first_origin = (uint64_t*) 0; // per target: first origin in source order, or NONE
uint64_t* next_origin  = (uint64_t*) 0; // per origin: next origin with the same target, or NONE
uint64_t* chain_index  = (uint64_t*) 0; // per origin: position in its target's chain of come-froms
uint64_t* is_long      = (uint64_t*) 0; // per origin: 1 if it needs a jal zero to reach its target

uint64_t* is_call_target = (uint64_t*) 0; // per source instruction: 1 if some jal ra targets it
uint64_t* return_of      = (uint64_t*) 0; // per call target: source index of its return jalr

uint64_t* prefix_pc   = (uint64_t*) 0; // per source instruction: address of its come-froms
uint64_t* body_pc     = (uint64_t*) 0; // per source instruction: address of its translation
uint64_t* origin_pc   = (uint64_t*) 0; // per origin: address of the beq paired with its come-from
uint64_t* jump_pc     = (uint64_t*) 0; // per long origin: address of its jal zero
uint64_t* come_from_pc = (uint64_t*) 0; // per origin: address of its come-from in the chain
uint64_t* island_pc   = (uint64_t*) 0; // per long origin: address of the come-from of its jal zero

uint64_t trailer_pc   = 0; // address of the exit code after the translated code
uint64_t exit_jump_pc = 0; // address of the jal zero in the prologue that reaches it

uint64_t dry_run         = 0; // 1 while laying out, counting instead of emitting
uint64_t translated_size = 0; // bytes counted or emitted so far
uint64_t translated_pc   = 0; // address of the next translated instruction

uint64_t new_code_size  = 0; // code size of the RISC-R binary
uint64_t new_data_start = 0; // data segment start of the RISC-R binary
uint64_t new_gp_value   = 0; // global pointer of the RISC-R binary
uint64_t new_gp_upper   = 0; // its lui immediate
uint64_t new_gp_lower   = 0; // its addi immediate

uint64_t number_of_long_origins = 0; // for reporting
uint64_t number_of_history_slots = 0; // static count of pushes


// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------ RISC-R SYSCALLS ------------------------
// -----------------------------------------------------------------

uint64_t* allocate_tape();

uint64_t* new_tape(uint64_t fd, uint64_t input);
void      reset_tape(uint64_t* tape);
void      reset_tapes();

uint64_t* get_tape(uint64_t fd);

uint64_t* tape_buffer_word(uint64_t* context, uint64_t vaddr);

void     fill_input_tape(uint64_t* tape, uint64_t head, uint64_t size);
uint64_t bytes_on_input_tape(uint64_t* tape, uint64_t head, uint64_t size);

void add_syscall_result(uint64_t* context, uint64_t result);

void implement_reversible_exit(uint64_t* context);
void implement_reversible_read(uint64_t* context);
void implement_reversible_write(uint64_t* context);
void implement_reversible_openat(uint64_t* context);
void implement_reversible_brk(uint64_t* context);

// RISC-R tapes: files are part of the machine state, see riscr.md

// tape
// +---+--------+
// | 0 | memory | pointer to tape memory of MAX_TAPE_SIZE bytes
// | 1 | length | number of words transferred between file and tape
// | 2 | head   | next word on tape to exchange with or append from memory
// | 3 | end    | size of file in bytes once its end was read, else UINT64_MAX
// | 4 | fd     | file descriptor on host, -1 if the file is not open
// | 5 | input  | 1 if tape is filled from file, 0 if tape is written to file
// +---+--------+

uint64_t* get_tape_memory(uint64_t* tape) { return (uint64_t*) *tape; }
uint64_t  get_tape_length(uint64_t* tape) { return             *(tape + 1); }
uint64_t  get_tape_head(uint64_t* tape)   { return             *(tape + 2); }
uint64_t  get_tape_end(uint64_t* tape)    { return             *(tape + 3); }
uint64_t  get_tape_fd(uint64_t* tape)     { return             *(tape + 4); }
uint64_t  is_input_tape(uint64_t* tape)   { return             *(tape + 5); }

void set_tape_memory(uint64_t* tape, uint64_t* memory) { *tape       = (uint64_t) memory; }
void set_tape_length(uint64_t* tape, uint64_t length)  { *(tape + 1) = length; }
void set_tape_head(uint64_t* tape, uint64_t head)      { *(tape + 2) = head; }
void set_tape_end(uint64_t* tape, uint64_t end)        { *(tape + 3) = end; }
void set_tape_fd(uint64_t* tape, uint64_t fd)          { *(tape + 4) = fd; }
void set_input_tape(uint64_t* tape, uint64_t input)    { *(tape + 5) = input; }

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t MAX_TAPE_SIZE       = 8388608; // 8MB per tape: selfie reads one byte per read, one word on the tape
uint64_t MAX_NUMBER_OF_TAPES = 64;      // including standard input, output, and error

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* tapes           = (uint64_t*) 0; // tapes indexed by RISC-R file descriptors
uint64_t  number_of_tapes = 0;             // next RISC-R file descriptor, 3 after reset

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------    A R C H I T E C T U R E    -----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------- RISC-R INSTRUCTIONS ----------------------
// -----------------------------------------------------------------

uint64_t instruction_address();
void     continue_at(uint64_t address);

uint64_t is_distinct_rd(uint64_t rs1, uint64_t rs2);
uint64_t update_rd(uint64_t value);
uint64_t flip_rd(uint64_t value);

uint64_t is_come_from(uint64_t target, uint64_t origin);

void do_riscr_lui();
void do_riscr_addi();

void do_riscr_add();
void do_riscr_sub();
void do_riscr_mul();
void do_riscr_divu();
void do_riscr_remu();
void do_riscr_sltu();

uint64_t do_riscr_load();

void do_riscr_beq();
void do_riscr_jal();
void do_riscr_jalr();

void do_riscr_ecall();

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void init_reversible_interpreter();

uint64_t fetch_instruction(uint64_t vaddr);

void fetch_reversibly();
void execute_reversibly();

void run_reversibly_until_exception();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t EXCEPTION_IRREVERSIBLEINSTRUCTION = 10; // extends mipster's exceptions

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t reverse = 0; // flag for executing RISC-R code backward

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

void reset_reversible_registers_profile();

void boot_reversibly(uint64_t megabytes);

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

uint64_t* reversible_switch(uint64_t* to_context, uint64_t timeout);

uint64_t handle_reversible_system_call(uint64_t* context);
uint64_t handle_reversible_exception(uint64_t* context);

uint64_t riscr(uint64_t* to_context);
uint64_t riscr_backward(uint64_t* to_context, uint64_t steps);

uint64_t next_mapped_page(uint64_t page);
void     take_initial_snapshot();
uint64_t is_initial_state_restored();

uint64_t selfie_run_reversibly();

// ------------------------ GLOBAL VARIABLES -----------------------

// snapshot of the initial machine state, see take_initial_snapshot

uint64_t  snapshot_pc            = 0;
uint64_t* snapshot_registers     = (uint64_t*) 0;
uint64_t  snapshot_program_break = 0;

uint64_t  snapshot_number_of_pages = 0;
uint64_t* snapshot_pages           = (uint64_t*) 0; // page numbers, ascending
uint64_t* snapshot_memory          = (uint64_t*) 0; // page contents

uint64_t  snapshot_number_of_tapes = 0;
uint64_t* snapshot_tape_heads      = (uint64_t*) 0;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------     L I B R A R Y     ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------- EXCLUSIVE OR --------------------------
// -----------------------------------------------------------------

void init_xor_table() {
  uint64_t a;
  uint64_t b;

  // C* has no bitwise operators: tabulate exclusive or of bytes
  // using bitwise_xor(a, b) == 2 * bitwise_xor(a / 2, b / 2) + (a + b) % 2

  xor_table = (char*) zmalloc(256 * 256);

  a = 0;

  while (a < 256) {
    b = 0;

    while (b < 256) {
      store_character(xor_table, a * 256 + b,
        left_shift(load_character(xor_table, (a / 2) * 256 + b / 2), 1) + (a + b) % 2);

      b = b + 1;
    }

    a = a + 1;
  }
}

uint64_t bitwise_xor(uint64_t a, uint64_t b) {
  uint64_t x;
  uint64_t i;

  if (xor_table == (char*) 0)
    init_xor_table();

  x = 0;
  i = 0;

  // byte-wise exclusive or; the loaded character is masked because
  // with gcc char is signed and bytes >= 128 would be sign-extended
  while (i < SIZEOFUINT64INBITS) {
    x = x + left_shift(get_bits(load_character(xor_table, get_bits(a, i, 8) * 256 + get_bits(b, i, 8)), 0, 8), i);

    i = i + 8;
  }

  return x;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------    C O M P I L E R    ---------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// -------------------------- TRANSLATOR ---------------------------
// -----------------------------------------------------------------

void translation_error(uint64_t i, char* message) {
  printf("%s: cannot translate %s: %s at instruction %lu (address 0x%lX)\n", selfie_name,
    binary_name, message, i, code_start + i * INSTRUCTIONSIZE);

  exit(EXITCODE_COMPILERERROR);
}

uint64_t is_reserved_register(uint64_t reg) {
  // the translated program owns s2-s7, which starc never uses
  if (reg >= REG_HP)
    if (reg <= REG_Y)
      return 1;

  return 0;
}

void put_instruction(uint64_t instruction) {
  // in a dry run only count, otherwise emit into code_binary
  if (dry_run == 0)
    emit_instruction(instruction);

  translated_size = translated_size + INSTRUCTIONSIZE;
  translated_pc   = translated_pc + INSTRUCTIONSIZE;
}

void put_lui(uint64_t reg, uint64_t immediate) {
  if (dry_run)
    put_instruction(0);
  else
    put_instruction(encode_u_format(immediate, reg, OP_LUI));
}

void put_addi(uint64_t reg, uint64_t rs, uint64_t immediate) {
  if (dry_run)
    put_instruction(0);
  else
    put_instruction(encode_i_format(immediate, rs, F3_ADDI, reg, OP_IMM));
}

void put_op(uint64_t instruction_id, uint64_t reg, uint64_t rs, uint64_t rt) {
  // add, sub, mul, divu, remu, sltu with destination reg and sources rs, rt
  if (dry_run)
    put_instruction(0);
  else if (instruction_id == ADD)
    put_instruction(encode_r_format(F7_ADD, rt, rs, F3_ADD, reg, OP_OP));
  else if (instruction_id == SUB)
    put_instruction(encode_r_format(F7_SUB, rt, rs, F3_SUB, reg, OP_OP));
  else if (instruction_id == MUL)
    put_instruction(encode_r_format(F7_MUL, rt, rs, F3_MUL, reg, OP_OP));
  else if (instruction_id == DIVU)
    put_instruction(encode_r_format(F7_DIVU, rt, rs, F3_DIVU, reg, OP_OP));
  else if (instruction_id == REMU)
    put_instruction(encode_r_format(F7_REMU, rt, rs, F3_REMU, reg, OP_OP));
  else if (instruction_id == SLTU)
    put_instruction(encode_r_format(F7_SLTU, rt, rs, F3_SLTU, reg, OP_OP));
  else
    translation_error(0, "unknown arithmetic instruction");
}

void put_add(uint64_t reg, uint64_t rs, uint64_t rt) {
  put_op(ADD, reg, rs, rt);
}

void put_sub(uint64_t reg, uint64_t rs, uint64_t rt) {
  put_op(SUB, reg, rs, rt);
}

void put_ld(uint64_t reg, uint64_t rs, uint64_t immediate) {
  // RISC-R ld: exchange reg with the memory word at rs + immediate
  if (dry_run)
    put_instruction(0);
  else
    put_instruction(encode_i_format(immediate, rs, F3_LD, reg, OP_LOAD));
}

void put_beq(uint64_t rs, uint64_t rt, uint64_t immediate) {
  if (dry_run)
    put_instruction(0);
  else
    put_instruction(encode_b_format(immediate, rt, rs, F3_BEQ, OP_BRANCH));
}

void put_jal(uint64_t reg, uint64_t immediate) {
  if (dry_run)
    put_instruction(0);
  else
    put_instruction(encode_j_format(immediate, reg, OP_JAL));
}

void put_jalr(uint64_t reg, uint64_t rs, uint64_t immediate) {
  if (dry_run)
    put_instruction(0);
  else
    put_instruction(encode_i_format(immediate, rs, F3_JALR, reg, OP_JALR));
}

void put_ecall() {
  if (dry_run)
    put_instruction(0);
  else
    put_instruction(encode_i_format(F12_ECALL, REG_ZR, F3_ECALL, REG_ZR, OP_SYSTEM));
}

void put_push(uint64_t reg) {
  // exchange reg with the zeroed slot at the history pointer, reg becomes zero
  put_ld(reg, REG_HP, 0);
  put_addi(REG_HP, REG_ZR, WORDSIZE);

  if (dry_run == 0)
    number_of_history_slots = number_of_history_slots + 1;
}

void put_pop(uint64_t reg) {
  // inverse of push: reg must be zero, the slot becomes zero
  put_addi(REG_HP, REG_ZR, -WORDSIZE);
  put_ld(reg, REG_HP, 0);
}

void put_source(uint64_t reg) {
  // the decoded source instruction with destination reg, which must be zero
  if (is == LUI)
    put_lui(reg, imm);
  else if (is == ADDI)
    put_addi(reg, rs1, imm);
  else
    put_op(is, reg, rs1, rs2);
}

void decode_source(uint64_t i) {
  // decode instruction i once, then reuse the decoded fields
  ir = *(source_code + i);

  if (*(source_is + i) == 0) {
    decode();

    *(source_is + i)  = is;
    *(source_rd + i)  = rd;
    *(source_rs1 + i) = rs1;
    *(source_rs2 + i) = rs2;
    *(source_imm + i) = imm;
  } else {
    is  = *(source_is + i);
    rd  = *(source_rd + i);
    rs1 = *(source_rs1 + i);
    rs2 = *(source_rs2 + i);
    imm = *(source_imm + i);
  }
}

uint64_t origin_target(uint64_t i) {
  if (*(origin_kind + i) == ORIGIN_SYNTHETIC)
    return i + 1;
  else
    return *(target_of + i);
}

uint64_t syscall_number(uint64_t i) {
  // starc loads the system call number right before the ecall
  if (i > 0) {
    decode_source(i - 1);

    if (is == ADDI)
      if (rd == REG_A7)
        if (rs1 == REG_ZR)
          return imm;
  }

  translation_error(i, "ecall without system call number");

  return 0;
}

void load_source() {
  uint64_t i;

  number_of_source_instructions = code_size / INSTRUCTIONSIZE;

  source_code = zmalloc(number_of_source_instructions * sizeof(uint64_t));

  i = 0;

  while (i < number_of_source_instructions) {
    *(source_code + i) = load_instruction(i * INSTRUCTIONSIZE);

    i = i + 1;
  }
}

void classify_source(uint64_t i) {
  uint64_t target;

  decode_source(i);

  *(kind + i)        = TK_COPY;
  *(target_of + i)   = NONE;
  *(origin_kind + i) = ORIGIN_NONE;

  if (is == LUI) {
    if (is_reserved_register(rd))
      translation_error(i, "reserved register");

    if (rd != REG_ZR)
      *(kind + i) = TK_PUSHOP;
  } else if (is == ADDI) {
    if (or(is_reserved_register(rd), is_reserved_register(rs1)))
      translation_error(i, "reserved register");

    if (rd == REG_ZR)
      *(kind + i) = TK_COPY;
    else if (rd == rs1)
      *(kind + i) = TK_INPLACE;
    else
      *(kind + i) = TK_PUSHOP;
  } else if (or(or(is == ADD, is == SUB), or(or(is == MUL, is == DIVU), or(is == REMU, is == SLTU)))) {
    if (or(is_reserved_register(rd), or(is_reserved_register(rs1), is_reserved_register(rs2))))
      translation_error(i, "reserved register");

    if (rd == REG_ZR)
      *(kind + i) = TK_COPY;
    else if (and(rd != rs1, rd != rs2))
      *(kind + i) = TK_PUSHOP;
    else if (is == ADD) {
      // rd += the other source
      if (rs1 != rs2)
        *(kind + i) = TK_INPLACE;
      else
        *(kind + i) = TK_SCRATCH;
    } else if (is == SUB) {
      // rd -= rs2
      if (and(rd == rs1, rd != rs2))
        *(kind + i) = TK_INPLACE;
      else
        *(kind + i) = TK_SCRATCH;
    } else
      *(kind + i) = TK_SCRATCH;
  } else if (is == LOAD) {
    if (or(is_reserved_register(rd), is_reserved_register(rs1)))
      translation_error(i, "reserved register");

    if (rd == REG_ZR)
      *(kind + i) = TK_COPY;
    else if (rd != rs1)
      *(kind + i) = TK_LOAD;
    else
      *(kind + i) = TK_LOADSAME;
  } else if (is == STORE) {
    if (or(is_reserved_register(rs1), is_reserved_register(rs2)))
      translation_error(i, "reserved register");

    *(kind + i) = TK_STORE;
  } else if (is == BEQ) {
    if (or(is_reserved_register(rs1), is_reserved_register(rs2)))
      translation_error(i, "reserved register");

    target = (i * INSTRUCTIONSIZE + imm) / INSTRUCTIONSIZE;

    if (target >= number_of_source_instructions)
      translation_error(i, "branch target outside of code");

    *(kind + i)        = TK_BEQ;
    *(target_of + i)   = target;
    *(origin_kind + i) = ORIGIN_BEQ;
  } else if (is == JAL) {
    target = (i * INSTRUCTIONSIZE + imm) / INSTRUCTIONSIZE;

    if (target >= number_of_source_instructions)
      translation_error(i, "jump target outside of code");

    if (rd == REG_ZR) {
      *(kind + i)        = TK_JALZ;
      *(target_of + i)   = target;
      *(origin_kind + i) = ORIGIN_JALZ;
    } else if (rd == REG_RA) {
      *(kind + i)      = TK_CALL;
      *(target_of + i) = target;

      *(is_call_target + target) = 1;
    } else
      translation_error(i, "jal with unexpected link register");
  } else if (is == JALR) {
    if (and(rd == REG_ZR, and(rs1 == REG_RA, imm == 0)))
      *(kind + i) = TK_RET;
    else
      translation_error(i, "jalr other than return");
  } else if (is == ECALL) {
    *(kind + i) = TK_ECALL;

    syscall_number(i);
  } else
    translation_error(i, "unknown instruction");
}

void analyze_source() {
  uint64_t n;
  uint64_t i;
  uint64_t t;
  uint64_t k;
  uint64_t o;

  n = number_of_source_instructions;

  // starc replaces the bootstrap by addi a0,zero,0 if procedures are undefined
  if (get_opcode(*source_code) == OP_IMM)
    if (get_rd(*source_code) == REG_A0)
      translation_error(0, "binary has undefined procedures, compile with selfie.h");

  kind         = zmalloc(n * sizeof(uint64_t));
  target_of    = zmalloc(n * sizeof(uint64_t));
  origin_kind  = zmalloc(n * sizeof(uint64_t));
  first_origin = zmalloc(n * sizeof(uint64_t));
  next_origin  = zmalloc(n * sizeof(uint64_t));
  chain_index  = zmalloc(n * sizeof(uint64_t));
  is_long      = zmalloc(n * sizeof(uint64_t));

  is_call_target = zmalloc(n * sizeof(uint64_t));
  return_of      = zmalloc(n * sizeof(uint64_t));

  prefix_pc    = zmalloc(n * sizeof(uint64_t));
  body_pc      = zmalloc(n * sizeof(uint64_t));
  origin_pc    = zmalloc(n * sizeof(uint64_t));
  jump_pc      = zmalloc(n * sizeof(uint64_t));
  come_from_pc = zmalloc(n * sizeof(uint64_t));
  island_pc    = zmalloc(n * sizeof(uint64_t));

  // decode and classify, keeping the decoded fields
  source_is  = zmalloc(n * sizeof(uint64_t));
  source_rd  = zmalloc(n * sizeof(uint64_t));
  source_rs1 = zmalloc(n * sizeof(uint64_t));
  source_rs2 = zmalloc(n * sizeof(uint64_t));
  source_imm = zmalloc(n * sizeof(uint64_t));

  body_length = zmalloc(n * sizeof(uint64_t));

  i = 0;

  while (i < n) {
    classify_source(i);

    *(first_origin + i) = NONE;

    i = i + 1;
  }

  // the global pointer is loaded first, with lui and addi into t0, see emit_bootstrapping
  decode_source(0);

  if (or(is != LUI, rd != REG_T0))
    translation_error(0, "expected lui t0 loading the global pointer");

  decode_source(1);

  if (or(is != ADDI, or(rd != REG_T0, rs1 != REG_T0)))
    translation_error(1, "expected addi t0 loading the global pointer");

  // falling into a procedure entry becomes a jump over its come-from
  i = 0;

  while (i < n) {
    if (*(is_call_target + i)) {
      if (i == 0)
        translation_error(i, "procedure entry at code start");

      if (and(*(kind + i - 1) != TK_RET, *(kind + i - 1) != TK_JALZ)) {
        if (*(origin_kind + i - 1) != ORIGIN_NONE)
          translation_error(i - 1, "branch falls into a procedure entry");

        *(origin_kind + i - 1) = ORIGIN_SYNTHETIC;
      }

      // the return of the procedure is its first jalr
      t = i;

      while (t < n) {
        if (*(kind + t) == TK_RET) {
          *(return_of + i) = t;

          t = n;
        } else
          t = t + 1;
      }

      if (*(return_of + i) == 0)
        translation_error(i, "procedure without return");
    }

    i = i + 1;
  }

  // origins in source order per target
  i = n;

  while (i > 0) {
    i = i - 1;

    if (*(origin_kind + i) != ORIGIN_NONE) {
      t = origin_target(i);

      if (*(is_call_target + t))
        if (*(origin_kind + i) != ORIGIN_SYNTHETIC)
          translation_error(i, "branch to a procedure entry");

      *(next_origin + i)  = *(first_origin + t);
      *(first_origin + t) = i;
    }
  }

  i = 0;

  while (i < n) {
    o = *(first_origin + i);
    k = 0;

    while (o != NONE) {
      *(chain_index + o) = k;

      k = k + 1;
      o = *(next_origin + o);
    }

    i = i + 1;
  }
}

void put_prologue() {
  uint64_t g;
  uint64_t heap_start;
  uint64_t hop_pc;

  // one, history pointer, and program break register
  put_addi(REG_ONE, REG_ZR, 1);

  heap_start = round_up(new_data_start + data_size, PAGESIZE);

  if (heap_start >= two_to_the_power_of(31))
    translation_error(0, "heap start exceeds 2GB");

  put_lui(REG_HP, heap_start / PAGESIZE);

  g = 0;

  while (g < HISTORY_GIGABYTES) {
    // 2^18 * 2^12 = 1GB
    put_lui(REG_BRK, two_to_the_power_of(18));

    g = g + 1;
  }

  put_add(REG_BRK, REG_HP, REG_ZR);

  // allocate the history stack by growing the heap to the program break register
  put_add(REG_A1, REG_BRK, REG_ZR);
  put_addi(REG_A7, REG_ZR, SYSCALL_BRK);
  put_ecall();

  // a0 holds the previous program break, zero if allocation failed:
  // exit through the trailer at the end of the code
  put_addi(REG_FL, REG_ZR, 1);
  put_beq(REG_A0, REG_ZR, 4 * INSTRUCTIONSIZE);
  put_addi(REG_FL, REG_ZR, -1);
  put_addi(REG_FL, REG_ZR, 1);
  hop_pc = translated_pc;
  put_beq(REG_FL, REG_ONE, 3 * INSTRUCTIONSIZE);
  put_beq(REG_A0, REG_ZR, -4 * INSTRUCTIONSIZE);
  exit_jump_pc = translated_pc;
  put_jal(REG_ZR, trailer_pc - translated_pc);
  put_beq(REG_FL, REG_ONE, hop_pc - translated_pc);
  put_addi(REG_FL, REG_ZR, -1);

  // uncompute a0, a1, and a7
  put_sub(REG_A0, REG_ZR, REG_HP);
  put_sub(REG_A1, REG_ZR, REG_BRK);
  put_addi(REG_A7, REG_ZR, -SYSCALL_BRK);
}

void put_trailer() {
  // reached from the prologue only if the history stack could not be allocated
  put_jal(REG_ZR, exit_jump_pc - translated_pc);
  put_addi(REG_A7, REG_ZR, SYSCALL_EXIT - SYSCALL_BRK);
  put_sub(REG_A1, REG_ZR, REG_BRK);
  put_addi(REG_A1, REG_ZR, EXITCODE_OUTOFVIRTUALMEMORY);
  put_ecall();
}

void put_prefix(uint64_t i) {
  uint64_t o;
  uint64_t m;
  uint64_t k;
  uint64_t chain_pc;
  uint64_t hop_pc;
  uint64_t island_end_pc;

  // come-froms in front of the translation of instruction i

  if (*(is_call_target + i))
    // callers land after this come-from
    put_jalr(REG_RA, REG_RA, 0);

  if (*(first_origin + i) == NONE)
    return;

  m = 0;
  o = *(first_origin + i);

  while (o != NONE) {
    if (*(is_long + o))
      m = m + 1;

    o = *(next_origin + o);
  }

  if (m > 0)
    chain_pc = translated_pc + (4 + 2 * m) * INSTRUCTIONSIZE;
  else
    chain_pc = translated_pc;

  o = *(first_origin + i);

  while (o != NONE) {
    *(come_from_pc + o) = chain_pc + *(chain_index + o) * 2 * INSTRUCTIONSIZE;

    o = *(next_origin + o);
  }

  if (m > 0) {
    // islands for long origins, hopped over by the fall-through path
    put_addi(REG_FL, REG_ZR, 1);

    hop_pc        = translated_pc;
    island_end_pc = hop_pc + (1 + 2 * m) * INSTRUCTIONSIZE;

    put_beq(REG_FL, REG_ONE, island_end_pc - hop_pc);

    o = *(first_origin + i);

    while (o != NONE) {
      if (*(is_long + o)) {
        // come-from of the long jump, then a short hop into the chain
        *(island_pc + o) = translated_pc;

        put_jal(REG_ZR, *(jump_pc + o) - translated_pc);

        *(origin_pc + o) = translated_pc;

        put_beq(REG_FL, REG_ONE, *(come_from_pc + o) - translated_pc);
      }

      o = *(next_origin + o);
    }

    put_beq(REG_FL, REG_ONE, hop_pc - translated_pc);
    put_addi(REG_FL, REG_ZR, -1);
  }

  // chain of come-froms, one per origin, with the flag decremented in between
  o = *(first_origin + i);
  k = 0;

  while (o != NONE) {
    if (k > 0)
      put_addi(REG_FL, REG_ZR, -1);

    put_beq(REG_FL, REG_ONE, *(origin_pc + o) - translated_pc);

    k = k + 1;
    o = *(next_origin + o);
  }

  // the flag records which way control arrived
  put_push(REG_FL);
}

void put_origin(uint64_t i) {
  uint64_t conditional;
  uint64_t cf;

  // a transfer to the come-from of i in the chain of its target

  conditional = *(origin_kind + i) == ORIGIN_BEQ;

  cf = *(come_from_pc + i);

  put_addi(REG_FL, REG_ZR, 1);

  if (*(is_long + i) == 0) {
    *(origin_pc + i) = translated_pc;

    if (conditional)
      put_beq(rs1, rs2, cf - translated_pc);
    else
      put_beq(REG_FL, REG_ONE, cf - translated_pc);

    if (conditional)
      put_addi(REG_FL, REG_ZR, -1);
  } else if (conditional) {
    // branch into a local island holding the long jump, hopped over by the fall-through path
    put_beq(rs1, rs2, 4 * INSTRUCTIONSIZE);
    put_addi(REG_FL, REG_ZR, -1);
    put_addi(REG_FL, REG_ZR, 1);
    put_beq(REG_FL, REG_ONE, 3 * INSTRUCTIONSIZE);
    put_beq(rs1, rs2, -4 * INSTRUCTIONSIZE);

    *(jump_pc + i) = translated_pc;

    put_jal(REG_ZR, *(island_pc + i) - translated_pc);
    put_beq(REG_FL, REG_ONE, -3 * INSTRUCTIONSIZE);
    put_addi(REG_FL, REG_ZR, -1);
  } else {
    *(jump_pc + i) = translated_pc;

    put_jal(REG_ZR, *(island_pc + i) - translated_pc);
  }
}

void put_syscall(uint64_t i) {
  uint64_t number;

  number = syscall_number(i);

  // RISC-R system calls take their arguments in a1-a3 and add their result into a0, see riscr.md

  if (number == SYSCALL_EXIT) {
    put_push(REG_A1);
    put_addi(REG_A1, REG_A0, 0);
    put_ecall();
  } else if (or(number == SYSCALL_READ, number == SYSCALL_WRITE)) {
    put_push(REG_A3);
    put_addi(REG_A3, REG_A2, 0);
    put_push(REG_A2);
    put_addi(REG_A2, REG_A1, 0);
    put_push(REG_A1);
    put_addi(REG_A1, REG_A0, 0);
    put_push(REG_A0);
    put_ecall();
  } else if (number == SYSCALL_OPENAT) {
    // directory descriptor in a0 is dropped, filename, flags, and mode are in a1-a3 already
    put_push(REG_A0);
    put_ecall();
  } else if (number == SYSCALL_BRK) {
    // RISC-U brk(a0) returns the new break on success and the current break otherwise,
    // in particular brk(0) returns the current break; RISC-R brk(a1) requires a0 == 0 and
    // adds the previous break into a0 on success; the program break register tracks the break
    put_push(REG_A1);
    put_addi(REG_A1, REG_A0, 0);
    put_push(REG_A0);
    put_ecall();
    put_addi(REG_FL, REG_ZR, 1);
    put_beq(REG_A0, REG_ZR, 9 * INSTRUCTIONSIZE);
    put_addi(REG_FL, REG_ZR, -1);
    // success: a0 == previous break, new break is a1
    put_sub(REG_A0, REG_ZR, REG_BRK);
    put_push(REG_BRK);
    put_add(REG_BRK, REG_A1, REG_ZR);
    put_add(REG_A0, REG_A1, REG_ZR);
    put_addi(REG_FL, REG_ZR, 1);
    put_beq(REG_FL, REG_ONE, 4 * INSTRUCTIONSIZE);
    // failure: a0 == 0, result is the current break
    put_beq(REG_FL, REG_ONE, -9 * INSTRUCTIONSIZE);
    put_addi(REG_FL, REG_ZR, -1);
    put_add(REG_A0, REG_BRK, REG_ZR);
    // join
    put_beq(REG_FL, REG_ONE, -4 * INSTRUCTIONSIZE);
    put_push(REG_FL);
  } else
    // context switching is unsupported, riscr refuses the ecall at run time
    put_ecall();
}

void put_body(uint64_t i) {
  uint64_t k;
  uint64_t t;

  decode_source(i);

  k = *(kind + i);

  if (k == TK_COPY)
    put_instruction(ir);
  else if (k == TK_INPLACE) {
    if (is == ADDI) {
      if (i == 1)
        // global pointer of the RISC-R binary
        put_addi(rd, REG_ZR, new_gp_lower);
      else
        put_addi(rd, REG_ZR, imm);
    } else if (is == ADD) {
      if (rd == rs1)
        put_add(rd, rs2, REG_ZR);
      else
        put_add(rd, rs1, REG_ZR);
    } else
      put_sub(rd, REG_ZR, rs2);
  } else if (k == TK_PUSHOP) {
    put_push(rd);

    if (i == 0)
      // global pointer of the RISC-R binary
      put_lui(rd, new_gp_upper);
    else
      put_source(rd);
  } else if (k == TK_SCRATCH) {
    // compute into the zeroed scratch register, then exchange through the history slot
    put_source(REG_X);
    put_ld(REG_X, REG_HP, 0);
    put_ld(rd, REG_HP, 0);
    put_addi(REG_HP, REG_ZR, WORDSIZE);

    if (dry_run == 0)
      number_of_history_slots = number_of_history_slots + 1;
  } else if (k == TK_LOAD) {
    // copy the memory word through the scratch register
    put_push(rd);
    put_ld(REG_X, rs1, imm);
    put_add(rd, REG_X, REG_ZR);
    put_ld(REG_X, rs1, imm);
  } else if (k == TK_LOADSAME) {
    // rd is the address register: copy first, then exchange through the history slot
    put_ld(REG_X, rs1, imm);
    put_add(REG_Y, REG_X, REG_ZR);
    put_ld(REG_X, rs1, imm);
    put_ld(REG_Y, REG_HP, 0);
    put_ld(rd, REG_HP, 0);
    put_addi(REG_HP, REG_ZR, WORDSIZE);

    if (dry_run == 0)
      number_of_history_slots = number_of_history_slots + 1;
  } else if (k == TK_STORE) {
    // move the memory word onto the history stack, then copy rs2 into memory
    put_ld(REG_X, rs1, imm);
    put_ld(REG_X, REG_HP, 0);
    put_add(REG_X, rs2, REG_ZR);
    put_ld(REG_X, rs1, imm);
    put_addi(REG_HP, REG_ZR, WORDSIZE);

    if (dry_run == 0)
      number_of_history_slots = number_of_history_slots + 1;
  } else if (or(k == TK_BEQ, k == TK_JALZ))
    put_origin(i);
  else if (k == TK_CALL) {
    // push the link register, call, come-from of the return, then exchange the
    // zeroed link register with the word below hp: the callee's last push, which
    // starc's code never reads after a call, or ra itself if the callee pushed
    // nothing; either way the slot is freed, see riscr.md
    t = *(target_of + i);

    put_push(REG_RA);
    put_jal(REG_RA, *(prefix_pc + t) - translated_pc);
    put_jal(REG_RA, *(body_pc + *(return_of + t)) - translated_pc);
    put_pop(REG_RA);
  } else if (k == TK_RET)
    put_jalr(REG_RA, REG_RA, 0);
  else if (k == TK_ECALL)
    put_syscall(i);

  if (*(origin_kind + i) == ORIGIN_SYNTHETIC)
    // jump over the come-from of the procedure entry that follows
    put_origin(i);
}

void layout_translation() {
  uint64_t changed;
  uint64_t pass;
  uint64_t n;
  uint64_t i;
  uint64_t d;
  uint64_t lower;
  uint64_t upper;

  n = number_of_source_instructions;

  dry_run = 1;
  changed = 1;
  pass    = 0;

  while (changed) {
    changed = 0;

    translated_pc = code_start;

    put_prologue();

    i = 0;

    while (i < n) {
      *(prefix_pc + i) = translated_pc;

      put_prefix(i);

      *(body_pc + i) = translated_pc;

      if (pass == 0)
        put_body(i);
      else if (*(origin_kind + i) != ORIGIN_NONE)
        // only origins change their length when they become long
        put_body(i);
      else
        translated_pc = translated_pc + *(body_length + i);

      *(body_length + i) = translated_pc - *(body_pc + i);

      i = i + 1;
    }

    pass = pass + 1;

    trailer_pc = translated_pc;

    put_trailer();

    // origins whose come-froms are out of reach of a beq become long
    i = 0;

    while (i < n) {
      if (*(origin_kind + i) != ORIGIN_NONE)
        if (*(is_long + i) == 0) {
          d = *(come_from_pc + i) - *(origin_pc + i);

          if (not(is_signed_integer(d, 13))) {
            *(is_long + i) = 1;

            number_of_long_origins = number_of_long_origins + 1;

            changed = 1;
          }
        }

      i = i + 1;
    }

    new_code_size  = translated_pc - code_start;
    new_data_start = round_up(code_start + new_code_size, PAGESIZE);
    new_gp_value   = new_data_start + data_size;
  }

  dry_run = 0;

  if (new_code_size > MAX_CODE_SIZE)
    translation_error(0, "translated code exceeds maximum code size");

  if (new_gp_value >= two_to_the_power_of(31) - two_to_the_power_of(12))
    translation_error(0, "global pointer exceeds 2GB");

  // load the global pointer as starc does, see load_upper_value
  lower = get_bits(new_gp_value,  0, 12);
  upper = get_bits(new_gp_value, 12, 20);

  if (lower >= two_to_the_power_of(11))
    upper = upper + 1;

  new_gp_upper = sign_extend(upper, 20);
  new_gp_lower = sign_extend(lower, 12);
}

void emit_translation() {
  uint64_t n;
  uint64_t i;

  n = number_of_source_instructions;

  code_binary      = zmalloc(MAX_CODE_SIZE);
  code_size        = 0;
  code_line_number = (uint64_t*) 0;

  translated_pc = code_start;

  put_prologue();

  i = 0;

  while (i < n) {
    if (translated_pc != *(prefix_pc + i))
      translation_error(i, "internal error: layout and emission disagree");

    put_prefix(i);

    if (translated_pc != *(body_pc + i))
      translation_error(i, "internal error: layout and emission disagree");

    put_body(i);

    i = i + 1;
  }

  if (translated_pc != trailer_pc)
    translation_error(n, "internal error: layout and emission disagree");

  put_trailer();

  if (code_size != new_code_size)
    translation_error(n, "internal error: layout and emission disagree");

  data_start = new_data_start;
  e_flags    = EF_RISCR;
}

uint64_t selfie_translate() {
  char* filename;
  uint64_t n;

  // argument is -t, the next argument names the RISC-R binary

  if (number_of_remaining_arguments() == 0)
    return EXITCODE_BADARGUMENTS;

  filename = get_argument();

  if (code_size == 0) {
    printf("%s: nothing to translate\n", selfie_name);

    return EXITCODE_BADARGUMENTS;
  } else if ((e_flags / EF_RISCR) % 2) {
    printf("%s: %s is a RISC-R binary already\n", selfie_name, binary_name);

    return EXITCODE_BADARGUMENTS;
  }

  n = code_size / INSTRUCTIONSIZE;

  printf("%s: translating %lu RISC-U instructions of %s into RISC-R in Bennett mode\n", selfie_name, n, binary_name);

  load_source();
  analyze_source();
  layout_translation();
  emit_translation();

  printf("%s: %lu RISC-R instructions, %lu.%lu per RISC-U instruction, ", selfie_name,
    code_size / INSTRUCTIONSIZE,
    code_size / INSTRUCTIONSIZE / n,
    (code_size / INSTRUCTIONSIZE * 10 / n) % 10);
  printf("%lu pushes in code, %lu long transfers, %luGB history stack\n",
    number_of_history_slots,
    number_of_long_origins,
    HISTORY_GIGABYTES);

  selfie_output(filename);

  return EXITCODE_NOERROR;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------ RISC-R SYSCALLS ------------------------
// -----------------------------------------------------------------

uint64_t* allocate_tape() {
  return smalloc(1 * sizeof(uint64_t*) + 5 * sizeof(uint64_t));
}

uint64_t* new_tape(uint64_t fd, uint64_t input) {
  uint64_t* tape;

  tape = allocate_tape();

  set_tape_memory(tape, zmalloc(MAX_TAPE_SIZE));

  reset_tape(tape);

  set_tape_fd(tape, fd);
  set_input_tape(tape, input);

  return tape;
}

void reset_tape(uint64_t* tape) {
  zero_memory(get_tape_memory(tape), MAX_TAPE_SIZE);

  set_tape_length(tape, 0);
  set_tape_head(tape, 0);
  set_tape_end(tape, UINT64_MAX);
}

void reset_tapes() {
  uint64_t fd;
  uint64_t* tape;

  if (tapes == (uint64_t*) 0)
    tapes = zmalloc(MAX_NUMBER_OF_TAPES * sizeof(uint64_t*));

  fd = 0;

  while (fd < MAX_NUMBER_OF_TAPES) {
    tape = (uint64_t*) *(tapes + fd);

    if (tape != (uint64_t*) 0) {
      reset_tape(tape);

      if (fd >= 3)
        // files are reopened when opened again
        set_tape_fd(tape, -1);
    } else if (fd < 3)
      // standard input, output, and error of riscr
      *(tapes + fd) = (uint64_t) new_tape(fd, fd == 0);

    fd = fd + 1;
  }

  number_of_tapes = 3;
}

uint64_t* get_tape(uint64_t fd) {
  uint64_t* tape;

  // tape of open file with RISC-R file descriptor fd, or 0

  if (fd < number_of_tapes) {
    tape = (uint64_t*) *(tapes + fd);

    if (tape != (uint64_t*) 0)
      if (not(signed_less_than(get_tape_fd(tape), 0)))
        return tape;
  }

  return (uint64_t*) 0;
}

uint64_t* tape_buffer_word(uint64_t* context, uint64_t vaddr) {
  // physical address of memory word at vaddr, mapping its page if necessary

  if (is_virtual_address_valid(vaddr, WORDSIZE))
    if (is_data_stack_heap_address(context, vaddr)) {
      if (not(is_virtual_address_mapped(get_pt(context), vaddr))) {
        if (pavailable())
          map_page(context, page_of_virtual_address(vaddr), (uint64_t) palloc());
        else {
          printf("%s: tape buffer at virtual address 0x%08lX out of physical memory\n", selfie_name, vaddr);

          exit(EXITCODE_OUTOFPHYSICALMEMORY);
        }
      }

      return translate_virtual_to_physical(get_pt(context), vaddr);
    }

  printf("%s: tape buffer at virtual address 0x%08lX is invalid\n", selfie_name, vaddr);

  exit(EXITCODE_UNCAUGHTEXCEPTION);

  return (uint64_t*) 0;
}

void fill_input_tape(uint64_t* tape, uint64_t head, uint64_t size) {
  uint64_t words;
  uint64_t length;
  uint64_t bytes;
  uint64_t read_bytes;

  // read bytes from file onto zeroed input tape up to head + size bytes

  words  = round_up(size, WORDSIZE) / WORDSIZE;
  length = get_tape_length(tape);

  if (head + words > length) {
    if (get_tape_end(tape) == UINT64_MAX)
      if (length * WORDSIZE < head * WORDSIZE + size) {
        bytes = head * WORDSIZE + size - length * WORDSIZE;

        read_bytes = sign_extend(
          read(get_tape_fd(tape), (uint64_t*) ((uint64_t) get_tape_memory(tape) + length * WORDSIZE), bytes),
          SYSCALL_BITWIDTH);

        if (signed_less_than(read_bytes, bytes)) {
          // end of file
          if (signed_less_than(read_bytes, 0))
            read_bytes = 0;

          set_tape_end(tape, length * WORDSIZE + read_bytes);
        }
      }

    set_tape_length(tape, head + words);
  }
}

uint64_t bytes_on_input_tape(uint64_t* tape, uint64_t head, uint64_t size) {
  uint64_t end;

  // number of bytes a read of size bytes at head returns, recomputable backward

  end = get_tape_end(tape);

  if (end == UINT64_MAX)
    return size;
  else if (head * WORDSIZE >= end)
    return 0;
  else if (end - head * WORDSIZE < size)
    return end - head * WORDSIZE;
  else
    return size;
}

void add_syscall_result(uint64_t* context, uint64_t result) {
  // RISC-R system calls add their result into a0 forward and
  // subtract it backward, see riscr.md

  if (reverse) {
    *(get_regs(context) + REG_A0) = *(get_regs(context) + REG_A0) - result;

    set_pc(context, get_pc(context) - INSTRUCTIONSIZE);
  } else {
    *(get_regs(context) + REG_A0) = *(get_regs(context) + REG_A0) + result;

    set_pc(context, get_pc(context) + INSTRUCTIONSIZE);
  }

  if (debug_syscalls) {
    printf(" -> ");
    print_register_value(REG_A0);
    println();
  }
}

void implement_reversible_exit(uint64_t* context) {
  // parameter
  uint64_t signed_int_exit_code;

  if (debug_syscalls) {
    printf("(exit): ");
    print_register_hexadecimal(REG_A1);
    printf(" |- ->\n");
  }

  signed_int_exit_code = *(get_regs(context) + REG_A1);

  set_exit_code(context, sign_shrink(signed_int_exit_code, SYSCALL_BITWIDTH));
}

void implement_reversible_read(uint64_t* context) {
  // parameters
  uint64_t fd;
  uint64_t vbuffer;
  uint64_t size;

  uint64_t* tape;
  uint64_t words;
  uint64_t head;
  uint64_t result;
  uint64_t i;
  uint64_t* paddr;
  uint64_t word;

  if (debug_syscalls) {
    printf("(read): ");
    print_register_value(REG_A1);
    printf(",");
    print_register_hexadecimal(REG_A2);
    printf(",");
    print_register_value(REG_A3);
    printf(" |- ");
    print_register_value(REG_A0);
  }

  fd      = *(get_regs(context) + REG_A1);
  vbuffer = *(get_regs(context) + REG_A2);
  size    = *(get_regs(context) + REG_A3);

  // RISC-R read exchanges words between memory and input tape, see riscr.md

  tape = get_tape(fd);

  if (tape == (uint64_t*) 0)
    result = sign_shrink(-1, SYSCALL_BITWIDTH);
  else if (not(is_input_tape(tape)))
    result = sign_shrink(-1, SYSCALL_BITWIDTH);
  else {
    words = round_up(size, WORDSIZE) / WORDSIZE;
    head  = get_tape_head(tape);

    if (reverse) {
      if (head < words) {
        printf("%s: input tape rewound before its beginning\n", selfie_name);

        exit(EXITCODE_UNCAUGHTEXCEPTION);
      }

      head = head - words;
    } else {
      if (head + words > MAX_TAPE_SIZE / WORDSIZE) {
        printf("%s: input tape is full\n", selfie_name);

        exit(EXITCODE_OUTOFVIRTUALMEMORY);
      }

      fill_input_tape(tape, head, size);
    }

    result = bytes_on_input_tape(tape, head, size);

    i = 0;

    while (i < words) {
      paddr = tape_buffer_word(context, vbuffer + i * WORDSIZE);

      word = load_physical_memory(paddr);

      store_physical_memory(paddr, load_word(get_tape_memory(tape), (head + i) * WORDSIZE, 1));

      store_word(get_tape_memory(tape), (head + i) * WORDSIZE, 1, word);

      i = i + 1;
    }

    if (reverse)
      set_tape_head(tape, head);
    else
      set_tape_head(tape, head + words);
  }

  add_syscall_result(context, result);
}

void implement_reversible_write(uint64_t* context) {
  // parameters
  uint64_t fd;
  uint64_t vbuffer;
  uint64_t size;

  uint64_t* tape;
  uint64_t words;
  uint64_t head;
  uint64_t result;
  uint64_t i;
  uint64_t word;

  if (debug_syscalls) {
    printf("(write): ");
    print_register_value(REG_A1);
    printf(",");
    print_register_hexadecimal(REG_A2);
    printf(",");
    print_register_value(REG_A3);
    printf(" |- ");
    print_register_value(REG_A0);
  }

  fd      = *(get_regs(context) + REG_A1);
  vbuffer = *(get_regs(context) + REG_A2);
  size    = *(get_regs(context) + REG_A3);

  // RISC-R write appends words from memory to output tape, see riscr.md

  tape = get_tape(fd);

  if (tape == (uint64_t*) 0)
    result = sign_shrink(-1, SYSCALL_BITWIDTH);
  else if (is_input_tape(tape))
    result = sign_shrink(-1, SYSCALL_BITWIDTH);
  else {
    words = round_up(size, WORDSIZE) / WORDSIZE;
    head  = get_tape_head(tape);

    if (reverse) {
      if (head < words) {
        printf("%s: output tape rewound before its beginning\n", selfie_name);

        exit(EXITCODE_UNCAUGHTEXCEPTION);
      }

      head = head - words;

      i = 0;

      // erase words from output tape, they are still in memory
      while (i < words) {
        store_word(get_tape_memory(tape), (head + i) * WORDSIZE, 1, 0);

        i = i + 1;
      }

      set_tape_head(tape, head);
    } else {
      if (head + words > MAX_TAPE_SIZE / WORDSIZE) {
        printf("%s: output tape is full\n", selfie_name);

        exit(EXITCODE_OUTOFVIRTUALMEMORY);
      }

      if (size >= IO_buffer_size) {
        // integer-align and accommodate potentially needed null terminator
        IO_buffer_size = round_up(size + 1, sizeof(uint64_t));

        // buffer must be fully mapped for subsequent read syscalls with greater sizes
        IO_buffer = touch(smalloc(IO_buffer_size), IO_buffer_size);
      }

      // null-terminate buffer
      *(IO_buffer + size / sizeof(uint64_t)) = 0;

      i = 0;

      while (i < words) {
        word = load_physical_memory(tape_buffer_word(context, vbuffer + i * WORDSIZE));

        store_word(get_tape_memory(tape), (head + i) * WORDSIZE, 1, word);

        store_word(IO_buffer, i * WORDSIZE, 1, word);

        i = i + 1;
      }

      set_tape_head(tape, head + words);

      // output tape is also written to file
      write_to_printf(get_tape_fd(tape), IO_buffer, size);
    }

    result = size;
  }

  add_syscall_result(context, result);
}

void implement_reversible_openat(uint64_t* context) {
  // parameters
  uint64_t vfilename;
  uint64_t flags;
  uint64_t mode;

  uint64_t* tape;
  uint64_t fd;
  uint64_t result;

  if (debug_syscalls) {
    printf("(openat): ");
    print_register_hexadecimal(REG_A1);
    printf(",");
    print_register_hexadecimal(REG_A2);
    printf(",");
    print_register_octal(REG_A3);
    printf(" |- ");
    print_register_value(REG_A0);
  }

  vfilename = *(get_regs(context) + REG_A1);
  flags     = *(get_regs(context) + REG_A2);
  mode      = *(get_regs(context) + REG_A3);

  // RISC-R openat allocates the next file descriptor and its tape, see riscr.md

  if (reverse)
    number_of_tapes = number_of_tapes - 1;
  else if (number_of_tapes >= MAX_NUMBER_OF_TAPES) {
    printf("%s: too many open files\n", selfie_name);

    exit(EXITCODE_OUTOFVIRTUALMEMORY);
  }

  tape = (uint64_t*) *(tapes + number_of_tapes);

  if (not(reverse)) {
    if (tape != (uint64_t*) 0)
      if (not(signed_less_than(get_tape_fd(tape), 0)))
        // tape of a file opened before executing backward, keep it
        fd = get_tape_fd(tape);
      else
        fd = -1;
    else
      fd = -1;

    if (signed_less_than(fd, 0)) {
      // open file on host
      if (down_load_string(context, vfilename, filename_buffer)) {
        if (flags == LINUX_O_CREAT_TRUNC_WRONLY)
          // use correct flags for host operating system
          flags = O_CREAT_TRUNC_WRONLY;

        fd = sign_extend(open(filename_buffer, flags, mode), SYSCALL_BITWIDTH);
      }

      if (tape == (uint64_t*) 0) {
        tape = new_tape(fd, 0);

        *(tapes + number_of_tapes) = (uint64_t) tape;
      } else {
        reset_tape(tape);

        set_tape_fd(tape, fd);
      }

      if (flags == O_RDONLY)
        set_input_tape(tape, 1);
      else
        set_input_tape(tape, flags == 0);

      if (debug_open)
        printf("%s: opened file %s with flags 0x%lX and mode 0o%lo returning file descriptor %lu\n", selfie_name,
          filename_buffer, flags, mode, number_of_tapes);
    }
  }

  if (signed_less_than(get_tape_fd(tape), 0))
    result = sign_shrink(-1, SYSCALL_BITWIDTH);
  else
    result = number_of_tapes;

  if (not(reverse))
    number_of_tapes = number_of_tapes + 1;

  add_syscall_result(context, result);
}

void implement_reversible_brk(uint64_t* context) {
  // parameter
  uint64_t new_program_break;

  // local variable
  uint64_t previous_program_break;

  if (debug_syscalls) {
    printf("(brk): ");
    print_register_hexadecimal(REG_A1);
    printf(" |- ");
    print_register_hexadecimal(REG_A0);
  }

  new_program_break      = *(get_regs(context) + REG_A1);
  previous_program_break = get_program_break(context);

  // RISC-R brk adds the previous program break into a0 if it succeeds, see riscr.md

  if (reverse) {
    if (*(get_regs(context) + REG_A0) != 0) {
      // a0 holds the previous program break, restore it
      set_program_break(context, *(get_regs(context) + REG_A0));

      set_lc_malloc(context, get_lc_malloc(context) - 1);

      add_syscall_result(context, *(get_regs(context) + REG_A0));
    } else
      add_syscall_result(context, 0);
  } else if (new_program_break > previous_program_break) {
    if (try_brk(context, new_program_break) == new_program_break) {
      set_lc_malloc(context, get_lc_malloc(context) + 1);

      add_syscall_result(context, previous_program_break);
    } else
      add_syscall_result(context, 0);
  } else
    add_syscall_result(context, 0);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------    A R C H I T E C T U R E    -----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------- RISC-R INSTRUCTIONS ----------------------
// -----------------------------------------------------------------

uint64_t instruction_address() {
  // address of the executing instruction
  if (reverse)
    // executing backward: the instruction before pc
    return pc - INSTRUCTIONSIZE;
  else
    return pc;
}

void continue_at(uint64_t address) {
  // forward execution continues after address,
  // backward execution continues at address
  if (reverse)
    pc = address;
  else
    pc = address + INSTRUCTIONSIZE;
}

uint64_t is_distinct_rd(uint64_t rs1, uint64_t rs2) {
  // rd must be distinct from source registers rs1 and rs2 unless rd is zero,
  // otherwise the instruction is irreversible and has no effect

  if (rd != REG_ZR) {
    if (rd == rs1)
      throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, instruction_address());
    else if (rd == rs2)
      throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, instruction_address());
    else
      return 1;

    return 0;
  }

  return 1;
}

uint64_t update_rd(uint64_t value) {
  uint64_t next_rd_value;

  // rd += value forward, rd -= value backward, returns 1 if effective nop

  if (rd != REG_ZR) {
    if (reverse)
      next_rd_value = *(registers + rd) - value;
    else
      next_rd_value = *(registers + rd) + value;

    if (*(registers + rd) != next_rd_value) {
      *(registers + rd) = next_rd_value;

      return 0;
    }
  }

  return 1;
}

uint64_t flip_rd(uint64_t value) {
  // rd ^= value, its own inverse, returns 1 if effective nop

  if (rd != REG_ZR)
    if (value != 0) {
      *(registers + rd) = bitwise_xor(*(registers + rd), value);

      return 0;
    }

  return 1;
}

uint64_t is_come_from(uint64_t target, uint64_t origin) {
  uint64_t partner;

  // is the instruction at target the come-from of the
  // control-flow instruction at origin? see riscr.md

  if (is_virtual_address_valid(target, INSTRUCTIONSIZE))
    if (is_code_address(current_context, target)) {
      partner = fetch_instruction(target);

      if (is == BEQ) {
        // beq pointing back whose condition holds
        if (get_opcode(partner) == OP_BRANCH)
          if (get_funct3(partner) == F3_BEQ)
            if (get_immediate_b_format(partner) == origin - target)
              return *(registers + get_rs1(partner)) == *(registers + get_rs2(partner));
      } else if (is == JAL) {
        if (rd == REG_ZR) {
          // jal zero pointing back
          if (get_opcode(partner) == OP_JAL)
            if (get_rd(partner) == REG_ZR)
              return get_immediate_j_format(partner) == origin - target;
        } else {
          // jalr rd,0(rd) uncomputing the link in rd
          if (get_opcode(partner) == OP_JALR)
            if (get_funct3(partner) == F3_JALR)
              if (get_rd(partner) == rd)
                if (get_rs1(partner) == rd)
                  return get_immediate_i_format(partner) == 0;
        }
      } else if (is == JALR) {
        // jal rd pointing back
        if (get_opcode(partner) == OP_JAL)
          if (get_rd(partner) == rd)
            return get_immediate_j_format(partner) == origin - target;
      }
    }

  return 0;
}

void do_riscr_lui() {
  // semantics of RISC-R lui: rd += imm * 2^12, backward rd -= imm * 2^12

  nopc_lui = nopc_lui + update_rd(left_shift(imm, 12));

  write_register(rd);

  continue_at(instruction_address());

  ic_lui = ic_lui + 1;
}

void do_riscr_addi() {
  // semantics of RISC-R addi: rd += rs1 + imm, backward rd -= rs1 + imm

  // tolerate unwrapped values in register-to-register transfers
  read_register_check_wrap(rs1, imm);

  if (is_distinct_rd(rs1, rs1)) {
    nopc_addi = nopc_addi + update_rd(*(registers + rs1) + imm);

    write_register(rd);

    continue_at(instruction_address());
  }

  ic_addi = ic_addi + 1;
}

void do_riscr_add() {
  // semantics of RISC-R add: rd += rs1 + rs2, backward rd -= rs1 + rs2

  read_register(rs1);
  read_register(rs2);

  if (is_distinct_rd(rs1, rs2)) {
    nopc_add = nopc_add + update_rd(*(registers + rs1) + *(registers + rs2));

    write_register(rd);

    continue_at(instruction_address());
  }

  ic_add = ic_add + 1;
}

void do_riscr_sub() {
  // semantics of RISC-R sub: rd += rs1 - rs2, backward rd -= rs1 - rs2

  read_register(rs1);
  read_register(rs2);

  if (is_distinct_rd(rs1, rs2)) {
    nopc_sub = nopc_sub + update_rd(*(registers + rs1) - *(registers + rs2));

    write_register(rd);

    continue_at(instruction_address());
  }

  ic_sub = ic_sub + 1;
}

void do_riscr_mul() {
  // semantics of RISC-R mul: rd ^= rs1 * rs2, its own inverse

  read_register(rs1);
  read_register(rs2);

  if (is_distinct_rd(rs1, rs2)) {
    // TODO: support of 128-bit resolution

    nopc_mul = nopc_mul + flip_rd(*(registers + rs1) * *(registers + rs2));

    write_register(rd);

    continue_at(instruction_address());
  }

  ic_mul = ic_mul + 1;
}

void do_riscr_divu() {
  // semantics of RISC-R divu: rd ^= rs1 / rs2, its own inverse

  if (*(registers + rs2) != 0) {
    read_register(rs1);
    read_register(rs2);

    if (is_distinct_rd(rs1, rs2)) {
      nopc_divu = nopc_divu + flip_rd(*(registers + rs1) / *(registers + rs2));

      write_register(rd);

      continue_at(instruction_address());
    }
  } else
    throw_exception(EXCEPTION_DIVISIONBYZERO, instruction_address());

  ic_divu = ic_divu + 1;
}

void do_riscr_remu() {
  // semantics of RISC-R remu: rd ^= rs1 % rs2, its own inverse

  if (*(registers + rs2) != 0) {
    read_register(rs1);
    read_register(rs2);

    if (is_distinct_rd(rs1, rs2)) {
      nopc_remu = nopc_remu + flip_rd(*(registers + rs1) % *(registers + rs2));

      write_register(rd);

      continue_at(instruction_address());
    }
  } else
    throw_exception(EXCEPTION_DIVISIONBYZERO, instruction_address());

  ic_remu = ic_remu + 1;
}

void do_riscr_sltu() {
  // semantics of RISC-R sltu: rd ^= (rs1 < rs2), its own inverse

  read_register(rs1);
  read_register(rs2);

  if (is_distinct_rd(rs1, rs2)) {
    nopc_sltu = nopc_sltu + flip_rd(*(registers + rs1) < *(registers + rs2));

    write_register(rd);

    continue_at(instruction_address());
  }

  ic_sltu = ic_sltu + 1;
}

uint64_t do_riscr_load() {
  uint64_t vaddr;
  uint64_t next_rd_value;
  uint64_t a;

  // semantics of RISC-R ld: exchange rd with memory word, its own inverse

  read_register(rs1);

  vaddr = *(registers + rs1) + imm;

  if (not(is_distinct_rd(rs1, rs1)))
    return vaddr;

  if (is_virtual_address_valid(vaddr, WORDSIZE)) {
    if (is_valid_segment_write(vaddr)) {
      if (is_virtual_address_mapped(pt, vaddr)) {
        if (rd != REG_ZR) {
          next_rd_value = load_cached_virtual_memory(pt, vaddr);

          if (*(registers + rd) != next_rd_value) {
            // tolerate storing unwrapped values
            read_register_check_wrap(rd, 0);

            store_cached_virtual_memory(pt, vaddr, *(registers + rd));

            *(registers + rd) = next_rd_value;
          } else
            nopc_load = nopc_load + 1;
        } else
          nopc_load = nopc_load + 1;

        // load values unwrapped
        write_register_wrap(rd, 0);

        // keep track of instruction address for profiling loads
        a = (instruction_address() - code_start) / INSTRUCTIONSIZE;

        continue_at(instruction_address());

        // keep track of number of loads in total
        ic_load = ic_load + 1;

        // and individually
        *(loads_per_instruction + a) = *(loads_per_instruction + a) + 1;
      } else
        throw_exception(EXCEPTION_PAGEFAULT, page_of_virtual_address(vaddr));
    } else
      throw_exception(EXCEPTION_SEGMENTATIONFAULT, vaddr);
  } else
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);

  return vaddr;
}

void do_riscr_beq() {
  uint64_t origin;

  // semantics of RISC-R beq: if rs1 == rs2 jump over the come-from at pc + imm,
  // backward jump onto the come-from, see riscr.md

  read_register(rs1);
  read_register(rs2);

  origin = instruction_address();

  if (*(registers + rs1) == *(registers + rs2)) {
    if (is_come_from(origin + imm, origin))
      continue_at(origin + imm);
    else
      throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, origin);
  } else {
    continue_at(origin);

    nopc_beq = nopc_beq + 1;
  }

  ic_beq = ic_beq + 1;
}

void do_riscr_jal() {
  uint64_t origin;
  uint64_t a;

  // semantics of RISC-R jal: link into zeroed rd and jump over the come-from
  // at pc + imm, backward jump onto the come-from, see riscr.md

  origin = instruction_address();

  if (rd != REG_ZR)
    if (*(registers + rd) != 0) {
      // link register must be zero
      throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, origin);

      return;
    }

  if (is_come_from(origin + imm, origin)) {
    if (rd != REG_ZR) {
      // link to the instruction after the jal, backward to the jal itself
      // which is where the come-from jalr executed forward jumps over
      if (reverse)
        *(registers + rd) = origin;
      else
        *(registers + rd) = origin + INSTRUCTIONSIZE;

      // come-from address for profiling procedure calls
      a = (origin + imm - code_start) / INSTRUCTIONSIZE;

      // keep track of number of procedure calls in total
      calls = calls + 1;

      // and individually
      *(calls_per_procedure + a) = *(calls_per_procedure + a) + 1;
    } else if (signed_less_than(imm, 0)) {
      // come-from address for profiling loop iterations
      a = (origin + imm - code_start) / INSTRUCTIONSIZE;

      // keep track of number of loop iterations in total
      iterations = iterations + 1;

      // and individually
      *(iterations_per_loop + a) = *(iterations_per_loop + a) + 1;
    }

    continue_at(origin + imm);
  } else
    throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, origin);

  write_register(rd);

  ic_jal = ic_jal + 1;
}

void do_riscr_jalr() {
  uint64_t origin;
  uint64_t target;

  // semantics of RISC-R jalr: rd == rs1 holds the address of the jal that
  // links here, backward of the instruction after that jal; jump over
  // that jal, backward jump onto it, and uncompute rd, see riscr.md

  read_register(rs1);

  origin = instruction_address();

  if (rd != rs1)
    throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, origin);
  else if (rd == REG_ZR)
    throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, origin);
  else if (imm != 0)
    throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, origin);
  else {
    if (reverse)
      target = *(registers + rs1) - INSTRUCTIONSIZE;
    else
      target = *(registers + rs1);

    if (is_come_from(target, origin)) {
      // uncompute link: rd -= rd
      *(registers + rd) = 0;

      continue_at(target);
    } else
      throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, origin);
  }

  write_register(rd);

  ic_jalr = ic_jalr + 1;
}

void do_riscr_ecall() {
  uint64_t a7;

  // semantics of RISC-R ecall: arguments in a1-a3, result added into a0, see riscr.md

  read_register(REG_A7);

  ic_ecall = ic_ecall + 1;

  a7 = *(registers + REG_A7);

  if (a7 == SYSCALL_SWITCH) {
    printf("%s: context switching is unsupported in RISC-R\n", selfie_name);

    exit(EXITCODE_UNSUPPORTEDSYSCALL);
  } else if (a7 == SYSCALL_EXIT) {
    if (reverse)
      // exit is never executed backward
      throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, instruction_address());
    else {
      read_register(REG_A1);

      throw_exception(EXCEPTION_SYSCALL, a7);
    }
  } else {
    read_register(REG_A0);
    read_register(REG_A1);

    if (a7 == SYSCALL_BRK) {
      if (not(reverse))
        if (*(registers + REG_A0) != 0) {
          // brk must find a0 zero to be reversible
          throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, instruction_address());

          return;
        }
    } else {
      read_register(REG_A2);
      read_register(REG_A3);
    }

    // all other system calls are handled by exception
    throw_exception(EXCEPTION_SYSCALL, a7);
  }
}

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void init_reversible_interpreter() {
  uint64_t* exceptions;
  uint64_t e;

  // extend mipster's exceptions, call after init_interpreter()

  exceptions = smalloc((EXCEPTION_IRREVERSIBLEINSTRUCTION + 1) * sizeof(uint64_t*));

  e = 0;

  while (e < EXCEPTION_IRREVERSIBLEINSTRUCTION) {
    *(exceptions + e) = *(EXCEPTIONS + e);

    e = e + 1;
  }

  *(exceptions + EXCEPTION_IRREVERSIBLEINSTRUCTION) = (uint64_t) "irreversible instruction";

  EXCEPTIONS = exceptions;
}

uint64_t fetch_instruction(uint64_t vaddr) {
  // assert: is_virtual_address_valid(vaddr, INSTRUCTIONSIZE) == 1
  // assert: is_code_address(current_context, vaddr) == 1
  // assert: is_virtual_address_mapped(pt, vaddr) == 1

  if (vaddr % WORDSIZE == 0)
    return get_low_word(load_cached_instruction_word(pt, vaddr));
  else
    return get_high_word(load_cached_instruction_word(pt, vaddr - INSTRUCTIONSIZE));
}

void fetch_reversibly() {
  uint64_t vaddr;

  // executing backward fetches the instruction before pc
  vaddr = instruction_address();

  if (is_virtual_address_valid(vaddr, INSTRUCTIONSIZE)) {
    if (is_code_address(current_context, vaddr)) {
      ir = fetch_instruction(vaddr);

      return;
    } else
      throw_exception(EXCEPTION_SEGMENTATIONFAULT, vaddr);
  } else
    throw_exception(EXCEPTION_INVALIDADDRESS, vaddr);

  // reset instruction register
  ir = encode_nop();
}

void execute_reversibly() {
  if (is == ADDI)
    do_riscr_addi();
  else if (is == LOAD)
    do_riscr_load();
  else if (is == STORE)
    // RISC-R has no store, use ld to exchange
    throw_exception(EXCEPTION_IRREVERSIBLEINSTRUCTION, instruction_address());
  else if (is == ADD)
    do_riscr_add();
  else if (is == SUB)
    do_riscr_sub();
  else if (is == MUL)
    do_riscr_mul();
  else if (is == DIVU)
    do_riscr_divu();
  else if (is == REMU)
    do_riscr_remu();
  else if (is == SLTU)
    do_riscr_sltu();
  else if (is == BEQ)
    do_riscr_beq();
  else if (is == JAL)
    do_riscr_jal();
  else if (is == JALR)
    do_riscr_jalr();
  else if (is == LUI)
    do_riscr_lui();
  else if (is == ECALL)
    do_riscr_ecall();
}

void run_reversibly_until_exception() {
  trap = 0;

  while (not(trap)) {
    fetch_reversibly();
    decode();
    execute_reversibly();

    interrupt();
  }

  trap = 0;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// -------------------------- MICROKERNEL --------------------------
// -----------------------------------------------------------------

void reset_reversible_registers_profile() {
  uint64_t reg;

  // RISC-R: all registers are initialized to zero

  reg = 0;

  while (reg < NUMBEROFREGISTERS) {
    *(writes_per_register + reg) = 1;

    reg = reg + 1;
  }
}

void boot_reversibly(uint64_t megabytes) {
  // prepare current_context to run the loaded RISC-R binary

  reset_interpreter();
  reset_profiler();
  reset_reversible_registers_profile();
  reset_microkernel();

  init_memory(megabytes);

  reset_tapes();

  current_context = create_context(MY_CONTEXT, 0);

  // assert: number_of_remaining_arguments() > 0

  boot_loader(current_context);
}

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

uint64_t* reversible_switch(uint64_t* to_context, uint64_t timeout) {
  // unlike mipster_switch, a6 is left alone: registers are part of
  // the reversible state, and context switching is unsupported

  restore_context(to_context);

  current_context = to_context;

  timer = timeout;

  run_reversibly_until_exception();

  save_context(current_context);

  return current_context;
}

uint64_t handle_reversible_system_call(uint64_t* context) {
  uint64_t a7;

  set_exception(context, EXCEPTION_NOEXCEPTION);

  set_ec_syscall(context, get_ec_syscall(context) + 1);

  a7 = *(get_regs(context) + REG_A7);

  // RISC-R: system calls act on tapes and add results into a0, see riscr.md

  if (a7 == SYSCALL_READ)
    implement_reversible_read(context);
  else if (a7 == SYSCALL_WRITE)
    implement_reversible_write(context);
  else if (a7 == SYSCALL_OPENAT)
    implement_reversible_openat(context);
  else if (a7 == SYSCALL_BRK)
    implement_reversible_brk(context);
  else if (a7 == SYSCALL_EXIT) {
    implement_reversible_exit(context);

    return EXIT;
  } else {
    printf("%s: system call %lu is not reversible\n", selfie_name, a7);

    set_exit_code(context, EXITCODE_UNSUPPORTEDSYSCALL);

    return EXIT;
  }

  return DONOTEXIT;
}

uint64_t handle_reversible_exception(uint64_t* context) {
  uint64_t exception;

  exception = get_exception(context);

  if (exception == EXCEPTION_SYSCALL)
    return handle_reversible_system_call(context);
  else if (exception == EXCEPTION_IRREVERSIBLEINSTRUCTION) {
    printf("%s: context %s threw uncaught exception: ", selfie_name, get_name(context));
    print_exception(exception, get_fault(context));
    printf(" at address 0x%08lX\n", get_fault(context));

    set_exit_code(context, EXITCODE_UNCAUGHTEXCEPTION);

    return EXIT;
  } else
    // page faults, division by zero, timer, and all other exceptions as in mipster
    return handle_exception(context);
}

uint64_t riscr(uint64_t* to_context) {
  uint64_t* from_context;

  // execute RISC-R code forward until it exits

  reverse = 0;

  while (1) {
    from_context = reversible_switch(to_context, TIMESLICE);

    if (handle_reversible_exception(from_context) == EXIT)
      return get_exit_code(from_context);
    else
      to_context = from_context;
  }
}

uint64_t riscr_backward(uint64_t* to_context, uint64_t steps) {
  uint64_t timeout;
  uint64_t executed;
  uint64_t* from_context;

  // execute steps instructions backward, see riscr.md

  reverse = 1;

  while (steps > 0) {
    if (steps < TIMESLICE)
      timeout = steps;
    else
      timeout = TIMESLICE;

    executed = get_total_number_of_instructions();

    from_context = reversible_switch(to_context, timeout);

    executed = get_total_number_of_instructions() - executed;

    if (executed < steps)
      steps = steps - executed;
    else
      steps = 0;

    if (handle_reversible_exception(from_context) == EXIT) {
      reverse = 0;

      return get_exit_code(from_context);
    } else
      to_context = from_context;
  }

  reverse = 0;

  return get_exit_code(to_context);
}

uint64_t next_mapped_page(uint64_t page) {
  // smallest mapped page >= page, or NUMBEROFPAGES; skips empty leaf page tables

  while (page < NUMBEROFPAGES) {
    if (PAGETABLETREE)
      if (*(get_pt(current_context) + root_PDE_offset(page)) == 0) {
        page = (root_PDE_offset(page) + 1) * NUMBEROFLEAFPTES;

        if (page >= NUMBEROFPAGES)
          return NUMBEROFPAGES;
      }

    if (is_page_mapped(get_pt(current_context), page))
      return page;

    page = page + 1;
  }

  return NUMBEROFPAGES;
}

void take_initial_snapshot() {
  uint64_t r;
  uint64_t page;
  uint64_t i;
  uint64_t vaddr;
  uint64_t offset;

  // record pc, registers, program break, all mapped pages, and tape heads

  snapshot_pc = get_pc(current_context);

  snapshot_registers = smalloc(NUMBEROFREGISTERS * sizeof(uint64_t));

  r = 0;

  while (r < NUMBEROFREGISTERS) {
    *(snapshot_registers + r) = *(get_regs(current_context) + r);

    r = r + 1;
  }

  snapshot_program_break = get_program_break(current_context);

  snapshot_number_of_pages = 0;

  page = next_mapped_page(0);

  while (page < NUMBEROFPAGES) {
    snapshot_number_of_pages = snapshot_number_of_pages + 1;

    page = next_mapped_page(page + 1);
  }

  snapshot_pages  = smalloc(snapshot_number_of_pages * sizeof(uint64_t));
  snapshot_memory = smalloc(snapshot_number_of_pages * PAGESIZE);

  i    = 0;
  page = next_mapped_page(0);

  while (page < NUMBEROFPAGES) {
    *(snapshot_pages + i) = page;

    vaddr  = virtual_address_of_page(page);
    offset = i * PAGESIZE;

    while (offset < (i + 1) * PAGESIZE) {
      store_word(snapshot_memory, offset, 1, load_virtual_memory(get_pt(current_context), vaddr));

      vaddr  = vaddr + WORDSIZE;
      offset = offset + WORDSIZE;
    }

    i = i + 1;

    page = next_mapped_page(page + 1);
  }

  snapshot_number_of_tapes = number_of_tapes;

  snapshot_tape_heads = smalloc(number_of_tapes * sizeof(uint64_t));

  r = 0;

  while (r < number_of_tapes) {
    *(snapshot_tape_heads + r) = get_tape_head((uint64_t*) *(tapes + r));

    r = r + 1;
  }
}

uint64_t is_initial_state_restored() {
  uint64_t r;
  uint64_t page;
  uint64_t i;
  uint64_t vaddr;
  uint64_t offset;
  uint64_t expected;

  // returns 1 if the machine state is bit for bit the snapshot;
  // pages mapped after the snapshot must be zero

  if (get_pc(current_context) != snapshot_pc) {
    printf("%s: pc is 0x%lX, expected 0x%lX\n", selfie_name, get_pc(current_context), snapshot_pc);

    return 0;
  }

  r = 0;

  while (r < NUMBEROFREGISTERS) {
    if (*(get_regs(current_context) + r) != *(snapshot_registers + r)) {
      printf("%s: register %s is 0x%lX, expected 0x%lX\n", selfie_name,
        get_register_name(r), *(get_regs(current_context) + r), *(snapshot_registers + r));

      return 0;
    }

    r = r + 1;
  }

  if (get_program_break(current_context) != snapshot_program_break) {
    printf("%s: program break is 0x%lX, expected 0x%lX\n", selfie_name,
      get_program_break(current_context), snapshot_program_break);

    return 0;
  }

  i    = 0;
  page = next_mapped_page(0);

  while (page < NUMBEROFPAGES) {
    vaddr  = virtual_address_of_page(page);
    offset = 0;

    while (offset < PAGESIZE) {
      if (i < snapshot_number_of_pages) {
        if (*(snapshot_pages + i) == page)
          expected = load_word(snapshot_memory, i * PAGESIZE + offset, 1);
        else
          expected = 0;
      } else
        expected = 0;

      if (load_virtual_memory(get_pt(current_context), vaddr) != expected) {
        printf("%s: memory at 0x%lX is 0x%lX, expected 0x%lX\n", selfie_name,
          vaddr, load_virtual_memory(get_pt(current_context), vaddr), expected);

        return 0;
      }

      vaddr  = vaddr + WORDSIZE;
      offset = offset + WORDSIZE;
    }

    if (i < snapshot_number_of_pages)
      if (*(snapshot_pages + i) == page)
        i = i + 1;

    page = next_mapped_page(page + 1);
  }

  if (i < snapshot_number_of_pages) {
    printf("%s: page 0x%lX is no longer mapped\n", selfie_name, *(snapshot_pages + i));

    return 0;
  }

  if (number_of_tapes != snapshot_number_of_tapes) {
    printf("%s: %lu open files, expected %lu\n", selfie_name, number_of_tapes, snapshot_number_of_tapes);

    return 0;
  }

  r = 0;

  // tape contents before the heads are empty in the initial state
  while (r < number_of_tapes) {
    if (get_tape_head((uint64_t*) *(tapes + r)) != *(snapshot_tape_heads + r)) {
      printf("%s: head of tape %lu is at word %lu, expected %lu\n", selfie_name,
        r, get_tape_head((uint64_t*) *(tapes + r)), *(snapshot_tape_heads + r));

      return 0;
    }

    r = r + 1;
  }

  return 1;
}

uint64_t selfie_run_reversibly() {
  uint64_t backward;
  uint64_t exit_code;
  uint64_t steps;

  if (string_compare(argument, "-m"))
    backward = 0;
  else if (string_compare(argument, "-rev"))
    backward = 1;
  else
    return EXITCODE_BADARGUMENTS;

  if (code_size == 0) {
    printf("%s: nothing to run\n", selfie_name);

    return EXITCODE_BADARGUMENTS;
  } else if ((e_flags / EF_RISCR) % 2 == 0) {
    printf("%s: %s is not a RISC-R binary\n", selfie_name, binary_name);

    return EXITCODE_BADARGUMENTS;
  }

  init_reversible_interpreter();

  boot_reversibly(atoi(peek_argument(0)));

  // current_context is ready to run

  run = 1;

  printf("%s: %lu-bit riscr executing %lu-bit RISC-R binary %s with %luMB physical memory", selfie_name,
    SIZEOFUINT64INBITS,
    WORDSIZEINBITS,
    binary_name,
    PHYSICALMEMORYSIZE / MEGABYTE);

  if (backward)
    printf(", forward and then backward");

  printf("\n%s: >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n\n", selfie_name);

  if (backward)
    take_initial_snapshot();

  exit_code = riscr(current_context);

  printf("\n%s: <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<\n", selfie_name);

  printf("%s: %lu-bit riscr terminating %lu-bit RISC-R binary %s with exit code %ld\n", selfie_name,
    SIZEOFUINT64INBITS,
    WORDSIZEINBITS,
    binary_name,
    sign_extend(exit_code, SYSCALL_BITWIDTH));

  if (backward) {
    if (get_exception(current_context) == EXCEPTION_NOEXCEPTION) {
      // undo all executed instructions but the exit system call
      steps = get_total_number_of_instructions() - 1;

      printf("%s: %lu-bit riscr executing %lu instructions backward\n", selfie_name,
        SIZEOFUINT64INBITS,
        steps);

      riscr_backward(current_context, steps);

      printf("%s: %lu-bit riscr terminating backward execution at pc==0x%lX\n", selfie_name,
        SIZEOFUINT64INBITS,
        get_pc(current_context));

      if (is_initial_state_restored())
        printf("%s: initial state restored bit for bit\n", selfie_name);
      else {
        printf("%s: initial state NOT restored\n", selfie_name);

        exit_code = EXITCODE_SYSTEMERROR;
      }
    } else
      printf("%s: not executing backward after uncaught exception\n", selfie_name);
  }

  print_profile();

  run = 0;

  printf("%s: ################################################################################\n", selfie_name);

  return exit_code;
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

int main(int argc, char** argv) {
  uint64_t exit_code;

  init_selfie((uint64_t) argc, (uint64_t*) argv);

  init_library();
  init_system();
  init_target();
  init_kernel();

  // RISC-R binaries are about four times larger than RISC-U binaries
  MAX_CODE_SIZE   = 4 * MAX_CODE_SIZE;
  MAX_BINARY_SIZE = 4 * MAX_BINARY_SIZE;

  exit_code = selfie(1);

  if (exit_code == EXITCODE_MOREARGUMENTS) {
    if (string_compare(argument, "-t")) {
      exit_code = selfie_translate();

      if (exit_code == EXITCODE_NOERROR) {
        if (number_of_remaining_arguments() > 0) {
          get_argument();

          exit_code = selfie_run_reversibly();
        } else
          printf("%s: ################################################################################\n", selfie_name);
      }
    } else
      exit_code = selfie_run_reversibly();
  }

  return exit_selfie(exit_code, " [ -t binary ] [ ( -m | -rev ) 0-4096 ... ]");
}
