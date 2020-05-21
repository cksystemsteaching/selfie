#include "../selfie.h"
#define uint64_t unsigned long long

uint64_t UNKNOWN_VALUE = 3735928559; // magic number representing unknown value
uint64_t* unknown_regs = (uint64_t*) 0;
uint64_t nops = 0;

// helper functions

uint64_t is_reg_unknown(uint64_t reg) {
  return *(unknown_regs + reg);
}

void set_reg_unknown(uint64_t reg) {
  *(unknown_regs + reg) = 1;
  *(registers + reg) = UNKNOWN_VALUE;
}

uint64_t set_reg(uint64_t reg, uint64_t value) {
  *(registers + reg) = value;
  *(unknown_regs + reg) = 0;
}

/////////////////////
// IN EDGE COUNTER //
/////////////////////


uint64_t* num_in_edges = (uint64_t*) 0;

uint64_t is_jump() {
  if (is == JALR)
    return 1;
  if (is == JAL)
    return 1;
  return 0;
}

uint64_t is_jump_or_branch() {
  if (is_jump())
    return 1;
  if (is == BEQ)
    return 1;
  return 0;
}

uint64_t is_return() {
  if (is_jump())
    if (rd == REG_ZR)
      return 1;
  return 0;
}

void count_in_edges() {
  uint64_t i;
  uint64_t useless;

  num_in_edges = zalloc(code_length / INSTRUCTIONSIZE * SIZEOFUINT64);
  *num_in_edges = 1;

  i = 1;

  while (i < code_length / INSTRUCTIONSIZE ) {
    ir = load_instruction((i - 1) * INSTRUCTIONSIZE);
    decode();
    if (is_return())useless=1;else {
      *(num_in_edges + i) = *(num_in_edges + i) + 1;
      if (is_jump_or_branch()) {
        *(num_in_edges + i-1 + imm/INSTRUCTIONSIZE) = *(num_in_edges + i-1 + imm/INSTRUCTIONSIZE) + 1;
      }
    }
    i = i + 1;
  }
  i = 0;
  while (i < code_length / INSTRUCTIONSIZE) {
    //printf2("%d: %d\n", i, *(num_in_edges + i));
    i = i + 1;
  }
}



//////////////////////////////
//     PATTERN MATCHER      //
//////////////////////////////

uint64_t ANY = 50159747054; // = 0xBADC0FFEE

// instructon type struct:
// any information may be ANY
// +---+--------+
// | 0 | next   | pointer to next instruction prototype
// | 1 | opcode | 
// | 2 | funct3 | 
// | 3 | funct7 | 
// | 4 | rs1    | 
// | 5 | rs2    | 
// | 6 | rd     | 
// | 7 | imm    | 
// +---+--------+

uint64_t* allocate_itype() {
  return smalloc(1 * SIZEOFUINT64STAR + 7 * SIZEOFUINT64);
}

uint64_t* get_it_next   (uint64_t* itype) { return (uint64_t*) *(itype + 0); }
uint64_t  get_it_opcode (uint64_t* itype) { return             *(itype + 1); }
uint64_t  get_it_funct3 (uint64_t* itype) { return             *(itype + 2); }
uint64_t  get_it_funct7 (uint64_t* itype) { return             *(itype + 3); }
uint64_t  get_it_rs1    (uint64_t* itype) { return             *(itype + 4); }
uint64_t  get_it_rs2    (uint64_t* itype) { return             *(itype + 5); }
uint64_t  get_it_rd     (uint64_t* itype) { return             *(itype + 6); }
uint64_t  get_it_imm    (uint64_t* itype) { return             *(itype + 7); }

void set_it_next   (uint64_t* itype, uint64_t* val) { *(itype + 0) = (uint64_t) val; }
void set_it_opcode (uint64_t* itype, uint64_t  val) { *(itype + 1) =            val; }
void set_it_funct3 (uint64_t* itype, uint64_t  val) { *(itype + 2) =            val; }
void set_it_funct7 (uint64_t* itype, uint64_t  val) { *(itype + 3) =            val; }
void set_it_rs1    (uint64_t* itype, uint64_t  val) { *(itype + 4) =            val; }
void set_it_rs2    (uint64_t* itype, uint64_t  val) { *(itype + 5) =            val; }
void set_it_rd     (uint64_t* itype, uint64_t  val) { *(itype + 6) =            val; }
void set_it_imm    (uint64_t* itype, uint64_t  val) { *(itype + 7) =            val; }


// return 1 if instruction at $at matches $itype
uint64_t match_instruction(uint64_t* itype, uint64_t at) {
  uint64_t pc_buffer;
  uint64_t matches;

  matches = 1;

  pc_buffer = pc;
  pc = at;

  ir = load_instruction(pc);
  decode();

  if (get_it_opcode(itype) != ANY)
    if (get_it_opcode(itype) != opcode)
      matches = 0;

  if (get_it_funct3(itype) != ANY)
    if (get_it_funct3(itype) != funct3)
      matches = 0;

  if (get_it_funct7(itype) != ANY)
    if (get_it_funct7(itype) != funct7)
      matches = 0;

  if (get_it_rs1(itype) != ANY)
    if (get_it_rs1(itype) != rs1)
      matches = 0;

  if (get_it_rs2(itype) != ANY)
    if (get_it_rs2(itype) != rs2)
      matches = 0;

  if (get_it_rd(itype) != ANY)
    if (get_it_rd(itype) != rd)
      matches = 0;

  if (get_it_imm(itype) != ANY)
    if (get_it_imm(itype) != imm)
      matches = 0;

  pc = pc_buffer;

  return matches;
}


// return 1 if instructions starting at $at match the *linked list* $itype
uint64_t match_instructions(uint64_t* itype, uint64_t at) {
  uint64_t position;
  uint64_t* current_itype;

  position = at;
  current_itype = itype;

  while (current_itype) {
    if (position >= code_length)
      return 0;

    else if (match_instruction(current_itype, position)) {
      current_itype = get_it_next(current_itype);
      position = position + 4;
    }

    else 
      return 0;
  }

  return 1;
}


uint64_t find_snippet(uint64_t* itype, uint64_t from) {
  uint64_t position;

  position = from;

  while (match_instructions(itype, position) == 0) {
    position = position + 4;

    if (position > code_length)
      return -1;
  }

  return position;
}



///////////////////////////////////
// POINTER DEREF PATTERN MATCHER //
///////////////////////////////////

// Create linked list of instruction type structs matching selfie's pointer dereferencing
uint64_t* create_pdr_itypes(){
  uint64_t* itype;
  uint64_t* first;

  itype = allocate_itype();
  first = itype;

  set_it_opcode(itype, OP_IMM);
  set_it_funct3(itype, F3_ADDI);
  set_it_funct7(itype, 0);
  set_it_rs1(itype, REG_ZR);
  set_it_rd(itype, REG_T1);
  set_it_imm(itype, ANY);

  set_it_next(itype, allocate_itype());
  itype = get_it_next(itype);

  set_it_opcode(itype, OP_IMM);
  set_it_funct3(itype, F3_ADDI);
  set_it_funct7(itype, 0);
  set_it_rs1(itype, REG_ZR);
  set_it_rd(itype, REG_T2);
  set_it_imm(itype, 8);

  set_it_next(itype, allocate_itype());
  itype = get_it_next(itype);

  set_it_opcode(itype, OP_OP);
  set_it_funct3(itype, F3_MUL);
  set_it_funct7(itype, F7_MUL);
  set_it_rs1(itype, REG_T1);
  set_it_rs2(itype, REG_T2);
  set_it_rd(itype, REG_T1);

  set_it_next(itype, allocate_itype());
  itype = get_it_next(itype);

  set_it_opcode(itype, OP_OP);
  set_it_funct3(itype, F3_ADD);
  set_it_funct7(itype, F7_ADD);
  set_it_rs1(itype, REG_T0);
  set_it_rs2(itype, REG_T1);
  set_it_rd(itype, REG_T0);

  return first;
}

uint64_t replacePtrDeref(uint64_t at, uint64_t imm) {
  uint64_t i;

  store_instruction(at, encode_i_format(imm, REG_T0, F3_ADDI, REG_T0, OP_IMM));

  i = 1;
  while (i < 4) // insert 3 nops
    store_instruction(at + 4 * i, encode_i_format(0, REG_ZR, F3_NOP, REG_ZR, OP_IMM));
  
}



// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

int main(int argc, char **argv) {
  uint64_t* patternlib;
  uint64_t pos;

  patternlib = create_pdr_itypes();

  init_selfie((uint64_t) argc, (uint64_t *) argv);

  init_library();

  init_scanner();
  init_register();
  init_interpreter();

  selfie_load();

  //count_in_edges();

  pc = 0;
  while (pc != -1) {
    pc = find_snippet(patternlib, pc);
    printf1("match at %d\n", (char*) (pc/4));
    pc = pc + 4;
  }
  
  binary_name = replace_extension(binary_name, "nop2");
  selfie_output(binary_name);

  return EXITCODE_NOERROR;
}
