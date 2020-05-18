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


//////////////////////////
// EFFECTIVE NOP FINDER //
//////////////////////////


// Reset all registers' states to unknown
void reset_all() {
  uint64_t i;
  uint64_t gp_cache;
  gp_cache = *(registers + REG_GP);

  i=0;
  while(i < NUMBEROFREGISTERS) {
    set_reg_unknown(i);
    i = i + 1;
  }

  // reset GP and ZR as they are never touched
  set_reg(REG_ZR, 0);
  set_reg(REG_GP, gp_cache);
}

void insert_nop() {
  uint64_t real_binary_length;

  real_binary_length = binary_length;
  binary_length = pc;
  emit_addi(REG_ZR, REG_ZR, 0);
  binary_length = real_binary_length;
}

// iterates over entire code segment while keeping track of the current state of registers
//
// at instruction i the contents of register r are either 
//   * UNKNOWN_VALUE if they might differ per execution
//   * or a value introduced via constants in the previous k instructions
//
// k is the number of instructions since the last one with more than one inedge.
//
// TODO: double check the in edge logic
void find_nops() {
  uint64_t i;
  uint64_t addi_rd;
  uint64_t addi_rs1;
  uint64_t addi_imm;
  uint64_t stop;
  uint64_t previous_rd;

  pc = 0;

  while (pc < code_length) {
    ir = load_instruction(pc);

    decode();

    //printf1("[%d]", *(num_in_edges + (pc/4))); // print the number of inedges

    if (*(num_in_edges + (pc/4)) != 1) {
      // if there are more than 1 inedges
      //print(" ?\n");
      reset_all();

    } else if (is == ADDI){
      printf1("%p ", pc);
      translate_to_assembler();
      print_addi_before();

      if (rd != REG_ZR) {

        if (!is_reg_unknown(rs1)) { // if the registers' contents are not unknown

          previous_rd = *(registers + rd);

          set_reg(rd, *(registers + rs1) + imm); // do the addi

          if (!is_reg_unknown(rd))
            if (previous_rd == *(registers + rd)) {
              nops = nops + 1;
              insert_nop();
              print(" [NOP]");
            }

        } else { // else rd is now unknown too
          set_reg_unknown(rd);
        }
      }

      print_addi_add_sub_mul_divu_remu_sltu_after();
      println();
    }

    // handle "weird" instructions
    else if (is == LD){
      set_reg_unknown(rd);
    }
    else if (is == SD){}
    else if (is == BEQ){
      reset_all();
    }
    else if (is == JAL){
      reset_all();
    }
    else if (is == JALR){
      reset_all();
    }
    else if (is == LUI){
      if (rd != REG_ZR) {
        set_reg(rd, left_shift(imm, 12));
      }
    }
    else if (is == ECALL){
      set_reg_unknown(REG_A0);
    }

    else {
      printf1("%p ", pc);
      translate_to_assembler();
      print_add_sub_mul_divu_remu_sltu_before();

      // analogous to ADDI but with two potentially unknown registers
      if (rd != REG_ZR) {

        if (is_reg_unknown(rs1)) {
          set_reg_unknown(rd);

        } else if (is_reg_unknown(rs2)) {
          set_reg_unknown(rd);

        } else { // only do stuff if both aren't unknown

          previous_rd = *(registers + rd);

          if (is == ADD) {
            set_reg(rd, *(registers + rs1) + *(registers + rs2));
          } else if (is == SUB) {
            set_reg(rd, *(registers + rs1) - *(registers + rs2));
          } else if (is == MUL) {
            set_reg(rd, *(registers + rs1) * *(registers + rs2));
          } else if (is == DIVU) {
            if (*(registers + rs2) != 0)
              set_reg(rd, *(registers + rs1) / *(registers + rs2));
          } else if (is == REMU) {
            if (*(registers + rs2) != 0)
              set_reg(rd, *(registers + rs1) % *(registers + rs2));
          } else if (is == SLTU) {
            if (*(registers + rs1) < *(registers + rs2))
              set_reg(rd, 1);
            else
              set_reg(rd, 0);
          }

          if (previous_rd == *(registers + rd)) {
            nops = nops + 1;
            insert_nop();
            print(" [NOP]");
          }
        }
      }

      print_addi_add_sub_mul_divu_remu_sltu_after();
      println();

    }

    pc = pc + INSTRUCTIONSIZE;
  }
}


// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

int main(int argc, char **argv) {
  init_selfie((uint64_t) argc, (uint64_t *) argv);

  init_library();

  init_scanner();
  init_register();
  init_interpreter();

  selfie_load();

  registers = malloc(NUMBEROFREGISTERS * REGISTERSIZE);
  unknown_regs = zalloc(NUMBEROFREGISTERS * REGISTERSIZE);

  reset_all();

  count_in_edges();
  find_nops();
  printf1("found and patched %d effective nops\n", nops);
  binary_name = replace_extension(binary_name, "nop2");
  selfie_output(binary_name);

  return EXITCODE_NOERROR;
}
