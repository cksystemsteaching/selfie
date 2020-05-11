#include "../selfie.h"
#define uint64_t unsigned long long

uint64_t UNKNOWN_VALUE = 3735928559; // magic number representing unknown value


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
    *(registers+i) = UNKNOWN_VALUE;
    i = i + 1;
  }

  // reset GP and ZR as they are never touched
  *(registers + REG_ZR) = 0;
  *(registers + REG_GP) = gp_cache;
}

// iterates over entire code segment while keeping track of the current state of registers
//
// at instruction i the contents of register r are either 
//   * UNKNOWN_VALUE if they might differ per execution
//   * a value introduced via constants in the previous k instructions
//
// k is determined by the last instruction with more than one inedge.
void find_nops() {
  uint64_t i;
  uint64_t addi_rd;
  uint64_t addi_rs1;
  uint64_t addi_imm;
  uint64_t stop;

  pc = 0;

  while (pc < code_length) {
    ir = load_instruction(pc);

    decode();

    printf1("[%d]", *(num_in_edges + (pc/4))); // print the number of inedges

    if (*(num_in_edges + (pc/4)) != 1) {
      // if there are more than 1 inedges
      println();
      reset_all();

    } else if (is == ADDI){
      translate_to_assembler();
      print_addi_before();

      if (rd != REG_ZR) { 

        if (*(registers + rs1) != UNKNOWN_VALUE) { // if the registers' contents are not unknown
          *(registers + rd) = *(registers + rs1) + imm; // do the addi

        } else { // else rd is now unknown too
          *(registers + rd) = UNKNOWN_VALUE;
        }
      }

      print_addi_add_sub_mul_divu_remu_sltu_after();
      println();
    }

    // ignore these for now...
    else if (is == LD){println();}
    else if (is == SD){println();}
    else if (is == BEQ){println();}
    else if (is == JAL){println();}
    else if (is == JALR){println();}
    else if (is == LUI){println();}
    else if (is == ECALL){println();}

    else { 
      translate_to_assembler();
      print_add_sub_mul_divu_remu_sltu_before();

      // analogous to ADDI but with two potentially unknown registers
      if (rd != REG_ZR) {

        if (*(registers + rs1) == UNKNOWN_VALUE) {
          *(registers + rd) = UNKNOWN_VALUE;

        } else if (*(registers + rs2) == UNKNOWN_VALUE) {
          *(registers + rd) = UNKNOWN_VALUE;

        } else { // only do stuff if both aren't unknown

          if (is == ADD) {
            *(registers + rd) = *(registers + rs1) + *(registers + rs2);
          } else if (is == SUB) {
            *(registers + rd) = *(registers + rs1) - *(registers + rs2);
          } else if (is == MUL) {
            *(registers + rd) = *(registers + rs1) * *(registers + rs2);
          } else if (is == DIVU) {
            *(registers + rd) = *(registers + rs1) / *(registers + rs2);
          } else if (is == REMU) {
            *(registers + rd) = *(registers + rs1) % *(registers + rs2);
          } else if (is == SLTU) {
            if (*(registers + rs1) < *(registers + rs2))
              *(registers + rd) = 1;
            else
              *(registers + rd) = 0;
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

  count_in_edges();
  find_nops();

  // assert: binary_name is mapped and not longer than MAX_FILENAME_LENGTH

  // selfie_output(binary_name);

  return EXITCODE_NOERROR;
}
