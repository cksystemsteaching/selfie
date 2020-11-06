#include "../selfie.h"
#define uint64_t unsigned long long

uint64_t* addrmap;
uint64_t found_nops = 0;
uint64_t INSTR_NOP = 19;




uint64_t load_instruction_from(uint64_t* binary, uint64_t baddr) {
  if (baddr % REGISTERSIZE == 0)
    return get_low_word(*(binary + baddr / REGISTERSIZE));
  else
    return get_high_word(*(binary + baddr / REGISTERSIZE));
}

void store_instruction_to(uint64_t* binary, uint64_t baddr, uint64_t instruction) {
  uint64_t temp;

  if (baddr >= MAX_CODE_LENGTH) {
    syntax_error_message("maximum code length exceeded");

    exit(EXITCODE_COMPILERERROR);
  }

  temp = *(binary + baddr / REGISTERSIZE);

  if (baddr % REGISTERSIZE == 0)
    // replace low word
    temp = left_shift(get_high_word(temp), WORDSIZEINBITS) + instruction;
  else
    // replace high word
    temp = left_shift(instruction, WORDSIZEINBITS) + get_low_word(temp);

  *(binary + baddr / REGISTERSIZE) = temp;
}



void build_addrmap() {
  uint64_t current_address;
  uint64_t mapped_address;

  current_address = 0;
  mapped_address = 0;

  addrmap = malloc(SIZEOFUINT64 * code_length / INSTRUCTIONSIZE);

  while (current_address < code_length) {
    ir = load_instruction(current_address);
    decode();

    if (ir == INSTR_NOP) {
      found_nops = found_nops + 1;

      *(addrmap + current_address / INSTRUCTIONSIZE) = -1;

    } else {

      *(addrmap + current_address / INSTRUCTIONSIZE) = mapped_address;

      mapped_address = mapped_address + INSTRUCTIONSIZE;
    }

    current_address = current_address + INSTRUCTIONSIZE;
  }
}


uint64_t get_mapped_addr(uint64_t addr) {
  uint64_t mapped;

  mapped = *(addrmap + addr / INSTRUCTIONSIZE);

  // if addr is itself a nop, return the next non-nop mapped address
  while (mapped == -1) {
    addr = addr + INSTRUCTIONSIZE;
    mapped = *(addrmap + addr / INSTRUCTIONSIZE);
  }

  return mapped;
} 

uint64_t get_mapped_jump_imm(uint64_t addr, uint64_t imm) {
  return get_mapped_addr(addr + imm) - get_mapped_addr(addr);
}


void patch_nops() {
  uint64_t data_length;
  uint64_t gp;
  uint64_t current_address;
  uint64_t mapped_address;

  data_length = binary_length - code_length;

  current_address = 0;
  mapped_address = 0;

  while (current_address < code_length) {
    ir = load_instruction(current_address);
    decode();

    if (is == JAL) {
      // replace imm with mapped imm
      imm = get_mapped_jump_imm(current_address, imm);
      ir = encode_j_format(imm, rd, OP_JAL);

    } else if (is == JALR) {
      // replace imm with mapped imm
      // (note: in selfie, imm is always 0)
      imm = get_mapped_jump_imm(current_address, imm);
      ir = encode_i_format(imm, rs1, F3_JALR, rd, OP_JALR);

    } else if (is == BEQ) {
      // replace imm with mapped imm
      imm = get_mapped_jump_imm(current_address, imm);
      ir = encode_b_format(imm, rs2, rs1, F3_BEQ, OP_BRANCH);
    } 

    if (ir != INSTR_NOP) {
      // Copy instruction into new position
      store_instruction(mapped_address, ir);
      mapped_address = mapped_address + INSTRUCTIONSIZE;
    } 

    current_address = current_address + INSTRUCTIONSIZE;
  }

  if (mapped_address % REGISTERSIZE != 0) {
    store_instruction(mapped_address, encode_nop());
    mapped_address = mapped_address + INSTRUCTIONSIZE;
    current_address = current_address + INSTRUCTIONSIZE;
  }

  code_length = mapped_address;

  // copy data segment
  while (current_address < binary_length) {
    *(binary + mapped_address / REGISTERSIZE) = *(binary + current_address / REGISTERSIZE);
    current_address = current_address + REGISTERSIZE;
    mapped_address = mapped_address + REGISTERSIZE;
  }

  binary_length = mapped_address;

  // update gp
  gp = ELF_ENTRY_POINT + binary_length;
  binary_length = 0;
  load_integer(gp);

  binary_length = mapped_address;
}

void print_addrmap() {
  uint64_t i;
  i = 0;

  while (i < code_length / INSTRUCTIONSIZE) {
    printf2("%x -> %x\n", i * INSTRUCTIONSIZE, *(addrmap + i));
    i = i + 1;
  }
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

int main(int argc, char **argv) {
  uint64_t enop;

  init_selfie((uint64_t) argc, (uint64_t *) argv);

  init_library();

  init_scanner();
  init_register();
  init_interpreter();

  selfie_load();

  reset_library();
  reset_interpreter();

  // need to manually init this so emit_instruction() actually works
  // also: zero it before emitting disassmebly so there's no useless code lines
  code_line_number = zalloc(MAX_CODE_LENGTH / INSTRUCTIONSIZE * SIZEOFUINT64);

  build_addrmap();
  //print_addrmap();

  printf1("found %d nops\n", (char*) found_nops);

  // assert: binary_name is mapped and not longer than MAX_FILENAME_LENGTH

  patch_nops();

  ELF_header = create_elf_header(binary_length, code_length);

  code_line_number = 0;

  binary_name = replace_extension(binary_name, "nonop");
  selfie_disassemble(1); // TODO DEBUG
  selfie_output(binary_name);

  return EXITCODE_NOERROR;
}
