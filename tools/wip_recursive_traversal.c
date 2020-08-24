#include "../selfie.h"
#define uint64_t unsigned long long

uint64_t *machine_states = (uint64_t *) 0;

uint64_t *tmp_state = (uint64_t *) 0; // re-use this to avoid unnecessary allocations (since we can't free memory)

uint64_t *get_unknown_regs(uint64_t *state) { return (uint64_t *) *state; }

uint64_t *get_reg_values(uint64_t *state) { return (uint64_t *) *(state + 1); }

void set_unknown_regs(uint64_t *state, uint64_t *unknown_regs) { *state = (uint64_t) unknown_regs; }

void set_reg_values(uint64_t *state, uint64_t *reg_values) { *(state + 1) = (uint64_t) reg_values; }

uint64_t *get_state(uint64_t pc) {
  if (machine_states == (uint64_t*) 0) {
    print("Machine states aren't initialized yet!");
    exit(1);
  }

  return (uint64_t *) *(machine_states + pc / INSTRUCTIONSIZE);
}

void set_state(uint64_t pc, uint64_t *state) {
  *(machine_states + pc / INSTRUCTIONSIZE) = (uint64_t) state;
}

uint64_t is_reg_unknown(uint64_t *state, uint64_t reg) {
  return (uint64_t) (*(get_unknown_regs(state) + reg) == 1);
}

void set_reg_unknown(uint64_t *state, uint64_t reg) {
  if (reg != REG_ZR)
    *(get_unknown_regs(state) + reg) = 1;
}

void set_reg(uint64_t *state, uint64_t reg, uint64_t value) {
  if (reg != REG_ZR) {
    *(get_reg_values(state) + reg) = value;
    *(get_unknown_regs(state) + reg) = 0;
  }
}

uint64_t *new_machine_state() {
  uint64_t *result;
  uint64_t *unknown_regs;
  uint64_t *reg_values;
  uint64_t i;

  i = 0;
  unknown_regs = malloc(NUMBEROFREGISTERS * SIZEOFUINT64);
  reg_values = malloc(NUMBEROFREGISTERS * SIZEOFUINT64);
  while (i < NUMBEROFREGISTERS) {
    if (i == REG_ZR) {
      *(unknown_regs + i) = 0;
      *(reg_values + i) = 0;
    } else {
      *(unknown_regs + i) = 1;
    }
    i = i + 1;
  }

  result = malloc(2 * SIZEOFUINT64STAR);
  set_unknown_regs(result, unknown_regs);
  set_reg_values(result, reg_values);
  return result;
}

uint64_t get_reg(uint64_t *state, uint64_t reg) {
  if (is_reg_unknown(state, reg)) {
    print("Attempted to get value of unknown register!");
    exit(1);
  }
  return *(get_reg_values(state) + reg);
}

void copy_state(uint64_t *source, uint64_t *dest) {
  uint64_t i = 1;

  while (i < NUMBEROFREGISTERS) {
    if (is_reg_unknown(source, i)) {
      set_reg_unknown(dest, i);
    } else {
      set_reg(dest, i, get_reg(source, i));
    }
    i = i + 1;
  }
}

// Return 1 iff machine states a and b are equal
uint64_t test_states_equal(uint64_t *a, uint64_t *b) {
  uint64_t i;
  i = 0;
  
  while (i < NUMBEROFREGISTERS) {
    if (is_reg_unknown(a, i) != 1) { // If a is known
      if (is_reg_unknown(b, i) != 1) { // If b is known
        if (get_reg(a, i) != get_reg(b, i)) { // Check that states are same
          return 0;
        }

      // If we're here, a is known but b isn't
      } else {
        return 0;
      }

    // Here, a is unknown, we need to check that b is too.
    } else {
      if (is_reg_unknown(b, i) != 1) { 
        return 0;
      }
    }

    i = i + 1;
  }

  return 1;
}

// merge source state into dest state
uint64_t merge_states(uint64_t *source, uint64_t *dest) {
  uint64_t i;
  uint64_t changed;

  changed = 0;
  i = 0;

  while (i < NUMBEROFREGISTERS) {
    // merging unknown register always results in unknown register
    if (is_reg_unknown(source, i)) {
      if (!is_reg_unknown(dest, i)) {
        set_reg_unknown(dest, i);
        changed = changed + 1;
      }
    }
    // merging two known registers results in known register if values match
    // unknown register otherwise
    else {
      if (!is_reg_unknown(dest, i)) {
        if (get_reg(source, i) != get_reg(dest, i)) {
          set_reg_unknown(dest, i);
          changed = changed + 1;
        }
      }
    }
    i = i + 1;
  }
  return changed;
}

// apply effects of current instruction to machine state
// Return 1 iff the instruction had a quantifiable effect
uint64_t apply_effects(uint64_t *state) {
  uint64_t *registers;
  uint64_t tracked_change;
  tracked_change = 0;

  registers = get_reg_values(state);

  if (is == ADDI) {
    if (!is_reg_unknown(state, rs1)) { // if the register's contents are not unknown
      set_reg(state, rd, *(registers + rs1) + imm); // do the addi
      tracked_change = 1;
    } else { // else rd is now unknown too
      set_reg_unknown(state, rd);
    }
  } else if (is == LUI) {
    set_reg(state, rd, left_shift(imm, 12));
    tracked_change = 1;
  }

  // handle "weird" instructions
  else if (is == LD) {
    set_reg_unknown(state, rd);
  } else if (is == SD) { /* ignore memory writes */ }
  else if (is == BEQ) { /* nothing to do here, as control flow is handled by the recursive traversal function */ }
  else if (is == JAL) {
    set_reg_unknown(state, rd); // we currently don't keep track of the actual program counter
  } else if (is == JALR) {
    set_reg_unknown(state, rd); // rd is always zero register in selfie code
  } else if (is == ECALL) {
    set_reg_unknown(state, REG_A0); // ecall puts result in a0
  }
  // handle instructions with 2 source registers
  else {
    if (is_reg_unknown(state, rs1)) {
      set_reg_unknown(state, rd);

    } else if (is_reg_unknown(state, rs2)) {
      set_reg_unknown(state, rd);

    } else { // only do stuff if both aren't unknown
      if (is == ADD) {
        set_reg(state, rd, *(registers + rs1) + *(registers + rs2));
      } else if (is == SUB) {
        set_reg(state, rd, *(registers + rs1) - *(registers + rs2));
      } else if (is == MUL) {
        set_reg(state, rd, *(registers + rs1) * *(registers + rs2));
      } else if (is == DIVU) {
        if (*(registers + rs2) != 0)
          set_reg(state, rd, *(registers + rs1) / *(registers + rs2));
      } else if (is == REMU) {
        if (*(registers + rs2) != 0)
          set_reg(state, rd, *(registers + rs1) % *(registers + rs2));
      } else if (is == SLTU) {
        if (*(registers + rs1) < *(registers + rs2))
          set_reg(state, rd, 1);
        else
          set_reg(state, rd, 0);
      }
      tracked_change = 1;
    }
  }

  return tracked_change;
}

uint64_t depth = 0;

void traverse_recursive(uint64_t pc, uint64_t prev_pc, uint64_t current_ra) {
  uint64_t created_new_state;
  uint64_t *state;
  uint64_t force_continue;
  uint64_t i;

  depth = depth + 1;
  force_continue = 0;

  while (1) {
    if (pc >= code_length) {
      print("Error: pc went past end of code!");
      exit(1);
    }

    created_new_state = 0;
    state = get_state(pc);
    if (state == (uint64_t *) 0) {
      state = new_machine_state();
      set_state(pc, state);
      created_new_state = 1;
    }

    if (prev_pc != (uint64_t) -1) { // can't apply effects if last pc is undefined/unknown
      copy_state(get_state(prev_pc), tmp_state);
      apply_effects(tmp_state); // apply effects of current instruction to new machine state
      if (created_new_state) {
        copy_state(tmp_state, state);
      } else if (!merge_states(tmp_state, state)) { // merge current machine states
        if (!force_continue) {
          // if merge didn't result in any changes: return
          depth = depth - 1;
          return;
        }
      }
    }

    force_continue = 0;

    ir = load_instruction(pc);
    decode();

    if (debug) {
      printf1("%d: ", (char *) depth);
      print_instruction();
      printf1(" (%d):", (char *) pc);
      i = 1;
      while (i < NUMBEROFREGISTERS) {
        if (!is_reg_unknown(state, i)) {
          printf2(" %s=%d", (char *) *(REGISTERS + i), (char *) get_reg(state, i));
        }
        i = i + 1;
      }
      print("\n");
    }

    prev_pc = pc;

    if (is == BEQ) {
      traverse_recursive(pc + imm, pc, current_ra);
      // last loaded instruction from recursive call remains
      // so we need to "refresh" the actual last instruction for the case where the branch isn't taken
      // (the loaded instruction ends up being the beq itself, which has no effect)
      ir = load_instruction(pc);
      decode();
    } else if (is == JAL) {
      if (rd == REG_RA) { // procedure call
        traverse_recursive(pc + imm, pc, pc + INSTRUCTIONSIZE);

        // load and decode jal again
        ir = load_instruction(pc);
        decode();

        // force continuation of execution along this path, even if the next iteration results in a merge with no change
        // this is needed because the machine state at the next instruction got modified by the recursive call earlier
        // but we still need to follow that path as the following machine states haven't been updated yet
        force_continue = 1;
      }
    } else if (is == JALR) {
      // for now: assume that every jalr returns from a function
      if (rd == REG_ZR) {
        depth = depth - 1;
        if (get_state(current_ra) == 0) {
          set_state(current_ra, new_machine_state());
          copy_state(state, get_state(current_ra));
        } else {
          merge_states(state, get_state(current_ra));
        }
        return;
      } else {
        print("Error: jalr with non-zero destination register not supported!");
        exit(1);
      }
    } else if (is == ECALL) {
      // assume that value of a7 is always known
      if (get_reg(state, REG_A7) == SYSCALL_EXIT) {
        depth = depth - 1;
        return;
      }
    }
    pc = pc + INSTRUCTIONSIZE;
  }
}

void selfie_traverse() {
  // allocate for each instruction
  machine_states = zalloc(SIZEOFUINT64STAR * (code_length / INSTRUCTIONSIZE));

  // binary_name = replace_extension(binary_name, "opt");

  reset_library();
  reset_interpreter();

  run = 0;

  set_state(0, new_machine_state());
  tmp_state = new_machine_state();

  traverse_recursive(0, (uint64_t) -1, (uint64_t) -1);
}

void insert_nop(uint64_t position) {
  store_instruction(position, encode_i_format(0, REG_ZR, F3_ADDI, REG_ZR, OP_IMM));
}

void print_state(uint64_t* machine_state) {
  uint64_t i;

  if (machine_state == 0)
    return;

  i = 0;
  while (i < NUMBEROFREGISTERS) {
    if (!is_reg_unknown(machine_state, i)) {
      printf2("\t%s:\t%d\n", (char *) *(REGISTERS + i), (char *) get_reg(machine_state, i));
    }

    i = i + 1;
  }
}

void print_states() {
  uint64_t i;

  i = 0;
  while (i < code_length / INSTRUCTIONSIZE) {
    printf1("%x\n", (char *) (i * INSTRUCTIONSIZE));
    print_state((uint64_t *) *(machine_states + i));
    i = i + 1;
  }
}

// Return first pc after from_pc that is an effective nop, or -1
uint64_t find_next_enop(uint64_t from_pc) {
  uint64_t i;
  uint64_t* state;

  i = from_pc + INSTRUCTIONSIZE; // will miss if first instruction is literally a nop, but doesn't matter
  state = new_machine_state();

  while (i < code_length) {
    if (get_state(i) != 0) {
      copy_state(get_state(i), state);

      ir = load_instruction(i);
      decode();

      if (apply_effects(state) == 1) {
        if (test_states_equal(get_state(i), state)) {
          return i;
        } //else {print_state(get_state(i));print("->\n");print_state(state);print("\n");}
      }
    }

    i = i + INSTRUCTIONSIZE;
  }

  return -1;
}

uint64_t found_enops = 0;

void print_enops() {
  uint64_t last_enop;
  last_enop = find_next_enop(0);
  found_enops = 0;

  while (last_enop != -1) {
    found_enops = found_enops + 1;
    printf1("enop at: %x\n", (char*) last_enop);
    print_state(get_state(last_enop));
    print_instruction();
    print("\n\n");
    last_enop = find_next_enop(last_enop);
  }
}

void patch_enops() {
  uint64_t last_enop;
  last_enop = find_next_enop(0);
  found_enops = 0;

  while (last_enop != -1) {
    found_enops = found_enops + 1;
    insert_nop(last_enop);
    last_enop = find_next_enop(last_enop);
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

  debug = 0;
  selfie_traverse();

  // This is testing code, remove later
  // print_states();
  // printf1("1==1: %d\n", (char*) test_states_equal(machine_states, machine_states));
  // print("109\n");
  // print_state((uint64_t *) *(machine_states + 109));
  // print("110\n");
  // print_state((uint64_t *) *(machine_states + 110));
  // print("111\n");
  // print_state((uint64_t *) *(machine_states + 111));
  // print("114\n");
  // print_state((uint64_t *) *(machine_states + 114));
  // printf1("109==110: %d\n", (char*) test_states_equal((uint64_t*) *(machine_states + 109), (uint64_t*) *(machine_states + 110)));
  // printf1("110==111: %d\n", (char*) test_states_equal((uint64_t*) *(machine_states + 110), (uint64_t*) *(machine_states + 111)));
  // printf1("110==114: %d\n", (char*) test_states_equal((uint64_t*) *(machine_states + 110), (uint64_t*) *(machine_states + 114)));
  // printf1("110==110: %d\n", (char*) test_states_equal((uint64_t*) *(machine_states + 110), (uint64_t*) *(machine_states + 110)));

  //print_states();
  //print_enops();

  patch_enops();

  printf1("found %d enops\n", (char*) found_enops);

  // assert: binary_name is mapped and not longer than MAX_FILENAME_LENGTH

  binary_name = replace_extension(binary_name, "opt");
  selfie_output(binary_name);
  selfie_disassemble(1);

  return EXITCODE_NOERROR;
}
