#include "../selfie.h"
#define uint64_t unsigned long long

uint64_t *machine_states = (uint64_t *) 0;
uint64_t *cached_machine_states = (uint64_t *) 0;

uint64_t *tmp_state = (uint64_t *) 0; // re-use this to avoid unnecessary allocations (since we can't free memory)

uint64_t *get_unknown_regs(uint64_t *state) { return (uint64_t *) *state; }

uint64_t *get_reg_values(uint64_t *state) { return (uint64_t *) *(state + 1); }

uint64_t *get_vars(uint64_t *state) { return (uint64_t *) *(state + 2); }

void set_unknown_regs(uint64_t *state, uint64_t *unknown_regs) { *state = (uint64_t) unknown_regs; }

void set_reg_values(uint64_t *state, uint64_t *reg_values) { *(state + 1) = (uint64_t) reg_values; }

void set_vars(uint64_t *state, uint64_t *vars) { *(state + 2) = (uint64_t) vars; }

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

uint64_t *get_cached_state(uint64_t pc) {
  if (cached_machine_states == (uint64_t*) 0) {
    print("Cached states aren't initialized yet!");
    exit(1);
  }

  return (uint64_t *) *(cached_machine_states + pc / INSTRUCTIONSIZE);
}

void set_cached_state(uint64_t pc, uint64_t *state) {
  *(cached_machine_states + pc / INSTRUCTIONSIZE) = (uint64_t) state;
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

void set_var_unknown(uint64_t *state, uint64_t var) {
  *(get_vars(state) + var) = 52596306927616181; // TODO don't use magic number
}

uint64_t is_var_unknown(uint64_t *state, uint64_t var) {
  return (uint64_t) (*(get_vars(state) + var) == 52596306927616181);
}

void set_var(uint64_t *state, uint64_t var, uint64_t value) {
  *(get_vars(state) + var) = value;
  // TODO
  //*(get_unknown_regs(state) + reg) = 0;
}

uint64_t get_var(uint64_t *state, uint64_t var) {
  if (is_var_unknown(state, var)) {
    print("Attempted to get value of unknown register!");
    exit(1);
  }
  return *(get_vars(state) + var);
}


uint64_t *new_machine_state() {
  uint64_t *result;
  uint64_t *unknown_regs;
  uint64_t *reg_values;
  uint64_t *vars;
  uint64_t i;

  unknown_regs = malloc(NUMBEROFREGISTERS * SIZEOFUINT64);
  reg_values = malloc(NUMBEROFREGISTERS * SIZEOFUINT64);
  vars = malloc(2048 * SIZEOFUINT64);

  i = 0;
  while (i < NUMBEROFREGISTERS) {
    if (i == REG_ZR) {
      *(unknown_regs + i) = 0;
      *(reg_values + i) = 0;
    } else {
      *(unknown_regs + i) = 1;
    }
    i = i + 1;
  }

  i = 0;
  while (i < 2048) {
    *(vars + i) = 0;
    i = i + 1;
  }

  result = malloc(3 * SIZEOFUINT64STAR);
  set_unknown_regs(result, unknown_regs);
  set_reg_values(result, reg_values);
  set_vars(result, vars);
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

  i = 0;
  while (i < 2048) {
    set_var(dest, i, get_var(source, i));
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

uint64_t *call_stack = (uint64_t *) 0;
uint64_t call_stack_index = 0;

uint64_t call_stack_peek() {
  return call_stack[call_stack_index - 1];
}

uint64_t call_stack_pop() {
  call_stack_index = call_stack_index - 1;
  return call_stack[call_stack_index];
}

void call_stack_push(uint64_t address) {
  call_stack[call_stack_index] = address;
  call_stack_index = call_stack_index + 1;
}

// check if current top address is also somewhere else on the stack to detect recursion
uint64_t call_stack_recursion_check() {
  uint64_t address;
  uint64_t index;

  if (call_stack_index == 1) {
    return 0;
  }

  address = call_stack_peek();
  index = 0;

  while (index < call_stack_index - 1) {
    if (call_stack[index] == address) {
      return 1;
    }
    index = index + 1;
  }
  return 0;
}

// copy or merge
void update_state(uint64_t address, uint64_t* new_state) {
  if (get_state(address) == 0) {
    set_state(address, new_machine_state());
    copy_state(new_state, get_state(address));
  } else {
    merge_states(new_state, get_state(address));
  }
}

void update_cached_state(uint64_t address, uint64_t* new_state) {
  if (get_cached_state(address) == 0) {
    set_cached_state(address, new_machine_state());
    copy_state(new_state, get_cached_state(address));
  } else {
    merge_states(new_state, get_cached_state(address));
  }
}

uint64_t* cfg;
uint64_t* inverse_cfg;

uint64_t* new_edge() {
  return malloc(SIZEOFUINT64STAR + SIZEOFUINT64);
}

uint64_t* get_next_edge(uint64_t* edge) { return (uint64_t*) *edge; }
uint64_t get_to_pc(uint64_t* edge)      { return *(edge + 1); }

void set_next_edge(uint64_t* edge, uint64_t* next) { *edge = (uint64_t) next; }
void set_to_pc(uint64_t* edge, uint64_t to)        { *(edge + 1) = to; }

uint64_t* get_edges(uint64_t* graph, uint64_t pc) {
  return (uint64_t*) *(graph + pc/INSTRUCTIONSIZE);
}

void set_edges(uint64_t* graph, uint64_t pc, uint64_t* edges) {
  *(graph + pc/INSTRUCTIONSIZE) = (uint64_t) edges;
}

uint64_t add_edge(uint64_t* graph, uint64_t from_pc, uint64_t to_pc) {
  uint64_t* head;
  uint64_t* current;
  uint64_t* new;

  head = get_edges(graph, from_pc);
  current = head;

  while (current != (uint64_t*) 0) {
    if (get_to_pc(current) == to_pc) {
      return 0;
    }
    current = get_next_edge(current);
  }

  new = new_edge();
  set_to_pc(new, to_pc);
  set_next_edge(new, head);
  set_edges(graph, from_pc, new);

  return 1;
}

void add_cfg_edge(uint64_t from_pc, uint64_t to_pc) {
  add_edge(cfg, from_pc, to_pc);
  add_edge(inverse_cfg, to_pc, from_pc);
}

uint64_t* cached_returns = (uint64_t*) 0;

uint64_t* new_return() {
  return malloc(SIZEOFUINT64STAR + SIZEOFUINT64);
}

uint64_t* get_next_return(uint64_t* ret) { return (uint64_t*) *ret; }
uint64_t get_return_pc(uint64_t* ret)    { return *(ret + 1); }

void set_next_return(uint64_t* ret, uint64_t* next) { *ret = (uint64_t) next; }
void set_return_pc(uint64_t* ret, uint64_t pc)      { *(ret + 1) = pc; }

uint64_t* get_returns(uint64_t function) {
  return (uint64_t*) *(cached_returns + function/INSTRUCTIONSIZE);
}

void set_returns(uint64_t function, uint64_t* returns) {
  *(cached_returns + function/INSTRUCTIONSIZE) = (uint64_t) returns;
}

uint64_t function_exits(uint64_t function) {
  return (uint64_t) ((uint64_t) get_returns(function) == -1);
}

void set_function_exits(uint64_t function) {
  // assumption: a function that does an exit ecall does not have any returns in it
  *(cached_returns + function/INSTRUCTIONSIZE) = (uint64_t) -1;
}

uint64_t add_return(uint64_t function, uint64_t ret_pc) {
  uint64_t* head;
  uint64_t* current;
  uint64_t* new;

  head = get_returns(function);
  current = head;

  while (current != (uint64_t*) 0) {
    if (get_return_pc(current) == ret_pc) {
      return 0;
    }
    current = get_next_return(current);
  }

  new = new_return();
  set_return_pc(new, ret_pc);
  set_next_return(new, head);
  set_returns(function, new);

  return 1;
}

uint64_t* exits = (uint64_t*) 0;

uint64_t* new_exit() {
  return malloc(SIZEOFUINT64STAR + SIZEOFUINT64);
}

uint64_t* get_next_exit(uint64_t* exit) { return (uint64_t*) *exit; }
uint64_t get_exit_pc(uint64_t* exit)    { return *(exit + 1); }

void set_next_exit(uint64_t* exit, uint64_t* next) { *exit = (uint64_t) next; }
void set_exit_pc(uint64_t* exit, uint64_t pc)      { *(exit + 1) = pc; }

void add_exit(uint64_t pc) {
  uint64_t* new;

  new = new_exit();
  set_exit_pc(new, pc);
  set_next_exit(new, exits);

  exits = new;
}

void build_cfg_recursive(uint64_t pc, uint64_t prev_pc, uint64_t current_func) {
  uint64_t ecall_is_exit;
  uint64_t already_visited;

  ecall_is_exit = 0;
  while (1) {
    if (pc >= code_length) {
      print("Error: pc went past end of code!");
      exit(1);
    }

    already_visited = (uint64_t) (get_edges(inverse_cfg, pc) != (uint64_t *) 0);

    if (prev_pc != -1) {
      add_cfg_edge(prev_pc, pc);
    }

    if (already_visited) {
      return;
    }

    prev_pc = pc;

    ir = load_instruction(pc);
    decode();

    if (is == ADDI) {
      if (rs1 == REG_ZR) {
        if (rd == REG_A7) {
          ecall_is_exit = (uint64_t) (imm == 93);
        }
      }
    }

    if (is == BEQ) {
      build_cfg_recursive(pc + imm, pc, current_func);
    } else if (is == JAL) {
      if (rd == REG_RA) { // procedure call
        build_cfg_recursive(pc + imm, pc, pc + imm);

        ir = load_instruction(pc);
        decode();

        if (function_exits(pc + imm)) {
          return;
        }
        prev_pc = (uint64_t) -1;
      }
      else if (rd == REG_ZR) { // "normal" jump
        pc = pc + imm - INSTRUCTIONSIZE; // subtract INSTRUCTIONSIZE because it gets added again at the end of the loop
      }
      else { // other
        print("Error: jal doesn't seem to be procedure call or \"normal\" jump!");
        exit(1);
      }
    } else if (is == JALR) {
      // for now: assume that every jalr returns from a function
      if (rd == REG_ZR) {
        if (current_func == (uint64_t) -1) {
          print("Error: tried to return from top level");
          exit(1);
        }
        add_return(current_func, pc);
        return;
      } else {
        print("Error: jalr with non-zero destination register not supported!");
        exit(1);
      }
    } else if (is == ECALL) {
      if (ecall_is_exit) {
        add_exit(pc);
        set_function_exits(current_func);
        return;
      }
    }
    pc = pc + INSTRUCTIONSIZE;
  }
}

void traverse_recursive(uint64_t pc, uint64_t prev_pc, uint64_t current_ra) {
  uint64_t created_new_state;
  uint64_t *state;
  uint64_t force_continue;
  uint64_t i;

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
          if (current_ra != -1) {
            if (get_cached_state(call_stack_peek()) != 0) {
              if (!call_stack_recursion_check()) {
                update_state(current_ra, get_cached_state(call_stack_peek()));
              }
            }
          }
          return;
        }
      }
    }

    force_continue = 0;

    ir = load_instruction(pc);
    decode();

    if (debug) {
      printf1("%d: ", (char *) call_stack_index);
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
      // if the registers being compared have known values: explore the corresponding branch only
      if (is_reg_unknown(state, rs1) + is_reg_unknown(state, rs2) == 0) {
        if (get_reg(state, rs1) == get_reg(state, rs2)) {
          // explore branch and return
          traverse_recursive(pc + imm, pc, current_ra);
          return;
        }
        // else: continue exploring current path
      }
        // explore both branches
      else {
        // explore branch in recursive call and continue executing non-branch path in current call
        traverse_recursive(pc + imm, pc, current_ra);
        // last loaded instruction from recursive call remains
        // so we need to "refresh" the actual last instruction for the case where the branch isn't taken
        // (the loaded instruction ends up being the beq itself, which has no effect)
        ir = load_instruction(pc);
        decode();
      }

    } else if (is == JAL) {
      if (rd == REG_RA) { // procedure call
        call_stack_push(pc + imm);
        traverse_recursive(pc + imm, pc, pc + INSTRUCTIONSIZE);

        if (function_exits(call_stack_pop())) {
          // the function we just called doesn't have any returns, only exits
          // therefore the path doesn't continue after the call
          return;
        }

        // load and decode jal again
        // not necessary as we set prev_pc to -1,
        // therefore the next iteration won't attempt to apply the effects of the previous instruction
        /*
        ir = load_instruction(pc);
        decode();
         */

        // force continuation of execution along this path, even if the next iteration results in a merge with no change
        // this is needed because the machine state at the next instruction got modified by the recursive call earlier
        // but we still need to follow that path as the following machine states haven't been updated yet
        force_continue = 1;
        prev_pc = (uint64_t) -1;
      }
      else if (rd == REG_ZR) { // "normal" jump
        pc = pc + imm - INSTRUCTIONSIZE; // subtract INSTRUCTIONSIZE because it gets added again at the end of the loop
      }
      else { // other
        print("Error: jal doesn't seem to be procedure call or \"normal\" jump!");
        exit(1);
      }
    } else if (is == JALR) {
      // for now: assume that every jalr returns from a function
      if (rd == REG_ZR) {
        if (!call_stack_recursion_check()) {
          update_state(current_ra, state);
          update_cached_state(call_stack_peek(), state);
        }
        return;
      } else {
        print("Error: jalr with non-zero destination register not supported!");
        exit(1);
      }
    } else if (is == ECALL) {
      // assume that value of a7 is always known
      if (get_reg(state, REG_A7) == SYSCALL_EXIT) {
        return;
      }
    }
    pc = pc + INSTRUCTIONSIZE;
  }
}

void add_return_edges() {
  uint64_t* current;

  pc = 0;

  while (pc < code_length) {
    ir = load_instruction(pc);
    decode();

    if (is == JAL) {
      if (rd == REG_RA) {
        // function call
        current = get_returns(pc + imm);

        if (current != (uint64_t*) -1) {
          while (current != (uint64_t *) 0) {
            add_cfg_edge(get_return_pc(current), pc + INSTRUCTIONSIZE);
            current = get_next_return(current);
          }
        }
      }
    }
    pc = pc + INSTRUCTIONSIZE;
  }
}

uint64_t* livedeads = (uint64_t*) 0;

uint64_t* tmp_livedead = (uint64_t*) 0;

uint64_t is_reg_live(uint64_t* livedead, uint64_t reg) { return *(livedead + reg); }

void set_reg_live(uint64_t* livedead, uint64_t reg)    { *(livedead + reg) = 1; }
void set_reg_dead(uint64_t* livedead, uint64_t reg) {
  if (reg != REG_ZR) {
    *(livedead + reg) = 0;
  }
}

uint64_t* new_livedead() {
  uint64_t* new;

  new = zalloc(SIZEOFUINT64 * NUMBEROFREGISTERS);
  set_reg_live(new, REG_ZR);
  return new;
}

uint64_t* get_livedead(uint64_t pc) { return (uint64_t*) *(livedeads + pc/INSTRUCTIONSIZE); }

void set_livedead(uint64_t pc, uint64_t* livedead) { *(livedeads + pc/INSTRUCTIONSIZE) = (uint64_t) livedead; }

void copy_livedead(uint64_t* source, uint64_t* dest) {
  uint64_t i;

  i = 0;
  while (i < NUMBEROFREGISTERS) {
    if (is_reg_live(source, i)) {
      set_reg_live(dest, i);
    }
    i = i + 1;
  }
}

uint64_t merge_livedead(uint64_t *source, uint64_t *dest) {
  uint64_t i;
  uint64_t changed;

  changed = 0;
  i = 0;

  while (i < NUMBEROFREGISTERS) {
    if (is_reg_live(source, i)) {
      if (!is_reg_live(dest, i)) {
        set_reg_live(dest, i);
        changed = changed + 1;
      }
    }
    i = i + 1;
  }
  return changed;
}

void apply_livedead_effects(uint64_t *livedead) {
  if ((is == LUI) + (is == JAL)) {
    set_reg_dead(livedead, rd);
  }
  else if ((is == ADDI) + (is == LD) + (is == JALR)) {
    set_reg_dead(livedead, rd);
    set_reg_live(livedead, rs1);
  }
  else if ((is == SD) + (is == BEQ)) {
    set_reg_live(livedead, rs1);
    set_reg_live(livedead, rs2);
  }
  else if ((is == ADD) + (is == SUB) + (is == MUL) + (is == DIVU) + (is == REMU) + (is == SLTU)) {
    set_reg_dead(livedead, rd);
    set_reg_live(livedead, rs1);
    set_reg_live(livedead, rs2);
  }
  else if (is == ECALL) {
    set_reg_dead(livedead, REG_A0);
    set_reg_live(livedead, REG_A7);
  }
  else {
    print("Error: unhandled instruction in apply_livedead_effects!\n");
    exit(1);
  }
}

void recursive_livedead(uint64_t pc, uint64_t prev_pc) {
  uint64_t* livedead;
  uint64_t created_new;
  uint64_t* current;

  while (1) {
    if (pc >= code_length) {
      print("Error: pc went past end of code!");
      exit(1);
    }

    created_new = 0;
    livedead = get_livedead(pc);
    if (livedead == (uint64_t *) 0) {
      livedead = new_livedead();
      set_livedead(pc, livedead);
      created_new = 1;
    }

    ir = load_instruction(pc);
    decode();

    if (prev_pc != (uint64_t) -1) {
      copy_livedead(get_livedead(prev_pc), tmp_livedead);
    }
    else {
      tmp_livedead = new_livedead();
    }

    apply_livedead_effects(tmp_livedead); // apply effects of current instruction to live/dead information
    if (created_new) {
      copy_livedead(tmp_livedead, livedead);
    } else if (!merge_livedead(tmp_livedead, livedead)) { // merge current live/dead information
      // if merge didn't result in any changes: return
      return;
    }

    current = get_edges(inverse_cfg, pc);

    if (current == (uint64_t*) 0) {
      if (pc != 0) {
        printf1("Error! No in-edges at pc=%x", (char*) pc);
        exit(1);
      }
      else {
        // reached cfg root
        return;
      }
    }

    while (get_next_edge(current) != 0) {
      recursive_livedead(get_to_pc(current), pc);
      current = get_next_edge(current);
    }

    // traverse last edge without recursion to avoid a stack overflow
    prev_pc = pc;
    pc = get_to_pc(current);
  }
}

void selfie_traverse() {
  uint64_t num_instructions;
  uint64_t* exit;

  num_instructions = code_length / INSTRUCTIONSIZE;
  // allocate for each instruction
  machine_states = zalloc(SIZEOFUINT64STAR * num_instructions);
  // these allocations could be way smaller (with more complicated code)
  // but we need O(n) memory with n = number of instructions anyway
  cached_machine_states = zalloc(SIZEOFUINT64STAR * num_instructions);
  cached_returns = zalloc(SIZEOFUINT64STAR * num_instructions);
  cfg = zalloc(SIZEOFUINT64STAR * num_instructions);
  inverse_cfg = zalloc(SIZEOFUINT64STAR * num_instructions);
  livedeads = zalloc(SIZEOFUINT64STAR * num_instructions);
  call_stack = malloc(SIZEOFUINT64STAR * num_instructions);

  // binary_name = replace_extension(binary_name, "opt");

  reset_library();
  reset_interpreter();

  run = 0;

  build_cfg_recursive(0, (uint64_t) -1, (uint64_t) -1);

  tmp_state = new_machine_state();
  traverse_recursive(0, (uint64_t) -1, (uint64_t) -1);

  add_return_edges();

  exit = exits;
  while (exit != (uint64_t) 0) {
    recursive_livedead(get_exit_pc(exit), (uint64_t) -1);
    exit = get_next_exit(exit);
  }
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

void print_livedead(uint64_t* livedead) {
  uint64_t i;

  if (livedead == 0)
    return;

  i = 0;

  print("\tlive:\t");
  while (i < NUMBEROFREGISTERS) {
    if (is_reg_live(livedead, i)) {
      printf1("%s ", (char *) *(REGISTERS + i));
    }

    i = i + 1;
  }
  println();
}

void print_states_and_livedeads() {
  uint64_t i;
  uint64_t* edge;

  i = 0;
  while (i < code_length / INSTRUCTIONSIZE) {
    printf1("%x:", (char *) (i * INSTRUCTIONSIZE));
    ir = load_instruction(i * INSTRUCTIONSIZE);
    decode();
    print("\t");
    print_instruction();
    println();
    print_state((uint64_t *) *(machine_states + i));
    print_livedead((uint64_t *) *(livedeads + i));
    print("\tnext:\t");
    edge = get_edges(cfg, i * INSTRUCTIONSIZE);
    while (edge != (uint64_t *) 0) {
      printf1("%x ", (char *) get_to_pc(edge));
      edge = get_next_edge(edge);
    }
    println();
    println();
    i = i + 1;
  }
}


// ---------------------------------------------------------------------------------
// ----------------------------- PATTERN MATCHER VARS ------------------------------
// ---------------------------------------------------------------------------------

uint64_t ANY = (uint64_t) -1; // matches anything
uint64_t ANY_TEMPORARY = (uint64_t) -2; // use selfies is_temporary_register

// The patter matcher will match the currently decoded instruction against these variables
// if it's not set to ANY, the instruction has to match it.
// For registers (e.g. rd) setting ANY_TEMPORARY will match t0-t6
uint64_t match_opcode = 0;
uint64_t match_rs1    = 0;
uint64_t match_rs2    = 0;
uint64_t match_rd     = 0;
uint64_t match_imm    = 0;
uint64_t match_funct3 = 0;
uint64_t match_funct7 = 0;

// If this is not ANY, this overrides the previous settings, matching the exact instruction given by this.
uint64_t match_ir = 0;

// set by pattern library
uint64_t number_of_instructions_in_pattern = 0;

// Number of instructions that the current pattern has matched
uint64_t number_of_matched_instructions = 0;

uint64_t current_pattern = 0;

uint64_t PATTERN_NONE = 0;
uint64_t POINTLESS_JAL = 1;


// ----------------------------------------------------------------------------
// ----------------------------- PATTERN LIBRARY ------------------------------
// ----------------------------------------------------------------------------


// jal which only goes to next instruction
void pattern_pointless_jal() {
  number_of_instructions_in_pattern = 1;

  // 4194415 = 0x0040006F = jal zero,1
  match_ir = 4194415;
}

void set_pattern() {
  if (current_pattern == POINTLESS_JAL)
    pattern_pointless_jal();
}

// ----------------------------------------------------------------------------
// ----------------------------- PATTERN MATCHER ------------------------------
// ----------------------------------------------------------------------------

void reset_pattern_matcher() {
  match_opcode = 0;
  match_rs1    = 0;
  match_rs2    = 0;
  match_rd     = 0;
  match_imm    = 0;
  match_funct3 = 0;
  match_funct7 = 0;
  match_ir = 0;
}

// Match currently decoded instruction against current pattern
uint64_t match_current() {
  if (match_ir != ANY) {
    if (match_ir == ir)
      return 1;
    else
      return 0;
  }

  if (match_opcode != ANY)
    if (match_opcode != opcode)
      return 0;

  //... TODO match everything else

  if (match_rd != ANY)
    if (match_rd != ANY_TEMPORARY) {
      if (!is_temporary_register(rd))
        return 0;
      else if (match_rd != rd)
        return 0;
    }

  return 1;
}

// Return first pc after from_pc that matches the current pattern, or -1
uint64_t next_match(uint64_t from_pc) {
  uint64_t i;
  uint64_t did_break = 0;

  i = from_pc + INSTRUCTIONSIZE;
  number_of_matched_instructions = 0;

  while (i < code_length) {
    // match each instruction in the pattern
    while (number_of_matched_instructions != number_of_instructions_in_pattern) {
      ir = load_instruction(i);
      decode();

      if (match_current()) {
        number_of_matched_instructions = number_of_matched_instructions + 1;
        set_pattern(); // go to pattern's next instruction
        i = i + INSTRUCTIONSIZE;
      } else {
        did_break = 1;
        i = i - number_of_matched_instructions;
        number_of_matched_instructions = number_of_instructions_in_pattern;
      }
    }

    if (!did_break) {
        return i - number_of_matched_instructions;
    }
  }

  return (uint64_t) -1;
}

uint64_t eliminate_matches() {
  // care: after eliming n instructions, move pc n instructions further
}


// ----------------------------------------------------------------------------
// ----------------------------- TRANSFORMATIONS ------------------------------
// ----------------------------------------------------------------------------

void insert_nop(uint64_t position) {
  store_instruction(position, encode_i_format(0, REG_ZR, F3_ADDI, REG_ZR, OP_IMM));
}


uint64_t find_next_dead_op(uint64_t from_pc) {
  uint64_t i;

  i = from_pc + INSTRUCTIONSIZE; // will miss if first instruction is literally a nop, but doesn't matter

  while (i < code_length) {
    ir = load_instruction(i);
    decode();

    if (i < code_length - INSTRUCTIONSIZE)
      if (i > 1000) // skip ecalls etc.
        if (is != JAL) // don't replace jumps
          if (is != BEQ)
            if (is != JALR)
              if (get_livedead(i + INSTRUCTIONSIZE))
                if (is_reg_live(get_livedead(i + INSTRUCTIONSIZE), rd) == 0)
                  return i;
    i = i + INSTRUCTIONSIZE;
  }

  return (uint64_t) -1;
}

uint64_t number_of_dead_ops;

void patch_dead_ops() {
  uint64_t last_dead_op;
  last_dead_op = find_next_dead_op(0);
  number_of_dead_ops = 0;

  while (last_dead_op != -1) {
    number_of_dead_ops = number_of_dead_ops + 1;
    insert_nop(last_dead_op);
    last_dead_op = find_next_dead_op(last_dead_op);
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
        } 
      }

    // TODO move to find_dead_code or something
    } else {
      return i;
    }

    i = i + INSTRUCTIONSIZE;
  }

  return (uint64_t) -1;
}

uint64_t number_of_enops = 0;

void print_enops() {
  uint64_t last_enop;
  last_enop = find_next_enop(0);
  number_of_enops = 0;

  while (last_enop != -1) {
    number_of_enops = number_of_enops + 1;
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
  number_of_enops = 0;

  while (last_enop != -1) {
    number_of_enops = number_of_enops + 1;
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

  /////////////////////////
  // OPTIMIZATION PASSES //
  /////////////////////////

  // TODO un-unroll this
  selfie_traverse();
  patch_enops();
  printf1("found %d enops\n", (char*) number_of_enops);

  selfie_traverse();
  patch_dead_ops();
  printf1("pass 1: found %d dead ops\n", (char*) number_of_dead_ops);

  selfie_traverse();
  patch_dead_ops();
  printf1("pass 2: found %d dead ops\n", (char*) number_of_dead_ops);

  selfie_traverse();
  patch_dead_ops();
  printf1("pass 3: found %d dead ops\n", (char*) number_of_dead_ops);


  // assert: binary_name is mapped and not longer than MAX_FILENAME_LENGTH

  binary_name = replace_extension(binary_name, "opt");
  selfie_output(binary_name);
  selfie_disassemble(1);

  return EXITCODE_NOERROR;
}
