#include "../selfie.h"
#define uint64_t unsigned long long

uint64_t opt_debug = 0; // debug output. levels = {0,1,2}
uint64_t opt_UNKNOWN = 52596306927616181;
uint64_t opt_pc = 0;

uint64_t opt_memtrack_ld_enable = 0;
uint64_t opt_memtrack_sd_enable = 0;
// Track memory from address BEGIN to (BEGIN - BYTES)
uint64_t opt_memtrack_region_begin = 0; // The memory address to start tracking at (usually gp)
uint64_t opt_memtrack_region_bytes = 4096; // TODO set this to data segment size instead of hardcoded size
uint64_t opt_memtrack_region_words = 512;  //  "


uint64_t access_in_tracked_region(uint64_t addr) {
  //printf3("\tbegin: %x addr: %x end %x", opt_memtrack_region_begin, addr, opt_memtrack_region_begin - opt_memtrack_region_bytes);
  if (addr != opt_UNKNOWN) {
    if (addr <= opt_memtrack_region_begin)
      if (addr > opt_memtrack_region_begin - opt_memtrack_region_bytes)
        return 1;
  }
  return 0;
}

uint64_t *machine_states = (uint64_t *) 0;
uint64_t *cached_machine_states = (uint64_t *) 0;

uint64_t *tmp_state = (uint64_t *) 0; // re-use this to avoid unnecessary allocations (since we can't free memory)
uint64_t *unknown_state = (uint64_t *) 0; // used when setting state to unknown without having to allocate memory

uint64_t *get_unknown_regs(uint64_t *state) { return (uint64_t *) *state; }

uint64_t *get_reg_values(uint64_t *state) { return (uint64_t *) *(state + 1); }

uint64_t *get_vars(uint64_t *state) { return (uint64_t *) *(state + 2); }

void set_unknown_regs(uint64_t *state, uint64_t *unknown_regs) { *state = (uint64_t) unknown_regs; }

void set_reg_values(uint64_t *state, uint64_t *reg_values) { *(state + 1) = (uint64_t) reg_values; }

void set_vars(uint64_t *state, uint64_t *vars) { *(state + 2) = (uint64_t) vars; }

uint64_t get_reg(uint64_t *state, uint64_t reg);

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

uint64_t is_reg_known(uint64_t *state, uint64_t reg) {
  return (uint64_t) (*(get_unknown_regs(state) + reg) == 0);
}

uint64_t is_reg_unknown(uint64_t *state, uint64_t reg) {
  return (uint64_t) (*(get_unknown_regs(state) + reg) == 1);
}

uint64_t is_gp_known(uint64_t *state) { 
  return (uint64_t) (*(get_unknown_regs(state) + REG_GP) == 0);
}

uint64_t gp(uint64_t* state) {
  if (is_reg_unknown(state, REG_GP))
    return opt_UNKNOWN;
  else
    return get_reg(state, REG_GP);
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


// map address to variable *index*
uint64_t addrmap(uint64_t addr) {
  addr = opt_memtrack_region_begin - addr;
  return addr / REGISTERSIZE;
}

void memtrack_boundschk(uint64_t var) {
  if (var >= opt_memtrack_region_words) {
    printf2("attempt to access var %d out of %d tracked", (char*) var, (char*) opt_memtrack_region_words);
    exit(1);
  }
}

void set_var_unknown(uint64_t *state, uint64_t var) {
  memtrack_boundschk(var);
  *(get_vars(state) + var) = opt_UNKNOWN; // TODO don't use magic number
}

void set_var(uint64_t *state, uint64_t var, uint64_t value) {
  memtrack_boundschk(var);
  *(get_vars(state) + var) = value;
}

uint64_t get_var(uint64_t *state, uint64_t var) {
  memtrack_boundschk(var);
  return *(get_vars(state) + var);
}

uint64_t is_var_unknown(uint64_t *state, uint64_t var) {
  memtrack_boundschk(var);
  return get_var(state, var) == opt_UNKNOWN;
}


uint64_t count_nonzero_vars(uint64_t* state) {
  uint64_t count;
  uint64_t i;
  i = 0;
  count = 0;
  while (i < opt_memtrack_region_words) {
    if (is_var_unknown(state, i) == 0) {
      count = count + 1;
    }
    i = i + 1;
  }
  return count;
}


uint64_t *new_machine_state() {
  uint64_t *result;
  uint64_t *unknown_regs;
  uint64_t *reg_values;
  uint64_t *vars;
  uint64_t i;

  unknown_regs = malloc(NUMBEROFREGISTERS * SIZEOFUINT64);
  reg_values = malloc(NUMBEROFREGISTERS * SIZEOFUINT64);
  vars = malloc(opt_memtrack_region_words * SIZEOFUINT64);

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
  while (i < opt_memtrack_region_words) {
    *(vars + i) = opt_UNKNOWN;
    i = i + 1;
  }

  result = malloc(3 * SIZEOFUINT64STAR);
  set_unknown_regs(result, unknown_regs);
  set_reg_values(result, reg_values);
  set_vars(result, vars);
  return result;
}

void upload_data_segment(uint64_t* state) {
  uint64_t current_address;
  uint64_t current_var;
  uint64_t region_begin;
  uint64_t region_end;

  if (binary == 0) {
    print("Binary not yet loaded!");
    exit(1);
  }

  region_begin = binary_length;
  region_end = region_begin - opt_memtrack_region_words * SIZEOFUINT64;

  // current_address is *decreasing* while current_var is *increasing*
  current_address = region_begin;
  current_var = 0;

  while (current_address > region_end) {
    set_var(state, current_var, *(binary + current_address / SIZEOFUINT64));
    //printf2("%x is %x\n", current_address, get_var(state, current_var));
    current_address = current_address - SIZEOFUINT64;
    current_var = current_var + 1;
  }
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
  while (i < opt_memtrack_region_words) {
    set_var(dest, i, get_var(source, i));
    i = i + 1;
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

  printf1("\tknown vars: %d\n", count_nonzero_vars(machine_state));
  //print("\tsample:");
  //i = 0;
  //while (i < 10) {
  //  printf2("\t\tvar %d: %x\n", i, get_var(machine_state, i));
  //  i = i + 1;
  //}
}

// Return 1 iff machine states a and b are equal
uint64_t test_states_equal(uint64_t *a, uint64_t *b) {
  uint64_t i;
  i = 0;

  while (i < NUMBEROFREGISTERS) {
    if (is_reg_unknown(a, i) == 0) { // If a is known
      if (is_reg_unknown(b, i) == 0) { // If b is known
        if (get_reg(a, i) != get_reg(b, i)) { // Check that states are same
          return 0;
        }

      // If we're here, a is known but b isn't
      } else {
        return 0;
      }

    // Here, a is unknown, we need to check that b is too.
    } else {
      if (is_reg_unknown(b, i) == 0) {
        return 0;
      }
    }

    i = i + 1;
  }

  // do basically the same again for global variables
  i = 0;
  while (i < opt_memtrack_region_words) {
    if (is_var_unknown(a, i) == 0) { // If a is known
      if (is_var_unknown(b, i) == 0) { // If b is known
        if (get_var(a, i) != get_var(b, i)) { // Check that states are same
          return 0;
        }

      // If we're here, a is known but b isn't
      } else {
        return 0;
      }

    // Here, a is unknown, we need to check that b is too.
    } else {
      if (is_var_unknown(b, i) == 0) {
        return 0;
      }
    }
    i = i + 1;
  }

  //print("states equal:\n");
  //print("a:\n");
  //print_state(a);
  //print("b:\n");
  //print_state(b);

  return 1;
}

// merge source state into dest state
uint64_t merge_states(uint64_t *source, uint64_t *dest) {
  uint64_t i;
  uint64_t changed;
  uint64_t gp_known; // debugging var

  changed = 0;
  i = 0;

  if (opt_debug == 2) {
    gp_known = 0;
    if (is_reg_known(source, REG_GP))
      gp_known = 1;
    if (is_reg_known(dest, REG_GP))
      gp_known = 1;

    print("Merging ---\n");
    print("Source:\n");
    print_state(source);
    print("dest:\n");
    print_state(dest);
  }

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

  if (opt_debug == 2)
    if (gp_known)
      if (is_reg_unknown(dest, REG_GP)) {
        print("Merge resulted in unknown gp!\n");
        print("merged:\n");
        print_state(dest);
      }

  // do basically the same again for global variables
  i = 0;
  while (i < opt_memtrack_region_words) {
    if (is_var_unknown(source, i)) {
      if (is_var_unknown(dest, i) == 0) {
        set_var_unknown(dest, i);
        changed = changed + 1;
      }

    } else {
      if (is_var_unknown(source, i) == 0) {
        if (get_var(source, i) != get_var(dest, i)) {
          set_var_unknown(dest, i);
          changed = changed + 1;
        }
      }
    }
    i = i + 1;
  }
  return changed;
}

uint64_t gp_val = 0;

// apply effects of current instruction to machine state
// Return 1 iff the instruction had a quantifiable effect
uint64_t apply_effects(uint64_t *state) {
  uint64_t *registers;
  uint64_t tracked_change;
  uint64_t addr;

  if (opt_debug == 2) {
    printf1("applying %x ", opt_pc);
    print_instruction();
    print(":\n");
  }

  tracked_change = 0;

  registers = get_reg_values(state);

  if (is == ADDI) {
    if (is_reg_known(state, rs1)) { // if the register's contents are known
      set_reg(state, rd, *(registers + rs1) + imm); // do the addi

      if (rd == REG_GP) {
        gp_val = *(registers + rs1) + imm;
      }

      tracked_change = 1;

      // On first write to global pointer, also set the memory region to be tracked
      if (rd == REG_GP) {
        if (opt_memtrack_region_begin != 0)
          if (opt_memtrack_region_begin != get_reg(state, rd)) {
            print("gp is mutated!\n");
            exit(1);
          }

        opt_memtrack_region_begin = get_reg(state, rd);
      }

    } else { // else rd is now unknown too
      set_reg_unknown(state, rd);
    }

  } else if (is == LUI) {
    set_reg(state, rd, left_shift(imm, 12));
    tracked_change = 1;
  }

  // handle "weird" instructions
  else if (is == LD) {
    if (opt_memtrack_ld_enable) {
      if (is_reg_known(state, rs1)) {
        addr = get_reg(state, rs1) + imm;

        if (access_in_tracked_region(addr)) {
          printf2("\t%x\tTRACKED load %d", opt_pc, addrmap(addr));
          if (get_var(state, addrmap(addr)) != opt_UNKNOWN)  {
            set_reg(state, rd, get_var(state, addrmap(addr)));
            tracked_change = 1;
          }
          printf1(" -> %x\n", get_var(state, addrmap(addr)));
        }
      }
    }

    if (tracked_change == 0) 
      set_reg_unknown(state, rd);
  } 

  else if (is == SD) {
    if (opt_memtrack_sd_enable) {
      if (is_reg_known(state, rs1)) {
          addr = get_reg(state, rs1) + imm;

          if (access_in_tracked_region(addr)) {
            printf2("\t%x\tTRACKED save %d", opt_pc, addrmap(addr));
            printf1("\t = %x", get_var(state, addrmap(addr)));

            if (is_reg_known(state, rs2)) {
              set_var(state, addrmap(addr), get_reg(state, rs2));
              tracked_change = 1;
            } else
              set_var_unknown(state, addrmap(addr));

            printf1(" -> %x\n", get_var(state, addrmap(addr)));
          }
      }
    }
  }
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

  if (opt_debug == 2) {
    print_state(state);
    print("\n");
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

uint64_t* cfg = 0;
uint64_t* inverse_cfg = 0;

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
uint64_t* return_targets = (uint64_t*) 0;

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

uint64_t is_return_target(uint64_t pc) {
  return *(return_targets + pc/INSTRUCTIONSIZE);
}

void set_return_target(uint64_t pc) {
  *(return_targets + pc/INSTRUCTIONSIZE) = 1;
}

uint64_t function_exits(uint64_t function) {
  return (uint64_t) ((uint64_t) get_returns(function) == -1);
}

void set_function_exits(uint64_t function) {
  // assumption: a function that does an exit ecall does not have any returns in it
  *(cached_returns + function/INSTRUCTIONSIZE) = (uint64_t) -1;
}

uint64_t* ins_to_func = (uint64_t*) 0; // mapping from the address of an instruction to the address of the function it belongs to

void set_ins_to_func(uint64_t ins, uint64_t func) { *(ins_to_func + ins/INSTRUCTIONSIZE) = func; }
uint64_t get_ins_to_func(uint64_t ins)            { return *(ins_to_func + ins/INSTRUCTIONSIZE); }

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

    set_ins_to_func(pc, current_func);

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
        if (current_func == 0) {
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
  uint64_t i;

  if (opt_debug == 2) {
    printf3("CALLED with prev_pc=%x, pc=%x, ra=%x\n", prev_pc, pc, current_ra);
  }

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

      if (pc == 0) {
        upload_data_segment(state);
      }
    }

    if (opt_debug == 2) {
      printf4("traverse_recursive iter: prev_pc=%x, pc=%x, ra=%x, gp=%x\n", prev_pc, pc, current_ra, gp(tmp_state));
      printf1("\tstate %x:\n", prev_pc);
      print_state(get_state(prev_pc));
    }

    if (prev_pc != (uint64_t) -1) { // can't apply effects if last pc is undefined/unknown
      copy_state(get_state(prev_pc), tmp_state);
      opt_pc = prev_pc;
      if (debug) {
        printf1("copied from %x:\n", prev_pc);
        print_state(tmp_state);
      }
      apply_effects(tmp_state); // apply effects of current instruction to new machine state
      if (created_new_state) {
        copy_state(tmp_state, state);
      } else if (!merge_states(tmp_state, state)) { // merge current machine states
        // if merge didn't result in any changes: return
        if (current_ra != -1) {
          if (call_stack_recursion_check()) {
            update_state(current_ra, unknown_state);
            set_reg(get_state(current_ra), REG_GP, gp_val); // temporary workaround
          } else if (get_cached_state(call_stack_peek()) != 0) {
            update_state(current_ra, get_cached_state(call_stack_peek()));
          }
        }
        return;
      }
      //printf4("%d known words at %x, prev_pc=%x, known=%d\n", count_nonzero_vars(state), pc, prev_pc, count_nonzero_vars(get_state(prev_pc)));
    }

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
        update_state(current_ra, state);
        update_cached_state(call_stack_peek(), state);
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
        set_return_target(pc + INSTRUCTIONSIZE);
      }
    }
    pc = pc + INSTRUCTIONSIZE;
  }
}

uint64_t* livedeads = (uint64_t*) 0;

uint64_t* tmp_livedead = (uint64_t*) 0;
uint64_t* unknown_livedead = (uint64_t*) 0;

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

uint64_t* new_unknown_livedead() {
  uint64_t* new;
  uint64_t i;

  new = new_livedead();

  i = 1;

  while (i < NUMBEROFREGISTERS) {
    set_reg_live(new, i);
    i = i + 1;
  }
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
    else {
      set_reg_dead(dest, i);
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

// merge or update
// returns 0 if nothing changed, otherwise a number > 0
uint64_t update_livedead(uint64_t address, uint64_t* new) {
  if (get_livedead(address) == 0) {
    set_livedead(address, new_livedead());
    copy_livedead(new, get_livedead(address));
    return 1;
  } else {
    return merge_livedead(new, get_livedead(address));
  }
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

void recursive_livedead_function(uint64_t pc, uint64_t prev_pc, uint64_t call_pc) {
  uint64_t* livedead;
  uint64_t created_new;
  uint64_t* current;
  uint64_t force_continue;

  force_continue = 0;

  while (1) {
    //printf2("depth=%d, pc=%x\n", call_stack_index, pc);
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
      // printf1("Created new livedead at pc=%x\n", pc);
    }

    ir = load_instruction(pc);
    decode();

    if (prev_pc != (uint64_t) -1) {
      copy_livedead(get_livedead(prev_pc), tmp_livedead);
    }
    else {
      copy_livedead(livedead, tmp_livedead);
    }

    apply_livedead_effects(tmp_livedead); // apply effects of current instruction to live/dead information
    if (created_new) {
      copy_livedead(tmp_livedead, livedead);
    } else if (!merge_livedead(tmp_livedead, livedead)) { // merge current live/dead information
      // if merge didn't result in any changes: return
      if (!force_continue) {
        if (call_pc != -1) {
          if (call_stack_recursion_check()) {
            update_livedead(call_pc, unknown_livedead);
            // printf1("Updated livedead at call_pc=%x (set to unknown)\n", call_pc);
          }
          else if (get_livedead(get_ins_to_func(pc)) != 0) {
            update_livedead(call_pc, get_livedead(get_ins_to_func(pc)));
            // printf1("Updated livedead at call_pc=%x\n", call_pc);
          }
        }
        if (prev_pc != (uint64_t) -1) {
          return;
        }
      }
    }

    force_continue = 0;

    if (pc == get_ins_to_func(pc)) {
      // reached first instruction of the function
      if (call_pc != -1) {
        update_livedead(call_pc, livedead);
        // printf1("Updated livedead at pc=%x (2)\n", call_pc);
      }
      // printf1("Exiting at pc=%x because we reached the top of the function\n", pc);
      return;
    } else {
      current = get_edges(inverse_cfg, pc);

      if (current == (uint64_t *) 0) {
        printf1("Error! No in-edges at pc=%x", (char *) pc);
        exit(1);
      }

      if (is_return_target(pc)) {
        // procedure call

        while (current != 0) {
          call_stack_push(get_ins_to_func(get_to_pc(current)));
          recursive_livedead_function(get_to_pc(current), pc, pc - INSTRUCTIONSIZE);
          call_stack_pop();
          current = get_next_edge(current);
        }

        // continue at the call instruction
        prev_pc = (uint64_t) -1;
        pc = pc - INSTRUCTIONSIZE;

        force_continue = 1;
      }
      else {
        while (get_next_edge(current) != 0) {
          recursive_livedead_function(get_to_pc(current), pc, call_pc);
          current = get_next_edge(current);
        }

        // traverse last edge without recursion to avoid a stack overflow
        prev_pc = pc;
        pc = get_to_pc(current);
      }
    }
  }
}

void recursive_livedead_helper(uint64_t pc) {
  uint64_t func;
  uint64_t* parent;
  uint64_t parent_pc;

  func = get_ins_to_func(pc);

  call_stack_push(func);
  recursive_livedead_function(pc, -1, -1);
  call_stack_pop();

  parent = get_edges(inverse_cfg, func);

  while (parent != (uint64_t*) 0) {
    parent_pc = get_to_pc(parent);
    if (update_livedead(parent_pc, get_livedead(func))) {
      recursive_livedead_helper(parent_pc);
    }
    parent = get_next_edge(parent);
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
  return_targets = zalloc(SIZEOFUINT64 * num_instructions);
  cfg = zalloc(SIZEOFUINT64STAR * num_instructions);
  inverse_cfg = zalloc(SIZEOFUINT64STAR * num_instructions);
  ins_to_func = zalloc(SIZEOFUINT64 * num_instructions);
  livedeads = zalloc(SIZEOFUINT64STAR * num_instructions);
  call_stack = malloc(SIZEOFUINT64STAR * num_instructions);

  // binary_name = replace_extension(binary_name, "opt");

  reset_library();
  reset_interpreter();

  run = 0;

  build_cfg_recursive(0, (uint64_t) -1, 0);

  tmp_state = new_machine_state();
  unknown_state = new_machine_state();

  traverse_recursive(0, (uint64_t) -1, (uint64_t) -1);

  add_return_edges();

  tmp_livedead = new_livedead();
  unknown_livedead = new_unknown_livedead();

  exit = exits;
  while (exit != (uint64_t) 0) {
    recursive_livedead_helper(get_exit_pc(exit));
    exit = get_next_exit(exit);
  }
}


void print_livedead(uint64_t* livedead) {
  uint64_t i;

  if (livedead == 0)
    return;

  i = 0;

  print("\tdead:\t");
  while (i < NUMBEROFREGISTERS) {
    if (!is_reg_live(livedead, i)) {
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
uint64_t ANY_TEMPORARY = (uint64_t) -2;
uint64_t REPLACE = (uint64_t) -3;

// The patter matcher will match the currently decoded instruction against these variables
// if it's not set to ANY, the instruction has to match it.
// For registers (e.g. rd) setting ANY_TEMPORARY will match t0-t6
uint64_t match_is     = 0;
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

// ----------------------------------------------------------------------------
// ----------------------------- PATTERN MATCHER ------------------------------
// ----------------------------------------------------------------------------

// The general workflow works like so:
// * iterate over all instructions
// * try to match each against a pattern:
//   * decode instruction
//   * match it against the pattern's current instruction
//   * if it matches, move pc and pattern to the next instruction
//   * else, reset the pattern and go back n-1 steps

void update_pattern(uint64_t matched_instructions);

void reset_pattern_matcher() {
  match_is     = ANY;
  match_opcode = ANY;
  match_rs1    = ANY;
  match_rs2    = ANY;
  match_rd     = ANY;
  match_imm    = ANY;
  match_funct3 = ANY;
  match_funct7 = ANY;
  match_ir     = ANY;
}

void print_pattern_state() {
  print("current pattern state:");
  printf1("\tmatch_opcode: %x\n", (char*) match_opcode);
  printf1("\tmatch_rs1   : %x\n", (char*) match_rs1);
  printf1("\tmatch_rs2   : %x\n", (char*) match_rs2);
  printf1("\tmatch_rd    : %x\n", (char*) match_rd);
  printf1("\tmatch_imm   : %x\n", (char*) match_imm);
  printf1("\tmatch_funct3: %x\n", (char*) match_funct3);
  printf1("\tmatch_funct7: %x\n", (char*) match_funct7);
  printf1("\tmatch_ir    : %x\n", (char*) match_ir);
  printf1("\tmatch_is    : %x\n", (char*) match_is);
}

// Match currently decoded instruction against current pattern's instruction
// TODO: check that non-ANY registers are dead
uint64_t instruction_matches() {
  // check that there are no in-edges
  if (get_edges(inverse_cfg, pc)!= (uint64_t*) 0) {
    return 0;
  }

  // match_ir overrides
  if (match_ir != ANY) {
    if (match_ir == ir)
      return 1;
    else
      return 0;
  }

  // finally, check for a match
  if (match_rs1 != ANY) {
    if (match_rs1 == ANY_TEMPORARY) {
      if (!is_temporary_register(rs1))
        return 0;
    } else if (match_rs1 != rs1)
      return 0;
  }

  if (match_rs2 != ANY) {
    if (match_rs2 == ANY_TEMPORARY) {
      if (!is_temporary_register(rs2))
        return 0;
    } else if (match_rs2 != rs2)
      return 0;
  }

  if (match_rd != ANY) {
    if (match_rd == ANY_TEMPORARY) {
      if (!is_temporary_register(rd))
        return 0;
    } else if (match_rd != rd)
      return 0;
  }

  if (match_is != ANY)
    if (match_is != is)
      return 0;

  if (match_opcode != ANY)
    if (match_opcode != opcode)
      return 0;

  if (match_imm != ANY)
    if (match_imm != imm)
      return 0;

  if (match_funct3 != ANY)
    if (match_funct3 != funct3)
      return 0;

  if (match_funct7 != ANY)
    if (match_funct7 != funct7)
      return 0;

  return 1;
}

// Return first pc after from_pc that matches the current pattern, or -1
uint64_t next_match(uint64_t from_pc) {
  uint64_t i;
  uint64_t did_break;

  i = from_pc + INSTRUCTIONSIZE;
  number_of_matched_instructions = 0;

  while (i < code_length) {
    did_break = 0;
    update_pattern(0); // go to pattern's next instruction

    // match each instruction in the pattern
    while (number_of_matched_instructions < number_of_instructions_in_pattern) {
      ir = load_instruction(i);
      decode();

      if (instruction_matches()) {
        // We call this twice because it's the simplest way to get the API described in PATTERN LIBRARY
        update_pattern(number_of_matched_instructions); 
        number_of_matched_instructions = number_of_matched_instructions + 1;
        update_pattern(number_of_matched_instructions); 
        i = i + INSTRUCTIONSIZE;

      } else {
        did_break = 1;
        i = i - (number_of_matched_instructions * INSTRUCTIONSIZE);
        number_of_matched_instructions = number_of_instructions_in_pattern; // break out of this loop
      }
    }

    if (!did_break) {
      return i - (number_of_matched_instructions * INSTRUCTIONSIZE);
    }

    i = i + INSTRUCTIONSIZE;
    number_of_matched_instructions = 0;
  }

  return (uint64_t) -1;
}

// ----------------------------------------------------------------------------
// ----------------------------- PATTERN LIBRARY ------------------------------
// ----------------------------------------------------------------------------

uint64_t PATTERN_NONE    = 0;
uint64_t PATTERN_JAL_NOP = 1;
uint64_t PATTERN_POINTER = 2;
uint64_t PATTERN_RETC    = 3;
uint64_t PATTERN_RELOAD  = 4;


// variables to hold state specific to a pattern, required to perform the substitution

uint64_t PATTERN_POINTER_VAL1 = 0;
uint64_t PATTERN_POINTER_VAL2 = 0;
uint64_t PATTERN_POINTER_RD1 = 0;
uint64_t PATTERN_POINTER_RD2 = 0;
uint64_t PATTERN_POINTER_RD3 = 0;

uint64_t PATTERN_RETC_VAL = 0;


// The "API" exposed here is simple:
// A function registered in update_pattern is called and passed a `matched_instructions` parameter.
// This gives the number of instructions that have previously been matched; for example:
//
// 0x908(~512): 0x00300313: addi t1,zero,3
// 0x90C(~512): 0x00800393: addi t2,zero,8    <--- If we are here, matched_instructions is 1.
// 0x910(~512): 0x02730333: mul t1,t1,t2
// 0x914(~512): 0x006282B3: add t0,t0,t1
//
// Functions can assume that they will *eventually* be called with the current instruction decoded into selfie's is, rd, rs1, imm, ... variables.
// That is, in the above example, is=ADDI, rd=REG_T2, rs1=REG_ZR, imm=8
// This isn't guaranteed to happen in the first call to e.g. pattern_pointer(1), but in a subsequent call.



// PATTERN: jal which only goes to next instruction
//
// Example:
//
// 0x800(~506): 0x0040006F: jal zero,1[0x804]
//
// to:
//
// 0x800(~506): 0x00000013: nop
//
void pattern_jal_nop(uint64_t matched_instructions) {
  number_of_instructions_in_pattern = 1;

  // 4194415 = 0x0040006F = jal zero,1
  match_ir = 4194415;
}



// PATTERN: return constant. Avoid using a temporary
//
// Example:
//
// 0x6874(~2615): 0x00100293: addi t0,zero,1
// 0x6878(~2615): 0x00028513: addi a0,t0,0
//
// to:
//
// 0x6878(~2615): 0x00028513: addi a0,zero,1
//
void pattern_retc(uint64_t matched_instructions) {
  number_of_instructions_in_pattern = 2;

  if (matched_instructions == 0) {
    match_is = ADDI;
    match_rd = REG_T0;
    match_rs1 = REG_ZR;
    PATTERN_RETC_VAL = imm;

  } else if (matched_instructions == 1) {
    match_is = ADDI;
    match_rd = REG_A0;
    match_rs1 = REG_T0;
    match_imm = 0;
  }
}

void pattern_retc_replace(uint64_t position) {
  store_instruction(position, encode_i_format(PATTERN_RETC_VAL, REG_ZR, F3_ADDI, REG_A0, OP_IMM));
}



// PATTERN: load/unload. selfie seems to emit a few useless instructions here
//
// Example:
//
// 0x7F4(~506): 0x00050293: addi t0,a0,0
// 0x7F8(~506): 0x00000513: addi a0,zero,0
// 0x7FC(~506): 0x00028513: addi a0,t0,0
//
void pattern_reload(uint64_t matched_instructions) {
  number_of_instructions_in_pattern = 3;

  if (matched_instructions == 0) {
    match_is = ADDI;
    match_rd = REG_T0;
    match_rs1 = REG_A0;
    match_imm = 0;

  } else if (matched_instructions == 1) {
    match_is = ADDI;
    match_rd = REG_A0;
    match_rs1 = REG_ZR;
    match_imm = 0;

  } else if (matched_instructions == 2) {
    match_is = ADDI;
    match_rd = REG_A0;
    match_rs1 = REG_T0;
    match_imm = 0;

  }
}



// PATTERN: Pointer dereference
//
// Example:
//
// 0x908(~512): 0x00300313: addi t1,zero,3
// 0x90C(~512): 0x00800393: addi t2,zero,8
// 0x910(~512): 0x02730333: mul t1,t1,t2
// 0x914(~512): 0x006282B3: add t0,t0,t1
//
// to
//
// 0x908(~512): 0x006282B3: addi t0,t0,24
//
void pattern_pointer(uint64_t matched_instructions) {
  number_of_instructions_in_pattern = 4;

  if (matched_instructions == 0) {
    match_is = ADDI;
    match_rd = ANY_TEMPORARY;
    match_rs1 = REG_ZR;
    PATTERN_POINTER_VAL1 = imm;
    PATTERN_POINTER_RD1 = rd;

  } else if (matched_instructions == 1) {
    match_is = ADDI;
    match_rd = ANY_TEMPORARY;
    match_rs1 = REG_ZR;
    PATTERN_POINTER_VAL2 = imm;
    PATTERN_POINTER_RD2 = rd;

  } else if (matched_instructions == 2) {
    match_is = MUL;
    match_rd = PATTERN_POINTER_RD1;
    match_rs1 = PATTERN_POINTER_RD1;
    match_rs2 = PATTERN_POINTER_RD2;

  } else if (matched_instructions == 3) {
    match_is = ADD;
    match_rd = ANY_TEMPORARY;
    match_rs1 = ANY_TEMPORARY;
    match_rs2 = PATTERN_POINTER_RD1;
    PATTERN_POINTER_RD3 = rd;
  } 
}

void pattern_pointer_replace(uint64_t position) {
  store_instruction(position, encode_i_format(PATTERN_POINTER_VAL1 * PATTERN_POINTER_VAL2, PATTERN_POINTER_RD3, F3_ADDI, PATTERN_POINTER_RD3, OP_IMM));
}

void update_pattern(uint64_t matched_instructions) {
  reset_pattern_matcher();

  if (current_pattern == PATTERN_JAL_NOP)
    pattern_jal_nop(matched_instructions);
  else if (current_pattern == PATTERN_POINTER)
    pattern_pointer(matched_instructions);
  else if (current_pattern == PATTERN_RETC)
    pattern_retc(matched_instructions);
  else if (current_pattern == PATTERN_RELOAD)
    pattern_reload(matched_instructions);
}

void replace_pattern(uint64_t position) {
  if (current_pattern == PATTERN_POINTER)
    pattern_pointer_replace(position);
  else if (current_pattern == PATTERN_RETC)
    pattern_retc_replace(position);
}


// ----------------------------------------------------------------------------
// ----------------------------- TRANSFORMATIONS ------------------------------
// ----------------------------------------------------------------------------

void insert_nop(uint64_t position) {
  store_instruction(position, encode_i_format(0, REG_ZR, F3_ADDI, REG_ZR, OP_IMM));
}

void insert_nops(uint64_t position, uint64_t n) {
  uint64_t i;
  i = 0;

  while (i < n) {
    insert_nop(position + (i * INSTRUCTIONSIZE));
    i = i + 1;
  }
}



uint64_t number_of_matches;

// peephole transformations
void patch_peephole(uint64_t pattern) {
  uint64_t last_match;

  current_pattern = pattern;

  last_match = next_match(0);

  number_of_matches = 0;

  while (last_match != -1) {

    if (opt_debug == 2) {
      printf1("%x\tmatches: ", (char*) last_match);
      print_instruction();
      print("\n");
    }

    number_of_matches = number_of_matches + 1;
    insert_nops(last_match, number_of_instructions_in_pattern);
    replace_pattern(last_match);

    // move past the last instruction in this pattern
    last_match = last_match + (number_of_instructions_in_pattern * INSTRUCTIONSIZE);
    last_match = next_match(last_match);
  }
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


// not in use - broken in weird ways. otherwise; add this code in main()
//print("patching DEAD_OP... ");
//selfie_traverse();
//patch_dead_ops();
//printf1("found %d", (char*) number_of_dead_ops);
//selfie_traverse();
//patch_dead_ops();
//printf1(" + %d", (char*) number_of_dead_ops);
//selfie_traverse();
//patch_dead_ops();
//printf1(" + %d instances\n", (char*) number_of_dead_ops);
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

      if (opt_debug) {
        printf1("%x ", i);
        print_instruction();
        print("\n");
        print_state(state);
        print("\n");
      }


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
  uint64_t total = 0;

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

  print("patching RELOAD... ");
  selfie_traverse();
  patch_peephole(PATTERN_RELOAD);
  total = total + number_of_matches;
  printf1("%d hits\n", (char*) number_of_matches);

  print("patching RETC... ");
  selfie_traverse();
  patch_peephole(PATTERN_RETC);
  total = total + number_of_matches;
  printf1("%d hits\n", (char*) number_of_matches);

  print("patching JAL_NOP... ");
  selfie_traverse();
  patch_peephole(PATTERN_JAL_NOP);
  total = total + number_of_matches;
  printf1("%d hits\n", (char*) number_of_matches);

  print("patching POINTER_DEREF... ");
  selfie_traverse();
  patch_peephole(PATTERN_POINTER);
  total = total + number_of_matches;
  printf1("%d hits\n", (char*) number_of_matches);

  // needs to go after peephole optimizations
  print("patching ENOP... ");
  selfie_traverse();
  patch_enops();
  // number_of_enops also counts previously replaces instructions, so we discount it here
  printf1("%d hits\n", (char*) (number_of_enops - total));

  

  printf1("passes completed! total: %d hits\n", (char*) number_of_enops);

  // assert: binary_name is mapped and not longer than MAX_FILENAME_LENGTH
  binary_name = replace_extension(binary_name, "opt");
  selfie_output(binary_name);
  selfie_disassemble(1);

  return EXITCODE_NOERROR;
}
