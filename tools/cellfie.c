/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

Cellfie is an instruction-level reversible cellular machine for
RISC-R in C*, see projects/reversible.md and cellfie.md. The machine
is a grid of cells on a torus and one token. A cell holds one RISC-R
instruction, one memory word, a mirror, a router, or nothing. The
token is at one cell, has a heading, and carries the program counter,
the register file, and two words for what is in transit, an address
and a datum. In one tick the cell under the token acts on the token
and the token moves one cell along its heading. Nothing else changes,
so the simulator is event-driven: a tick costs one cell.

The cell rule is RISC-R per cell plus token movement: an instruction
cell applies its instruction to the registers of a token that enters
it along its path. Control flow and memory access are movement: an
instruction cell is a mirror for a token that takes a branch, jumps,
or exchanges a register with memory, and sends it off its path onto
wire, which is blank cells, mirrors, and routers that are mirrors
only if a bit of the token's program counter or address is set. The
token enters the instruction cell at the other end, or returns to
the one it left, from the side.

Every cell permutes the headings and is a bijection on the rest of
the token and on itself, so the rule is a bijection on all states,
and the inverse rule, move back and undo, runs the machine backward
without a trace. Bitr proves both, on the BTOR2 models that cellfie
generates of its rule and its inverse rule for a given grid size.

Usage: cellfie { -l layout | -o layout | -f ticks | -b ticks | -rev ticks |
                 -inverse | -noproperties | -btor2 width height | -check states }

-l loads a layout, -o writes the grid and the token as layout; -f
runs at most ticks forward, stopping where a property holds for the
token, at an exit system call for instance; -b runs ticks backward;
-rev runs forward and then as many ticks backward, and checks that
the grid and the token are restored bit for bit. -btor2 writes the
rule for a grid of width times height cells as BTOR2 model, with
-inverse before it the inverse rule, with -noproperties without the
properties that say where a token stops. -check compares the
simulator with the model, forward and backward, on random states.
*/

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------------- CELLFIE ----------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------------- GRID ------------------------------
// -----------------------------------------------------------------

void allocate_grid(uint64_t width, uint64_t height);

uint64_t cell_index(uint64_t x, uint64_t y);

uint64_t get_cell_kind(uint64_t cell)        { return cell % 8; }
uint64_t get_cell_orientation(uint64_t cell) { return cell / 8 % 4; }
uint64_t get_cell_mirror(uint64_t cell)      { return cell / 32 % 2; }

uint64_t encode_cell(uint64_t kind, uint64_t orientation, uint64_t mirror_kind) {
  return kind + orientation * 8 + mirror_kind * 32;
}

uint64_t get_router_bit(uint64_t word)   { return word % 64; }
uint64_t get_router_field(uint64_t word) { return word / 64 % 2; }

// ------------------------ GLOBAL CONSTANTS -----------------------

// cell kinds, all other kinds are blank as well

uint64_t CELL_BLANK       = 0; // the token passes
uint64_t CELL_MIRROR      = 1; // turns the token
uint64_t CELL_ROUTER      = 2; // turns the token if a bit of its pc or address is set
uint64_t CELL_MEMORY      = 3; // exchanges its word with the datum of the token
uint64_t CELL_INSTRUCTION = 4; // applies its RISC-R instruction to the token

// headings and orientations, counterclockwise; row 0 is the northern row

uint64_t EAST  = 0;
uint64_t NORTH = 1;
uint64_t WEST  = 2;
uint64_t SOUTH = 3;

// mirrors: a slash exchanges east with north and west with south,
// a backslash exchanges east with south and west with north

uint64_t SLASH     = 0;
uint64_t BACKSLASH = 1;

// what a router looks at

uint64_t FIELD_PC      = 0;
uint64_t FIELD_ADDRESS = 1;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t grid_width  = 0; // in cells, a power of two
uint64_t grid_height = 0; // in cells, a power of two

uint64_t grid_size = 0; // number of cells

uint64_t* cell_kinds = (uint64_t*) 0; // kind, orientation, and mirror of each cell
uint64_t* cell_words = (uint64_t*) 0; // instruction, memory word, or router bit and field

// -----------------------------------------------------------------
// ----------------------------- TOKEN -----------------------------
// -----------------------------------------------------------------

uint64_t  get_token_register(uint64_t reg);
void      set_token_register(uint64_t reg, uint64_t value);

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t token_x       = 0; // column of the cell the token is at
uint64_t token_y       = 0; // row
uint64_t token_heading = 0; // where the token moves next

uint64_t token_pc      = 0; // address of the instruction the token enters next, or travels to
uint64_t token_address = 0; // in transit: address of the memory word, or of the instruction left
uint64_t token_data    = 0; // in transit: register value on its way to memory, or back

uint64_t* token_registers = (uint64_t*) 0; // register file

// -----------------------------------------------------------------
// --------------------------- CELL RULE ---------------------------
// -----------------------------------------------------------------

uint64_t mirror_heading(uint64_t heading, uint64_t mirror_kind);

void decode_cell(uint64_t word);

uint64_t is_reversible_instruction();

void advance_on_path();

void cell_compute();
void cell_exchange(uint64_t on_path);
void cell_branch(uint64_t on_path);
void cell_jump(uint64_t on_path);
void cell_return(uint64_t on_path);

void act_instruction(uint64_t orientation, uint64_t mirror_kind, uint64_t word);
void act();

void move_token();

void tick();

uint64_t token_property();

// ------------------------ GLOBAL CONSTANTS -----------------------

// properties of a token at a cell: where a RISC-R program stops

uint64_t PROPERTY_NONE                = 0;
uint64_t PROPERTY_ILLEGAL_INSTRUCTION = 1; // not RISC-R: unknown, sd, rd is a source, malformed jalr
uint64_t PROPERTY_IRREVERSIBLE_LINK   = 2; // jal with nonzero link register
uint64_t PROPERTY_DIVISION_BY_ZERO    = 3;
uint64_t PROPERTY_EXIT                = 4; // exit system call
uint64_t PROPERTY_UNSUPPORTED_SYSCALL = 5; // any other system call

uint64_t NUMBER_OF_PROPERTIES = 5;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t reverse = 0; // flag for running the rule backward and for generating the inverse model

uint64_t executed_ticks        = 0; // ticks forward minus ticks backward
uint64_t executed_instructions = 0; // instructions forward minus instructions backward

// -----------------------------------------------------------------
// ---------------------------- LAYOUT -----------------------------
// -----------------------------------------------------------------

uint64_t* read_file(char* name);

uint64_t layout_character();
void     next_layout_character();

void layout_error(char* message);

uint64_t is_decimal_digit(uint64_t c);
uint64_t hexadecimal_value(uint64_t c);

void     skip_layout_blanks();
void     skip_layout_spaces();
void     skip_layout_line();
void     expect_layout_character(uint64_t c);
uint64_t scan_decimal();
uint64_t scan_hexadecimal(uint64_t digits);
uint64_t scan_mirror();
uint64_t scan_heading();

void load_token();
void load_register();
void load_header();
void load_cells();
void load_layout(char* name);

void print_hexadecimal_digits(uint64_t value, uint64_t digits);
void print_heading(uint64_t heading);
void print_mirror(uint64_t mirror_kind);
void print_cell(uint64_t index);

uint64_t is_blank_cell(uint64_t index);
uint64_t are_cells_equal(uint64_t i, uint64_t j);

void write_layout(char* name);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t LAYOUT_CHUNK = 4096; // bytes read at once

// ------------------------ GLOBAL VARIABLES -----------------------

char* layout_name = (char*) 0;

uint64_t* layout_text = (uint64_t*) 0;
uint64_t  layout_size = 0; // in bytes
uint64_t  layout_pos  = 0;
uint64_t  layout_line = 1;

// -----------------------------------------------------------------
// --------------------------- SIMULATOR ---------------------------
// -----------------------------------------------------------------

uint64_t  snapshot_size();
uint64_t* take_snapshot(uint64_t* snapshot);
void      restore_snapshot(uint64_t* snapshot);
uint64_t  is_snapshot(uint64_t* snapshot, uint64_t reporting);

void print_token();
void print_property(uint64_t property);

uint64_t run_forward(uint64_t ticks);
void     run_backward(uint64_t ticks);

uint64_t run_forward_and_backward(uint64_t ticks);

// -----------------------------------------------------------------
// ----------------------------- MODEL -----------------------------
// -----------------------------------------------------------------

uint64_t* new_sort(uint64_t bits);
uint64_t* new_number(uint64_t* sid, uint64_t value);

uint64_t* new_not(uint64_t* a);
uint64_t* new_and(uint64_t* a, uint64_t* b);
uint64_t* new_or(uint64_t* a, uint64_t* b);
uint64_t* new_eq(uint64_t* a, uint64_t* b);
uint64_t* new_ite(uint64_t* condition, uint64_t* a, uint64_t* b);
uint64_t* new_add(uint64_t* a, uint64_t* b);
uint64_t* new_sub(uint64_t* a, uint64_t* b);
uint64_t* new_bits(uint64_t* value, uint64_t upper, uint64_t lower);
uint64_t* new_join(uint64_t* upper, uint64_t* lower);

uint64_t* new_is_field(uint64_t* field, uint64_t value);

uint64_t* new_delta(uint64_t* sid, uint64_t* low_nid, uint64_t* high_nid);
uint64_t* new_delta_x(uint64_t* heading_nid);
uint64_t* new_delta_y(uint64_t* heading_nid);

uint64_t* new_effect(uint64_t* effect);
uint64_t* new_choice(uint64_t* condition_nid, uint64_t* then_effect, uint64_t* else_effect);

uint64_t* new_arithmetic_choice(uint64_t* funct3_nid, uint64_t* funct7_nid, uint64_t* same,
  uint64_t* add_effect, uint64_t* sub_effect, uint64_t* mul_effect,
  uint64_t* divu_effect, uint64_t* remu_effect, uint64_t* sltu_effect);

void model_sorts(uint64_t xbits, uint64_t ybits);
void model_states();
void model_rule();

void print_model(char* name, uint64_t properties);

// ------------------------ GLOBAL CONSTANTS -----------------------

// states of the model, in the order of the state of the simulator

uint64_t STATE_X         = 0;
uint64_t STATE_Y         = 1;
uint64_t STATE_HEADING   = 2;
uint64_t STATE_PC        = 3;
uint64_t STATE_ADDRESS   = 4;
uint64_t STATE_DATA      = 5;
uint64_t STATE_REGISTERS = 6;
uint64_t STATE_KINDS     = 7;
uint64_t STATE_WORDS     = 8;

uint64_t NUMBER_OF_STATES = 9;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* SID_HEADING   = (uint64_t*) 0;
uint64_t* SID_X         = (uint64_t*) 0;
uint64_t* SID_Y         = (uint64_t*) 0;
uint64_t* SID_INDEX     = (uint64_t*) 0;
uint64_t* SID_CELL      = (uint64_t*) 0;
uint64_t* SID_WORD      = (uint64_t*) 0;
uint64_t* SID_REGISTER  = (uint64_t*) 0;
uint64_t* SID_REGISTERS = (uint64_t*) 0;
uint64_t* SID_KINDS     = (uint64_t*) 0;
uint64_t* SID_WORDS     = (uint64_t*) 0;

uint64_t* NID_FALSE = (uint64_t*) 0;
uint64_t* NID_TRUE  = (uint64_t*) 0;

uint64_t* state_nids = (uint64_t*) 0; // state lines

uint64_t* forward_nids = (uint64_t*) 0; // next value of each state in the rule
uint64_t* inverse_nids = (uint64_t*) 0; // next value of each state in the inverse rule

uint64_t* property_nids = (uint64_t*) 0; // condition of each property, forward only

uint64_t printing_properties = 1; // flag for printing the properties into the model

// -----------------------------------------------------------------
// ----------------------------- CHECK -----------------------------
// -----------------------------------------------------------------

uint64_t random_number();
uint64_t random_below(uint64_t n);
uint64_t random_value();
uint64_t random_register();
uint64_t random_instruction();

void random_state();

void set_model_state();
void step_model(uint64_t* next_nids);
void advance_model();

uint64_t is_model_state(char* direction);

uint64_t check_rule(uint64_t states);

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t random_seed = 1;

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

uint64_t cellfie();

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------------- GRID ------------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

void allocate_grid(uint64_t width, uint64_t height) {
  // the grid is a torus of blank cells, its width and height are the
  // powers of two of at least two cells that width and height fit in

  grid_width = 2;

  while (grid_width < width)
    grid_width = grid_width * 2;

  grid_height = 2;

  while (grid_height < height)
    grid_height = grid_height * 2;

  grid_size = grid_width * grid_height;

  cell_kinds = zmalloc(grid_size * sizeof(uint64_t));
  cell_words = zmalloc(grid_size * sizeof(uint64_t));

  if (token_registers == (uint64_t*) 0)
    token_registers = zmalloc(NUMBEROFREGISTERS * sizeof(uint64_t));
}

uint64_t cell_index(uint64_t x, uint64_t y) {
  return y * grid_width + x;
}

// -----------------------------------------------------------------
// ----------------------------- TOKEN -----------------------------
// -----------------------------------------------------------------

uint64_t get_token_register(uint64_t reg) {
  return *(token_registers + reg);
}

void set_token_register(uint64_t reg, uint64_t value) {
  // register zero is always 0
  if (reg != REG_ZR)
    *(token_registers + reg) = value;
}

// -----------------------------------------------------------------
// --------------------------- CELL RULE ---------------------------
// -----------------------------------------------------------------

uint64_t mirror_heading(uint64_t heading, uint64_t mirror_kind) {
  // a slash exchanges east with north and west with south,
  // a backslash exchanges east with south and west with north

  if (mirror_kind == SLASH) {
    if (heading % 2 == 0)
      return heading + 1;
    else
      return heading - 1;
  } else
    return 3 - heading;
}

void decode_cell(uint64_t word) {
  // decodes the lower half of the word of an instruction cell as RISC-U
  // encoding into selfie's variables; is is 0 if it is no such encoding

  ir = get_bits(word, 0, INSTRUCTIONSIZEINBITS);

  opcode = get_opcode(ir);
  rd     = get_rd(ir);
  funct3 = get_funct3(ir);
  rs1    = get_rs1(ir);
  rs2    = get_rs2(ir);
  funct7 = get_funct7(ir);

  imm = 0;

  is = 0;

  if (opcode == OP_IMM) {
    imm = get_immediate_i_format(ir);

    if (funct3 == F3_ADDI)
      is = ADDI;
  } else if (opcode == OP_LOAD) {
    imm = get_immediate_i_format(ir);

    if (funct3 == F3_LD)
      is = LOAD;
  } else if (opcode == OP_STORE) {
    if (funct3 == F3_SD)
      is = STORE;
  } else if (opcode == OP_OP) {
    if (funct3 == F3_ADD) {
      if (funct7 == F7_ADD)
        is = ADD;
      else if (funct7 == F7_SUB)
        is = SUB;
      else if (funct7 == F7_MUL)
        is = MUL;
    } else if (funct3 == F3_DIVU) {
      if (funct7 == F7_DIVU)
        is = DIVU;
    } else if (funct3 == F3_REMU) {
      if (funct7 == F7_REMU)
        is = REMU;
    } else if (funct3 == F3_SLTU) {
      if (funct7 == F7_SLTU)
        is = SLTU;
    }
  } else if (opcode == OP_BRANCH) {
    imm = get_immediate_b_format(ir);

    if (funct3 == F3_BEQ)
      is = BEQ;
  } else if (opcode == OP_JAL) {
    imm = get_immediate_j_format(ir);

    is = JAL;
  } else if (opcode == OP_JALR) {
    imm = get_immediate_i_format(ir);

    if (funct3 == F3_JALR)
      is = JALR;
  } else if (opcode == OP_LUI) {
    imm = left_shift(get_immediate_u_format(ir), 12);

    is = LUI;
  } else if (opcode == OP_SYSTEM) {
    if (funct3 == F3_ECALL)
      is = ECALL;
  }
}

uint64_t is_reversible_instruction() {
  // the rules of RISC-R that only depend on the instruction, see riscr.md:
  // there is no sd, rd is distinct from rs1 and rs2 unless rd is zero, and
  // jalr is jalr rd,0(rd) with rd not zero; a cell with any other
  // instruction is blank

  if (is == LUI)
    return 1;
  else if (is == JAL)
    return 1;
  else if (is == BEQ)
    return 1;
  else if (is == ECALL)
    return 1;
  else if (is == JALR) {
    if (rd == rs1)
      if (rd != REG_ZR)
        return imm == 0;

    return 0;
  } else if (is == STORE)
    return 0;
  else if (is == 0)
    return 0;
  else if (rd == REG_ZR)
    return 1;
  else if (rd == rs1)
    return 0;
  else if (is == ADDI)
    return 1;
  else if (is == LOAD)
    return 1;
  else
    return rd != rs2;
}

void advance_on_path() {
  // the token stays on the path: its pc advances by one instruction,
  // backward it goes back by one

  if (reverse) {
    token_pc = token_pc - INSTRUCTIONSIZE;

    executed_instructions = executed_instructions - 1;
  } else {
    token_pc = token_pc + INSTRUCTIONSIZE;

    executed_instructions = executed_instructions + 1;
  }
}

void cell_compute() {
  uint64_t rs1_value;
  uint64_t rs2_value;
  uint64_t rd_value;

  // lui, addi, add, sub: rd += f(rs1, rs2), backward rd -= f(rs1, rs2);
  // mul, divu, remu, sltu: rd ^= f(rs1, rs2) in both directions; and
  // ld zero, which does nothing; the token stays on the path

  advance_on_path();

  if (rd == REG_ZR)
    return;

  rs1_value = get_token_register(rs1);
  rs2_value = get_token_register(rs2);
  rd_value  = get_token_register(rd);

  if (is == LUI)
    rs1_value = imm;
  else if (is == ADDI)
    rs1_value = rs1_value + imm;
  else if (is == ADD)
    rs1_value = rs1_value + rs2_value;
  else if (is == SUB)
    rs1_value = rs1_value - rs2_value;
  else {
    // a division by zero is a property of the token, the quotient
    // and the remainder are 0 here

    if (is == MUL)
      rs1_value = rs1_value * rs2_value;
    else if (is == SLTU)
      rs1_value = rs1_value < rs2_value;
    else if (rs2_value == 0)
      rs1_value = 0;
    else if (is == DIVU)
      rs1_value = rs1_value / rs2_value;
    else
      rs1_value = rs1_value % rs2_value;

    set_token_register(rd, bitwise_xor(rd_value, rs1_value));

    return;
  }

  if (reverse)
    set_token_register(rd, rd_value - rs1_value);
  else
    set_token_register(rd, rd_value + rs1_value);
}

void cell_exchange(uint64_t on_path) {
  uint64_t address;
  uint64_t rd_value;

  // ld rd,imm(rs1) with rd not zero exchanges rd with a memory word: the
  // token leaves the path with rd as its datum and the address of the
  // word, travels to the memory cell, which exchanges its word with the
  // datum, and returns from the side, where the datum becomes rd and the
  // address is uncomputed. Backward the same happens the other way round.

  address = get_token_register(rs1) + imm;

  if (on_path) {
    if (reverse) {
      // undo the return
      token_pc = token_pc - INSTRUCTIONSIZE;

      token_address = token_address + address;
    } else {
      token_address = token_address + address;

      executed_instructions = executed_instructions + 1;
    }
  } else if (reverse) {
    // undo the departure
    token_address = token_address - address;

    executed_instructions = executed_instructions - 1;
  } else {
    token_address = token_address - address;

    token_pc = token_pc + INSTRUCTIONSIZE;
  }

  rd_value = get_token_register(rd);

  set_token_register(rd, token_data);

  token_data = rd_value;
}

void cell_branch(uint64_t on_path) {
  // beq rs1,rs2,imm with rs1 == rs2: the token leaves the path for its
  // come-from at pc + imm, with the address of the branch as its address;
  // a token that arrives from the side has taken the branch at pc + imm
  // that this cell is the come-from of, its address is uncomputed and it
  // continues after this cell. Backward the same the other way round.

  if (on_path) {
    if (reverse) {
      // undo the arrival
      token_pc = token_pc - INSTRUCTIONSIZE;

      token_address = token_address + token_pc + imm;
    } else {
      token_address = token_address + token_pc;

      token_pc = token_pc + imm;

      executed_instructions = executed_instructions + 1;
    }
  } else if (reverse) {
    // undo the departure
    token_pc = token_pc - imm;

    token_address = token_address - token_pc;

    executed_instructions = executed_instructions - 1;
  } else {
    token_address = token_address - (token_pc + imm);

    token_pc = token_pc + INSTRUCTIONSIZE;
  }
}

void cell_jump(uint64_t on_path) {
  // jal rd,imm: as a taken branch, and the address of the instruction
  // after the jump is added into rd, which RISC-R requires to be zero;
  // a token that arrives from the side has jumped here from pc + imm,
  // with jal zero, or returned here with the jalr at pc + imm

  if (on_path) {
    if (reverse) {
      // undo the arrival
      token_pc = token_pc - INSTRUCTIONSIZE;

      token_address = token_address + token_pc + imm;
    } else {
      set_token_register(rd, get_token_register(rd) + token_pc + INSTRUCTIONSIZE);

      token_address = token_address + token_pc;

      token_pc = token_pc + imm;

      executed_instructions = executed_instructions + 1;
    }
  } else if (reverse) {
    // undo the departure
    token_pc = token_pc - imm;

    token_address = token_address - token_pc;

    set_token_register(rd, get_token_register(rd) - (token_pc + INSTRUCTIONSIZE));

    executed_instructions = executed_instructions - 1;
  } else {
    token_address = token_address - (token_pc + imm);

    token_pc = token_pc + INSTRUCTIONSIZE;
  }
}

void cell_return(uint64_t on_path) {
  uint64_t rd_value;

  // jalr rd,0(rd): the token leaves the path for the jal whose address is
  // in rd, with the address of the jalr as its address: pc, rd, and the
  // address rotate, which leaves rd zero since the address is zero on the
  // path; a token that arrives from the side has been called by the jal
  // before the address in rd, its address is uncomputed from rd

  rd_value = get_token_register(rd);

  if (on_path) {
    if (reverse) {
      // undo the arrival
      token_pc = token_pc - INSTRUCTIONSIZE;

      token_address = token_address + (rd_value - INSTRUCTIONSIZE);
    } else {
      set_token_register(rd, token_address);

      token_address = token_pc;

      token_pc = rd_value;

      executed_instructions = executed_instructions + 1;
    }
  } else if (reverse) {
    // undo the departure
    set_token_register(rd, token_pc);

    token_pc = token_address;

    token_address = rd_value;

    executed_instructions = executed_instructions - 1;
  } else {
    token_address = token_address - (rd_value - INSTRUCTIONSIZE);

    token_pc = token_pc + INSTRUCTIONSIZE;
  }
}

void act_instruction(uint64_t orientation, uint64_t mirror_kind, uint64_t word) {
  uint64_t on_path;

  // the cell acts on a token on its path, heading where the cell is
  // oriented, and on a token that crosses its path where its mirror
  // would turn it onto the path; all others pass, backward as well

  on_path = token_heading == orientation;

  if (not(on_path))
    if (token_heading != mirror_heading(orientation, mirror_kind))
      return;

  decode_cell(word);

  if (not(is_reversible_instruction()))
    return;

  if (is == ECALL)
    // a system call is a property of the token
    return;
  else if (is == BEQ) {
    if (get_token_register(rs1) != get_token_register(rs2)) {
      // not taken: the token stays on the path, or crosses it
      if (on_path)
        advance_on_path();

      return;
    }

    cell_branch(on_path);
  } else if (is == JAL)
    cell_jump(on_path);
  else if (is == JALR)
    cell_return(on_path);
  else if (and(is == LOAD, rd != REG_ZR))
    cell_exchange(on_path);
  else {
    // the token stays on the path, or crosses it
    if (on_path)
      cell_compute();

    return;
  }

  // the cell is a mirror for a token that leaves or joins its path

  token_heading = mirror_heading(token_heading, mirror_kind);
}

void act() {
  uint64_t index;
  uint64_t cell;
  uint64_t kind;
  uint64_t word;
  uint64_t bit;

  // the cell under the token acts on the token, and backward undoes that

  index = cell_index(token_x, token_y);

  cell = *(cell_kinds + index);
  word = *(cell_words + index);

  kind = get_cell_kind(cell);

  if (kind == CELL_MIRROR)
    token_heading = mirror_heading(token_heading, get_cell_mirror(cell));
  else if (kind == CELL_ROUTER) {
    // a mirror if the bit of the pc or the address of the token is set
    if (get_router_field(word) == FIELD_PC)
      bit = get_bits(token_pc, get_router_bit(word), 1);
    else
      bit = get_bits(token_address, get_router_bit(word), 1);

    if (bit)
      token_heading = mirror_heading(token_heading, get_cell_mirror(cell));
  } else if (kind == CELL_MEMORY) {
    // exchange the word with the datum
    *(cell_words + index) = token_data;

    token_data = word;
  } else if (kind == CELL_INSTRUCTION)
    act_instruction(get_cell_orientation(cell), get_cell_mirror(cell), word);
}

void move_token() {
  uint64_t heading;

  // one cell along the heading of the token, backward against it

  heading = token_heading;

  if (reverse)
    heading = (heading + 2) % 4;

  if (heading == EAST)
    token_x = (token_x + 1) % grid_width;
  else if (heading == NORTH)
    token_y = (token_y + grid_height - 1) % grid_height;
  else if (heading == WEST)
    token_x = (token_x + grid_width - 1) % grid_width;
  else
    token_y = (token_y + 1) % grid_height;
}

void tick() {
  // the rule: act, then move; the inverse rule: move back, then undo

  if (reverse) {
    move_token();

    act();

    executed_ticks = executed_ticks - 1;
  } else {
    act();

    move_token();

    executed_ticks = executed_ticks + 1;
  }
}

uint64_t token_property() {
  uint64_t cell;

  // where a RISC-R program stops: the token is about to enter, on its
  // path, an instruction cell whose instruction is not RISC-R, links
  // into a nonzero register, divides by zero, or is a system call; the
  // rule is defined for these states as well, they are not constraints

  cell = *(cell_kinds + cell_index(token_x, token_y));

  if (get_cell_kind(cell) != CELL_INSTRUCTION)
    return PROPERTY_NONE;

  if (token_heading != get_cell_orientation(cell))
    return PROPERTY_NONE;

  decode_cell(*(cell_words + cell_index(token_x, token_y)));

  if (not(is_reversible_instruction()))
    return PROPERTY_ILLEGAL_INSTRUCTION;

  if (is == JAL) {
    if (get_token_register(rd) != 0)
      return PROPERTY_IRREVERSIBLE_LINK;
  } else if (is == DIVU) {
    if (get_token_register(rs2) == 0)
      return PROPERTY_DIVISION_BY_ZERO;
  } else if (is == REMU) {
    if (get_token_register(rs2) == 0)
      return PROPERTY_DIVISION_BY_ZERO;
  } else if (is == ECALL) {
    if (get_token_register(REG_A7) == SYSCALL_EXIT)
      return PROPERTY_EXIT;
    else
      return PROPERTY_UNSUPPORTED_SYSCALL;
  }

  return PROPERTY_NONE;
}

// -----------------------------------------------------------------
// ---------------------------- LAYOUT -----------------------------
// -----------------------------------------------------------------

// A layout is a text file in the run-length encoding of cellular
// automata, extended with cell contents, see cellfie.md:
//
// #C comment
// #T x y heading pc address data      the token, heading is E, N, W, or S
// #R register value                   a register that is not zero
// x = width, y = height, rule = RISC-R
// 2.E/00100a13M0000000000000007$     cells, row by row, ended by !
//
// A cell is . (blank), / or \ (mirror), R with mirror, p or a, and two
// decimal digits (router on that bit of the pc or the address), M with
// 16 hexadecimal digits (memory word), or E, N, W, S with mirror and 8
// hexadecimal digits (instruction with orientation). A decimal number
// in front of a cell repeats it, $ ends a row, the rest of a row is
// blank. Numbers after #T and #R are hexadecimal, except x, y, register.

uint64_t* read_file(char* name) {
  uint64_t fd;
  uint64_t* buffer;
  uint64_t capacity;
  uint64_t* bigger;
  uint64_t bytes;
  uint64_t i;

  // reads the file into a word-aligned buffer, layout_size is its length
  // in bytes; mipster only reads into mapped memory at word-aligned
  // addresses, so the buffer is touched, and a short read ends the file

  fd = open_read_only(name);

  if (signed_less_than(fd, 0)) {
    printf("%s: could not open %s\n", selfie_name, name);

    exit(EXITCODE_IOERROR);
  }

  capacity = LAYOUT_CHUNK;
  buffer   = touch(zmalloc(capacity + LAYOUT_CHUNK), capacity + LAYOUT_CHUNK);

  layout_size = 0;

  bytes = LAYOUT_CHUNK;

  while (bytes == LAYOUT_CHUNK) {
    bytes = sign_extend(read(fd, (uint64_t*) ((uint64_t) buffer + layout_size), LAYOUT_CHUNK), SYSCALL_BITWIDTH);

    if (signed_less_than(0, bytes)) {
      layout_size = layout_size + bytes;

      if (layout_size + LAYOUT_CHUNK > capacity) {
        bigger = touch(zmalloc(2 * capacity + LAYOUT_CHUNK), 2 * capacity + LAYOUT_CHUNK);

        i = 0;

        while (i < round_up(layout_size, sizeof(uint64_t)) / sizeof(uint64_t)) {
          *(bigger + i) = *(buffer + i);

          i = i + 1;
        }

        buffer   = bigger;
        capacity = 2 * capacity;
      }
    }
  }

  return buffer;
}

uint64_t layout_character() {
  if (layout_pos < layout_size)
    return load_character((char*) layout_text, layout_pos);
  else
    return 0;
}

void next_layout_character() {
  if (layout_character() == 10)
    layout_line = layout_line + 1;

  layout_pos = layout_pos + 1;
}

void layout_error(char* message) {
  printf("%s: %s in line %lu of %s\n", selfie_name, message, layout_line, layout_name);

  exit(EXITCODE_SCANNERERROR);
}

uint64_t is_decimal_digit(uint64_t c) {
  if (c >= '0')
    return c <= '9';
  else
    return 0;
}

uint64_t hexadecimal_value(uint64_t c) {
  // value of a hexadecimal digit, or 16 if c is none

  if (is_decimal_digit(c))
    return c - '0';
  else if (c >= 'a') {
    if (c <= 'f')
      return c - 'a' + 10;
  } else if (c >= 'A')
    if (c <= 'F')
      return c - 'A' + 10;

  return 16;
}

void skip_layout_spaces() {
  while (1) {
    if (layout_character() == ' ')
      next_layout_character();
    else if (layout_character() == 9)
      next_layout_character();
    else
      return;
  }
}

void skip_layout_blanks() {
  while (1) {
    skip_layout_spaces();

    if (layout_character() == 10)
      next_layout_character();
    else if (layout_character() == 13)
      next_layout_character();
    else
      return;
  }
}

void skip_layout_line() {
  while (layout_pos < layout_size) {
    if (layout_character() == 10) {
      next_layout_character();

      return;
    }

    next_layout_character();
  }
}

void expect_layout_character(uint64_t c) {
  skip_layout_spaces();

  if (layout_character() != c)
    layout_error("unexpected character");

  next_layout_character();
}

uint64_t scan_decimal() {
  uint64_t n;

  skip_layout_spaces();

  if (not(is_decimal_digit(layout_character())))
    layout_error("decimal number expected");

  n = 0;

  while (is_decimal_digit(layout_character())) {
    n = n * 10 + layout_character() - '0';

    next_layout_character();
  }

  return n;
}

uint64_t scan_hexadecimal(uint64_t digits) {
  uint64_t n;
  uint64_t i;

  // a number of exactly that many hexadecimal digits, or, with 0 digits,
  // of as many as there are, at least one

  if (digits == 0)
    skip_layout_spaces();

  if (hexadecimal_value(layout_character()) == 16)
    layout_error("hexadecimal digit expected");

  n = 0;
  i = 0;

  while (hexadecimal_value(layout_character()) < 16) {
    n = n * 16 + hexadecimal_value(layout_character());

    next_layout_character();

    i = i + 1;

    if (i == digits)
      return n;
  }

  if (digits != 0)
    layout_error("hexadecimal digit expected");

  return n;
}

uint64_t scan_mirror() {
  uint64_t c;

  c = layout_character();

  next_layout_character();

  if (c == '/')
    return SLASH;
  else if (c == 92)
    return BACKSLASH;

  layout_error("mirror expected");

  return 0;
}

uint64_t scan_heading() {
  uint64_t c;

  skip_layout_spaces();

  c = layout_character();

  next_layout_character();

  if (c == 'E')
    return EAST;
  else if (c == 'N')
    return NORTH;
  else if (c == 'W')
    return WEST;
  else if (c == 'S')
    return SOUTH;

  layout_error("heading E, N, W, or S expected");

  return 0;
}

void load_token() {
  // #T x y heading pc address data

  token_x = scan_decimal();
  token_y = scan_decimal();

  token_heading = scan_heading();

  token_pc      = scan_hexadecimal(0);
  token_address = scan_hexadecimal(0);
  token_data    = scan_hexadecimal(0);
}

void load_register() {
  uint64_t reg;

  // #R register value

  reg = scan_decimal();

  if (reg >= NUMBEROFREGISTERS)
    layout_error("no such register");

  set_token_register(reg, scan_hexadecimal(0));
}

void load_header() {
  uint64_t width;
  uint64_t height;

  // x = width, y = height, rule = RISC-R

  expect_layout_character('x');
  expect_layout_character('=');

  width = scan_decimal();

  expect_layout_character(',');
  expect_layout_character('y');
  expect_layout_character('=');

  height = scan_decimal();

  expect_layout_character(',');
  expect_layout_character('r');
  expect_layout_character('u');
  expect_layout_character('l');
  expect_layout_character('e');
  expect_layout_character('=');

  // reversibility is a switch, a layout says which rule its cells follow;
  // the rule of RISC-U cells, which is no bijection, is not implemented yet

  expect_layout_character('R');
  expect_layout_character('I');
  expect_layout_character('S');
  expect_layout_character('C');
  expect_layout_character('-');

  skip_layout_spaces();

  if (layout_character() == 'U')
    layout_error("RISC-U layouts are not supported yet");

  expect_layout_character('R');

  allocate_grid(width, height);
}

void load_cells() {
  uint64_t x;
  uint64_t y;
  uint64_t n;
  uint64_t c;
  uint64_t cell;
  uint64_t word;

  x = 0;
  y = 0;

  while (1) {
    skip_layout_blanks();

    n = 1;

    if (is_decimal_digit(layout_character()))
      n = scan_decimal();

    c = layout_character();

    next_layout_character();

    cell = encode_cell(CELL_BLANK, 0, 0);
    word = 0;

    if (c == '!')
      return;
    else if (c == 0)
      layout_error("layout does not end with !");
    else if (c == '$') {
      x = 0;
      y = y + n;

      n = 0;
    } else if (c == '.')
      cell = encode_cell(CELL_BLANK, 0, 0);
    else if (c == '/')
      cell = encode_cell(CELL_MIRROR, 0, SLASH);
    else if (c == 92)
      cell = encode_cell(CELL_MIRROR, 0, BACKSLASH);
    else if (c == 'R') {
      cell = encode_cell(CELL_ROUTER, 0, scan_mirror());

      c = layout_character();

      next_layout_character();

      if (c == 'p')
        word = FIELD_PC * 64;
      else if (c == 'a')
        word = FIELD_ADDRESS * 64;
      else
        layout_error("router field p or a expected");

      if (not(is_decimal_digit(layout_character())))
        layout_error("router bit expected");

      c = layout_character() - '0';

      next_layout_character();

      if (not(is_decimal_digit(layout_character())))
        layout_error("router bit expected");

      c = c * 10 + layout_character() - '0';

      next_layout_character();

      if (c >= 64)
        layout_error("router bit beyond 63");

      word = word + c;
    } else if (c == 'M') {
      cell = encode_cell(CELL_MEMORY, 0, 0);

      word = scan_hexadecimal(16);
    } else {
      // instruction cell: orientation, mirror, instruction

      if (c == 'E')
        c = EAST;
      else if (c == 'N')
        c = NORTH;
      else if (c == 'W')
        c = WEST;
      else if (c == 'S')
        c = SOUTH;
      else
        layout_error("cell expected");

      cell = encode_cell(CELL_INSTRUCTION, c, scan_mirror());

      word = scan_hexadecimal(8);
    }

    while (n > 0) {
      if (x >= grid_width)
        layout_error("row is wider than the grid");
      else if (y >= grid_height)
        layout_error("more rows than the grid has");

      *(cell_kinds + cell_index(x, y)) = cell;
      *(cell_words + cell_index(x, y)) = word;

      x = x + 1;

      n = n - 1;
    }
  }
}

void load_layout(char* name) {
  uint64_t i;

  layout_name = name;

  layout_text = read_file(name);

  layout_pos  = 0;
  layout_line = 1;

  // the token is at the northwestern cell heading east, with pc 0
  // and all registers zero, unless the layout says otherwise

  token_x = 0;
  token_y = 0;

  token_heading = EAST;

  token_pc      = 0;
  token_address = 0;
  token_data    = 0;

  if (token_registers == (uint64_t*) 0)
    token_registers = zmalloc(NUMBEROFREGISTERS * sizeof(uint64_t));

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    *(token_registers + i) = 0;

    i = i + 1;
  }

  executed_ticks        = 0;
  executed_instructions = 0;

  skip_layout_blanks();

  while (layout_character() == '#') {
    next_layout_character();

    if (layout_character() == 'T') {
      next_layout_character();

      load_token();
    } else if (layout_character() == 'R') {
      next_layout_character();

      load_register();
    }

    skip_layout_line();

    skip_layout_blanks();
  }

  load_header();
  load_cells();

  if (token_x >= grid_width)
    layout_error("token is not on the grid");
  else if (token_y >= grid_height)
    layout_error("token is not on the grid");

  printf("%s: grid of %lux%lu cells loaded from %s\n", selfie_name, grid_width, grid_height, layout_name);
}

void print_hexadecimal_digits(uint64_t value, uint64_t digits) {
  uint64_t digit;

  while (digits > 0) {
    digits = digits - 1;

    digit = get_bits(value, digits * 4, 4);

    if (digit < 10)
      put_character('0' + digit);
    else
      put_character('a' + digit - 10);
  }
}

void print_heading(uint64_t heading) {
  if (heading == EAST)
    put_character('E');
  else if (heading == NORTH)
    put_character('N');
  else if (heading == WEST)
    put_character('W');
  else
    put_character('S');
}

void print_mirror(uint64_t mirror_kind) {
  if (mirror_kind == SLASH)
    put_character('/');
  else
    put_character(92);
}

void print_cell(uint64_t index) {
  uint64_t cell;
  uint64_t kind;
  uint64_t word;

  cell = *(cell_kinds + index);
  word = *(cell_words + index);

  kind = get_cell_kind(cell);

  if (kind == CELL_MIRROR)
    print_mirror(get_cell_mirror(cell));
  else if (kind == CELL_ROUTER) {
    put_character('R');

    print_mirror(get_cell_mirror(cell));

    if (get_router_field(word) == FIELD_PC)
      put_character('p');
    else
      put_character('a');

    put_character('0' + get_router_bit(word) / 10);
    put_character('0' + get_router_bit(word) % 10);
  } else if (kind == CELL_MEMORY) {
    put_character('M');

    print_hexadecimal_digits(word, 16);
  } else if (kind == CELL_INSTRUCTION) {
    print_heading(get_cell_orientation(cell));
    print_mirror(get_cell_mirror(cell));

    print_hexadecimal_digits(word, 8);
  } else
    put_character('.');
}

uint64_t is_blank_cell(uint64_t index) {
  uint64_t kind;

  // kinds that do not exist are blank

  kind = get_cell_kind(*(cell_kinds + index));

  if (kind < CELL_MIRROR)
    return 1;
  else
    return kind > CELL_INSTRUCTION;
}

uint64_t are_cells_equal(uint64_t i, uint64_t j) {
  uint64_t kind;

  // do the cells print the same?

  if (is_blank_cell(i))
    return is_blank_cell(j);
  else if (*(cell_kinds + i) % 64 != *(cell_kinds + j) % 64)
    return 0;

  kind = get_cell_kind(*(cell_kinds + i));

  if (kind == CELL_MIRROR)
    return 1;
  else if (kind == CELL_INSTRUCTION)
    return get_bits(*(cell_words + i), 0, INSTRUCTIONSIZEINBITS) == get_bits(*(cell_words + j), 0, INSTRUCTIONSIZEINBITS);
  else if (kind == CELL_ROUTER)
    return *(cell_words + i) % 128 == *(cell_words + j) % 128;
  else
    return *(cell_words + i) == *(cell_words + j);
}

void write_layout(char* name) {
  uint64_t fd;
  uint64_t x;
  uint64_t y;
  uint64_t n;
  uint64_t last;
  uint64_t i;

  // the grid and the token as layout, in one form only, so that
  // equal states are equal files

  fd = open_write_only(name, S_IRUSR_IWUSR_IRGRP_IROTH);

  if (signed_less_than(fd, 0)) {
    printf("%s: could not create %s\n", selfie_name, name);

    exit(EXITCODE_IOERROR);
  }

  output_name = name;
  output_fd   = fd;

  dprintf(output_fd, "#C cellfie layout, see cellfie.md\n");
  dprintf(output_fd, "#T %lu %lu ", token_x, token_y);

  print_heading(token_heading);

  put_character(' ');
  print_hexadecimal_digits(token_pc, 16);
  put_character(' ');
  print_hexadecimal_digits(token_address, 16);
  put_character(' ');
  print_hexadecimal_digits(token_data, 16);
  put_character(10);

  i = 1;

  while (i < NUMBEROFREGISTERS) {
    if (get_token_register(i) != 0) {
      dprintf(output_fd, "#R %lu ", i);

      print_hexadecimal_digits(get_token_register(i), 16);

      put_character(10);
    }

    i = i + 1;
  }

  dprintf(output_fd, "x = %lu, y = %lu, rule = RISC-R\n", grid_width, grid_height);

  y = 0;

  while (y < grid_height) {
    // a row without the blank cells at its end

    last = 0;

    x = 0;

    while (x < grid_width) {
      if (not(is_blank_cell(cell_index(x, y))))
        last = x + 1;

      x = x + 1;
    }

    x = 0;

    while (x < last) {
      n = 1;

      while (and(x + n < last, are_cells_equal(cell_index(x, y), cell_index((x + n) % grid_width, y))))
        // the cells of a row up to last are on the grid, the remainder keeps the index there
        n = n + 1;

      if (n > 1)
        dprintf(output_fd, "%lu", n);

      print_cell(cell_index(x, y));

      x = x + n;
    }

    y = y + 1;

    if (y < grid_height)
      put_character('$');
    else
      put_character('!');

    put_character(10);
  }

  output_name = (char*) 0;
  output_fd   = STDOUT_FD;

  printf("%s: grid of %lux%lu cells and token written to %s\n", selfie_name, grid_width, grid_height, name);
}

// -----------------------------------------------------------------
// --------------------------- SIMULATOR ---------------------------
// -----------------------------------------------------------------

uint64_t snapshot_size() {
  // the cells, the registers, and six words of the token
  return 2 * grid_size + NUMBEROFREGISTERS + 6;
}

uint64_t* take_snapshot(uint64_t* snapshot) {
  uint64_t i;

  // the whole state, into the given snapshot or a new one

  if (snapshot == (uint64_t*) 0)
    snapshot = zmalloc(snapshot_size() * sizeof(uint64_t));

  i = 0;

  while (i < grid_size) {
    *(snapshot + i)             = *(cell_kinds + i);
    *(snapshot + grid_size + i) = *(cell_words + i);

    i = i + 1;
  }

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    *(snapshot + 2 * grid_size + i) = *(token_registers + i);

    i = i + 1;
  }

  i = 2 * grid_size + NUMBEROFREGISTERS;

  *(snapshot + i)     = token_x;
  *(snapshot + i + 1) = token_y;
  *(snapshot + i + 2) = token_heading;
  *(snapshot + i + 3) = token_pc;
  *(snapshot + i + 4) = token_address;
  *(snapshot + i + 5) = token_data;

  return snapshot;
}

void restore_snapshot(uint64_t* snapshot) {
  uint64_t i;

  i = 0;

  while (i < grid_size) {
    *(cell_kinds + i) = *(snapshot + i);
    *(cell_words + i) = *(snapshot + grid_size + i);

    i = i + 1;
  }

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    *(token_registers + i) = *(snapshot + 2 * grid_size + i);

    i = i + 1;
  }

  i = 2 * grid_size + NUMBEROFREGISTERS;

  token_x       = *(snapshot + i);
  token_y       = *(snapshot + i + 1);
  token_heading = *(snapshot + i + 2);
  token_pc      = *(snapshot + i + 3);
  token_address = *(snapshot + i + 4);
  token_data    = *(snapshot + i + 5);
}

uint64_t is_snapshot(uint64_t* snapshot, uint64_t reporting) {
  uint64_t i;
  uint64_t is_same;

  // is the state the state of the snapshot, bit for bit?

  i = 0;

  while (i < grid_size) {
    if (*(cell_kinds + i) != *(snapshot + i)) {
      if (reporting)
        printf("%s: cell (%lu,%lu) is 0x%lX but was 0x%lX\n", selfie_name,
          i % grid_width, i / grid_width, *(cell_kinds + i), *(snapshot + i));

      return 0;
    } else if (*(cell_words + i) != *(snapshot + grid_size + i)) {
      if (reporting)
        printf("%s: word of cell (%lu,%lu) is 0x%lX but was 0x%lX\n", selfie_name,
          i % grid_width, i / grid_width, *(cell_words + i), *(snapshot + grid_size + i));

      return 0;
    }

    i = i + 1;
  }

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    if (*(token_registers + i) != *(snapshot + 2 * grid_size + i)) {
      if (reporting)
        printf("%s: register %lu is 0x%lX but was 0x%lX\n", selfie_name,
          i, *(token_registers + i), *(snapshot + 2 * grid_size + i));

      return 0;
    }

    i = i + 1;
  }

  i = 2 * grid_size + NUMBEROFREGISTERS;

  is_same = token_x == *(snapshot + i);
  is_same = is_same * (token_y == *(snapshot + i + 1));
  is_same = is_same * (token_heading == *(snapshot + i + 2));
  is_same = is_same * (token_pc == *(snapshot + i + 3));
  is_same = is_same * (token_address == *(snapshot + i + 4));
  is_same = is_same * (token_data == *(snapshot + i + 5));

  if (not(is_same))
    if (reporting) {
      printf("%s: ", selfie_name);

      print_token();

      printf(", address 0x%lX, and datum 0x%lX but was at (%lu,%lu) heading ", token_address, token_data,
        *(snapshot + i), *(snapshot + i + 1));

      print_heading(*(snapshot + i + 2));

      printf(" with pc 0x%lX, address 0x%lX, and datum 0x%lX\n",
        *(snapshot + i + 3), *(snapshot + i + 4), *(snapshot + i + 5));
    }

  return is_same;
}

void print_token() {
  printf("token at (%lu,%lu) heading ", token_x, token_y);

  print_heading(token_heading);

  printf(" with pc 0x%lX", token_pc);
}

void print_property(uint64_t property) {
  if (property == PROPERTY_ILLEGAL_INSTRUCTION)
    printf("illegal-instruction");
  else if (property == PROPERTY_IRREVERSIBLE_LINK)
    printf("irreversible-link");
  else if (property == PROPERTY_DIVISION_BY_ZERO)
    printf("division-by-zero");
  else if (property == PROPERTY_EXIT)
    printf("exit with exit code %ld", sign_extend(get_bits(get_token_register(REG_A1), 0, SYSCALL_BITWIDTH), SYSCALL_BITWIDTH));
  else if (property == PROPERTY_UNSUPPORTED_SYSCALL)
    printf("unsupported-syscall");
}

uint64_t run_forward(uint64_t ticks) {
  uint64_t property;
  uint64_t start;

  // at most ticks forward, until a property holds for the token;
  // returns the number of ticks executed

  reverse = 0;

  start = executed_ticks;

  property = token_property();

  while (and(property == PROPERTY_NONE, executed_ticks - start < ticks)) {
    tick();

    property = token_property();
  }

  printf("%s: ", selfie_name);

  print_token();

  if (property == PROPERTY_NONE)
    printf(" after %lu ticks and %lu instructions\n", executed_ticks, executed_instructions);
  else {
    printf(": ");

    print_property(property);

    printf(" after %lu ticks and %lu instructions\n", executed_ticks, executed_instructions);
  }

  return executed_ticks - start;
}

void run_backward(uint64_t ticks) {
  // ticks backward, the inverse rule has no properties

  reverse = 1;

  while (ticks > 0) {
    tick();

    ticks = ticks - 1;
  }

  reverse = 0;

  printf("%s: ", selfie_name);

  print_token();

  printf(" back at %ld ticks and %ld instructions\n", executed_ticks, executed_instructions);
}

uint64_t run_forward_and_backward(uint64_t ticks) {
  uint64_t* initial_state;

  // forward, then as many ticks backward: the grid and the token
  // must be restored bit for bit

  initial_state = take_snapshot((uint64_t*) 0);

  ticks = run_forward(ticks);

  if (ticks > 0)
    if (is_snapshot(initial_state, 0))
      printf("%s: the state after %lu ticks is the initial state\n", selfie_name, ticks);

  run_backward(ticks);

  if (is_snapshot(initial_state, 1)) {
    printf("%s: initial state restored after %lu ticks forward and %lu ticks backward\n", selfie_name, ticks, ticks);

    return 1;
  } else {
    printf("%s: initial state not restored after %lu ticks forward and %lu ticks backward\n", selfie_name, ticks, ticks);

    return 0;
  }
}

// -----------------------------------------------------------------
// ----------------------------- MODEL -----------------------------
// -----------------------------------------------------------------

// The model is the cell rule as BTOR2, for bitr: nine states, the
// position and heading of the token, its pc, address, datum, and
// register file, and the kinds and words of the cells, none of them
// initialized, so that a layout is the initial state. The inverse
// model is the same generator run with the reverse flag set, over
// the same states by name, as the BTOR2 profile requires.

uint64_t* new_sort(uint64_t bits) {
  return new_bitvec(bits, format_comment("%lu-bit", bits));
}

uint64_t* new_number(uint64_t* sid, uint64_t value) {
  return new_constant(OP_CONSTD, sid, value, NOCOMMENT);
}

uint64_t* new_not(uint64_t* a) {
  return new_unary_boolean(OP_NOT, a, NOCOMMENT);
}

uint64_t* new_and(uint64_t* a, uint64_t* b) {
  return new_binary_boolean(OP_AND, a, b, NOCOMMENT);
}

uint64_t* new_or(uint64_t* a, uint64_t* b) {
  return new_binary_boolean(OP_OR, a, b, NOCOMMENT);
}

uint64_t* new_eq(uint64_t* a, uint64_t* b) {
  return new_binary_boolean(OP_EQ, a, b, NOCOMMENT);
}

uint64_t* new_ite(uint64_t* condition, uint64_t* a, uint64_t* b) {
  return new_ternary(OP_ITE, get_sid(a), condition, a, b, NOCOMMENT);
}

uint64_t* new_add(uint64_t* a, uint64_t* b) {
  return new_binary(OP_ADD, get_sid(a), a, b, NOCOMMENT);
}

uint64_t* new_sub(uint64_t* a, uint64_t* b) {
  return new_binary(OP_SUB, get_sid(a), a, b, NOCOMMENT);
}

uint64_t* new_bits(uint64_t* value, uint64_t upper, uint64_t lower) {
  return new_slice(new_sort(upper - lower + 1), value, upper, lower, NOCOMMENT);
}

uint64_t* new_join(uint64_t* upper, uint64_t* lower) {
  return new_binary(OP_CONCAT,
    new_sort(eval_bitvec_size(get_sid(upper)) + eval_bitvec_size(get_sid(lower))),
    upper, lower, NOCOMMENT);
}

uint64_t* new_is_field(uint64_t* field, uint64_t value) {
  return new_eq(field, new_number(get_sid(field), value));
}

uint64_t* new_delta(uint64_t* sid, uint64_t* low_nid, uint64_t* high_nid) {
  uint64_t bits;

  // 1, -1, or 0 from its lowest bit and the bit all its other bits are

  bits = eval_bitvec_size(sid);

  if (bits == 1)
    return low_nid;
  else if (bits == 2)
    return new_binary(OP_CONCAT, sid, high_nid, low_nid, NOCOMMENT);
  else
    return new_binary(OP_CONCAT, sid,
      new_ext(OP_SEXT, new_sort(bits - 1), high_nid, bits - 2, NOCOMMENT), low_nid, NOCOMMENT);
}

uint64_t* new_delta_x(uint64_t* heading_nid) {
  uint64_t* horizontal_nid;

  // one column east or west: 1 heading east (0), -1 heading west (2), else
  // 0; computed from the bits of the heading rather than chosen, so that
  // moving back cancels moving without a case distinction

  horizontal_nid = new_not(new_bits(heading_nid, 0, 0));

  return new_delta(SID_X, horizontal_nid, new_and(horizontal_nid, new_bits(heading_nid, 1, 1)));
}

uint64_t* new_delta_y(uint64_t* heading_nid) {
  uint64_t* vertical_nid;

  // one row south or north: 1 heading south (3), -1 heading north (1), else 0

  vertical_nid = new_bits(heading_nid, 0, 0);

  return new_delta(SID_Y, vertical_nid, new_and(vertical_nid, new_not(new_bits(heading_nid, 1, 1))));
}

uint64_t* new_effect(uint64_t* effect) {
  uint64_t* copy;
  uint64_t i;

  // an effect is the next value of each state: a copy to change

  copy = zmalloc(NUMBER_OF_STATES * sizeof(uint64_t*));

  i = 0;

  while (i < NUMBER_OF_STATES) {
    *(copy + i) = *(effect + i);

    i = i + 1;
  }

  return copy;
}

uint64_t* new_choice(uint64_t* condition_nid, uint64_t* then_effect, uint64_t* else_effect) {
  uint64_t* effect;
  uint64_t i;

  // one effect if the condition holds, the other if not, state by state

  effect = new_effect(else_effect);

  i = 0;

  while (i < NUMBER_OF_STATES) {
    if (*(then_effect + i) != *(else_effect + i))
      *(effect + i) = (uint64_t) new_ite(condition_nid, (uint64_t*) *(then_effect + i), (uint64_t*) *(else_effect + i));

    i = i + 1;
  }

  return effect;
}

uint64_t* new_arithmetic_choice(uint64_t* funct3_nid, uint64_t* funct7_nid, uint64_t* same,
  uint64_t* add_effect, uint64_t* sub_effect, uint64_t* mul_effect,
  uint64_t* divu_effect, uint64_t* remu_effect, uint64_t* sltu_effect) {
  // add, sub, mul, divu, remu, sltu by function, any other function has no effect
  return new_choice(new_is_field(funct3_nid, F3_ADD),
    new_choice(new_is_field(funct7_nid, F7_ADD), add_effect,
      new_choice(new_is_field(funct7_nid, F7_SUB), sub_effect,
        new_choice(new_is_field(funct7_nid, F7_MUL), mul_effect, same))),
    new_choice(new_is_field(funct3_nid, F3_DIVU),
      new_choice(new_is_field(funct7_nid, F7_DIVU), divu_effect, same),
      new_choice(new_is_field(funct3_nid, F3_REMU),
        new_choice(new_is_field(funct7_nid, F7_REMU), remu_effect, same),
        new_choice(new_is_field(funct3_nid, F3_SLTU),
          new_choice(new_is_field(funct7_nid, F7_SLTU), sltu_effect, same),
          same))));
}

void model_sorts(uint64_t xbits, uint64_t ybits) {
  SID_BOOLEAN = new_bitvec(1, "Boolean");

  SID_HEADING = new_bitvec(2, "heading: east 0, north 1, west 2, south 3");

  SID_X = new_sort(xbits);
  SID_Y = new_sort(ybits);

  SID_INDEX = new_sort(xbits + ybits);

  SID_CELL = new_bitvec(8, "cell: 3-bit kind, 2-bit orientation, 1-bit mirror");
  SID_WORD = new_bitvec(64, "64-bit word");

  SID_REGISTER = new_bitvec(5, "5-bit register address");

  SID_REGISTERS = new_array(SID_REGISTER, SID_WORD, "register file");

  SID_KINDS = new_array(SID_INDEX, SID_CELL, "cells by row and column");
  SID_WORDS = new_array(SID_INDEX, SID_WORD, "cell words by row and column");

  NID_FALSE = new_constant(OP_CONSTD, SID_BOOLEAN, 0, "false");
  NID_TRUE  = new_constant(OP_CONSTD, SID_BOOLEAN, 1, "true");
}

void model_states() {
  state_nids = zmalloc(NUMBER_OF_STATES * sizeof(uint64_t*));

  *(state_nids + STATE_X)       = (uint64_t) new_input(OP_STATE, SID_X, "token-x", "column of the token");
  *(state_nids + STATE_Y)       = (uint64_t) new_input(OP_STATE, SID_Y, "token-y", "row of the token");
  *(state_nids + STATE_HEADING) = (uint64_t) new_input(OP_STATE, SID_HEADING, "token-heading", "heading of the token");
  *(state_nids + STATE_PC)      = (uint64_t) new_input(OP_STATE, SID_WORD, "token-pc", "program counter");
  *(state_nids + STATE_ADDRESS) = (uint64_t) new_input(OP_STATE, SID_WORD, "token-address", "address in transit");
  *(state_nids + STATE_DATA)    = (uint64_t) new_input(OP_STATE, SID_WORD, "token-data", "datum in transit");

  *(state_nids + STATE_REGISTERS) = (uint64_t) new_input(OP_STATE, SID_REGISTERS, "token-registers", "register file");

  *(state_nids + STATE_KINDS) = (uint64_t) new_input(OP_STATE, SID_KINDS, "cell-kinds", "kind, orientation, mirror of each cell");
  *(state_nids + STATE_WORDS) = (uint64_t) new_input(OP_STATE, SID_WORDS, "cell-words", "instruction, memory word, or router bit of each cell");

  forward_nids = zmalloc(NUMBER_OF_STATES * sizeof(uint64_t*));
  inverse_nids = zmalloc(NUMBER_OF_STATES * sizeof(uint64_t*));

  property_nids = zmalloc((NUMBER_OF_PROPERTIES + 1) * sizeof(uint64_t*));
}

void model_rule() {
  uint64_t* next_nids;

  uint64_t* x_nid;
  uint64_t* y_nid;
  uint64_t* heading_nid;
  uint64_t* pc_nid;
  uint64_t* address_nid;
  uint64_t* data_nid;
  uint64_t* registers_nid;
  uint64_t* words_nid;

  uint64_t* index_nid;
  uint64_t* cell_nid;
  uint64_t* word_nid;
  uint64_t* kind_nid;
  uint64_t* orientation_nid;
  uint64_t* mirror_nid;
  uint64_t* mirrored_nid;
  uint64_t* router_bit_nid;

  uint64_t* ir_nid;
  uint64_t* opcode_nid;
  uint64_t* rd_nid;
  uint64_t* funct3_nid;
  uint64_t* rs1_nid;
  uint64_t* rs2_nid;
  uint64_t* funct7_nid;

  uint64_t* i_imm_nid;
  uint64_t* u_imm_nid;
  uint64_t* b_imm_nid;
  uint64_t* j_imm_nid;

  uint64_t* is_rd_zero_nid;
  uint64_t* is_rd_rs1_nid;
  uint64_t* is_rd_rs2_nid;
  uint64_t* is_jalr_nid;
  uint64_t* is_taken_nid;
  uint64_t* is_division_by_zero_nid;

  uint64_t* rd_value_nid;
  uint64_t* rs1_value_nid;
  uint64_t* rs2_value_nid;

  uint64_t* load_address_nid;
  uint64_t* four_nid;
  uint64_t* origin_nid;
  uint64_t* value_nid;

  uint64_t* same;
  uint64_t* advance;
  uint64_t* effect;

  uint64_t* lui_effect;
  uint64_t* addi_effect;
  uint64_t* add_effect;
  uint64_t* sub_effect;
  uint64_t* mul_effect;
  uint64_t* divu_effect;
  uint64_t* remu_effect;
  uint64_t* sltu_effect;

  uint64_t* exchange_on_path;
  uint64_t* exchange_on_side;
  uint64_t* branch_on_path;
  uint64_t* branch_on_side;
  uint64_t* jump_on_path;
  uint64_t* jump_on_side;
  uint64_t* return_on_path;
  uint64_t* return_on_side;

  uint64_t* on_path;
  uint64_t* on_side;

  uint64_t* is_instruction_nid;
  uint64_t* is_reversible_nid;
  uint64_t* is_arithmetic_nid;

  uint64_t i;

  // the token

  x_nid         = (uint64_t*) *(state_nids + STATE_X);
  y_nid         = (uint64_t*) *(state_nids + STATE_Y);
  heading_nid   = (uint64_t*) *(state_nids + STATE_HEADING);
  pc_nid        = (uint64_t*) *(state_nids + STATE_PC);
  address_nid   = (uint64_t*) *(state_nids + STATE_ADDRESS);
  data_nid      = (uint64_t*) *(state_nids + STATE_DATA);
  registers_nid = (uint64_t*) *(state_nids + STATE_REGISTERS);
  words_nid     = (uint64_t*) *(state_nids + STATE_WORDS);

  if (reverse)
    next_nids = inverse_nids;
  else
    next_nids = forward_nids;

  four_nid = new_number(SID_WORD, INSTRUCTIONSIZE);

  // the rule acts with the cell under the token and then moves the token;
  // the inverse rule moves the token back and acts with the cell there

  if (reverse) {
    x_nid = new_sub(x_nid, new_delta_x(heading_nid));
    y_nid = new_sub(y_nid, new_delta_y(heading_nid));
  }

  // the cell: index is row times width plus column

  index_nid = new_binary(OP_CONCAT, SID_INDEX, y_nid, x_nid, "cell index");

  cell_nid = new_binary(OP_READ, SID_CELL, (uint64_t*) *(state_nids + STATE_KINDS), index_nid, "cell");
  word_nid = new_binary(OP_READ, SID_WORD, words_nid, index_nid, "cell word");

  kind_nid        = new_bits(cell_nid, 2, 0);
  orientation_nid = new_slice(SID_HEADING, cell_nid, 4, 3, "cell orientation");
  mirror_nid      = new_slice(SID_BOOLEAN, cell_nid, 5, 5, "cell mirror");

  // a slash flips the lower bit of a heading, a backslash both bits

  mirrored_nid = new_binary(OP_XOR, SID_HEADING, heading_nid,
    new_binary(OP_CONCAT, SID_HEADING, mirror_nid, NID_TRUE, NOCOMMENT), "heading mirrored");

  // a router looks at a bit of the pc or the address

  router_bit_nid = new_bits(
    new_binary(OP_SRL, SID_WORD,
      new_ite(new_slice(SID_BOOLEAN, word_nid, 6, 6, "router field"), address_nid, pc_nid),
      new_ext(OP_UEXT, SID_WORD, new_bits(word_nid, 5, 0), 58, NOCOMMENT),
      "pc or address from router bit on"),
    0, 0);

  // the instruction

  ir_nid = new_bits(word_nid, 31, 0);

  opcode_nid = new_bits(ir_nid, 6, 0);
  rd_nid     = new_slice(SID_REGISTER, ir_nid, 11, 7, "rd");
  funct3_nid = new_bits(ir_nid, 14, 12);
  rs1_nid    = new_slice(SID_REGISTER, ir_nid, 19, 15, "rs1");
  rs2_nid    = new_slice(SID_REGISTER, ir_nid, 24, 20, "rs2");
  funct7_nid = new_bits(ir_nid, 31, 25);

  i_imm_nid = new_ext(OP_SEXT, SID_WORD, new_bits(ir_nid, 31, 20), 52, "I-format immediate");

  u_imm_nid = new_ext(OP_SEXT, SID_WORD,
    new_join(new_bits(ir_nid, 31, 12), new_number(new_sort(12), 0)), 32, "U-format immediate times 4096");

  b_imm_nid = new_ext(OP_SEXT, SID_WORD,
    new_join(new_bits(ir_nid, 31, 31),
      new_join(new_bits(ir_nid, 7, 7),
        new_join(new_bits(ir_nid, 30, 25),
          new_join(new_bits(ir_nid, 11, 8), NID_FALSE)))), 51, "B-format immediate");

  j_imm_nid = new_ext(OP_SEXT, SID_WORD,
    new_join(new_bits(ir_nid, 31, 31),
      new_join(new_bits(ir_nid, 19, 12),
        new_join(new_bits(ir_nid, 20, 20),
          new_join(new_bits(ir_nid, 30, 21), NID_FALSE)))), 43, "J-format immediate");

  is_rd_zero_nid = new_is_field(rd_nid, REG_ZR);
  is_rd_rs1_nid  = new_eq(rd_nid, rs1_nid);
  is_rd_rs2_nid  = new_eq(rd_nid, rs2_nid);

  // jalr is jalr rd,0(rd) with rd not zero

  is_jalr_nid = new_and(new_is_field(funct3_nid, F3_JALR),
    new_and(is_rd_rs1_nid, new_and(new_not(is_rd_zero_nid), new_is_field(new_bits(ir_nid, 31, 20), 0))));

  rd_value_nid  = new_binary(OP_READ, SID_WORD, registers_nid, rd_nid, "rd value");
  rs1_value_nid = new_binary(OP_READ, SID_WORD, registers_nid, rs1_nid, "rs1 value");
  rs2_value_nid = new_binary(OP_READ, SID_WORD, registers_nid, rs2_nid, "rs2 value");

  is_taken_nid = new_eq(rs1_value_nid, rs2_value_nid);

  is_division_by_zero_nid = new_is_field(rs2_value_nid, 0);

  load_address_nid = new_add(rs1_value_nid, i_imm_nid);

  // no effect: every state stays as it is, the position is dealt with below

  same = zmalloc(NUMBER_OF_STATES * sizeof(uint64_t*));

  *(same + STATE_X)         = (uint64_t) x_nid;
  *(same + STATE_Y)         = (uint64_t) y_nid;
  *(same + STATE_HEADING)   = (uint64_t) heading_nid;
  *(same + STATE_PC)        = (uint64_t) pc_nid;
  *(same + STATE_ADDRESS)   = (uint64_t) address_nid;
  *(same + STATE_DATA)      = (uint64_t) data_nid;
  *(same + STATE_REGISTERS) = (uint64_t) registers_nid;
  *(same + STATE_KINDS)     = *(state_nids + STATE_KINDS);
  *(same + STATE_WORDS)     = (uint64_t) words_nid;

  // an instruction that stays on the path: the pc advances by one
  // instruction, backward it goes back by one

  advance = new_effect(same);

  if (reverse)
    *(advance + STATE_PC) = (uint64_t) new_sub(pc_nid, four_nid);
  else
    *(advance + STATE_PC) = (uint64_t) new_add(pc_nid, four_nid);

  // lui, addi, add, sub: rd += f forward and rd -= f backward

  lui_effect = new_effect(advance);

  value_nid = u_imm_nid;

  if (reverse)
    value_nid = new_sub(rd_value_nid, value_nid);
  else
    value_nid = new_add(rd_value_nid, value_nid);

  *(lui_effect + STATE_REGISTERS) = (uint64_t)
    new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, rd_nid, value_nid, "lui");

  addi_effect = new_effect(advance);

  value_nid = new_add(rs1_value_nid, i_imm_nid);

  if (reverse)
    value_nid = new_sub(rd_value_nid, value_nid);
  else
    value_nid = new_add(rd_value_nid, value_nid);

  *(addi_effect + STATE_REGISTERS) = (uint64_t)
    new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, rd_nid, value_nid, "addi");

  add_effect = new_effect(advance);

  value_nid = new_add(rs1_value_nid, rs2_value_nid);

  if (reverse)
    value_nid = new_sub(rd_value_nid, value_nid);
  else
    value_nid = new_add(rd_value_nid, value_nid);

  *(add_effect + STATE_REGISTERS) = (uint64_t)
    new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, rd_nid, value_nid, "add");

  sub_effect = new_effect(advance);

  value_nid = new_sub(rs1_value_nid, rs2_value_nid);

  if (reverse)
    value_nid = new_sub(rd_value_nid, value_nid);
  else
    value_nid = new_add(rd_value_nid, value_nid);

  *(sub_effect + STATE_REGISTERS) = (uint64_t)
    new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, rd_nid, value_nid, "sub");

  // mul, divu, remu, sltu: rd ^= f in both directions, with quotient
  // and remainder 0 if the divisor is zero, which is a property

  mul_effect = new_effect(advance);

  *(mul_effect + STATE_REGISTERS) = (uint64_t)
    new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, rd_nid,
      new_binary(OP_XOR, SID_WORD, rd_value_nid,
        new_binary(OP_MUL, SID_WORD, rs1_value_nid, rs2_value_nid, NOCOMMENT), NOCOMMENT), "mul");

  divu_effect = new_effect(advance);

  *(divu_effect + STATE_REGISTERS) = (uint64_t)
    new_ite(is_division_by_zero_nid,
      registers_nid,
      new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, rd_nid,
        new_binary(OP_XOR, SID_WORD, rd_value_nid,
          new_binary(OP_UDIV, SID_WORD, rs1_value_nid, rs2_value_nid, NOCOMMENT), NOCOMMENT), "divu"));

  remu_effect = new_effect(advance);

  *(remu_effect + STATE_REGISTERS) = (uint64_t)
    new_ite(is_division_by_zero_nid,
      registers_nid,
      new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, rd_nid,
        new_binary(OP_XOR, SID_WORD, rd_value_nid,
          new_binary(OP_UREM, SID_WORD, rs1_value_nid, rs2_value_nid, NOCOMMENT), NOCOMMENT), "remu"));

  sltu_effect = new_effect(advance);

  *(sltu_effect + STATE_REGISTERS) = (uint64_t)
    new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, rd_nid,
      new_binary(OP_XOR, SID_WORD, rd_value_nid,
        new_ext(OP_UEXT, SID_WORD,
          new_binary_boolean(OP_ULT, rs1_value_nid, rs2_value_nid, NOCOMMENT), 63, NOCOMMENT), NOCOMMENT), "sltu");

  // ld: the cell is a mirror, rd and the datum are exchanged, and the
  // address is computed where the token leaves and uncomputed where it
  // returns, after which its pc advances; backward the other way round

  exchange_on_path = new_effect(same);

  *(exchange_on_path + STATE_HEADING)   = (uint64_t) mirrored_nid;
  *(exchange_on_path + STATE_DATA)      = (uint64_t) rd_value_nid;
  *(exchange_on_path + STATE_REGISTERS) = (uint64_t)
    new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, rd_nid, data_nid, "ld");
  *(exchange_on_path + STATE_ADDRESS)   = (uint64_t) new_add(address_nid, load_address_nid);

  exchange_on_side = new_effect(exchange_on_path);

  *(exchange_on_side + STATE_ADDRESS) = (uint64_t) new_sub(address_nid, load_address_nid);

  if (reverse)
    *(exchange_on_path + STATE_PC) = *(advance + STATE_PC);
  else
    *(exchange_on_side + STATE_PC) = *(advance + STATE_PC);

  // beq taken: the cell is a mirror, the token leaves the path for the
  // come-from at pc + imm with the address of the branch as address;
  // the come-from uncomputes the address and the pc advances

  branch_on_path = new_effect(same);
  branch_on_side = new_effect(same);

  *(branch_on_path + STATE_HEADING) = (uint64_t) mirrored_nid;
  *(branch_on_side + STATE_HEADING) = (uint64_t) mirrored_nid;

  if (reverse) {
    // undo the arrival on the path and the departure on the side

    *(branch_on_path + STATE_PC) = *(advance + STATE_PC);

    *(branch_on_path + STATE_ADDRESS) = (uint64_t)
      new_add(address_nid, new_add(new_sub(pc_nid, four_nid), b_imm_nid));

    origin_nid = new_sub(pc_nid, b_imm_nid);

    *(branch_on_side + STATE_PC)      = (uint64_t) origin_nid;
    *(branch_on_side + STATE_ADDRESS) = (uint64_t) new_sub(address_nid, origin_nid);
  } else {
    *(branch_on_path + STATE_PC)      = (uint64_t) new_add(pc_nid, b_imm_nid);
    *(branch_on_path + STATE_ADDRESS) = (uint64_t) new_add(address_nid, pc_nid);

    *(branch_on_side + STATE_PC)      = *(advance + STATE_PC);
    *(branch_on_side + STATE_ADDRESS) = (uint64_t) new_sub(address_nid, new_add(pc_nid, b_imm_nid));
  }

  // jal: as a taken branch, and the address after the jal is added into rd

  jump_on_path = new_effect(same);
  jump_on_side = new_effect(same);

  *(jump_on_path + STATE_HEADING) = (uint64_t) mirrored_nid;
  *(jump_on_side + STATE_HEADING) = (uint64_t) mirrored_nid;

  if (reverse) {
    *(jump_on_path + STATE_PC) = *(advance + STATE_PC);

    *(jump_on_path + STATE_ADDRESS) = (uint64_t)
      new_add(address_nid, new_add(new_sub(pc_nid, four_nid), j_imm_nid));

    origin_nid = new_sub(pc_nid, j_imm_nid);

    *(jump_on_side + STATE_PC)      = (uint64_t) origin_nid;
    *(jump_on_side + STATE_ADDRESS) = (uint64_t) new_sub(address_nid, origin_nid);

    *(jump_on_side + STATE_REGISTERS) = (uint64_t)
      new_ite(is_rd_zero_nid,
        registers_nid,
        new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, rd_nid,
          new_sub(rd_value_nid, new_add(origin_nid, four_nid)), "jal"));
  } else {
    *(jump_on_path + STATE_PC)      = (uint64_t) new_add(pc_nid, j_imm_nid);
    *(jump_on_path + STATE_ADDRESS) = (uint64_t) new_add(address_nid, pc_nid);

    *(jump_on_path + STATE_REGISTERS) = (uint64_t)
      new_ite(is_rd_zero_nid,
        registers_nid,
        new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, rd_nid,
          new_add(rd_value_nid, new_add(pc_nid, four_nid)), "jal"));

    *(jump_on_side + STATE_PC)      = *(advance + STATE_PC);
    *(jump_on_side + STATE_ADDRESS) = (uint64_t) new_sub(address_nid, new_add(pc_nid, j_imm_nid));
  }

  // jalr: the cell is a mirror; on the path pc, rd, and address rotate,
  // which sends the token to the jal whose address is in rd; on the
  // side the address is uncomputed from rd and the pc advances

  return_on_path = new_effect(same);
  return_on_side = new_effect(same);

  *(return_on_path + STATE_HEADING) = (uint64_t) mirrored_nid;
  *(return_on_side + STATE_HEADING) = (uint64_t) mirrored_nid;

  if (reverse) {
    *(return_on_path + STATE_PC) = *(advance + STATE_PC);

    *(return_on_path + STATE_ADDRESS) = (uint64_t)
      new_add(address_nid, new_sub(rd_value_nid, four_nid));

    *(return_on_side + STATE_PC)      = (uint64_t) address_nid;
    *(return_on_side + STATE_ADDRESS) = (uint64_t) rd_value_nid;

    *(return_on_side + STATE_REGISTERS) = (uint64_t)
      new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, rd_nid, pc_nid, "jalr");
  } else {
    *(return_on_path + STATE_PC)      = (uint64_t) rd_value_nid;
    *(return_on_path + STATE_ADDRESS) = (uint64_t) pc_nid;

    *(return_on_path + STATE_REGISTERS) = (uint64_t)
      new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, rd_nid, address_nid, "jalr");

    *(return_on_side + STATE_PC) = *(advance + STATE_PC);

    *(return_on_side + STATE_ADDRESS) = (uint64_t)
      new_sub(address_nid, new_sub(rd_value_nid, four_nid));
  }

  // a token on the path of an instruction cell: by instruction, and
  // within an instruction by the rules of RISC-R; an instruction that
  // is not RISC-R has no effect, and neither has a system call

  on_path =
    new_choice(new_is_field(opcode_nid, OP_LUI),
      new_choice(is_rd_zero_nid, advance, lui_effect),
    new_choice(new_is_field(opcode_nid, OP_IMM),
      new_choice(new_is_field(funct3_nid, F3_ADDI),
        new_choice(is_rd_zero_nid, advance,
          new_choice(is_rd_rs1_nid, same, addi_effect)),
        same),
    new_choice(new_is_field(opcode_nid, OP_LOAD),
      new_choice(new_is_field(funct3_nid, F3_LD),
        new_choice(is_rd_zero_nid, advance,
          new_choice(is_rd_rs1_nid, same, exchange_on_path)),
        same),
    new_choice(new_is_field(opcode_nid, OP_OP),
      new_choice(is_rd_zero_nid,
        new_arithmetic_choice(funct3_nid, funct7_nid, same,
          advance, advance, advance, advance, advance, advance),
        new_choice(is_rd_rs1_nid, same,
          new_choice(is_rd_rs2_nid, same,
            new_arithmetic_choice(funct3_nid, funct7_nid, same,
              add_effect, sub_effect, mul_effect, divu_effect, remu_effect, sltu_effect)))),
    new_choice(new_is_field(opcode_nid, OP_BRANCH),
      new_choice(new_is_field(funct3_nid, F3_BEQ),
        new_choice(is_taken_nid, branch_on_path, advance),
        same),
    new_choice(new_is_field(opcode_nid, OP_JAL),
      jump_on_path,
    new_choice(new_is_field(opcode_nid, OP_JALR),
      new_choice(is_jalr_nid, return_on_path, same),
      same)))))));

  // a token on the side: the cell acts if the token leaves or joins its path there

  on_side =
    new_choice(new_is_field(opcode_nid, OP_LOAD),
      new_choice(new_is_field(funct3_nid, F3_LD),
        new_choice(is_rd_zero_nid, same,
          new_choice(is_rd_rs1_nid, same, exchange_on_side)),
        same),
    new_choice(new_is_field(opcode_nid, OP_BRANCH),
      new_choice(new_is_field(funct3_nid, F3_BEQ),
        new_choice(is_taken_nid, branch_on_side, same),
        same),
    new_choice(new_is_field(opcode_nid, OP_JAL),
      jump_on_side,
    new_choice(new_is_field(opcode_nid, OP_JALR),
      new_choice(is_jalr_nid, return_on_side, same),
      same))));

  effect = new_choice(new_eq(heading_nid, orientation_nid), on_path,
    new_choice(new_eq(heading_nid,
      new_binary(OP_XOR, SID_HEADING, orientation_nid,
        new_binary(OP_CONCAT, SID_HEADING, mirror_nid, NID_TRUE, NOCOMMENT), "orientation mirrored")),
      on_side, same));

  // memory cell: its word and the datum are exchanged

  on_path = new_effect(same);

  *(on_path + STATE_DATA)  = (uint64_t) word_nid;
  *(on_path + STATE_WORDS) = (uint64_t)
    new_ternary(OP_WRITE, SID_WORDS, words_nid, index_nid, data_nid, "memory word written");

  // mirror: turns the token; router: turns the token if its bit is set,
  // computed rather than chosen as the heading is where the token moves

  on_side = new_effect(same);

  *(on_side + STATE_HEADING) = (uint64_t) mirrored_nid;

  advance = new_effect(same);

  *(advance + STATE_HEADING) = (uint64_t) new_binary(OP_XOR, SID_HEADING, heading_nid,
    new_binary(OP_CONCAT, SID_HEADING, new_and(router_bit_nid, mirror_nid), router_bit_nid, NOCOMMENT),
    "heading mirrored if router bit is set");

  // the cell by kind, all other kinds are blank

  effect = new_choice(new_is_field(kind_nid, CELL_INSTRUCTION), effect,
    new_choice(new_is_field(kind_nid, CELL_MEMORY), on_path,
      new_choice(new_is_field(kind_nid, CELL_MIRROR), on_side,
        new_choice(new_is_field(kind_nid, CELL_ROUTER), advance, same))));

  // position: forward one cell along the new heading, backward the cell moved back to

  if (not(reverse)) {
    *(effect + STATE_X) = (uint64_t) new_add(x_nid, new_delta_x((uint64_t*) *(effect + STATE_HEADING)));
    *(effect + STATE_Y) = (uint64_t) new_add(y_nid, new_delta_y((uint64_t*) *(effect + STATE_HEADING)));
  }

  i = 0;

  while (i < NUMBER_OF_STATES) {
    *(next_nids + i) = *(effect + i);

    i = i + 1;
  }

  // properties: where a RISC-R program stops, of the rule only

  if (reverse)
    return;

  // the rules of RISC-R that only depend on the instruction

  is_arithmetic_nid = new_and(new_is_field(opcode_nid, OP_OP),
    new_or(
      new_and(new_is_field(funct3_nid, F3_ADD),
        new_or(new_is_field(funct7_nid, F7_ADD), new_or(new_is_field(funct7_nid, F7_SUB), new_is_field(funct7_nid, F7_MUL)))),
      new_or(
        new_and(new_is_field(funct3_nid, F3_DIVU), new_is_field(funct7_nid, F7_DIVU)),
        new_or(
          new_and(new_is_field(funct3_nid, F3_REMU), new_is_field(funct7_nid, F7_REMU)),
          new_and(new_is_field(funct3_nid, F3_SLTU), new_is_field(funct7_nid, F7_SLTU))))));

  is_reversible_nid =
    new_or(new_is_field(opcode_nid, OP_LUI),
    new_or(new_is_field(opcode_nid, OP_JAL),
    new_or(new_and(new_is_field(opcode_nid, OP_BRANCH), new_is_field(funct3_nid, F3_BEQ)),
    new_or(new_and(new_is_field(opcode_nid, OP_SYSTEM), new_is_field(funct3_nid, F3_ECALL)),
    new_or(new_and(new_is_field(opcode_nid, OP_JALR), is_jalr_nid),
    new_or(
      new_and(
        new_or(new_and(new_is_field(opcode_nid, OP_IMM), new_is_field(funct3_nid, F3_ADDI)),
          new_and(new_is_field(opcode_nid, OP_LOAD), new_is_field(funct3_nid, F3_LD))),
        new_or(is_rd_zero_nid, new_not(is_rd_rs1_nid))),
      new_and(is_arithmetic_nid,
        new_or(is_rd_zero_nid, new_and(new_not(is_rd_rs1_nid), new_not(is_rd_rs2_nid))))))))));

  set_comment(is_reversible_nid, "RISC-R instruction");

  // the token is about to enter an instruction cell on its path

  is_instruction_nid = new_and(new_is_field(kind_nid, CELL_INSTRUCTION), new_eq(heading_nid, orientation_nid));

  *(property_nids + PROPERTY_ILLEGAL_INSTRUCTION) = (uint64_t)
    new_and(is_instruction_nid, new_not(is_reversible_nid));

  is_instruction_nid = new_and(is_instruction_nid, is_reversible_nid);

  *(property_nids + PROPERTY_IRREVERSIBLE_LINK) = (uint64_t)
    new_and(is_instruction_nid,
      new_and(new_is_field(opcode_nid, OP_JAL),
        new_and(new_not(is_rd_zero_nid), new_not(new_is_field(rd_value_nid, 0)))));

  *(property_nids + PROPERTY_DIVISION_BY_ZERO) = (uint64_t)
    new_and(is_instruction_nid,
      new_and(new_is_field(opcode_nid, OP_OP),
        new_and(new_or(new_is_field(funct3_nid, F3_DIVU), new_is_field(funct3_nid, F3_REMU)),
          is_division_by_zero_nid)));

  value_nid = new_is_field(
    new_binary(OP_READ, SID_WORD, registers_nid, new_number(SID_REGISTER, REG_A7), "a7 value"), SYSCALL_EXIT);

  *(property_nids + PROPERTY_EXIT) = (uint64_t)
    new_and(is_instruction_nid, new_and(new_is_field(opcode_nid, OP_SYSTEM), value_nid));

  *(property_nids + PROPERTY_UNSUPPORTED_SYSCALL) = (uint64_t)
    new_and(is_instruction_nid, new_and(new_is_field(opcode_nid, OP_SYSTEM), new_not(value_nid)));
}

void print_model(char* name, uint64_t properties) {
  uint64_t fd;
  uint64_t* next_nids;
  uint64_t i;
  uint64_t* state_nid;

  fd = open_write_only(name, S_IRUSR_IWUSR_IRGRP_IROTH);

  if (signed_less_than(fd, 0)) {
    printf("%s: could not create %s\n", selfie_name, name);

    exit(EXITCODE_IOERROR);
  }

  output_name = name;
  output_fd   = fd;

  // lines are printed as they are, there are no constants to propagate

  printing_propagated_constants = 0;

  w = dprintf(output_fd, "; %s\n\n", SELFIE_URL);

  if (reverse) {
    w = w + dprintf(output_fd, "; cellfie's inverse cell rule for a grid of %lux%lu cells: the token moves back\n", grid_width, grid_height);
    w = w + dprintf(output_fd, "; one cell against its heading, and the cell there undoes what it does in the rule\n");

    next_nids = inverse_nids;
  } else {
    w = w + dprintf(output_fd, "; cellfie's cell rule for a grid of %lux%lu cells: the cell under the token acts\n", grid_width, grid_height);
    w = w + dprintf(output_fd, "; on the token, and the token moves one cell along its heading\n");

    next_nids = forward_nids;
  }

  print_break_comment("states: the token and the cells, a layout is their initial value");

  i = 0;

  while (i < NUMBER_OF_STATES) {
    print_line((uint64_t*) *(state_nids + i));

    i = i + 1;
  }

  print_break_comment("the rule");

  i = 0;

  while (i < NUMBER_OF_STATES) {
    state_nid = (uint64_t*) *(state_nids + i);

    print_break();

    print_line(new_next(get_sid(state_nid), state_nid, (uint64_t*) *(next_nids + i), (char*) get_arg1(state_nid)));

    i = i + 1;
  }

  if (properties) {
    print_break_comment("properties: where a RISC-R program stops");

    print_line(new_property(OP_BAD, (uint64_t*) *(property_nids + PROPERTY_ILLEGAL_INSTRUCTION),
      "illegal-instruction", "token enters an instruction cell whose instruction is not RISC-R"));

    print_break();

    print_line(new_property(OP_BAD, (uint64_t*) *(property_nids + PROPERTY_IRREVERSIBLE_LINK),
      "irreversible-link", "jal with nonzero link register"));

    print_break();

    print_line(new_property(OP_BAD, (uint64_t*) *(property_nids + PROPERTY_DIVISION_BY_ZERO),
      "division-by-zero", "divu or remu by zero"));

    print_break();

    print_line(new_property(OP_BAD, (uint64_t*) *(property_nids + PROPERTY_EXIT),
      "exit", "exit system call"));

    print_break();

    print_line(new_property(OP_BAD, (uint64_t*) *(property_nids + PROPERTY_UNSUPPORTED_SYSCALL),
      "unsupported-syscall", "any other system call"));
  }

  output_name = (char*) 0;
  output_fd   = STDOUT_FD;

  printf("%s: %lu characters of model formulae written into %s\n", selfie_name, w, name);
}

// -----------------------------------------------------------------
// ----------------------------- CHECK -----------------------------
// -----------------------------------------------------------------

// The simulator and the model state the rule twice. On random states,
// the check compares one tick of the simulator with one step of the
// model, forward and backward, and the properties of the token with
// the properties of the model, and it checks that a tick backward
// after a tick forward and a tick forward after a tick backward
// restore the state. Bitr proves the latter for the model.

uint64_t random_number() {
  // linear congruential generator with Knuth's MMIX constants, high bits only
  random_seed = random_seed * 6364136223846793005 + 1442695040888963407;

  return right_shift(random_seed, 16);
}

uint64_t random_below(uint64_t n) {
  return random_number() % n;
}

uint64_t random_value() {
  uint64_t r;

  // zeros, small numbers that are often equal, addresses of
  // instructions, and full words

  r = random_below(8);

  if (r < 2)
    return 0;
  else if (r < 5)
    return random_below(4);
  else if (r < 6)
    return random_below(64) * INSTRUCTIONSIZE;
  else
    return left_shift(random_number(), 32) + random_number();
}

uint64_t random_register() {
  // few registers, so that they are often the same
  return random_below(6);
}

uint64_t random_instruction() {
  uint64_t r;
  uint64_t rd_field;
  uint64_t rs1_field;
  uint64_t rs2_field;
  uint64_t fields;

  // mostly RISC-R instructions, some that are not, some that are noise

  r = random_below(32);

  if (r == 0)
    return left_shift(random_number(), 32) + random_number();

  rd_field  = random_register();
  rs1_field = random_register();
  rs2_field = random_register();

  if (r > 2) {
    // rd distinct from its sources unless it is zero
    if (rd_field != REG_ZR) {
      while (rs1_field == rd_field)
        rs1_field = random_register();

      while (rs2_field == rd_field)
        rs2_field = random_register();
    }
  }

  r = random_below(15);

  fields = left_shift(rs2_field, 20) + left_shift(rs1_field, 15) + left_shift(rd_field, 7);

  if (r == 0)
    return left_shift(random_below(1048576), 12) + left_shift(rd_field, 7) + OP_LUI;
  else if (r == 1)
    return left_shift(random_below(4096), 20) + left_shift(rs1_field, 15) + left_shift(F3_ADDI, 12) + left_shift(rd_field, 7) + OP_IMM;
  else if (r == 2)
    return left_shift(random_below(4096), 20) + left_shift(rs1_field, 15) + left_shift(F3_LD, 12) + left_shift(rd_field, 7) + OP_LOAD;
  else if (r == 3)
    return left_shift(random_below(128), 25) + fields + left_shift(F3_SD, 12) + OP_STORE;
  else if (r == 4)
    return left_shift(F7_ADD, 25) + fields + left_shift(F3_ADD, 12) + OP_OP;
  else if (r == 5)
    return left_shift(F7_SUB, 25) + fields + left_shift(F3_SUB, 12) + OP_OP;
  else if (r == 6)
    return left_shift(F7_MUL, 25) + fields + left_shift(F3_MUL, 12) + OP_OP;
  else if (r == 7)
    return left_shift(F7_DIVU, 25) + fields + left_shift(F3_DIVU, 12) + OP_OP;
  else if (r == 8)
    return left_shift(F7_REMU, 25) + fields + left_shift(F3_REMU, 12) + OP_OP;
  else if (r == 9)
    return left_shift(F7_SLTU, 25) + fields + left_shift(F3_SLTU, 12) + OP_OP;
  else if (r == 10)
    // the rd field of a branch is part of its immediate
    return left_shift(random_below(128), 25) + fields + left_shift(F3_BEQ, 12) + OP_BRANCH;
  else if (r == 11)
    return left_shift(random_below(1048576), 12) + left_shift(rd_field, 7) + OP_JAL;
  else if (r == 12) {
    // mostly jalr rd,0(rd) with rd not zero
    if (random_below(8) > 0) {
      if (rd_field == REG_ZR)
        rd_field = REG_RA;

      return left_shift(rd_field, 15) + left_shift(F3_JALR, 12) + left_shift(rd_field, 7) + OP_JALR;
    } else
      return left_shift(random_below(4096), 20) + left_shift(rs1_field, 15) + left_shift(F3_JALR, 12) + left_shift(rd_field, 7) + OP_JALR;
  } else if (r == 13)
    return left_shift(F3_ECALL, 12) + OP_SYSTEM;
  else
    // some other function
    return left_shift(random_below(128), 25) + fields + left_shift(random_below(8), 12) + OP_OP;
}

void random_state() {
  uint64_t i;
  uint64_t r;
  uint64_t cell;

  // cells of all kinds, kinds that do not exist included

  i = 0;

  while (i < grid_size) {
    r = random_below(16);

    if (r < 8) {
      *(cell_kinds + i) = encode_cell(CELL_INSTRUCTION, random_below(4), random_below(2)) + random_below(4) * 64;
      *(cell_words + i) = random_instruction();

      if (random_below(8) == 0)
        // the upper half of the word is not part of the instruction
        *(cell_words + i) = *(cell_words + i) + left_shift(random_number(), 32);
    } else if (r < 10) {
      *(cell_kinds + i) = encode_cell(CELL_MEMORY, random_below(4), random_below(2));
      *(cell_words + i) = random_value();
    } else if (r < 13) {
      *(cell_kinds + i) = encode_cell(CELL_ROUTER, random_below(4), random_below(2));
      *(cell_words + i) = random_below(128);

      if (random_below(8) == 0)
        *(cell_words + i) = left_shift(random_number(), 32) + random_number();
    } else if (r < 15) {
      *(cell_kinds + i) = encode_cell(CELL_MIRROR, random_below(4), random_below(2));
      *(cell_words + i) = random_value();
    } else {
      *(cell_kinds + i) = random_below(256);
      *(cell_words + i) = random_value();
    }

    i = i + 1;
  }

  // the token, mostly where a cell acts on it: on its path or on its side

  token_x = random_below(grid_width);
  token_y = random_below(grid_height);

  token_heading = random_below(4);

  cell = *(cell_kinds + cell_index(token_x, token_y));

  r = random_below(4);

  if (r == 0)
    token_heading = get_cell_orientation(cell);
  else if (r == 1)
    token_heading = mirror_heading(get_cell_orientation(cell), get_cell_mirror(cell));

  token_pc      = random_value();
  token_address = random_value();
  token_data    = random_value();

  i = 1;

  while (i < NUMBEROFREGISTERS) {
    *(token_registers + i) = random_value();

    i = i + 1;
  }

  if (random_below(4) == 0)
    *(token_registers + REG_A7) = SYSCALL_EXIT;
}

void set_model_state() {
  uint64_t i;

  // the state of the simulator becomes the state of the model

  set_state((uint64_t*) *(state_nids + STATE_X), token_x);
  set_state((uint64_t*) *(state_nids + STATE_Y), token_y);
  set_state((uint64_t*) *(state_nids + STATE_HEADING), token_heading);
  set_state((uint64_t*) *(state_nids + STATE_PC), token_pc);
  set_state((uint64_t*) *(state_nids + STATE_ADDRESS), token_address);
  set_state((uint64_t*) *(state_nids + STATE_DATA), token_data);

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    write_array_raw((uint64_t*) *(state_nids + STATE_REGISTERS), i, *(token_registers + i));

    i = i + 1;
  }

  i = 0;

  while (i < grid_size) {
    write_array_raw((uint64_t*) *(state_nids + STATE_KINDS), i, *(cell_kinds + i));
    write_array_raw((uint64_t*) *(state_nids + STATE_WORDS), i, *(cell_words + i));

    i = i + 1;
  }
}

void advance_model() {
  uint64_t i;

  // states move to the next step, the next step is one ahead of it

  i = 0;

  while (i < NUMBER_OF_STATES) {
    set_step((uint64_t*) *(state_nids + i), next_step);

    i = i + 1;
  }

  current_step = next_step;

  next_step = current_step + 1;
}

void step_model(uint64_t* next_nids) {
  uint64_t x;
  uint64_t y;
  uint64_t heading;
  uint64_t pc_value;
  uint64_t address;
  uint64_t data;

  // one step of the rule or the inverse rule: array writes are
  // logged while evaluating and applied afterwards

  x        = eval_line((uint64_t*) *(next_nids + STATE_X));
  y        = eval_line((uint64_t*) *(next_nids + STATE_Y));
  heading  = eval_line((uint64_t*) *(next_nids + STATE_HEADING));
  pc_value = eval_line((uint64_t*) *(next_nids + STATE_PC));
  address  = eval_line((uint64_t*) *(next_nids + STATE_ADDRESS));
  data     = eval_line((uint64_t*) *(next_nids + STATE_DATA));

  eval_line((uint64_t*) *(next_nids + STATE_REGISTERS));
  eval_line((uint64_t*) *(next_nids + STATE_WORDS));

  apply_writes();

  set_state((uint64_t*) *(state_nids + STATE_X), x);
  set_state((uint64_t*) *(state_nids + STATE_Y), y);
  set_state((uint64_t*) *(state_nids + STATE_HEADING), heading);
  set_state((uint64_t*) *(state_nids + STATE_PC), pc_value);
  set_state((uint64_t*) *(state_nids + STATE_ADDRESS), address);
  set_state((uint64_t*) *(state_nids + STATE_DATA), data);

  advance_model();
}

uint64_t is_model_state(char* direction) {
  uint64_t i;
  uint64_t expected;
  uint64_t actual;
  char* what;

  // is the state of the model the state of the simulator?

  what = (char*) 0;

  expected = 0;
  actual   = 0;

  if (get_state((uint64_t*) *(state_nids + STATE_X)) != token_x) {
    what     = "token-x";
    expected = token_x;
    actual   = get_state((uint64_t*) *(state_nids + STATE_X));
  } else if (get_state((uint64_t*) *(state_nids + STATE_Y)) != token_y) {
    what     = "token-y";
    expected = token_y;
    actual   = get_state((uint64_t*) *(state_nids + STATE_Y));
  } else if (get_state((uint64_t*) *(state_nids + STATE_HEADING)) != token_heading) {
    what     = "token-heading";
    expected = token_heading;
    actual   = get_state((uint64_t*) *(state_nids + STATE_HEADING));
  } else if (get_state((uint64_t*) *(state_nids + STATE_PC)) != token_pc) {
    what     = "token-pc";
    expected = token_pc;
    actual   = get_state((uint64_t*) *(state_nids + STATE_PC));
  } else if (get_state((uint64_t*) *(state_nids + STATE_ADDRESS)) != token_address) {
    what     = "token-address";
    expected = token_address;
    actual   = get_state((uint64_t*) *(state_nids + STATE_ADDRESS));
  } else if (get_state((uint64_t*) *(state_nids + STATE_DATA)) != token_data) {
    what     = "token-data";
    expected = token_data;
    actual   = get_state((uint64_t*) *(state_nids + STATE_DATA));
  }

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    if (read_array_raw((uint64_t*) *(state_nids + STATE_REGISTERS), i) != *(token_registers + i)) {
      what     = "token-registers";
      expected = *(token_registers + i);
      actual   = read_array_raw((uint64_t*) *(state_nids + STATE_REGISTERS), i);
    }

    i = i + 1;
  }

  i = 0;

  while (i < grid_size) {
    if (read_array_raw((uint64_t*) *(state_nids + STATE_KINDS), i) != *(cell_kinds + i)) {
      what     = "cell-kinds";
      expected = *(cell_kinds + i);
      actual   = read_array_raw((uint64_t*) *(state_nids + STATE_KINDS), i);
    } else if (read_array_raw((uint64_t*) *(state_nids + STATE_WORDS), i) != *(cell_words + i)) {
      what     = "cell-words";
      expected = *(cell_words + i);
      actual   = read_array_raw((uint64_t*) *(state_nids + STATE_WORDS), i);
    }

    i = i + 1;
  }

  if (what == (char*) 0)
    return 1;

  printf("%s: %s: %s is 0x%lX in the model and 0x%lX in the simulator\n", selfie_name, direction, what, actual, expected);

  return 0;
}

uint64_t check_rule(uint64_t states) {
  uint64_t* snapshot;
  uint64_t* state;
  uint64_t* sid;
  uint64_t i;
  uint64_t n;
  uint64_t failed;
  uint64_t property;
  uint64_t ok;
  uint64_t stopped;

  // a grid of 4x4 cells: all there is to a tick is the cell under
  // the token and, backward, the four cells around it

  allocate_grid(4, 4);

  model_sorts(log_two(grid_width), log_two(grid_height));
  model_states();

  reverse = 0;

  model_rule();

  reverse = 1;

  model_rule();

  reverse = 0;

  // the states of the model start zeroed, the evaluator needs that

  i = 0;

  while (i < NUMBER_OF_STATES) {
    state = (uint64_t*) *(state_nids + i);

    sid = get_sid(state);

    if (is_bitvector(sid))
      eval_init(new_init(sid, state, new_number(sid, 0), "zeroed"));
    else
      eval_init(new_init(sid, state, new_number(get_arg3(sid), 0), "zeroed"));

    i = i + 1;
  }

  next_step = current_step + 1;

  snapshot = (uint64_t*) 0;

  failed  = 0;
  stopped = 0;

  n = 0;

  while (n < states) {
    random_state();

    snapshot = take_snapshot(snapshot);

    ok = 1;

    // the properties, and one tick forward

    set_model_state();

    property = token_property();

    if (property != PROPERTY_NONE)
      stopped = stopped + 1;

    i = 1;

    while (i <= NUMBER_OF_PROPERTIES) {
      if (eval_line((uint64_t*) *(property_nids + i)) != (property == i)) {
        printf("%s: property %lu is %lu in the model but the simulator finds property %lu\n", selfie_name,
          i, eval_line((uint64_t*) *(property_nids + i)), property);

        ok = 0;
      }

      i = i + 1;
    }

    step_model(forward_nids);

    reverse = 0;

    tick();

    ok = ok * is_model_state("forward");

    // and back

    reverse = 1;

    tick();

    if (not(is_snapshot(snapshot, 1))) {
      printf("%s: a tick backward after a tick forward does not restore the state\n", selfie_name);

      ok = 0;
    }

    // one tick backward

    restore_snapshot(snapshot);

    set_model_state();

    step_model(inverse_nids);

    reverse = 1;

    tick();

    ok = ok * is_model_state("backward");

    // and forth

    reverse = 0;

    tick();

    if (not(is_snapshot(snapshot, 1))) {
      printf("%s: a tick forward after a tick backward does not restore the state\n", selfie_name);

      ok = 0;
    }

    if (not(ok)) {
      failed = failed + 1;

      if (failed == 1) {
        restore_snapshot(snapshot);

        write_layout("cellfie-check-failed.rle");
      }
    }

    n = n + 1;
  }

  executed_ticks        = 0;
  executed_instructions = 0;

  printf("%s: simulator and model agree forward and backward on %lu of %lu random states,\n", selfie_name, states - failed, states);
  printf("%s: and one tick is undone by the other; a property holds in %lu states\n", selfie_name, stopped);

  return failed == 0;
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

uint64_t cellfie() {
  uint64_t width;
  uint64_t height;
  char* name;

  if (number_of_remaining_arguments() == 0)
    return EXITCODE_NOARGUMENTS;

  while (number_of_remaining_arguments() > 0) {
    get_argument();

    if (string_compare(argument, "-inverse"))
      reverse = 1;
    else if (string_compare(argument, "-noproperties"))
      printing_properties = 0;
    else if (number_of_remaining_arguments() == 0)
      return EXITCODE_BADARGUMENTS;
    else if (string_compare(argument, "-l"))
      load_layout(get_argument());
    else if (string_compare(argument, "-check")) {
      if (not(check_rule(atoi(get_argument()))))
        return EXITCODE_SYSTEMERROR;
    } else if (string_compare(argument, "-btor2")) {
      if (number_of_remaining_arguments() < 2)
        return EXITCODE_BADARGUMENTS;

      width  = atoi(get_argument());
      height = atoi(get_argument());

      if (state_nids != (uint64_t*) 0) {
        // lines get their nids when printed
        printf("%s: one model per run\n", selfie_name);

        return EXITCODE_BADARGUMENTS;
      }

      allocate_grid(width, height);

      model_sorts(log_two(grid_width), log_two(grid_height));
      model_states();
      model_rule();

      name = string_alloc(MAX_FILENAME_LENGTH);

      if (reverse)
        sprintf(name, "cellfie-%lux%lu-inverse.btor2", grid_width, grid_height);
      else if (printing_properties)
        sprintf(name, "cellfie-%lux%lu.btor2", grid_width, grid_height);
      else
        sprintf(name, "cellfie-%lux%lu-noproperties.btor2", grid_width, grid_height);

      print_model(name, and(printing_properties, reverse == 0));

      reverse = 0;
    } else if (grid_size == 0) {
      printf("%s: no layout loaded\n", selfie_name);

      return EXITCODE_BADARGUMENTS;
    } else if (string_compare(argument, "-o"))
      write_layout(get_argument());
    else if (string_compare(argument, "-f"))
      run_forward(atoi(get_argument()));
    else if (string_compare(argument, "-b"))
      run_backward(atoi(get_argument()));
    else if (string_compare(argument, "-rev")) {
      if (not(run_forward_and_backward(atoi(get_argument()))))
        return EXITCODE_SYSTEMERROR;
    } else
      return EXITCODE_BADARGUMENTS;
  }

  return EXITCODE_NOERROR;
}

int main(int argc, char** argv) {
  uint64_t exit_code;

  init_selfie((uint64_t) argc, (uint64_t*) argv);

  init_library();
  init_system();
  init_target();

  init_model();

  exit_code = cellfie();

  return exit_selfie(exit_code, " { -l layout | -o layout | -f ticks | -b ticks | -rev ticks | -inverse | -noproperties | -btor2 width height | -check states }");
}
