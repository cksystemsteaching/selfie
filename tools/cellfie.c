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
                 -inverse | -noproperties | -btor2 width height | -check states |
                 -heap offset words | -stack words | -i file | -c binary |
                 -a abstraction heap-allowance stack-allowance |
                 -tapes descriptors | -tapewords words } [ -h binary ... ]

-c compiles a RISC-R binary into a layout: its instructions in a row,
memory cells for its data segment, for the regions of its heap given
with -heap before, as offset in bytes and number of words, and for
the top of its stack, 64 words or as many as given with -stack, tape
cells for standard output and error, and the bytes of the file given
with -i as its standard input, all wired by combs of routers. -a
then writes the abstraction that relates the layout to rotor's
RISC-R model of the binary with the given allowances in bytes, for
bitr's product of the two.

-h runs a RISC-R binary with the remaining arguments on the layout
that -c would write, without laying it out: the hybrid simulator has
the instruction cells and the cells of the words act on the token as
the rule says, and adds the ticks that the wire in between takes,
which the layout determines. Words are allocated when accessed, so
the grid can have a cell for every word of a large heap. Files are
the host's. -tapes before it sets the number of file descriptors, a
power of two, 4 by default, and gives each of them tapes, not only
the standard ones; -tapewords sets the words per tape, 16 by default.

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

void set_grid_size(uint64_t width, uint64_t height);
void allocate_grid(uint64_t width, uint64_t height);

uint64_t cell_index(uint64_t x, uint64_t y);

uint64_t get_cell_kind(uint64_t cell)        { return cell % 8; }
uint64_t get_cell_orientation(uint64_t cell) { return cell / 8 % 4; }
uint64_t get_cell_mirror(uint64_t cell)      { return cell / 32 % 2; }
uint64_t is_cell_tagged(uint64_t cell)       { return cell / 64 % 2; }

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
uint64_t CELL_TAPE        = 5; // flips the bits of its word by the datum of the token

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
uint64_t* cell_tags  = (uint64_t*) 0; // address of a tagged instruction, memory, or tape cell

// -----------------------------------------------------------------
// ----------------------------- TOKEN -----------------------------
// -----------------------------------------------------------------

void reset_token();

uint64_t  get_token_register(uint64_t reg);
void      set_token_register(uint64_t reg, uint64_t value);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t NUMBER_OF_TAPES = 4; // file descriptors, standard input, output, and error included; a power of two, see -tapes

// what a token in a read or write is on its way to, or back from

uint64_t LEG_NONE        = 0;
uint64_t LEG_BUFFER      = 1; // the buffer word, to fetch it
uint64_t LEG_TAPE        = 2; // the tape word
uint64_t LEG_BUFFER_BACK = 3; // the buffer word again, to put back what is its now

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t token_x       = 0; // column of the cell the token is at
uint64_t token_y       = 0; // row
uint64_t token_heading = 0; // where the token moves next

uint64_t token_pc      = 0; // address of the instruction the token enters next, or travels to
uint64_t token_address = 0; // in transit: address of the memory word, or of the instruction left
uint64_t token_data    = 0; // in transit: register value on its way to memory, or back

uint64_t* token_registers = (uint64_t*) 0; // register file

// the state of RISC-R's system calls, see riscr.md

uint64_t token_break      = 0; // program break
uint64_t token_open_files = 3; // next file descriptor

uint64_t* token_heads  = (uint64_t*) 0; // head of each tape, in words
uint64_t* token_ends   = (uint64_t*) 0; // end of each input file, in bytes, -1 if unknown
uint64_t* token_inputs = (uint64_t*) 0; // 1 for an input tape, 0 for an output tape
uint64_t* token_opens  = (uint64_t*) 0; // 1 if the host can open the file, for descriptors from 3 on

// in a read or write, between the cell of the ecall and memory or tape

uint64_t token_leg  = 0; // what the token is on its way to, LEG_NONE on a path
uint64_t token_word = 0; // which word of the buffer the token transfers

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

uint64_t transfer_words();
uint64_t is_transfer();
uint64_t transfer_result(uint64_t head);
uint64_t leg_address(uint64_t head);

void     cell_brk();
void     cell_openat();
uint64_t cell_transfer(uint64_t on_path);
uint64_t cell_system_call(uint64_t on_path);

void act_instruction(uint64_t orientation, uint64_t mirror_kind, uint64_t word);
void act_memory(uint64_t* word);
void act_tape(uint64_t* word);
void act();

void move_token();

void tick();

uint64_t instruction_property(uint64_t word);
uint64_t token_property();

// ------------------------ GLOBAL CONSTANTS -----------------------

// properties of a token at a cell: where a RISC-R program stops

uint64_t PROPERTY_NONE                = 0;
uint64_t PROPERTY_ILLEGAL_INSTRUCTION = 1; // not RISC-R: unknown, sd, rd is a source, malformed jalr
uint64_t PROPERTY_IRREVERSIBLE_LINK   = 2; // jal with nonzero link register
uint64_t PROPERTY_DIVISION_BY_ZERO    = 3;
uint64_t PROPERTY_EXIT                = 4; // exit system call
uint64_t PROPERTY_UNSUPPORTED_SYSCALL = 5; // system call other than exit, read, write, openat, brk
uint64_t PROPERTY_IRREVERSIBLE_BRK    = 6; // brk with nonzero a0 or zero program break
uint64_t PROPERTY_IRREVERSIBLE_TAPE   = 7; // read or write of 4GB or more
uint64_t PROPERTY_IRREVERSIBLE_OPENAT = 8; // openat with all file descriptors allocated
uint64_t PROPERTY_INVALID_ADDRESS     = 9; // token at a memory or tape cell that is not the cell of its address
uint64_t PROPERTY_INVALID_PC          = 10; // token on the path of an instruction cell that is not the cell of its pc

uint64_t NUMBER_OF_PROPERTIES = 10;

uint64_t SYSCALL_FAILURE = 4294967295; // -1 as 32-bit system call result
uint64_t LARGEST_TRANSFER = 4294967296; // a read or write transfers less than 4GB

uint64_t INPUT_TAPES  = 0; // addresses of input tape words: 2^63 + descriptor * 2^32 + position * 8
uint64_t OUTPUT_TAPES = 0; // addresses of output tape words: 2^62 + descriptor * 2^32 + position * 8

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t reverse = 0; // flag for running the rule backward and for generating the inverse model

uint64_t executed_ticks        = 0; // ticks forward minus ticks backward
uint64_t executed_instructions = 0; // instructions forward minus instructions backward

// what cells did, in both directions, for the check to report what it covers

uint64_t acted_instructions = 0; // instruction cells that acted on a token on their path or side
uint64_t acted_breaks       = 0; // brk that changed the program break
uint64_t acted_opens        = 0; // openat
uint64_t acted_legs         = 0; // read or write that began, went on, or ended a transfer

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
void load_system_state();
void load_file_descriptor();
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

uint64_t state_length(uint64_t state);
uint64_t get_state_word(uint64_t state, uint64_t i);
void     set_state_word(uint64_t state, uint64_t i, uint64_t value);
char*    state_name(uint64_t state);

uint64_t  snapshot_size();
uint64_t* take_snapshot(uint64_t* snapshot);
void      restore_snapshot(uint64_t* snapshot);
uint64_t  is_snapshot(uint64_t* snapshot, uint64_t reporting);

void print_token();
void print_property(uint64_t property);
void print_stop(uint64_t property);

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
void model_transfer(uint64_t reading);
void model_rule();

char* property_name(uint64_t property);
char* property_comment(uint64_t property);

void print_model(char* name, uint64_t properties);

// ------------------------ GLOBAL CONSTANTS -----------------------

// states of the model, in the order of the state of the simulator

uint64_t STATE_X          = 0;
uint64_t STATE_Y          = 1;
uint64_t STATE_HEADING    = 2;
uint64_t STATE_PC         = 3;
uint64_t STATE_ADDRESS    = 4;
uint64_t STATE_DATA       = 5;
uint64_t STATE_BREAK      = 6;
uint64_t STATE_OPEN_FILES = 7;
uint64_t STATE_LEG        = 8;
uint64_t STATE_WORD       = 9;
uint64_t STATE_REGISTERS  = 10;
uint64_t STATE_HEADS      = 11;
uint64_t STATE_ENDS       = 12;
uint64_t STATE_INPUTS     = 13;
uint64_t STATE_OPENS      = 14;
uint64_t STATE_KINDS      = 15;
uint64_t STATE_WORDS      = 16;
uint64_t STATE_TAGS       = 17;

uint64_t NUMBER_OF_STATES = 18;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* SID_HEADING   = (uint64_t*) 0;
uint64_t* SID_X         = (uint64_t*) 0;
uint64_t* SID_Y         = (uint64_t*) 0;
uint64_t* SID_INDEX     = (uint64_t*) 0;
uint64_t* SID_CELL      = (uint64_t*) 0;
uint64_t* SID_WORD      = (uint64_t*) 0;
uint64_t* SID_REGISTER  = (uint64_t*) 0;
uint64_t* SID_REGISTERS = (uint64_t*) 0;
uint64_t* SID_FD        = (uint64_t*) 0;
uint64_t* SID_TAPES     = (uint64_t*) 0;
uint64_t* SID_KINDS     = (uint64_t*) 0;
uint64_t* SID_WORDS     = (uint64_t*) 0;

uint64_t* NID_FALSE = (uint64_t*) 0;
uint64_t* NID_TRUE  = (uint64_t*) 0;

uint64_t* state_nids = (uint64_t*) 0; // state lines

uint64_t* forward_nids = (uint64_t*) 0; // next value of each state in the rule
uint64_t* inverse_nids = (uint64_t*) 0; // next value of each state in the inverse rule

uint64_t* property_nids = (uint64_t*) 0; // condition of each property, forward only

// lines and effects of the rule that its parts share

uint64_t* registers_nid = (uint64_t*) 0; // register file
uint64_t* address_nid   = (uint64_t*) 0; // address of the token
uint64_t* mirrored_nid  = (uint64_t*) 0; // heading of the token turned by the mirror of the cell

uint64_t* a0_index_nid = (uint64_t*) 0;
uint64_t* a0_nid       = (uint64_t*) 0; // values of the registers of a system call
uint64_t* a1_nid       = (uint64_t*) 0;
uint64_t* a2_nid       = (uint64_t*) 0;
uint64_t* a3_nid       = (uint64_t*) 0;
uint64_t* a7_nid       = (uint64_t*) 0;

uint64_t* heads_nid  = (uint64_t*) 0; // heads of the tapes
uint64_t* leg_nid    = (uint64_t*) 0; // leg of a transfer
uint64_t* number_nid = (uint64_t*) 0; // number of the word in transfer

uint64_t* fd_nid       = (uint64_t*) 0; // file descriptor in a1
uint64_t* head_nid     = (uint64_t*) 0; // head of its tape
uint64_t* count_nid    = (uint64_t*) 0; // words to transfer
uint64_t* last_word_nid     = (uint64_t*) 0; // number of the last word
uint64_t* buffer_nid   = (uint64_t*) 0; // address of the buffer word in transfer
uint64_t* is_open_nid  = (uint64_t*) 0;
uint64_t* is_input_nid = (uint64_t*) 0;
uint64_t* fits_nid     = (uint64_t*) 0; // transfer of less than 4GB
uint64_t* failure_nid  = (uint64_t*) 0; // -1 as system call result

uint64_t* same    = (uint64_t*) 0; // no effect
uint64_t* advance = (uint64_t*) 0; // the pc moves to the next instruction

uint64_t* system_on_path = (uint64_t*) 0; // system call by a token on the path
uint64_t* system_on_side = (uint64_t*) 0; // and on the side

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

uint64_t* next_values = (uint64_t*) 0; // next value of each bit-vector state of the model

// -----------------------------------------------------------------
// --------------------------- COMPILER ----------------------------
// -----------------------------------------------------------------

void boot_binary(char* name, uint64_t arguments);

uint64_t ceiling_log_two(uint64_t n);

void     add_region(uint64_t start, uint64_t words, uint64_t kind);
uint64_t find_region(uint64_t address);
uint64_t region_height(uint64_t lo, uint64_t hi);

uint64_t plan_path_combs(uint64_t* keys, uint64_t count);
void     plan_path();
void     plan_regions();
uint64_t initial_word(uint64_t address);
uint64_t count_strips(uint64_t bits);
void     plan_strips();
void     plan_rows();

uint64_t is_stack_strip(uint64_t strip);
uint64_t has_stack_strip(uint64_t lo, uint64_t hi);
uint64_t split_strips(uint64_t lo, uint64_t hi);

void     lay_strip_cell(uint64_t x, uint64_t y, uint64_t kind, uint64_t word);
uint64_t place_strips(uint64_t lo, uint64_t hi, uint64_t x, uint64_t y);

uint64_t get_word_strip(uint64_t address, uint64_t region);
uint64_t get_descending_column(uint64_t address);
uint64_t get_word_column(uint64_t address, uint64_t strip);
uint64_t get_word_row(uint64_t strip);

void lay_descending_comb(uint64_t* keys, uint64_t* xs, uint64_t lo, uint64_t hi, uint64_t x, uint64_t y, uint64_t down);
void     boot_token();

uint64_t differing_bit(uint64_t a, uint64_t b);
uint64_t comb_height(uint64_t* keys, uint64_t lo, uint64_t hi);

void lay_cell(uint64_t x, uint64_t y, uint64_t cell, uint64_t word);
void lay_tagged_cell(uint64_t x, uint64_t y, uint64_t cell, uint64_t word, uint64_t tag);
void lay_mirror(uint64_t x, uint64_t y, uint64_t mirror_kind);
void lay_comb(uint64_t* keys, uint64_t* xs, uint64_t lo, uint64_t hi, uint64_t y, uint64_t down, uint64_t field);
void lay_side_comb(uint64_t* keys, uint64_t* ys, uint64_t lo, uint64_t hi, uint64_t x, uint64_t field);

uint64_t lay_path_combs(uint64_t* keys, uint64_t* outs, uint64_t* ins, uint64_t count, uint64_t control);

void add_memory_word(uint64_t address, uint64_t value, uint64_t kind);

void compile_layout(char* name);

void print_difference(uint64_t index_sid, uint64_t state_nid, uint64_t index, uint64_t cell_state_nid, uint64_t cell_index);
void write_abstraction(char* name, uint64_t heap_allowance, uint64_t stack_allowance);

// ------------------------ GLOBAL CONSTANTS -----------------------


uint64_t TAPE_WORDS = 16; // words per tape, as in rotor's model

uint64_t MAX_HEAP_REGIONS = 8;
uint64_t MAX_REGIONS      = 64; // data, heap, stack, tapes

uint64_t COMB_COLUMN = 3; // first column of the combs over the strips of words

uint64_t CLASS_CONTROL = 1; // beq, jal, jalr
uint64_t CLASS_ACCESS  = 2; // ld with rd not zero, ecall

// ------------------------ GLOBAL VARIABLES -----------------------

// the heap has memory cells for regions of words, each an offset from its start

uint64_t* heap_offsets = (uint64_t*) 0;
uint64_t* heap_words   = (uint64_t*) 0;

uint64_t number_of_heap_regions = 0;

uint64_t tape_files = 3; // the file descriptors below have tapes: the standard ones, or all with -tapes

uint64_t stack_words = 64; // the stack has memory cells for that many words below its top

char* input_name = (char*) 0; // file whose bytes are on the tape of standard input

uint64_t* input_words = (uint64_t*) 0; // its bytes
uint64_t  input_size  = 0;             // its size in bytes

// the instructions that leave the path, by ascending address, and their columns

uint64_t* instruction_classes = (uint64_t*) 0; // of all instructions

uint64_t* control_keys = (uint64_t*) 0;
uint64_t* control_out  = (uint64_t*) 0;
uint64_t* control_in   = (uint64_t*) 0;

uint64_t controls = 0;

uint64_t* access_keys = (uint64_t*) 0;
uint64_t* access_out  = (uint64_t*) 0;
uint64_t* access_in   = (uint64_t*) 0;

uint64_t accesses = 0;

// the regions of words of memory and tapes that have a cell, by ascending address

uint64_t* region_starts = (uint64_t*) 0; // address of the first word
uint64_t* region_words  = (uint64_t*) 0; // number of words
uint64_t* region_kinds  = (uint64_t*) 0; // memory or tape cells
uint64_t* region_ranks  = (uint64_t*) 0; // number of words in the regions before

uint64_t number_of_regions      = 0;
uint64_t number_of_region_words = 0;

uint64_t last_region = 0; // the region found last

// the rows of the layout

// the path in strips: a strip is a row of the instructions whose addresses
// differ in their lower bits only, with its combs north and south of it

uint64_t path_bits    = 0; // the bits of an instruction address that select the column
uint64_t path_width   = 0; // instructions of a strip
uint64_t path_strips  = 0; // number of strips
uint64_t path_pitch   = 0; // rows of a strip
uint64_t path_column  = 0; // column of the first instruction of each strip

uint64_t control_height = 0; // rows of a comb of control of a strip
uint64_t access_height  = 0; // rows of a comb of access of a strip

uint64_t control_side_height = 0; // columns of a comb over the strips that transfer control
uint64_t access_side_height  = 0; // columns of a comb over the strips that access memory

uint64_t first_control_strip = 0; // the first strip that transfers control
uint64_t first_access_strip  = 0; // the first strip that accesses memory

uint64_t side_height = 0; // of the comb over the strips planned last
uint64_t first_strip = 0; // of the strips planned last

uint64_t* side_keys    = (uint64_t*) 0; // an address in each strip that has a comb
uint64_t* side_entries = (uint64_t*) 0; // the row in which a token enters each such strip
uint64_t* side_exits   = (uint64_t*) 0; // the row in which a token leaves each such strip

// the rows of a strip of the path, from its first row

uint64_t control_turn_row  = 0; // control leaves the strip west
uint64_t access_turn_row   = 0; // a token returns from memory east into the strip
uint64_t control_out_row   = 0;
uint64_t access_in_row     = 0;
uint64_t path_row          = 0;
uint64_t control_in_row    = 0;
uint64_t access_out_row    = 0;
uint64_t control_spine_row = 0; // control enters the strip east
uint64_t access_spine_row  = 0; // a token leaves the strip west for memory
uint64_t path_return_row   = 0; // the path leads west to the next strip

uint64_t memory_in_row = 0; // the first row of the first strip of words

// the strips of words: a strip is a row of the words whose addresses differ
// in their lower bits only, with a comb to them above and one from them below

uint64_t strip_bits   = 0; // the bits of a word address that select the column
uint64_t strip_height = 0; // rows of a comb of a strip
uint64_t strip_pitch  = 0; // rows of a strip

uint64_t* region_strips = (uint64_t*) 0; // the strip of the first word of each region
uint64_t* strip_keys    = (uint64_t*) 0; // the address of the first word of each strip
uint64_t* strip_lasts   = (uint64_t*) 0; // the address of the last word of each strip
uint64_t* strip_entries = (uint64_t*) 0; // the first row of each strip, from memory_in_row

uint64_t number_of_strips = 0;

uint64_t stack_start = 0; // address of the first word of the stack that has a cell

uint64_t laying_strips = 0; // the combs over the strips are laid, not only placed
uint64_t split_bit     = 0; // the bit that split the strips last

uint64_t comb_columns = 0; // columns of a comb over the strips
uint64_t memory_rows  = 0; // rows of all strips
uint64_t word_column  = 0; // first column of the words

// the words of memory and tapes that have a cell, by ascending address

uint64_t* word_addresses = (uint64_t*) 0;
uint64_t* word_values    = (uint64_t*) 0;
uint64_t* word_kinds     = (uint64_t*) 0; // memory or tape cell
uint64_t* word_cells     = (uint64_t*) 0; // index of the cell on the grid

uint64_t number_of_words = 0;

uint64_t heap_start_address = 0; // start of the heap of the compiled binary

uint64_t abstraction_nid  = 0; // next nid of the abstraction being written
uint64_t abstraction_step = 0; // nid of its output step

// -----------------------------------------------------------------
// ---------------------------- HYBRID -----------------------------
// -----------------------------------------------------------------

uint64_t* word_in_store(uint64_t address);
void      boot_store();

uint64_t* allocate_host_buffer(uint64_t words);

void host_openat();
void host_read();
void host_write();
void host_system_call();

void run_hybrid(char* name);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t PAGE_WORDS  = 4096;   // words of memory or of a tape are allocated in pages
uint64_t STORE_PAGES = 131072; // 4GB of memory and of each tape

// ------------------------ GLOBAL VARIABLES -----------------------

// the words of memory, of the input tapes, and of the output tapes, in pages

uint64_t* store = (uint64_t*) 0;

uint64_t* host_fds = (uint64_t*) 0; // file descriptors of the host by file descriptor

uint64_t* host_buffer       = (uint64_t*) 0; // bytes on their way from and to the host
uint64_t  host_buffer_words = 0;

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

uint64_t cellfie();

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------------- GRID ------------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

void set_grid_size(uint64_t width, uint64_t height) {
  // the width and height of the grid are the powers of two of at least
  // two cells that width and height fit in

  grid_width = 2;

  while (grid_width < width)
    grid_width = grid_width * 2;

  grid_height = 2;

  while (grid_height < height)
    grid_height = grid_height * 2;
}

void allocate_grid(uint64_t width, uint64_t height) {
  // the grid is a torus of blank cells

  set_grid_size(width, height);

  grid_size = grid_width * grid_height;

  cell_kinds = zmalloc(grid_size * sizeof(uint64_t));
  cell_words = zmalloc(grid_size * sizeof(uint64_t));
  cell_tags  = zmalloc(grid_size * sizeof(uint64_t));

  if (token_registers == (uint64_t*) 0)
    reset_token();
}

uint64_t cell_index(uint64_t x, uint64_t y) {
  return y * grid_width + x;
}

// -----------------------------------------------------------------
// ----------------------------- TOKEN -----------------------------
// -----------------------------------------------------------------

void reset_token() {
  uint64_t i;

  // the token as a RISC-R machine starts, without a program: at the
  // northwestern cell heading east, all registers zero, no program break,
  // the three standard files open with standard input the only input tape

  if (token_registers == (uint64_t*) 0) {
    token_registers = zmalloc(NUMBEROFREGISTERS * sizeof(uint64_t));

    token_heads  = zmalloc(NUMBER_OF_TAPES * sizeof(uint64_t));
    token_ends   = zmalloc(NUMBER_OF_TAPES * sizeof(uint64_t));
    token_inputs = zmalloc(NUMBER_OF_TAPES * sizeof(uint64_t));
    token_opens  = zmalloc(NUMBER_OF_TAPES * sizeof(uint64_t));
  }

  token_x = 0;
  token_y = 0;

  token_heading = EAST;

  token_pc      = 0;
  token_address = 0;
  token_data    = 0;

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    *(token_registers + i) = 0;

    i = i + 1;
  }

  token_break      = 0;
  token_open_files = 3;

  i = 0;

  while (i < NUMBER_OF_TAPES) {
    *(token_heads + i)  = 0;
    *(token_ends + i)   = 0;
    *(token_inputs + i) = i == 0;
    *(token_opens + i)  = 0;

    i = i + 1;
  }

  token_leg  = LEG_NONE;
  token_word = 0;
}

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

uint64_t transfer_words() {
  // a3 bytes rounded up to words
  return right_shift(get_token_register(REG_A3) + 7, 3);
}

uint64_t is_transfer() {
  uint64_t fd;

  // read from an open input tape, or write to an open output tape, of
  // less than 4GB; standard files are open, others if the host opened them

  fd = get_token_register(REG_A1);

  if (get_token_register(REG_A3) >= LARGEST_TRANSFER)
    return 0;
  else if (fd >= token_open_files)
    return 0;
  else if (fd >= 3)
    if (*(token_opens + fd % NUMBER_OF_TAPES) == 0)
      return 0;

  if (get_token_register(REG_A7) == SYSCALL_READ)
    return *(token_inputs + fd % NUMBER_OF_TAPES) != 0;
  else
    return *(token_inputs + fd % NUMBER_OF_TAPES) == 0;
}

uint64_t transfer_result(uint64_t head) {
  uint64_t size;
  uint64_t end;

  // write: the size; read: the bytes before the end of the file from
  // the head on, at most the size, as with a RISC-U read

  size = get_token_register(REG_A3);

  if (get_token_register(REG_A7) == SYSCALL_READ) {
    end = *(token_ends + get_token_register(REG_A1) % NUMBER_OF_TAPES);

    if (end == (uint64_t) -1)
      return size;
    else if (head * WORDSIZE >= end)
      return 0;
    else if (end - head * WORDSIZE < size)
      return end - head * WORDSIZE;
  }

  return size;
}

uint64_t leg_address(uint64_t head) {
  // where the token is on its way to, or back from: the word of the tape
  // at the head plus the number of the word, or the word of the buffer

  if (token_leg == LEG_TAPE) {
    if (get_token_register(REG_A7) == SYSCALL_READ)
      head = INPUT_TAPES + (head + token_word) * WORDSIZE;
    else
      head = OUTPUT_TAPES + (head + token_word) * WORDSIZE;

    return head + left_shift(get_token_register(REG_A1), 32);
  } else
    return get_token_register(REG_A2) + token_word * WORDSIZE;
}

void cell_brk() {
  uint64_t a0;
  uint64_t a1;

  // brk: if a0 is zero and a1 is a word-aligned address above the program
  // break, which is not zero, a1 becomes the program break and a0 the
  // previous one. This exchanges such states with the states in which a0 is
  // not zero and below the program break, and a1 is the word-aligned program
  // break, so backward the same undoes it, and forward on such a state as
  // well, where a0 is not zero, which is a property of the token.

  a0 = get_token_register(REG_A0);
  a1 = get_token_register(REG_A1);

  if (a1 % WORDSIZE == 0) {
    if (a0 == 0) {
      if (token_break != 0)
        if (a1 > token_break) {
          set_token_register(REG_A0, token_break);

          token_break = a1;

          acted_breaks = acted_breaks + 1;
        }
    } else if (a1 == token_break)
      if (a0 < token_break) {
        token_break = a0;

        set_token_register(REG_A0, 0);

        acted_breaks = acted_breaks + 1;
      }
  }
}

void cell_openat() {
  uint64_t fd;
  uint64_t kind;
  uint64_t result;

  // openat: allocates the next file descriptor, flips the kind of its tape
  // if the flags in a2 open an input tape, O_RDONLY or 0, and adds the
  // descriptor into a0, or -1 if the host cannot open the file; backward
  // it releases the descriptor, flips the kind, and subtracts

  acted_opens = acted_opens + 1;

  if (reverse)
    token_open_files = token_open_files - 1;

  fd = token_open_files % NUMBER_OF_TAPES;

  kind = get_token_register(REG_A2) == O_RDONLY;

  if (get_token_register(REG_A2) == 0)
    kind = 1;

  *(token_inputs + fd) = bitwise_xor(*(token_inputs + fd), kind);

  if (*(token_opens + fd) != 0)
    result = token_open_files;
  else
    result = SYSCALL_FAILURE;

  if (reverse)
    set_token_register(REG_A0, get_token_register(REG_A0) - result);
  else {
    set_token_register(REG_A0, get_token_register(REG_A0) + result);

    token_open_files = token_open_files + 1;
  }
}

uint64_t cell_transfer(uint64_t on_path) {
  uint64_t fd;
  uint64_t words;
  uint64_t head;

  // read and write of at least one word: the token leaves the path and
  // travels three legs for each word of the buffer, to the buffer word,
  // whose memory cell exchanges it with the datum, to the tape word at
  // the head plus the number of the word, and to the buffer word again.
  // The tape word of a read is a memory cell, so the two words end up
  // exchanged; that of a write is a tape cell, which flips its bits by
  // the datum, so the buffer word ends up where it was. After each leg
  // the token is back at this cell, on its side, and crosses it for the
  // next leg; after the last leg the head of the tape advances by the
  // words, the result is added into a0, and the token joins the path.
  // Backward the same happens the other way round. Returns 1 if the
  // cell turns the token.

  fd    = get_token_register(REG_A1) % NUMBER_OF_TAPES;
  words = transfer_words();
  head  = *(token_heads + fd);

  if (on_path) {
    if (and(token_leg == LEG_NONE, token_word == 0)) {
      acted_legs = acted_legs + 1;

      if (reverse) {
        // undo the return: the head moves back, the result is subtracted

        token_pc = token_pc - INSTRUCTIONSIZE;

        head = head - words;

        *(token_heads + fd) = head;

        set_token_register(REG_A0, get_token_register(REG_A0) - transfer_result(head));

        token_leg  = LEG_BUFFER_BACK;
        token_word = words - 1;

        token_address = token_address + leg_address(head);
      } else {
        token_leg = LEG_BUFFER;

        token_address = token_address + leg_address(head);

        executed_instructions = executed_instructions + 1;
      }

      return 1;
    }
  } else if (and(token_leg != LEG_NONE, token_word < words)) {
    acted_legs = acted_legs + 1;

    token_address = token_address - leg_address(head);

    if (reverse) {
      if (token_leg == LEG_BUFFER) {
        if (token_word == 0) {
          // undo the departure

          token_leg = LEG_NONE;

          executed_instructions = executed_instructions - 1;

          return 1;
        }

        token_leg  = LEG_BUFFER_BACK;
        token_word = token_word - 1;
      } else
        token_leg = token_leg - 1;
    } else if (token_leg == LEG_BUFFER_BACK) {
      if (token_word == words - 1) {
        // the last leg: the head advances, the result is added

        token_leg  = LEG_NONE;
        token_word = 0;

        *(token_heads + fd) = head + words;

        set_token_register(REG_A0, get_token_register(REG_A0) + transfer_result(head));

        token_pc = token_pc + INSTRUCTIONSIZE;

        return 1;
      }

      token_leg  = LEG_BUFFER;
      token_word = token_word + 1;
    } else
      token_leg = token_leg + 1;

    token_address = token_address + leg_address(head);
  }

  return 0;
}

uint64_t cell_system_call(uint64_t on_path) {
  uint64_t a7;
  uint64_t result;

  // ecall: exit is a property of the token and has no effect, and neither
  // has an unknown system call; brk and openat happen on the path; so do a
  // read or write that fails, which adds -1 into a0, or transfers no word;
  // any other read or write is a tour of the token. Returns 1 if the cell
  // turns the token.

  a7 = get_token_register(REG_A7);

  if (a7 == SYSCALL_BRK) {
    if (on_path) {
      cell_brk();

      advance_on_path();
    }
  } else if (a7 == SYSCALL_OPENAT) {
    if (on_path) {
      cell_openat();

      advance_on_path();
    }
  } else if (or(a7 == SYSCALL_READ, a7 == SYSCALL_WRITE)) {
    if (is_transfer()) {
      if (transfer_words() > 0)
        return cell_transfer(on_path);

      result = transfer_result(*(token_heads + get_token_register(REG_A1) % NUMBER_OF_TAPES));
    } else
      result = SYSCALL_FAILURE;

    if (on_path) {
      if (reverse)
        set_token_register(REG_A0, get_token_register(REG_A0) - result);
      else
        set_token_register(REG_A0, get_token_register(REG_A0) + result);

      advance_on_path();
    }
  }

  return 0;
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

  acted_instructions = acted_instructions + 1;

  if (is == ECALL) {
    if (not(cell_system_call(on_path)))
      return;
  } else if (is == BEQ) {
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

void act_memory(uint64_t* word) {
  uint64_t datum;

  // a memory cell exchanges its word with the datum

  datum = token_data;

  token_data = *word;

  *word = datum;
}

void act_tape(uint64_t* word) {
  // a tape cell flips the bits of its word by the datum

  *word = bitwise_xor(*word, token_data);
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
  } else if (kind == CELL_MEMORY)
    act_memory(cell_words + index);
  else if (kind == CELL_TAPE)
    act_tape(cell_words + index);
  else if (kind == CELL_INSTRUCTION)
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

uint64_t instruction_property(uint64_t word) {
  uint64_t a7;

  // the token is about to enter, on its path, an instruction cell with
  // this instruction, which is not RISC-R, links into a nonzero register,
  // divides by zero, or is a system call

  decode_cell(word);

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
    a7 = get_token_register(REG_A7);

    if (a7 == SYSCALL_EXIT)
      return PROPERTY_EXIT;
    else if (a7 == SYSCALL_BRK) {
      if (get_token_register(REG_A0) != 0)
        return PROPERTY_IRREVERSIBLE_BRK;
      else if (token_break == 0)
        return PROPERTY_IRREVERSIBLE_BRK;
    } else if (a7 == SYSCALL_OPENAT) {
      if (token_open_files >= NUMBER_OF_TAPES)
        return PROPERTY_IRREVERSIBLE_OPENAT;
    } else if (or(a7 == SYSCALL_READ, a7 == SYSCALL_WRITE)) {
      if (get_token_register(REG_A3) >= LARGEST_TRANSFER)
        return PROPERTY_IRREVERSIBLE_TAPE;
    } else
      return PROPERTY_UNSUPPORTED_SYSCALL;
  }

  return PROPERTY_NONE;
}

uint64_t token_property() {
  uint64_t cell;

  // where a RISC-R program stops: the token is where a tagged cell says
  // it should not be, or about to enter an instruction cell on its path
  // that stops it; the rule is defined for these states as well, they
  // are not constraints

  cell = *(cell_kinds + cell_index(token_x, token_y));

  // a tagged cell knows its address: a token that wire led to the cell
  // of another address, since its own has no cell, is not where it should be

  if (get_cell_kind(cell) != CELL_INSTRUCTION) {
    if (is_cell_tagged(cell))
      if (or(get_cell_kind(cell) == CELL_MEMORY, get_cell_kind(cell) == CELL_TAPE))
        if (token_address != *(cell_tags + cell_index(token_x, token_y)))
          return PROPERTY_INVALID_ADDRESS;

    return PROPERTY_NONE;
  }

  if (token_heading != get_cell_orientation(cell))
    return PROPERTY_NONE;

  if (is_cell_tagged(cell))
    if (token_pc != *(cell_tags + cell_index(token_x, token_y)))
      return PROPERTY_INVALID_PC;

  return instruction_property(*(cell_words + cell_index(token_x, token_y)));
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
// #S break open-files leg word        program break, next descriptor, transfer
// #F descriptor head end input open   a file descriptor and its tape
// x = width, y = height, rule = RISC-R
// 2.E/00100a13M0000000000000007$     cells, row by row, ended by !
//
// A cell is . (blank), / or \ (mirror), R with mirror, p or a, and two
// decimal digits (router on that bit of the pc or the address), M with
// 16 hexadecimal digits (memory word), T with 16 hexadecimal digits
// (tape word), or E, N, W, S with mirror and 8 hexadecimal digits
// (instruction with orientation). A memory, tape, or instruction cell
// may be followed by @ and 16 hexadecimal digits, its tag: the address
// of the word or the instruction. A decimal number in front of a cell
// repeats it, $ ends a row, the rest of a row is blank. Numbers after
// #T, #R, #S, and #F are hexadecimal, except x, y, register, descriptor.

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

void load_system_state() {
  // #S break open-files leg word

  token_break      = scan_hexadecimal(0);
  token_open_files = scan_hexadecimal(0);

  token_leg  = scan_hexadecimal(0);
  token_word = scan_hexadecimal(0);

  if (token_leg > LEG_BUFFER_BACK)
    layout_error("no such leg");
}

void load_file_descriptor() {
  uint64_t fd;

  // #F descriptor head end input open

  fd = scan_decimal();

  if (fd >= NUMBER_OF_TAPES)
    layout_error("no such file descriptor");

  *(token_heads + fd)  = scan_hexadecimal(0);
  *(token_ends + fd)   = scan_hexadecimal(0);
  *(token_inputs + fd) = scan_hexadecimal(0);
  *(token_opens + fd)  = scan_hexadecimal(0);
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
  uint64_t tag;

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
    } else if (c == 'T') {
      cell = encode_cell(CELL_TAPE, 0, 0);

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

    tag = 0;

    if (layout_character() == '@') {
      if (get_cell_kind(cell) < CELL_MEMORY)
        layout_error("only memory, tape, and instruction cells have tags");

      next_layout_character();

      tag = scan_hexadecimal(16);

      cell = cell + 64;
    }

    while (n > 0) {
      if (x >= grid_width)
        layout_error("row is wider than the grid");
      else if (y >= grid_height)
        layout_error("more rows than the grid has");

      *(cell_kinds + cell_index(x, y)) = cell;
      *(cell_words + cell_index(x, y)) = word;
      *(cell_tags + cell_index(x, y))  = tag;

      x = x + 1;

      n = n - 1;
    }
  }
}

void load_layout(char* name) {
  layout_name = name;

  layout_text = read_file(name);

  layout_pos  = 0;
  layout_line = 1;

  // the token is as a RISC-R machine starts unless the layout says otherwise

  reset_token();

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
    } else if (layout_character() == 'S') {
      next_layout_character();

      load_system_state();
    } else if (layout_character() == 'F') {
      next_layout_character();

      load_file_descriptor();
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
  } else if (kind == CELL_TAPE) {
    put_character('T');

    print_hexadecimal_digits(word, 16);
  } else if (kind == CELL_INSTRUCTION) {
    print_heading(get_cell_orientation(cell));
    print_mirror(get_cell_mirror(cell));

    print_hexadecimal_digits(word, 8);
  } else
    put_character('.');

  if (kind >= CELL_MEMORY)
    if (kind <= CELL_TAPE)
      if (is_cell_tagged(cell)) {
        put_character('@');

        print_hexadecimal_digits(*(cell_tags + index), 16);
      }
}

uint64_t is_blank_cell(uint64_t index) {
  uint64_t kind;

  // kinds that do not exist are blank

  kind = get_cell_kind(*(cell_kinds + index));

  if (kind < CELL_MIRROR)
    return 1;
  else
    return kind > CELL_TAPE;
}

uint64_t are_cells_equal(uint64_t i, uint64_t j) {
  uint64_t kind;

  // do the cells print the same?

  if (is_blank_cell(i))
    return is_blank_cell(j);
  else if (*(cell_kinds + i) % 64 != *(cell_kinds + j) % 64)
    return 0;

  kind = get_cell_kind(*(cell_kinds + i));

  if (kind >= CELL_MEMORY) {
    if (is_cell_tagged(*(cell_kinds + i)) != is_cell_tagged(*(cell_kinds + j)))
      return 0;
    else if (is_cell_tagged(*(cell_kinds + i)))
      if (*(cell_tags + i) != *(cell_tags + j))
        return 0;
  }

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

  if (or(token_break != 0, or(token_open_files != 3, or(token_leg != LEG_NONE, token_word != 0)))) {
    dprintf(output_fd, "#S ");

    print_hexadecimal_digits(token_break, 16);
    put_character(' ');
    print_hexadecimal_digits(token_open_files, 16);
    put_character(' ');
    print_hexadecimal_digits(token_leg, 1);
    put_character(' ');
    print_hexadecimal_digits(token_word, 16);
    put_character(10);
  }

  i = 0;

  while (i < NUMBER_OF_TAPES) {
    if (or(*(token_heads + i) != 0, or(*(token_ends + i) != 0, or(*(token_inputs + i) != (i == 0), *(token_opens + i) != 0)))) {
      dprintf(output_fd, "#F %lu ", i);

      print_hexadecimal_digits(*(token_heads + i), 16);
      put_character(' ');
      print_hexadecimal_digits(*(token_ends + i), 16);
      put_character(' ');
      print_hexadecimal_digits(*(token_inputs + i), 16);
      put_character(' ');
      print_hexadecimal_digits(*(token_opens + i), 16);
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

uint64_t state_length(uint64_t state) {
  // number of words of a state of the machine

  if (state < STATE_REGISTERS)
    return 1;
  else if (state == STATE_REGISTERS)
    return NUMBEROFREGISTERS;
  else if (state < STATE_KINDS)
    return NUMBER_OF_TAPES;
  else
    return grid_size;
}

uint64_t get_state_word(uint64_t state, uint64_t i) {
  if (state == STATE_X)
    return token_x;
  else if (state == STATE_Y)
    return token_y;
  else if (state == STATE_HEADING)
    return token_heading;
  else if (state == STATE_PC)
    return token_pc;
  else if (state == STATE_ADDRESS)
    return token_address;
  else if (state == STATE_DATA)
    return token_data;
  else if (state == STATE_BREAK)
    return token_break;
  else if (state == STATE_OPEN_FILES)
    return token_open_files;
  else if (state == STATE_LEG)
    return token_leg;
  else if (state == STATE_WORD)
    return token_word;
  else if (state == STATE_REGISTERS)
    return *(token_registers + i);
  else if (state == STATE_HEADS)
    return *(token_heads + i);
  else if (state == STATE_ENDS)
    return *(token_ends + i);
  else if (state == STATE_INPUTS)
    return *(token_inputs + i);
  else if (state == STATE_OPENS)
    return *(token_opens + i);
  else if (state == STATE_KINDS)
    return *(cell_kinds + i);
  else if (state == STATE_WORDS)
    return *(cell_words + i);
  else
    return *(cell_tags + i);
}

void set_state_word(uint64_t state, uint64_t i, uint64_t value) {
  if (state == STATE_X)
    token_x = value;
  else if (state == STATE_Y)
    token_y = value;
  else if (state == STATE_HEADING)
    token_heading = value;
  else if (state == STATE_PC)
    token_pc = value;
  else if (state == STATE_ADDRESS)
    token_address = value;
  else if (state == STATE_DATA)
    token_data = value;
  else if (state == STATE_BREAK)
    token_break = value;
  else if (state == STATE_OPEN_FILES)
    token_open_files = value;
  else if (state == STATE_LEG)
    token_leg = value;
  else if (state == STATE_WORD)
    token_word = value;
  else if (state == STATE_REGISTERS)
    *(token_registers + i) = value;
  else if (state == STATE_HEADS)
    *(token_heads + i) = value;
  else if (state == STATE_ENDS)
    *(token_ends + i) = value;
  else if (state == STATE_INPUTS)
    *(token_inputs + i) = value;
  else if (state == STATE_OPENS)
    *(token_opens + i) = value;
  else if (state == STATE_KINDS)
    *(cell_kinds + i) = value;
  else if (state == STATE_WORDS)
    *(cell_words + i) = value;
  else
    *(cell_tags + i) = value;
}

char* state_name(uint64_t state) {
  // the names of the states in the model

  if (state == STATE_X)
    return "token-x";
  else if (state == STATE_Y)
    return "token-y";
  else if (state == STATE_HEADING)
    return "token-heading";
  else if (state == STATE_PC)
    return "token-pc";
  else if (state == STATE_ADDRESS)
    return "token-address";
  else if (state == STATE_DATA)
    return "token-data";
  else if (state == STATE_BREAK)
    return "token-break";
  else if (state == STATE_OPEN_FILES)
    return "token-open-files";
  else if (state == STATE_LEG)
    return "token-leg";
  else if (state == STATE_WORD)
    return "token-word";
  else if (state == STATE_REGISTERS)
    return "token-registers";
  else if (state == STATE_HEADS)
    return "token-tape-heads";
  else if (state == STATE_ENDS)
    return "token-tape-ends";
  else if (state == STATE_INPUTS)
    return "token-tape-inputs";
  else if (state == STATE_OPENS)
    return "token-tape-opens";
  else if (state == STATE_KINDS)
    return "cell-kinds";
  else if (state == STATE_WORDS)
    return "cell-words";
  else
    return "cell-tags";
}

uint64_t snapshot_size() {
  uint64_t state;
  uint64_t size;

  // all words of all states

  size = 0;

  state = 0;

  while (state < NUMBER_OF_STATES) {
    size = size + state_length(state);

    state = state + 1;
  }

  return size;
}

uint64_t* take_snapshot(uint64_t* snapshot) {
  uint64_t state;
  uint64_t i;
  uint64_t n;

  // the whole state, into the given snapshot or a new one

  if (snapshot == (uint64_t*) 0)
    snapshot = zmalloc(snapshot_size() * sizeof(uint64_t));

  n = 0;

  state = 0;

  while (state < NUMBER_OF_STATES) {
    i = 0;

    while (i < state_length(state)) {
      *(snapshot + n) = get_state_word(state, i);

      n = n + 1;
      i = i + 1;
    }

    state = state + 1;
  }

  return snapshot;
}

void restore_snapshot(uint64_t* snapshot) {
  uint64_t state;
  uint64_t i;
  uint64_t n;

  n = 0;

  state = 0;

  while (state < NUMBER_OF_STATES) {
    i = 0;

    while (i < state_length(state)) {
      set_state_word(state, i, *(snapshot + n));

      n = n + 1;
      i = i + 1;
    }

    state = state + 1;
  }
}

uint64_t is_snapshot(uint64_t* snapshot, uint64_t reporting) {
  uint64_t state;
  uint64_t i;
  uint64_t n;

  // is the state the state of the snapshot, bit for bit?

  n = 0;

  state = 0;

  while (state < NUMBER_OF_STATES) {
    i = 0;

    while (i < state_length(state)) {
      if (get_state_word(state, i) != *(snapshot + n)) {
        if (reporting)
          printf("%s: %s[%lu] is 0x%lX but was 0x%lX\n", selfie_name,
            state_name(state), i, get_state_word(state, i), *(snapshot + n));

        return 0;
      }

      n = n + 1;
      i = i + 1;
    }

    state = state + 1;
  }

  return 1;
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
  else if (property == PROPERTY_IRREVERSIBLE_BRK)
    printf("irreversible-brk");
  else if (property == PROPERTY_IRREVERSIBLE_TAPE)
    printf("irreversible-tape");
  else if (property == PROPERTY_IRREVERSIBLE_OPENAT)
    printf("irreversible-openat");
  else if (property == PROPERTY_INVALID_ADDRESS)
    printf("invalid-address 0x%lX", token_address);
  else if (property == PROPERTY_INVALID_PC)
    printf("invalid-pc");
}

void print_stop(uint64_t property) {
  // where the token is, and the property that stopped it, if any

  printf("%s: ", selfie_name);

  print_token();

  if (property != PROPERTY_NONE) {
    printf(": ");

    print_property(property);
  }

  printf(" after %lu ticks and %lu instructions\n", executed_ticks, executed_instructions);
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

  print_stop(property);

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

  SID_HEADING = new_bitvec(2, "heading: east 0, north 1, west 2, south 3; file descriptor; leg of a transfer");

  SID_X = new_sort(xbits);
  SID_Y = new_sort(ybits);

  SID_INDEX = new_sort(xbits + ybits);

  SID_CELL = new_bitvec(8, "cell: 3-bit kind, 2-bit orientation, 1-bit mirror, 1-bit tagged");
  SID_WORD = new_bitvec(64, "64-bit word");

  SID_REGISTER = new_bitvec(5, "5-bit register address");

  SID_REGISTERS = new_array(SID_REGISTER, SID_WORD, "register file");

  if (NUMBER_OF_TAPES == 4)
    SID_FD = SID_HEADING;
  else
    SID_FD = new_bitvec(log_two(NUMBER_OF_TAPES), "file descriptor");

  SID_TAPES = new_array(SID_FD, SID_WORD, "a word per file descriptor");

  SID_KINDS = new_array(SID_INDEX, SID_CELL, "cells by row and column");
  SID_WORDS = new_array(SID_INDEX, SID_WORD, "cell words by row and column");

  NID_FALSE = new_constant(OP_CONSTD, SID_BOOLEAN, 0, "false");
  NID_TRUE  = new_constant(OP_CONSTD, SID_BOOLEAN, 1, "true");
}

void model_states() {
  uint64_t state;
  uint64_t* sid;
  char* comment;

  state_nids = zmalloc(NUMBER_OF_STATES * sizeof(uint64_t*));

  state = 0;

  while (state < NUMBER_OF_STATES) {
    sid = SID_WORD;

    if (state == STATE_X) {
      sid = SID_X;

      comment = "column of the token";
    } else if (state == STATE_Y) {
      sid = SID_Y;

      comment = "row of the token";
    } else if (state == STATE_HEADING) {
      sid = SID_HEADING;

      comment = "heading of the token";
    } else if (state == STATE_PC)
      comment = "program counter";
    else if (state == STATE_ADDRESS)
      comment = "address in transit";
    else if (state == STATE_DATA)
      comment = "datum in transit";
    else if (state == STATE_BREAK)
      comment = "program break";
    else if (state == STATE_OPEN_FILES)
      comment = "next file descriptor";
    else if (state == STATE_LEG) {
      sid = SID_HEADING;

      comment = "leg of a transfer: none 0, to the buffer 1, to the tape 2, to the buffer again 3";
    } else if (state == STATE_WORD)
      comment = "number of the word in transfer";
    else if (state == STATE_REGISTERS) {
      sid = SID_REGISTERS;

      comment = "register file";
    } else if (state == STATE_HEADS) {
      sid = SID_TAPES;

      comment = "head of each tape in words";
    } else if (state == STATE_ENDS) {
      sid = SID_TAPES;

      comment = "end of each input file in bytes, -1 if unknown";
    } else if (state == STATE_INPUTS) {
      sid = SID_TAPES;

      comment = "1 for an input tape, 0 for an output tape";
    } else if (state == STATE_OPENS) {
      sid = SID_TAPES;

      comment = "1 if the host can open the file";
    } else if (state == STATE_KINDS) {
      sid = SID_KINDS;

      comment = "kind, orientation, mirror of each cell, and whether it is tagged";
    } else if (state == STATE_WORDS) {
      sid = SID_WORDS;

      comment = "instruction, memory or tape word, or router bit of each cell";
    } else {
      sid = SID_WORDS;

      comment = "address of each tagged instruction, memory, or tape cell";
    }

    *(state_nids + state) = (uint64_t) new_input(OP_STATE, sid, state_name(state), comment);

    state = state + 1;
  }

  forward_nids = zmalloc(NUMBER_OF_STATES * sizeof(uint64_t*));
  inverse_nids = zmalloc(NUMBER_OF_STATES * sizeof(uint64_t*));

  property_nids = zmalloc((NUMBER_OF_PROPERTIES + 1) * sizeof(uint64_t*));
}

void model_transfer(uint64_t reading) {
  uint64_t* is_active_nid;
  uint64_t* tape_nid;
  uint64_t* next_nid;
  uint64_t* result_nid;
  uint64_t* value_nid;

  uint64_t* direct_effect;
  uint64_t* failure_effect;
  uint64_t* start_effect;
  uint64_t* last_effect;
  uint64_t* buffer_effect;
  uint64_t* tape_effect;
  uint64_t* back_effect;

  // read, if reading, or write, as part of the rule or the inverse rule:
  // what a token on the path and on the side of an ecall cell does

  if (reading) {
    is_active_nid = new_and(fits_nid, new_and(is_open_nid, is_input_nid));

    tape_nid = new_constant(OP_CONSTH, SID_WORD, INPUT_TAPES, "input tapes");
  } else {
    is_active_nid = new_and(fits_nid, new_and(is_open_nid, new_not(is_input_nid)));

    tape_nid = new_constant(OP_CONSTH, SID_WORD, OUTPUT_TAPES, "output tapes");
  }

  // the tape word in transfer: at the head plus the number of the word

  tape_nid = new_add(
    new_add(tape_nid, new_binary(OP_SLL, SID_WORD, a1_nid, new_number(SID_WORD, 32), "descriptor times 4GB")),
    new_binary(OP_SLL, SID_WORD, new_add(head_nid, number_nid), new_number(SID_WORD, 3), "position in bytes"));

  // the head when the transfer began, and the result from there: write
  // returns the size; read the bytes before the end of the file from
  // the head on, at most the size

  if (reverse)
    next_nid = new_sub(head_nid, count_nid);
  else
    next_nid = head_nid;

  if (reading) {
    result_nid = new_binary(OP_READ, SID_WORD, (uint64_t*) *(state_nids + STATE_ENDS), fd_nid, "end of file");

    value_nid = new_binary(OP_SLL, SID_WORD, next_nid, new_number(SID_WORD, 3), "head in bytes");

    result_nid = new_ite(new_is_field(result_nid, -1),
      a3_nid,
      new_ite(new_binary_boolean(OP_UGTE, value_nid, result_nid, "head at or beyond end of file"),
        new_number(SID_WORD, 0),
        new_ite(new_binary_boolean(OP_ULT, new_sub(result_nid, value_nid), a3_nid, "fewer bytes than requested"),
          new_sub(result_nid, value_nid),
          a3_nid)));
  } else
    result_nid = a3_nid;

  if (reverse)
    result_nid = new_sub(a0_nid, result_nid);
  else
    result_nid = new_add(a0_nid, result_nid);

  // no transfer: the result of a transfer of no word, with the head
  // where it is, or -1, is added into a0 on the path

  direct_effect = new_effect(advance);

  *(direct_effect + STATE_REGISTERS) = (uint64_t)
    new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, a0_index_nid, result_nid, "result of empty transfer");

  failure_effect = new_effect(advance);

  if (reverse)
    *(failure_effect + STATE_REGISTERS) = (uint64_t)
      new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, a0_index_nid, new_sub(a0_nid, failure_nid), "failure");
  else
    *(failure_effect + STATE_REGISTERS) = (uint64_t)
      new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, a0_index_nid, new_add(a0_nid, failure_nid), "failure");

  // a transfer: the token leaves the path for the first buffer word, and
  // after the last leg the head advances, the result is added into a0,
  // and the token joins the path; backward the other way round

  start_effect = new_effect(same);
  last_effect  = new_effect(same);

  *(start_effect + STATE_HEADING) = (uint64_t) mirrored_nid;
  *(last_effect + STATE_HEADING)  = (uint64_t) mirrored_nid;

  value_nid = new_add(a2_nid,
    new_binary(OP_SLL, SID_WORD, last_word_nid, new_number(SID_WORD, 3), "last word in bytes"));

  if (reverse) {
    // on the path: undo the return; on the side with the first leg
    // of the first word: undo the departure

    *(start_effect + STATE_PC)   = *(advance + STATE_PC);
    *(start_effect + STATE_LEG)  = (uint64_t) new_number(SID_HEADING, LEG_BUFFER_BACK);
    *(start_effect + STATE_WORD) = (uint64_t) last_word_nid;

    *(start_effect + STATE_HEADS) = (uint64_t)
      new_ternary(OP_WRITE, SID_TAPES, heads_nid, fd_nid, next_nid, "head moved back");
    *(start_effect + STATE_REGISTERS) = (uint64_t)
      new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, a0_index_nid, result_nid, "result subtracted");

    *(start_effect + STATE_ADDRESS) = (uint64_t) new_add(address_nid, value_nid);

    *(last_effect + STATE_LEG)     = (uint64_t) new_number(SID_HEADING, LEG_NONE);
    *(last_effect + STATE_ADDRESS) = (uint64_t) new_sub(address_nid, buffer_nid);
  } else {
    *(start_effect + STATE_LEG)     = (uint64_t) new_number(SID_HEADING, LEG_BUFFER);
    *(start_effect + STATE_ADDRESS) = (uint64_t) new_add(address_nid, buffer_nid);

    *(last_effect + STATE_PC)   = *(advance + STATE_PC);
    *(last_effect + STATE_LEG)  = (uint64_t) new_number(SID_HEADING, LEG_NONE);
    *(last_effect + STATE_WORD) = (uint64_t) new_number(SID_WORD, 0);

    *(last_effect + STATE_HEADS) = (uint64_t)
      new_ternary(OP_WRITE, SID_TAPES, heads_nid, fd_nid, new_add(head_nid, count_nid), "head advanced");
    *(last_effect + STATE_REGISTERS) = (uint64_t)
      new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, a0_index_nid, result_nid, "result added");

    *(last_effect + STATE_ADDRESS) = (uint64_t) new_sub(address_nid, value_nid);
  }

  // between two legs the token crosses the cell: the address of the leg
  // it returns from is uncomputed, that of the next leg computed

  buffer_effect = new_effect(same);
  tape_effect   = new_effect(same);
  back_effect   = new_effect(same);

  if (reverse) {
    // back from the buffer, first leg: on to the last leg of the word before

    value_nid = new_sub(number_nid, new_number(SID_WORD, 1));

    *(buffer_effect + STATE_LEG)     = (uint64_t) new_number(SID_HEADING, LEG_BUFFER_BACK);
    *(buffer_effect + STATE_WORD)    = (uint64_t) value_nid;
    *(buffer_effect + STATE_ADDRESS) = (uint64_t) new_add(new_sub(address_nid, buffer_nid),
      new_add(a2_nid, new_binary(OP_SLL, SID_WORD, value_nid, new_number(SID_WORD, 3), "word before in bytes")));

    *(tape_effect + STATE_LEG)     = (uint64_t) new_number(SID_HEADING, LEG_BUFFER);
    *(tape_effect + STATE_ADDRESS) = (uint64_t) new_add(new_sub(address_nid, tape_nid), buffer_nid);

    *(back_effect + STATE_LEG)     = (uint64_t) new_number(SID_HEADING, LEG_TAPE);
    *(back_effect + STATE_ADDRESS) = (uint64_t) new_add(new_sub(address_nid, buffer_nid), tape_nid);
  } else {
    *(buffer_effect + STATE_LEG)     = (uint64_t) new_number(SID_HEADING, LEG_TAPE);
    *(buffer_effect + STATE_ADDRESS) = (uint64_t) new_add(new_sub(address_nid, buffer_nid), tape_nid);

    *(tape_effect + STATE_LEG)     = (uint64_t) new_number(SID_HEADING, LEG_BUFFER_BACK);
    *(tape_effect + STATE_ADDRESS) = (uint64_t) new_add(new_sub(address_nid, tape_nid), buffer_nid);

    // back from the buffer, last leg: on to the first leg of the next word

    value_nid = new_add(number_nid, new_number(SID_WORD, 1));

    *(back_effect + STATE_LEG)     = (uint64_t) new_number(SID_HEADING, LEG_BUFFER);
    *(back_effect + STATE_WORD)    = (uint64_t) value_nid;
    *(back_effect + STATE_ADDRESS) = (uint64_t) new_add(new_sub(address_nid, buffer_nid),
      new_add(a2_nid, new_binary(OP_SLL, SID_WORD, value_nid, new_number(SID_WORD, 3), "next word in bytes")));
  }

  if (reverse)
    // the first leg of the first word ends the transfer backward
    buffer_effect = new_choice(new_is_field(number_nid, 0), last_effect, buffer_effect);
  else
    // the last leg of the last word ends the transfer forward
    back_effect = new_choice(new_eq(number_nid, last_word_nid), last_effect, back_effect);

  if (reading)
    value_nid = new_is_field(a7_nid, SYSCALL_READ);
  else
    value_nid = new_is_field(a7_nid, SYSCALL_WRITE);

  system_on_path = new_choice(value_nid,
    new_choice(is_active_nid,
      new_choice(new_is_field(count_nid, 0),
        direct_effect,
        new_choice(new_and(new_is_field(leg_nid, LEG_NONE), new_is_field(number_nid, 0)), start_effect, same)),
      failure_effect),
    system_on_path);

  system_on_side = new_choice(value_nid,
    new_choice(is_active_nid,
      new_choice(new_is_field(count_nid, 0),
        same,
        new_choice(new_binary_boolean(OP_ULT, number_nid, count_nid, "word in transfer"),
          new_choice(new_is_field(leg_nid, LEG_BUFFER), buffer_effect,
            new_choice(new_is_field(leg_nid, LEG_TAPE), tape_effect,
              new_choice(new_is_field(leg_nid, LEG_BUFFER_BACK), back_effect, same))),
          same)),
      same),
    system_on_side);
}

void model_rule() {
  uint64_t* next_nids;

  uint64_t* x_nid;
  uint64_t* y_nid;
  uint64_t* heading_nid;
  uint64_t* pc_nid;
  uint64_t* data_nid;
  uint64_t* words_nid;

  uint64_t* index_nid;
  uint64_t* cell_nid;
  uint64_t* word_nid;
  uint64_t* kind_nid;
  uint64_t* orientation_nid;
  uint64_t* mirror_nid;
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

  uint64_t* break_nid;
  uint64_t* open_files_nid;
  uint64_t* inputs_nid;

  uint64_t* result_nid;
  uint64_t* next_nid;

  uint64_t* brk_effect;
  uint64_t* openat_effect;
  uint64_t* tape_effect;

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

  same = new_effect(state_nids);

  *(same + STATE_X) = (uint64_t) x_nid;
  *(same + STATE_Y) = (uint64_t) y_nid;

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

  // system calls: the number is in a7, the arguments are in a1 to a3,
  // the result is added into a0, see riscr.md

  a0_index_nid = new_number(SID_REGISTER, REG_A0);

  a0_nid = new_binary(OP_READ, SID_WORD, registers_nid, a0_index_nid, "a0 value");
  a1_nid = new_binary(OP_READ, SID_WORD, registers_nid, new_number(SID_REGISTER, REG_A1), "a1 value");
  a2_nid = new_binary(OP_READ, SID_WORD, registers_nid, new_number(SID_REGISTER, REG_A2), "a2 value");
  a3_nid = new_binary(OP_READ, SID_WORD, registers_nid, new_number(SID_REGISTER, REG_A3), "a3 value");
  a7_nid = new_binary(OP_READ, SID_WORD, registers_nid, new_number(SID_REGISTER, REG_A7), "a7 value");

  break_nid      = (uint64_t*) *(state_nids + STATE_BREAK);
  open_files_nid = (uint64_t*) *(state_nids + STATE_OPEN_FILES);
  leg_nid        = (uint64_t*) *(state_nids + STATE_LEG);
  number_nid     = (uint64_t*) *(state_nids + STATE_WORD);
  heads_nid      = (uint64_t*) *(state_nids + STATE_HEADS);
  inputs_nid     = (uint64_t*) *(state_nids + STATE_INPUTS);

  failure_nid = new_constant(OP_CONSTD, SID_WORD, SYSCALL_FAILURE, "-1 as 32-bit system call result");

  // brk exchanges the states in which a0 is zero and a1 a word-aligned
  // address above the program break, which is not zero, with the states
  // in which a0 is not zero and below the program break and a1 is the
  // word-aligned program break: a1 becomes the program break and a0 the
  // previous one, or the other way round, in both directions

  brk_effect = new_effect(advance);

  *(brk_effect + STATE_BREAK)     = (uint64_t) a1_nid;
  *(brk_effect + STATE_REGISTERS) = (uint64_t)
    new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, a0_index_nid, break_nid, "brk");

  effect = new_effect(advance);

  *(effect + STATE_BREAK)     = (uint64_t) a0_nid;
  *(effect + STATE_REGISTERS) = (uint64_t)
    new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, a0_index_nid, new_number(SID_WORD, 0), "brk undone");

  brk_effect = new_choice(new_is_field(new_bits(a1_nid, 2, 0), 0),
    new_choice(new_is_field(a0_nid, 0),
      new_choice(new_is_field(break_nid, 0),
        advance,
        new_choice(new_binary_boolean(OP_ULT, break_nid, a1_nid, "a1 above program break"), brk_effect, advance)),
      new_choice(new_eq(a1_nid, break_nid),
        new_choice(new_binary_boolean(OP_ULT, a0_nid, break_nid, "a0 below program break"), effect, advance),
        advance)),
    advance);

  // openat allocates the next file descriptor, flips the kind of its tape
  // if the flags in a2 open an input tape, and adds the descriptor into
  // a0, or -1 if the host cannot open the file; backward it releases the
  // descriptor, flips, and subtracts

  if (reverse)
    next_nid = new_sub(open_files_nid, new_number(SID_WORD, 1));
  else
    next_nid = open_files_nid;

  fd_nid = new_slice(SID_FD, next_nid, log_two(NUMBER_OF_TAPES) - 1, 0, "next file descriptor");

  result_nid = new_ite(
    new_is_field(new_binary(OP_READ, SID_WORD, (uint64_t*) *(state_nids + STATE_OPENS), fd_nid, "host opens next file"), 0),
    failure_nid,
    next_nid);

  openat_effect = new_effect(advance);

  *(openat_effect + STATE_INPUTS) = (uint64_t)
    new_ternary(OP_WRITE, SID_TAPES, inputs_nid, fd_nid,
      new_binary(OP_XOR, SID_WORD,
        new_binary(OP_READ, SID_WORD, inputs_nid, fd_nid, "kind of next tape"),
        new_ext(OP_UEXT, SID_WORD,
          new_or(new_is_field(a2_nid, O_RDONLY), new_is_field(a2_nid, 0)), 63, "flags open an input tape"),
        NOCOMMENT),
      "openat");

  if (reverse) {
    *(openat_effect + STATE_OPEN_FILES) = (uint64_t) next_nid;

    *(openat_effect + STATE_REGISTERS) = (uint64_t)
      new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, a0_index_nid, new_sub(a0_nid, result_nid), "openat");
  } else {
    *(openat_effect + STATE_OPEN_FILES) = (uint64_t) new_add(open_files_nid, new_number(SID_WORD, 1));

    *(openat_effect + STATE_REGISTERS) = (uint64_t)
      new_ternary(OP_WRITE, SID_REGISTERS, registers_nid, a0_index_nid, new_add(a0_nid, result_nid), "openat");
  }

  // read and write: on an open tape of the right kind and of less than 4GB;
  // the standard files are open, others if the host opened them

  fd_nid = new_slice(SID_FD, a1_nid, log_two(NUMBER_OF_TAPES) - 1, 0, "file descriptor");

  head_nid = new_binary(OP_READ, SID_WORD, heads_nid, fd_nid, "head of tape");

  is_input_nid = new_not(new_is_field(new_binary(OP_READ, SID_WORD, inputs_nid, fd_nid, "kind of tape"), 0));

  is_open_nid = new_and(new_binary_boolean(OP_ULT, a1_nid, open_files_nid, "descriptor allocated"),
    new_or(new_binary_boolean(OP_ULT, a1_nid, new_number(SID_WORD, 3), "standard file"),
      new_not(new_is_field(
        new_binary(OP_READ, SID_WORD, (uint64_t*) *(state_nids + STATE_OPENS), fd_nid, "host opened file"), 0))));

  fits_nid = new_binary_boolean(OP_ULT, a3_nid, new_number(SID_WORD, LARGEST_TRANSFER), "less than 4GB");

  count_nid = new_binary(OP_SRL, SID_WORD,
    new_add(a3_nid, new_number(SID_WORD, 7)), new_number(SID_WORD, 3), "a3 bytes rounded up to words");

  last_word_nid = new_sub(count_nid, new_number(SID_WORD, 1));

  // the buffer word in transfer, and the buffer word of an arriving token:
  // the same word, named twice to tell the legs apart below

  buffer_nid = new_add(a2_nid,
    new_binary(OP_SLL, SID_WORD, number_nid, new_number(SID_WORD, 3), "word in bytes"));

  system_on_path = same;
  system_on_side = same;

  model_transfer(0);
  model_transfer(1);

  // exit and unknown system calls have no effect, they are properties

  system_on_path = new_choice(new_is_field(a7_nid, SYSCALL_BRK), brk_effect,
    new_choice(new_is_field(a7_nid, SYSCALL_OPENAT), openat_effect, system_on_path));

  // a token on the path of an instruction cell: by instruction, and
  // within an instruction by the rules of RISC-R; an instruction that
  // is not RISC-R has no effect

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
    new_choice(new_is_field(opcode_nid, OP_SYSTEM),
      new_choice(new_is_field(funct3_nid, F3_ECALL), system_on_path, same),
      same))))))));

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
    new_choice(new_is_field(opcode_nid, OP_SYSTEM),
      new_choice(new_is_field(funct3_nid, F3_ECALL), system_on_side, same),
      same)))));

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

  // tape cell: the bits of its word are flipped by the datum

  tape_effect = new_effect(same);

  *(tape_effect + STATE_WORDS) = (uint64_t)
    new_ternary(OP_WRITE, SID_WORDS, words_nid, index_nid,
      new_binary(OP_XOR, SID_WORD, word_nid, data_nid, NOCOMMENT), "tape word flipped");

  // the cell by kind, all other kinds are blank

  effect = new_choice(new_is_field(kind_nid, CELL_INSTRUCTION), effect,
    new_choice(new_is_field(kind_nid, CELL_MEMORY), on_path,
      new_choice(new_is_field(kind_nid, CELL_TAPE), tape_effect,
        new_choice(new_is_field(kind_nid, CELL_MIRROR), on_side,
          new_choice(new_is_field(kind_nid, CELL_ROUTER), advance, same)))));

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

  // a tagged cell knows its address: the token is at a memory or tape
  // cell that is not the cell of its address, or about to enter an
  // instruction cell on its path that is not the cell of its pc

  value_nid = new_binary(OP_READ, SID_WORD, (uint64_t*) *(state_nids + STATE_TAGS), index_nid, "cell tag");

  is_instruction_nid = new_and(new_is_field(kind_nid, CELL_INSTRUCTION), new_eq(heading_nid, orientation_nid));

  *(property_nids + PROPERTY_INVALID_ADDRESS) = (uint64_t)
    new_and(new_slice(SID_BOOLEAN, cell_nid, 6, 6, "cell tagged"),
      new_and(new_or(new_is_field(kind_nid, CELL_MEMORY), new_is_field(kind_nid, CELL_TAPE)),
        new_not(new_eq(address_nid, value_nid))));

  value_nid = new_and(new_slice(SID_BOOLEAN, cell_nid, 6, 6, "cell tagged"), new_not(new_eq(pc_nid, value_nid)));

  *(property_nids + PROPERTY_INVALID_PC) = (uint64_t) new_and(is_instruction_nid, value_nid);

  // the token is about to enter an instruction cell on its path, the cell of its pc

  is_instruction_nid = new_and(is_instruction_nid, new_not(value_nid));

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

  is_instruction_nid = new_and(is_instruction_nid, new_is_field(opcode_nid, OP_SYSTEM));

  *(property_nids + PROPERTY_EXIT) = (uint64_t)
    new_and(is_instruction_nid, new_is_field(a7_nid, SYSCALL_EXIT));

  *(property_nids + PROPERTY_IRREVERSIBLE_BRK) = (uint64_t)
    new_and(is_instruction_nid,
      new_and(new_is_field(a7_nid, SYSCALL_BRK),
        new_or(new_not(new_is_field(a0_nid, 0)), new_is_field(break_nid, 0))));

  *(property_nids + PROPERTY_IRREVERSIBLE_OPENAT) = (uint64_t)
    new_and(is_instruction_nid,
      new_and(new_is_field(a7_nid, SYSCALL_OPENAT),
        new_binary_boolean(OP_UGTE, open_files_nid, new_number(SID_WORD, NUMBER_OF_TAPES), "all descriptors allocated")));

  value_nid = new_or(new_is_field(a7_nid, SYSCALL_READ), new_is_field(a7_nid, SYSCALL_WRITE));

  *(property_nids + PROPERTY_IRREVERSIBLE_TAPE) = (uint64_t)
    new_and(is_instruction_nid, new_and(value_nid, new_not(fits_nid)));

  *(property_nids + PROPERTY_UNSUPPORTED_SYSCALL) = (uint64_t)
    new_and(is_instruction_nid,
      new_not(new_or(value_nid,
        new_or(new_is_field(a7_nid, SYSCALL_EXIT),
          new_or(new_is_field(a7_nid, SYSCALL_BRK), new_is_field(a7_nid, SYSCALL_OPENAT))))));
}

char* property_name(uint64_t property) {
  if (property == PROPERTY_ILLEGAL_INSTRUCTION)
    return "illegal-instruction";
  else if (property == PROPERTY_IRREVERSIBLE_LINK)
    return "irreversible-link";
  else if (property == PROPERTY_DIVISION_BY_ZERO)
    return "division-by-zero";
  else if (property == PROPERTY_EXIT)
    return "exit";
  else if (property == PROPERTY_UNSUPPORTED_SYSCALL)
    return "unsupported-syscall";
  else if (property == PROPERTY_IRREVERSIBLE_BRK)
    return "irreversible-brk";
  else if (property == PROPERTY_IRREVERSIBLE_TAPE)
    return "irreversible-tape";
  else if (property == PROPERTY_IRREVERSIBLE_OPENAT)
    return "irreversible-openat";
  else if (property == PROPERTY_INVALID_ADDRESS)
    return "invalid-address";
  else
    return "invalid-pc";
}

char* property_comment(uint64_t property) {
  if (property == PROPERTY_ILLEGAL_INSTRUCTION)
    return "token enters an instruction cell whose instruction is not RISC-R";
  else if (property == PROPERTY_IRREVERSIBLE_LINK)
    return "jal with nonzero link register";
  else if (property == PROPERTY_DIVISION_BY_ZERO)
    return "divu or remu by zero";
  else if (property == PROPERTY_EXIT)
    return "exit system call";
  else if (property == PROPERTY_UNSUPPORTED_SYSCALL)
    return "system call other than exit, read, write, openat, brk";
  else if (property == PROPERTY_IRREVERSIBLE_BRK)
    return "brk with nonzero a0 or zero program break";
  else if (property == PROPERTY_IRREVERSIBLE_TAPE)
    return "read or write of 4GB or more";
  else if (property == PROPERTY_IRREVERSIBLE_OPENAT)
    return "openat with all file descriptors allocated";
  else if (property == PROPERTY_INVALID_ADDRESS)
    return "token at a memory or tape cell that is not the cell of its address";
  else
    return "token on the path of an instruction cell that is not the cell of its pc";
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

    i = 1;

    while (i <= NUMBER_OF_PROPERTIES) {
      print_line(new_property(OP_BAD, (uint64_t*) *(property_nids + i), property_name(i), property_comment(i)));

      print_break();

      i = i + 1;
    }
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
  else if (r < 8)
    return left_shift(F3_ECALL, 12) + OP_SYSTEM;

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

  // tags: the tagged bit of a cell is random already

  i = 0;

  while (i < grid_size) {
    if (random_below(2) == 0)
      *(cell_kinds + i) = *(cell_kinds + i) % 64 + random_below(4) * 64;

    *(cell_tags + i) = random_value();

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

  // the state of the system calls: often what a system call is about

  token_break = random_below(64) * WORDSIZE;

  r = random_below(8);

  if (r == 0)
    token_break = 0;
  else if (r == 1)
    token_break = random_value();

  token_open_files = random_below(6);

  if (random_below(8) == 0)
    token_open_files = random_value();

  token_leg  = LEG_NONE;
  token_word = 0;

  if (random_below(2) == 0) {
    token_leg  = random_below(4);
    token_word = random_below(4);
  }

  // half of the time the cell under the token is the cell of its pc or address

  r = random_below(4);

  if (r == 0)
    *(cell_tags + cell_index(token_x, token_y)) = token_pc;
  else if (r == 1)
    *(cell_tags + cell_index(token_x, token_y)) = token_address;

  i = 0;

  while (i < NUMBER_OF_TAPES) {
    *(token_heads + i)  = random_below(4);
    *(token_ends + i)   = random_below(24);
    *(token_inputs + i) = random_below(2);
    *(token_opens + i)  = random_below(2);

    r = random_below(8);

    if (r == 0)
      *(token_heads + i) = random_value();
    else if (r == 1)
      *(token_ends + i) = (uint64_t) -1;
    else if (r == 2)
      *(token_ends + i) = random_value();
    else if (r == 3)
      *(token_inputs + i) = random_below(4);

    i = i + 1;
  }

  r = random_below(8);

  if (r < 6) {
    if (r == 0)
      *(token_registers + REG_A7) = SYSCALL_EXIT;
    else if (r == 1)
      *(token_registers + REG_A7) = SYSCALL_BRK;
    else if (r == 2)
      *(token_registers + REG_A7) = SYSCALL_OPENAT;
    else if (r < 5)
      *(token_registers + REG_A7) = SYSCALL_READ;
    else
      *(token_registers + REG_A7) = SYSCALL_WRITE;

    // a0 often zero; a1 a file descriptor, or an address at or near the
    // program break; a2 flags or a buffer; a3 a small size

    if (random_below(2) == 0)
      *(token_registers + REG_A0) = 0;
    else if (random_below(2) == 0)
      *(token_registers + REG_A0) = random_below(64) * WORDSIZE;

    r = random_below(8);

    if (r < 4)
      *(token_registers + REG_A1) = random_below(5);
    else if (r < 6)
      *(token_registers + REG_A1) = token_break;
    else if (r < 7)
      *(token_registers + REG_A1) = token_break + random_below(4) * WORDSIZE;

    r = random_below(4);

    if (r == 0)
      *(token_registers + REG_A2) = 0;
    else if (r == 1)
      *(token_registers + REG_A2) = O_RDONLY;

    if (random_below(8) > 0)
      *(token_registers + REG_A3) = random_below(40);

    // half of the time a state that brk exchanges, or a transfer on its way

    r = *(token_registers + REG_A7);

    if (random_below(2) == 0) {
      if (r == SYSCALL_BRK) {
        token_break = (1 + random_below(64)) * WORDSIZE;

        if (random_below(2) == 0) {
          *(token_registers + REG_A0) = 0;
          *(token_registers + REG_A1) = token_break + (1 + random_below(4)) * WORDSIZE;
        } else {
          *(token_registers + REG_A0) = random_below(token_break);
          *(token_registers + REG_A1) = token_break;
        }
      } else if (or(r == SYSCALL_READ, r == SYSCALL_WRITE)) {
        i = random_below(NUMBER_OF_TAPES);

        *(token_registers + REG_A1) = i;
        *(token_registers + REG_A3) = 1 + random_below(24);

        token_open_files = i + 1 + random_below(2);

        *(token_opens + i)  = 1;
        *(token_inputs + i) = r == SYSCALL_READ;

        if (random_below(4) > 0) {
          token_leg  = 1 + random_below(3);
          token_word = random_below(right_shift(*(token_registers + REG_A3) + 7, 3));
        } else {
          token_leg  = LEG_NONE;
          token_word = 0;
        }
      }
    }
  }
}

void set_model_state() {
  uint64_t state;
  uint64_t* line;
  uint64_t i;

  // the state of the simulator becomes the state of the model

  state = 0;

  while (state < NUMBER_OF_STATES) {
    line = (uint64_t*) *(state_nids + state);

    if (is_bitvector(get_sid(line)))
      set_state(line, get_state_word(state, 0));
    else {
      i = 0;

      while (i < state_length(state)) {
        write_array_raw(line, i, get_state_word(state, i));

        i = i + 1;
      }
    }

    state = state + 1;
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
  uint64_t state;
  uint64_t* line;
  uint64_t* values;

  // one step of the rule or the inverse rule: all next values are
  // evaluated before any is applied, array writes are logged while
  // evaluating and applied afterwards

  if (next_values == (uint64_t*) 0)
    next_values = zmalloc(NUMBER_OF_STATES * sizeof(uint64_t));

  values = next_values;

  state = 0;

  while (state < NUMBER_OF_STATES) {
    line = (uint64_t*) *(state_nids + state);

    if (*(next_nids + state) != (uint64_t) line)
      *(values + state) = eval_line((uint64_t*) *(next_nids + state));
    else
      // a state that the rule never changes
      *(values + state) = get_state(line);

    state = state + 1;
  }

  apply_writes();

  state = 0;

  while (state < NUMBER_OF_STATES) {
    line = (uint64_t*) *(state_nids + state);

    if (is_bitvector(get_sid(line)))
      set_state(line, *(values + state));

    state = state + 1;
  }

  advance_model();
}

uint64_t is_model_state(char* direction) {
  uint64_t state;
  uint64_t* line;
  uint64_t i;
  uint64_t value;

  // is the state of the model the state of the simulator?

  state = 0;

  while (state < NUMBER_OF_STATES) {
    line = (uint64_t*) *(state_nids + state);

    i = 0;

    while (i < state_length(state)) {
      if (is_bitvector(get_sid(line)))
        value = get_state(line);
      else
        value = read_array_raw(line, i);

      if (value != get_state_word(state, i)) {
        printf("%s: %s: %s[%lu] is 0x%lX in the model and 0x%lX in the simulator\n", selfie_name,
          direction, state_name(state), i, value, get_state_word(state, i));

        return 0;
      }

      i = i + 1;
    }

    state = state + 1;
  }

  return 1;
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
  printf("%s: in 4 ticks per state, %lu times a RISC-R instruction cell had a token on its path or side,\n", selfie_name, acted_instructions);
  printf("%s: %lu times brk changed the program break, %lu times openat ran, %lu times a read or write moved a transfer on\n", selfie_name,
    acted_breaks, acted_opens, acted_legs);

  return failed == 0;
}

// -----------------------------------------------------------------
// --------------------------- COMPILER ----------------------------
// -----------------------------------------------------------------

// The layout compiler turns a RISC-R binary into a layout that runs it.
// The instructions are a row of cells, the path, in the order of their
// addresses, every other column. All wire is combs. A comb is a binary
// tree over the addresses of its leaves, one row per level: a node is
// a router on the highest bit in which the addresses below it differ,
// in the column of its first leaf, and a mirror in the column of the
// first leaf with that bit set. A token that enters at the root is
// turned east by the routers whose bit is set in its pc or address and
// reaches the leaf with that address; a token that enters at a leaf
// is turned west by the same routers and reaches the root. Six combs:
//
// north of the path  the departures of beq, jal, jalr, by origin (address)
//                    the returns to ld and ecall, by pc
// south of the path  the arrivals at beq, jal, jalr, by target (pc)
//                    the departures of ld and ecall, by pc
// south of those     to the words of memory and tapes, by address
//                    and back from them, by address
//
// The roots are connected around the torus through columns 0 to 2. An
// instruction that neither transfers control nor accesses memory needs
// no wire. Distance is time: the compiler does not try to save any.

void boot_binary(char* name, uint64_t arguments) {
  uint64_t  saved_argc;
  uint64_t* saved_argv;

  // the machine as riscr and rotor boot it: the binary loaded, and on the
  // stack its name as only argument, or with all remaining arguments

  selfie_load(name);

  if ((e_flags / EF_RISCR) % 2 == 0) {
    printf("%s: %s is a RISC-U binary, cells of RISC-U are not supported yet\n", selfie_name, name);

    exit(EXITCODE_BADARGUMENTS);
  }

  saved_argc = selfie_argc;
  saved_argv = selfie_argv;

  if (arguments) {
    // the boot loader replaces the argument before the remaining ones

    selfie_argc = selfie_argc + 1;
    selfie_argv = selfie_argv - 1;
  } else {
    selfie_argc = 1;
    selfie_argv = smalloc(sizeof(uint64_t*));
  }

  reset_interpreter();
  reset_profiler();
  reset_microkernel();

  init_memory(1);

  current_context = create_context(MY_CONTEXT, 0);

  boot_loader(current_context);

  if (arguments) {
    // the arguments are the program's

    selfie_argv = saved_argv + saved_argc;
    selfie_argc = 0;
  } else {
    selfie_argc = saved_argc;
    selfie_argv = saved_argv;
  }
}

uint64_t differing_bit(uint64_t a, uint64_t b) {
  uint64_t bit;

  // the highest bit in which a and b differ, assert: a != b

  bit = 63;

  while (get_bits(a, bit, 1) == get_bits(b, bit, 1))
    bit = bit - 1;

  return bit;
}

uint64_t comb_height(uint64_t* keys, uint64_t lo, uint64_t hi) {
  uint64_t bit;
  uint64_t mid;
  uint64_t left;
  uint64_t right;

  // number of levels of the comb over the ascending keys from lo to hi - 1

  if (hi < lo + 2)
    return 0;

  bit = differing_bit(*(keys + lo), *(keys + hi - 1));

  mid = lo + 1;

  while (get_bits(*(keys + mid), bit, 1) == 0)
    mid = mid + 1;

  left  = comb_height(keys, lo, mid);
  right = comb_height(keys, mid, hi);

  if (left > right)
    return left + 1;
  else
    return right + 1;
}

void lay_cell(uint64_t x, uint64_t y, uint64_t cell, uint64_t word) {
  // every cell is laid once

  if (*(cell_kinds + cell_index(x, y)) != 0) {
    printf("%s: cell (%lu,%lu) is laid twice\n", selfie_name, x, y);

    exit(EXITCODE_COMPILERERROR);
  }

  *(cell_kinds + cell_index(x, y)) = cell;
  *(cell_words + cell_index(x, y)) = word;
}

void lay_tagged_cell(uint64_t x, uint64_t y, uint64_t cell, uint64_t word, uint64_t tag) {
  // an instruction, memory, or tape cell that knows its address, so that
  // a token on its way to an address without a cell does not go unnoticed

  lay_cell(x, y, cell + 64, word);

  *(cell_tags + cell_index(x, y)) = tag;
}

void lay_mirror(uint64_t x, uint64_t y, uint64_t mirror_kind) {
  lay_cell(x, y, encode_cell(CELL_MIRROR, 0, mirror_kind), 0);
}

void lay_comb(uint64_t* keys, uint64_t* xs, uint64_t lo, uint64_t hi, uint64_t y, uint64_t down, uint64_t field) {
  uint64_t bit;
  uint64_t mid;
  uint64_t mirror_kind;

  // the comb over the keys from lo to hi - 1 with its root in row y and
  // its leaves in the columns xs, south of the root if down and north of
  // it otherwise: a token heading for the leaves is turned east by a
  // backslash if they are south and by a slash if they are north

  if (hi < lo + 2)
    return;

  bit = differing_bit(*(keys + lo), *(keys + hi - 1));

  mid = lo + 1;

  while (get_bits(*(keys + mid), bit, 1) == 0)
    mid = mid + 1;

  if (down)
    mirror_kind = BACKSLASH;
  else
    mirror_kind = SLASH;

  lay_cell(*(xs + lo), y, encode_cell(CELL_ROUTER, 0, mirror_kind), bit + field * 64);

  lay_mirror(*(xs + mid), y, mirror_kind);

  if (down)
    y = y + 1;
  else
    y = y - 1;

  lay_comb(keys, xs, lo, mid, y, down, field);
  lay_comb(keys, xs, mid, hi, y, down, field);
}

void lay_side_comb(uint64_t* keys, uint64_t* ys, uint64_t lo, uint64_t hi, uint64_t x, uint64_t field) {
  uint64_t bit;
  uint64_t mid;

  // a comb on its side, over the keys from lo to hi - 1 with its root in
  // column x and its leaves in the rows ys east of it: a token heading
  // east for the leaves is turned south by a router if the bit is set
  // and east again in the row of its half, and a token heading west from
  // the leaves is turned north in its row and west again by the router

  if (hi < lo + 2)
    return;

  bit = differing_bit(*(keys + lo), *(keys + hi - 1));

  mid = lo + 1;

  while (get_bits(*(keys + mid), bit, 1) == 0)
    mid = mid + 1;

  lay_cell(x, *(ys + lo), encode_cell(CELL_ROUTER, 0, BACKSLASH), bit + field * 64);

  lay_mirror(x, *(ys + mid), BACKSLASH);

  lay_side_comb(keys, ys, lo, mid, x + 1, field);
  lay_side_comb(keys, ys, mid, hi, x + 1, field);
}

uint64_t lay_path_combs(uint64_t* keys, uint64_t* outs, uint64_t* ins, uint64_t count, uint64_t control) {
  uint64_t strips;
  uint64_t strip;
  uint64_t top;
  uint64_t lo;
  uint64_t hi;
  uint64_t i;

  // the combs of the strips of the path over the instructions with these
  // ascending addresses, which leave the path in the columns outs and
  // join it from the columns ins, and the wire from the roots of the
  // combs to the rows in which a token leaves and enters a strip; sets
  // side_keys, side_exits, and side_entries for the combs over the
  // strips and returns the number of strips

  strips = 0;

  lo = 0;

  while (lo < count) {
    strip = (*(keys + lo) - code_start) / INSTRUCTIONSIZE / path_width;

    hi = lo + 1;

    while (and(hi < count, (*(keys + hi) - code_start) / INSTRUCTIONSIZE / path_width == strip))
      hi = hi + 1;

    top = strip * path_pitch;

    if (control) {
      // north out of the cell to the root and on to the first row, there west;
      // from the west in the row south of the combs, north to the root, to
      // the row south of the path, and west and north into the cell

      lay_comb(keys, outs, lo, hi, top + control_out_row, 1, FIELD_ADDRESS);
      lay_comb(keys, ins, lo, hi, top + control_in_row, 0, FIELD_PC);

      lay_mirror(*(outs + lo), top + control_turn_row, BACKSLASH);
      lay_mirror(*(ins + lo), top + control_spine_row, SLASH);

      *(side_exits + strips)   = top + control_turn_row;
      *(side_entries + strips) = top + control_spine_row;
    } else {
      // south out of the cell to the root and on to the row south of all
      // combs, there west; from the west in the second row, south to the
      // root, to the row north of the path, and west and south into the cell

      lay_comb(keys, outs, lo, hi, top + access_out_row, 0, FIELD_PC);
      lay_comb(keys, ins, lo, hi, top + access_in_row, 1, FIELD_PC);

      lay_mirror(*(outs + lo), top + access_spine_row, SLASH);
      lay_mirror(*(ins + lo), top + access_turn_row, BACKSLASH);

      *(side_exits + strips)   = top + access_spine_row;
      *(side_entries + strips) = top + access_turn_row;
    }

    i = lo;

    while (i < hi) {
      if (control) {
        lay_mirror(*(ins + i), top + path_row + 1, BACKSLASH);
        lay_mirror(*(outs + i), top + path_row + 1, BACKSLASH);
      } else {
        lay_mirror(*(ins + i), top + path_row - 1, SLASH);
        lay_mirror(*(outs + i), top + path_row - 1, SLASH);
      }

      i = i + 1;
    }

    *(side_keys + strips) = *(keys + lo);

    strips = strips + 1;

    lo = hi;
  }

  return strips;
}

void lay_descending_comb(uint64_t* keys, uint64_t* xs, uint64_t lo, uint64_t hi, uint64_t x, uint64_t y, uint64_t down) {
  uint64_t bit;
  uint64_t mid;
  uint64_t mirror_kind;
  uint64_t column;

  // the comb of a strip of the stack over the keys from lo to hi - 1, with
  // the words in the columns xs, which descend by address, entered by a
  // token heading south in column x and row y if down, and left by one
  // there otherwise: the token is turned east, a router turns it south
  // if the bit is set, and a mirror further east if not

  if (down)
    mirror_kind = BACKSLASH;
  else
    mirror_kind = SLASH;

  if (hi == lo + 1) {
    // the way east to the column of the word, if the strip has no word in between

    if (*(xs + lo) != x) {
      lay_mirror(x, y, mirror_kind);
      lay_mirror(*(xs + lo), y, mirror_kind);
    }

    return;
  }

  bit = differing_bit(*(keys + lo), *(keys + hi - 1));

  mid = lo + 1;

  while (get_bits(*(keys + mid), bit, 1) == 0)
    mid = mid + 1;

  // the column in which the comb of all words that differ from these keys
  // in this bit and the bits below would begin: that of its first word,
  // which has them all set, less its rows

  column = left_shift(right_shift(*(keys + lo), bit + 1), bit + 1) + two_to_the_power_of(bit + 1) - WORDSIZE;
  column = word_column + get_descending_column(column) - (bit - 2);

  lay_mirror(x, y, mirror_kind);

  lay_cell(column + 1, y, encode_cell(CELL_ROUTER, 0, mirror_kind), bit + FIELD_ADDRESS * 64);

  lay_mirror(column + two_to_the_power_of(bit - 2), y, mirror_kind);

  if (down)
    y = y + 1;
  else
    y = y - 1;

  lay_descending_comb(keys, xs, mid, hi, column + 1, y, down);
  lay_descending_comb(keys, xs, lo, mid, column + two_to_the_power_of(bit - 2), y, down);
}

void add_memory_word(uint64_t address, uint64_t value, uint64_t kind) {
  // assert: addresses are added in ascending order

  if (number_of_words > 0)
    if (address <= *(word_addresses + number_of_words - 1)) {
      printf("%s: memory regions overlap or are not in ascending order at 0x%lX\n", selfie_name, address);

      exit(EXITCODE_BADARGUMENTS);
    }

  *(word_addresses + number_of_words) = address;
  *(word_values + number_of_words)    = value;
  *(word_kinds + number_of_words)     = kind;

  number_of_words = number_of_words + 1;
}

uint64_t ceiling_log_two(uint64_t n) {
  uint64_t l;
  uint64_t p;

  // the least l with n <= 2^l

  l = 0;
  p = 1;

  while (p < n) {
    l = l + 1;
    p = p * 2;
  }

  return l;
}

void add_region(uint64_t start, uint64_t words, uint64_t kind) {
  uint64_t previous;

  // words of memory or of a tape that have a cell, from start on;
  // assert: regions are added in ascending order

  if (words == 0)
    return;

  if (number_of_regions >= MAX_REGIONS) {
    printf("%s: more than %lu regions of memory and tapes\n", selfie_name, MAX_REGIONS);

    exit(EXITCODE_BADARGUMENTS);
  }

  if (number_of_regions > 0) {
    previous = number_of_regions - 1;

    if (start < *(region_starts + previous) + *(region_words + previous) * WORDSIZE) {
      printf("%s: memory regions overlap or are not in ascending order at 0x%lX\n", selfie_name, start);

      exit(EXITCODE_BADARGUMENTS);
    }
  }

  *(region_starts + number_of_regions) = start;
  *(region_words + number_of_regions)  = words;
  *(region_kinds + number_of_regions)  = kind;
  *(region_ranks + number_of_regions)  = number_of_region_words;

  number_of_regions = number_of_regions + 1;

  number_of_region_words = number_of_region_words + words;
}

uint64_t find_region(uint64_t address) {
  uint64_t i;

  // the region with the word at address, number_of_regions if there is none

  if (address % WORDSIZE != 0)
    return number_of_regions;

  i = last_region;

  if (address >= *(region_starts + i))
    if ((address - *(region_starts + i)) / WORDSIZE < *(region_words + i))
      return i;

  i = 0;

  while (i < number_of_regions) {
    if (address >= *(region_starts + i))
      if ((address - *(region_starts + i)) / WORDSIZE < *(region_words + i)) {
        last_region = i;

        return i;
      }

    i = i + 1;
  }

  return number_of_regions;
}

uint64_t region_height(uint64_t lo, uint64_t hi) {
  uint64_t bit;
  uint64_t split;
  uint64_t below;
  uint64_t above;
  uint64_t i;
  uint64_t left;
  uint64_t right;

  // number of levels of the comb over the words from address lo to hi,
  // which is comb_height of their addresses: the comb splits where the
  // highest differing bit of lo and hi is set; assert: lo and hi have cells

  if (lo == hi)
    return 0;

  bit = differing_bit(lo, hi);

  split = left_shift(right_shift(hi, bit), bit);

  if (find_region(lo) == find_region(hi)) {
    // contiguous words: a comb over the n words up to a multiple of a power
    // of two no less than n, or from one on, has as many levels as n has bits

    left  = ceiling_log_two((split - lo) / WORDSIZE);
    right = ceiling_log_two((hi - split) / WORDSIZE + 1);
  } else {
    // the last word below the split and the first word from the split on

    below = lo;
    above = hi;

    i = 0;

    while (i < number_of_regions) {
      if (*(region_starts + i) < split) {
        below = *(region_starts + i) + (*(region_words + i) - 1) * WORDSIZE;

        if (below >= split)
          below = split - WORDSIZE;
      }

      i = i + 1;
    }

    i = number_of_regions;

    while (i > 0) {
      i = i - 1;

      if (*(region_starts + i) + (*(region_words + i) - 1) * WORDSIZE >= split) {
        above = *(region_starts + i);

        if (above < split)
          above = split;
      }
    }

    left  = region_height(lo, below);
    right = region_height(above, hi);
  }

  if (left > right)
    return left + 1;
  else
    return right + 1;
}

uint64_t plan_path_combs(uint64_t* keys, uint64_t count) {
  uint64_t* firsts;
  uint64_t strips;
  uint64_t strip;
  uint64_t height;
  uint64_t highest;
  uint64_t lo;
  uint64_t hi;

  // the combs over the instructions with these ascending addresses: returns
  // the rows of the highest comb of a strip, and sets side_height to the
  // columns of the comb over the strips that have one and first_strip to
  // the first of them

  firsts = zmalloc(path_strips * sizeof(uint64_t));

  strips  = 0;
  highest = 0;

  first_strip = 0;

  lo = 0;

  while (lo < count) {
    strip = (*(keys + lo) - code_start) / INSTRUCTIONSIZE / path_width;

    hi = lo + 1;

    while (and(hi < count, (*(keys + hi) - code_start) / INSTRUCTIONSIZE / path_width == strip))
      hi = hi + 1;

    height = comb_height(keys, lo, hi);

    if (height > highest)
      highest = height;

    if (strips == 0)
      first_strip = strip;

    *(firsts + strips) = *(keys + lo);

    strips = strips + 1;

    lo = hi;
  }

  side_height = comb_height(firsts, 0, strips);

  return highest;
}

void plan_path() {
  uint64_t n;
  uint64_t i;
  uint64_t cost;
  uint64_t best;

  // the path in two dimensions: as many bits of an instruction address
  // select the column that the width of a strip plus the height of all
  // strips is least, with a comb taken to have as many rows as bits

  n = code_size / INSTRUCTIONSIZE;

  path_bits = 1;

  best = 4 + (n + 1) / 2 * 12;

  i = 2;

  while (two_to_the_power_of(i - 1) < n) {
    cost = two_to_the_power_of(i + 1) + (n + two_to_the_power_of(i) - 1) / two_to_the_power_of(i) * (4 * i + 8);

    if (cost < best) {
      best = cost;

      path_bits = i;
    }

    i = i + 1;
  }

  path_width  = two_to_the_power_of(path_bits);
  path_strips = (n + path_width - 1) / path_width;

  // the instructions: beq, jal, and jalr transfer control, ld with rd not
  // zero and ecall access memory, both leave and join the path sideways

  instruction_classes = zmalloc(n * sizeof(uint64_t));

  control_keys = zmalloc(n * sizeof(uint64_t));
  control_out  = zmalloc(n * sizeof(uint64_t));
  control_in   = zmalloc(n * sizeof(uint64_t));

  access_keys = zmalloc(n * sizeof(uint64_t));
  access_out  = zmalloc(n * sizeof(uint64_t));
  access_in   = zmalloc(n * sizeof(uint64_t));

  controls = 0;
  accesses = 0;

  i = 0;

  while (i < n) {
    decode_cell(load_instruction(i * INSTRUCTIONSIZE));

    if (is_reversible_instruction()) {
      if (or(is == BEQ, or(is == JAL, is == JALR))) {
        *(instruction_classes + i) = CLASS_CONTROL;

        *(control_keys + controls) = code_start + i * INSTRUCTIONSIZE;

        controls = controls + 1;
      } else if (or(is == ECALL, and(is == LOAD, rd != REG_ZR))) {
        *(instruction_classes + i) = CLASS_ACCESS;

        *(access_keys + accesses) = code_start + i * INSTRUCTIONSIZE;

        accesses = accesses + 1;
      }
    }

    i = i + 1;
  }

  // the combs of the strips, and the combs over the strips west of them

  control_height = plan_path_combs(control_keys, controls);

  control_side_height = side_height;
  first_control_strip = first_strip;

  access_height = plan_path_combs(access_keys, accesses);

  access_side_height = side_height;
  first_access_strip = first_strip;

  // one column west of the strips leads the path from a strip to the next

  path_column = COMB_COLUMN + 2 * control_side_height + 2 * access_side_height + 1;

  // control leaves north in its column and arrives from the south from the
  // next column, access leaves south in its column and returns from the north
  // from the next column

  i = 0;

  while (i < controls) {
    *(control_out + i) = path_column + 2 * ((*(control_keys + i) - code_start) / INSTRUCTIONSIZE % path_width);
    *(control_in + i)  = *(control_out + i) + 1;

    i = i + 1;
  }

  i = 0;

  while (i < accesses) {
    *(access_out + i) = path_column + 2 * ((*(access_keys + i) - code_start) / INSTRUCTIONSIZE % path_width);
    *(access_in + i)  = *(access_out + i) + 1;

    i = i + 1;
  }

  side_keys    = zmalloc(path_strips * sizeof(uint64_t));
  side_entries = zmalloc(path_strips * sizeof(uint64_t));
  side_exits   = zmalloc(path_strips * sizeof(uint64_t));
}

void plan_regions() {
  uint64_t i;

  // the words that have a cell, by ascending address: the data segment,
  // the regions of the heap, the top of the stack, the output tapes of
  // the file descriptors that have tapes, and the input tapes of standard
  // input, with the input, and of the other files that have tapes

  input_words = (uint64_t*) 0;
  input_size  = 0;

  if (input_name != (char*) 0) {
    input_words = read_file(input_name);
    input_size  = layout_size;

    if (input_size > TAPE_WORDS * WORDSIZE) {
      printf("%s: %s has more than the %lu bytes of a tape\n", selfie_name, input_name, TAPE_WORDS * WORDSIZE);

      exit(EXITCODE_BADARGUMENTS);
    }
  }

  heap_start_address = get_program_break(current_context);

  region_starts = zmalloc(MAX_REGIONS * sizeof(uint64_t));
  region_words  = zmalloc(MAX_REGIONS * sizeof(uint64_t));
  region_kinds  = zmalloc(MAX_REGIONS * sizeof(uint64_t));
  region_ranks  = zmalloc(MAX_REGIONS * sizeof(uint64_t));

  number_of_regions      = 0;
  number_of_region_words = 0;

  last_region = 0;

  add_region(data_start, data_size / WORDSIZE, CELL_MEMORY);

  i = 0;

  while (i < number_of_heap_regions) {
    add_region(heap_start_address + *(heap_offsets + i), *(heap_words + i), CELL_MEMORY);

    i = i + 1;
  }

  add_region(VIRTUALMEMORYSIZE * GIGABYTE - stack_words * WORDSIZE, stack_words, CELL_MEMORY);

  if (*(get_regs(current_context) + REG_SP) < VIRTUALMEMORYSIZE * GIGABYTE - stack_words * WORDSIZE) {
    printf("%s: the stack of %s needs more than %lu words\n", selfie_name, binary_name, stack_words);

    exit(EXITCODE_BADARGUMENTS);
  }

  i = 1;

  while (i < tape_files) {
    add_region(OUTPUT_TAPES + left_shift(i, 32), TAPE_WORDS, CELL_TAPE);

    i = i + 1;
  }

  add_region(INPUT_TAPES, TAPE_WORDS, CELL_MEMORY);

  i = 3;

  while (i < tape_files) {
    add_region(INPUT_TAPES + left_shift(i, 32), TAPE_WORDS, CELL_MEMORY);

    i = i + 1;
  }
}

uint64_t initial_word(uint64_t address) {
  // the word at address as the boot loader left the machine: the data
  // segment and the arguments on the stack, and the input on its tape

  if (address >= INPUT_TAPES) {
    if (address - INPUT_TAPES < input_size)
      return *(input_words + (address - INPUT_TAPES) / WORDSIZE);
  } else if (address < OUTPUT_TAPES)
    if (is_virtual_address_mapped(get_pt(current_context), address))
      return load_virtual_memory(get_pt(current_context), address);

  return 0;
}

uint64_t count_strips(uint64_t bits) {
  uint64_t strips;
  uint64_t first;
  uint64_t last;
  uint64_t previous;
  uint64_t i;

  // the number of strips if the lower bits of a word address select the
  // column and the others the strip, and the strip of each region's first word

  strips   = 0;
  previous = 0;

  i = 0;

  while (i < number_of_regions) {
    first = right_shift(*(region_starts + i), bits + 3);
    last  = right_shift(*(region_starts + i) + (*(region_words + i) - 1) * WORDSIZE, bits + 3);

    if (and(strips > 0, first == previous))
      // the region begins in the strip in which the region before ends
      strips = strips - 1;

    *(region_strips + i) = strips;

    strips = strips + last - first + 1;

    previous = last;

    i = i + 1;
  }

  return strips;
}

void plan_strips() {
  uint64_t i;
  uint64_t strip;
  uint64_t prefix;
  uint64_t first;
  uint64_t last;
  uint64_t end;
  uint64_t height;
  uint64_t cost;
  uint64_t best;

  // memory in two dimensions: as many bits select the column that the
  // width of a strip plus the height of all strips is least, which is
  // how far the last word is from the first

  region_strips = zmalloc(MAX_REGIONS * sizeof(uint64_t));

  strip_bits = 1;

  best = count_strips(1) * 5 + 2;

  i = 2;

  while (i < 30) {
    cost = count_strips(i) * (2 * i + 3) + two_to_the_power_of(i);

    if (cost < best) {
      best = cost;

      strip_bits = i;
    }

    i = i + 1;
  }

  number_of_strips = count_strips(strip_bits);

  // the first and the last word of each strip

  strip_keys  = zmalloc(number_of_strips * sizeof(uint64_t));
  strip_lasts = zmalloc(number_of_strips * sizeof(uint64_t));

  i = 0;

  while (i < number_of_regions) {
    end = *(region_starts + i) + (*(region_words + i) - 1) * WORDSIZE;

    prefix = right_shift(*(region_starts + i), strip_bits + 3);

    strip = *(region_strips + i);

    while (prefix <= right_shift(end, strip_bits + 3)) {
      first = left_shift(prefix, strip_bits + 3);
      last  = first + (two_to_the_power_of(strip_bits) - 1) * WORDSIZE;

      if (first < *(region_starts + i))
        first = *(region_starts + i);

      if (last > end)
        last = end;

      if (*(strip_keys + strip) == 0)
        *(strip_keys + strip) = first;

      *(strip_lasts + strip) = last;

      prefix = prefix + 1;
      strip  = strip + 1;
    }

    i = i + 1;
  }

  // all strips have the rows of the highest comb; a comb of a strip of
  // the stack has one more row, in which wire reaches a word whose strip
  // has few words

  stack_start = VIRTUALMEMORYSIZE * GIGABYTE - stack_words * WORDSIZE;

  strip_height = 0;

  i = 0;

  while (i < number_of_strips) {
    height = region_height(*(strip_keys + i), *(strip_lasts + i)) + is_stack_strip(i);

    if (height > strip_height)
      strip_height = height;

    i = i + 1;
  }

  strip_pitch = 2 * strip_height + 3;

  // the rows of the strips and the columns of the combs over them

  strip_entries = zmalloc(number_of_strips * sizeof(uint64_t));

  laying_strips = 0;

  comb_columns = 0;

  memory_rows = place_strips(0, number_of_strips, 0, 0);

  word_column = COMB_COLUMN + 2 * comb_columns;
}

uint64_t is_stack_strip(uint64_t strip) {
  // a strip with a word of the stack
  if (*(strip_lasts + strip) >= stack_start)
    return *(strip_lasts + strip) < VIRTUALMEMORYSIZE * GIGABYTE;
  else
    return 0;
}

uint64_t has_stack_strip(uint64_t lo, uint64_t hi) {
  // the strips of the stack are the last of memory
  while (lo < hi) {
    if (is_stack_strip(lo))
      return 1;

    lo = lo + 1;
  }

  return 0;
}

uint64_t split_strips(uint64_t lo, uint64_t hi) {
  uint64_t mid;

  // the first of the strips from lo to hi - 1 in whose addresses the
  // highest differing bit of all of them is set, which is split_bit

  split_bit = differing_bit(*(strip_keys + lo), *(strip_keys + hi - 1));

  mid = lo + 1;

  while (get_bits(*(strip_keys + mid), split_bit, 1) == 0)
    mid = mid + 1;

  return mid;
}

void lay_strip_cell(uint64_t x, uint64_t y, uint64_t kind, uint64_t word) {
  // a cell of the comb to the strips, in its column x and row y from
  // memory_in_row, and the same cell of the comb from the strips, which
  // is the same comb west of it and as many rows south as a strip has
  // between its first and its last: what turns a token heading east
  // south and east again turns one heading west north and west again

  if (x >= comb_columns)
    comb_columns = x + 1;

  if (laying_strips) {
    lay_cell(COMB_COLUMN + comb_columns + x, memory_in_row + y, encode_cell(kind, 0, BACKSLASH), word);
    lay_cell(COMB_COLUMN + x, memory_in_row + y + strip_pitch - 1, encode_cell(kind, 0, BACKSLASH), word);
  }
}

uint64_t place_strips(uint64_t lo, uint64_t hi, uint64_t x, uint64_t y) {
  uint64_t mid;
  uint64_t rows;
  uint64_t length;
  uint64_t stair;
  uint64_t l;

  // The comb over the strips from lo to hi - 1, entered by a token heading
  // east in its column x and row y: places the strips in rows, lays the
  // comb if laying_strips, and returns the number of rows. A router turns
  // a token south if a bit of its address is set, so the strips with the
  // bit set are south of the others. The strips of the stack have all
  // such bits set and would be last, and its top the last word of the
  // last strip, where a program has its most used words. For the stack
  // the comb is another: a token is turned south first, so that a router
  // turns it east if the bit is set, and south is where the others go.

  if (hi == lo + 1) {
    *(strip_entries + lo) = y;

    return strip_pitch;
  }

  mid = split_strips(lo, hi);

  if (not(has_stack_strip(mid, hi))) {
    // strips without the bit continue east, strips with the bit are south of them

    lay_strip_cell(x, y, CELL_ROUTER, split_bit + FIELD_ADDRESS * 64);

    rows = place_strips(lo, mid, x + 1, y);

    lay_strip_cell(x, y + rows, CELL_MIRROR, 0);

    return rows + place_strips(mid, hi, x + 1, y + rows);
  } else if (has_stack_strip(lo, mid)) {
    // within the stack: strips with the bit first

    lay_strip_cell(x, y, CELL_MIRROR, 0);
    lay_strip_cell(x, y + 1, CELL_ROUTER, split_bit + FIELD_ADDRESS * 64);

    rows = 1 + place_strips(mid, hi, x + 1, y + 1);

    lay_strip_cell(x, y + rows, CELL_MIRROR, 0);

    return rows + place_strips(lo, mid, x + 1, y + rows);
  }

  // the way to the stack: a stair of routers, each a column east and a
  // row south of the one before, that tokens for the stack descend, and
  // that others leave south, each in the column of its router

  length = 0;

  l = lo;

  mid = split_strips(l, hi);

  while (and(has_stack_strip(mid, hi), not(has_stack_strip(l, mid)))) {
    lay_strip_cell(x + length, y + length, CELL_MIRROR, 0);
    lay_strip_cell(x + length, y + length + 1, CELL_ROUTER, split_bit + FIELD_ADDRESS * 64);

    length = length + 1;

    l = mid;

    if (hi > l + 1)
      mid = split_strips(l, hi);
    else
      // one strip is left, the stack: the stair ends
      mid = hi;
  }

  // the stack first, then the others by ascending address, all east of the stair

  rows = length + place_strips(l, hi, x + length, y + length);

  stair = 0;

  l = lo;

  while (stair < length) {
    mid = split_strips(l, hi);

    lay_strip_cell(x + stair, y + rows, CELL_MIRROR, 0);

    rows = rows + place_strips(l, mid, x + length, y + rows);

    stair = stair + 1;

    l = mid;
  }

  return rows;
}

uint64_t get_word_strip(uint64_t address, uint64_t region) {
  // the strip of the word at address, which is in region
  return *(region_strips + region) + right_shift(address, strip_bits + 3) - right_shift(*(region_starts + region), strip_bits + 3);
}

uint64_t get_descending_column(uint64_t address) {
  uint64_t column;
  uint64_t j;

  // the column, from the first, of a word in a strip of the stack, where
  // the words with a bit set come first: one column for a set bit, two
  // to the power of its number, from 1, for another

  column = 0;

  j = 1;

  while (j <= strip_bits) {
    if (get_bits(address, j + 2, 1))
      column = column + 1;
    else
      column = column + two_to_the_power_of(j);

    j = j + 1;
  }

  return column;
}

uint64_t get_word_column(uint64_t address, uint64_t strip) {
  if (is_stack_strip(strip))
    return word_column + get_descending_column(address);
  else
    return word_column + get_bits(address, 3, strip_bits);
}

uint64_t get_word_row(uint64_t strip) {
  // the words of a strip are below the comb to them
  return memory_in_row + *(strip_entries + strip) + strip_height + 1;
}

void plan_rows() {
  // the rows of a strip of the path, from north to south: two rows in
  // which wire leaves and enters the strip west of the combs below, the
  // combs north of the path, the path, the combs south of it, two rows in
  // which wire enters and leaves the strip, and the row in which the path
  // returns west; the strips of words are south of all strips of the path

  plan_strips();

  control_turn_row = 0;
  access_turn_row  = 1;

  control_out_row = 2;
  access_in_row   = control_out_row + control_height;

  // one row north and one south of the path lead from the next column into a cell

  path_row = access_in_row + access_height + 1;

  // the roots of the combs south of the path are in their southern rows

  control_in_row = path_row + 1 + control_height;
  access_out_row = control_in_row + access_height;

  control_spine_row = access_out_row + 1;
  access_spine_row  = control_spine_row + 1;

  path_return_row = access_spine_row + 1;

  path_pitch = path_return_row + 1;

  memory_in_row = path_strips * path_pitch;
}

void boot_token() {
  uint64_t i;

  // the token: at the first instruction, as the boot loader left the machine

  reset_token();

  token_x = path_column;
  token_y = path_row;

  token_pc = get_pc(current_context);

  i = 1;

  while (i < NUMBEROFREGISTERS) {
    *(token_registers + i) = *(get_regs(current_context) + i);

    i = i + 1;
  }

  token_break = heap_start_address;

  *token_ends = input_size;

  executed_ticks        = 0;
  executed_instructions = 0;
}

void compile_layout(char* name) {
  uint64_t n;
  uint64_t i;
  uint64_t j;
  uint64_t x;
  uint64_t address;
  uint64_t value;
  uint64_t lo;
  uint64_t hi;
  uint64_t* word_xs;
  uint64_t* word_ys;
  uint64_t* word_strips;
  uint64_t entry;
  uint64_t exit_row;

  boot_binary(name, 0);

  plan_path();
  plan_regions();
  plan_rows();

  n = code_size / INSTRUCTIONSIZE;

  // the words of the regions

  word_addresses = zmalloc(number_of_region_words * sizeof(uint64_t));
  word_values    = zmalloc(number_of_region_words * sizeof(uint64_t));
  word_kinds     = zmalloc(number_of_region_words * sizeof(uint64_t));
  word_cells     = zmalloc(number_of_region_words * sizeof(uint64_t));
  word_xs        = zmalloc(number_of_region_words * sizeof(uint64_t));
  word_ys        = zmalloc(number_of_region_words * sizeof(uint64_t));
  word_strips    = zmalloc(number_of_region_words * sizeof(uint64_t));

  number_of_words = 0;

  j = 0;

  while (j < number_of_regions) {
    i = 0;

    while (i < *(region_words + j)) {
      address = *(region_starts + j) + i * WORDSIZE;

      *(word_strips + number_of_words) = get_word_strip(address, j);

      *(word_xs + number_of_words) = get_word_column(address, get_word_strip(address, j));
      *(word_ys + number_of_words) = get_word_row(get_word_strip(address, j));

      add_memory_word(address, initial_word(address), *(region_kinds + j));

      i = i + 1;
    }

    j = j + 1;
  }

  x = path_column + 2 * path_width + 2;

  if (x < word_column + two_to_the_power_of(strip_bits + 1) + 1)
    x = word_column + two_to_the_power_of(strip_bits + 1) + 1;

  allocate_grid(x, memory_in_row + memory_rows);

  // the path, strip by strip: from the last instruction of a strip two
  // columns east, south to the last row of the strip, west to the column
  // west of the strips, south to the path of the next strip, and east

  i = 0;

  while (i < n) {
    value = load_instruction(i * INSTRUCTIONSIZE);

    decode_cell(value);

    x = path_column + 2 * (i % path_width);

    j = SLASH;

    if (is_reversible_instruction())
      if (or(is == ECALL, and(is == LOAD, rd != REG_ZR)))
        j = BACKSLASH;

    lay_tagged_cell(x, i / path_width * path_pitch + path_row, encode_cell(CELL_INSTRUCTION, EAST, j), value, code_start + i * INSTRUCTIONSIZE);

    i = i + 1;
  }

  i = 0;

  while (i + 1 < path_strips) {
    lay_mirror(path_column + 2 * path_width, i * path_pitch + path_row, BACKSLASH);
    lay_mirror(path_column + 2 * path_width, i * path_pitch + path_return_row, SLASH);
    lay_mirror(path_column - 1, i * path_pitch + path_return_row, SLASH);
    lay_mirror(path_column - 1, (i + 1) * path_pitch + path_row, BACKSLASH);

    i = i + 1;
  }

  // control: through the comb of departures of its strip, west through the
  // comb from the strips to column 0, south to the row in which control
  // enters the first strip that has any, east through the comb to the
  // strips, and through the comb of arrivals of its strip

  if (controls > 0) {
    i = lay_path_combs(control_keys, control_out, control_in, controls, 1);

    lay_side_comb(side_keys, side_exits, 0, i, COMB_COLUMN, FIELD_ADDRESS);
    lay_side_comb(side_keys, side_entries, 0, i, COMB_COLUMN + control_side_height + access_side_height, FIELD_PC);

    lay_mirror(0, *side_exits, SLASH);
    lay_mirror(0, *side_entries, BACKSLASH);
  }

  // memory: through the comb of departures of its strip, west through the
  // comb from the strips to column 1, south past all strips of the path
  // and east to the root of the comb over the strips of words, east in
  // the row of the strip to the root of its comb to the words, through
  // the cell of the word and the comb back from the words of the strip,
  // west through the comb back from the strips of words to column 2,
  // north to the row in which a token enters the first strip of the path
  // that has any access, east through the comb to the strips, and
  // through the comb of returns of its strip

  if (accesses > 0) {
    i = lay_path_combs(access_keys, access_out, access_in, accesses, 0);

    lay_side_comb(side_keys, side_entries, 0, i, COMB_COLUMN + control_side_height, FIELD_PC);
    lay_side_comb(side_keys, side_exits, 0, i, COMB_COLUMN + 2 * control_side_height + access_side_height, FIELD_PC);

    lay_mirror(1, *side_exits, SLASH);
    lay_mirror(2, *side_entries, SLASH);

    lay_mirror(1, memory_in_row, BACKSLASH);

    lo = 0;

    while (lo < number_of_words) {
      // the words of a strip

      j = *(word_strips + lo);

      hi = lo + 1;

      while (and(hi < number_of_words, *(word_strips + hi) == j))
        hi = hi + 1;

      entry    = memory_in_row + *(strip_entries + j);
      exit_row = entry + strip_pitch - 1;

      if (is_stack_strip(j)) {
        lay_mirror(word_column, entry, BACKSLASH);

        lay_descending_comb(word_addresses, word_xs, lo, hi, word_column, entry + 1, 1);
        lay_descending_comb(word_addresses, word_xs, lo, hi, word_column, exit_row - 1, 0);

        lay_mirror(word_column, exit_row, SLASH);
      } else {
        lay_mirror(*(word_xs + lo), entry, BACKSLASH);

        lay_comb(word_addresses, word_xs, lo, hi, entry + 1, 1, FIELD_ADDRESS);
        lay_comb(word_addresses, word_xs, lo, hi, exit_row - 1, 0, FIELD_ADDRESS);

        lay_mirror(*(word_xs + lo), exit_row, SLASH);
      }

      lo = hi;
    }

    // the combs to and from the strips

    laying_strips = 1;

    place_strips(0, number_of_strips, 0, 0);

    laying_strips = 0;

    lay_mirror(2, memory_in_row + strip_pitch - 1, BACKSLASH);
  }

  i = 0;

  while (i < number_of_words) {
    lay_tagged_cell(*(word_xs + i), *(word_ys + i), encode_cell(*(word_kinds + i), 0, 0), *(word_values + i), *(word_addresses + i));

    *(word_cells + i) = cell_index(*(word_xs + i), *(word_ys + i));

    i = i + 1;
  }

  boot_token();

  printf("%s: %lu instructions of %s on a grid of %lux%lu cells: %lu transfer control, %lu access memory, %lu words of memory and tapes\n", selfie_name,
    n, name, grid_width, grid_height, controls, accesses, number_of_words);
}

// The abstraction relates the layout to rotor's RISC-R model of the binary
// for bitr's product, see cellfie.md: rotor's model takes a step when the
// token is on the path of an instruction cell, and the two must then agree
// on the pc, the registers, the state of the system calls, and all words
// of memory and tapes that have a cell. Rotor's model must be generated
// with the given heap and stack allowance in bytes and its default tapes.

void print_difference(uint64_t index_sid, uint64_t state_nid, uint64_t index, uint64_t cell_state_nid, uint64_t cell_index) {
  // a word of a state of rotor's model and a word of a state of cellfie's
  // model, of a cell or by the same index, differ when a step is due;
  // the symbol of the bad state follows

  dprintf(output_fd, "%lu constd %lu %lu\n", abstraction_nid, index_sid, index);
  dprintf(output_fd, "%lu read 2 %lu %lu\n", abstraction_nid + 1, state_nid, abstraction_nid);

  if (cell_state_nid == 56) {
    dprintf(output_fd, "%lu constd 23 %lu\n", abstraction_nid + 2, cell_index);
    dprintf(output_fd, "%lu read 2 56 %lu\n", abstraction_nid + 3, abstraction_nid + 2);
  } else
    dprintf(output_fd, "%lu read 2 %lu %lu\n", abstraction_nid + 3, cell_state_nid, abstraction_nid);

  dprintf(output_fd, "%lu neq 1 %lu %lu\n", abstraction_nid + 4, abstraction_nid + 1, abstraction_nid + 3);
  dprintf(output_fd, "%lu and 1 %lu %lu\n", abstraction_nid + 5, abstraction_step, abstraction_nid + 4);
  dprintf(output_fd, "%lu bad %lu ", abstraction_nid + 6, abstraction_nid + 5);

  abstraction_nid = abstraction_nid + 10;
}

void write_abstraction(char* name, uint64_t heap_allowance, uint64_t stack_allowance) {
  uint64_t fd;
  uint64_t i;
  uint64_t address;
  uint64_t bits;
  uint64_t loaded;
  uint64_t stack_start_address;

  if (number_of_words == 0) {
    printf("%s: no binary compiled\n", selfie_name);

    exit(EXITCODE_BADARGUMENTS);
  }

  fd = open_write_only(name, S_IRUSR_IWUSR_IRGRP_IROTH);

  if (signed_less_than(fd, 0)) {
    printf("%s: could not create %s\n", selfie_name, name);

    exit(EXITCODE_IOERROR);
  }

  output_name = name;
  output_fd   = fd;

  dprintf(output_fd, "; %s\n\n", SELFIE_URL);
  dprintf(output_fd, "; abstraction for bitr's product of rotor's RISC-R model of a binary, with\n");
  dprintf(output_fd, "; %lu bytes heap and %lu bytes stack allowance, with cellfie's cell rule on\n", heap_allowance, stack_allowance);
  dprintf(output_fd, "; the layout of the binary on a grid of %lux%lu cells, see cellfie.md\n\n", grid_width, grid_height);

  dprintf(output_fd, "1 sort bitvec 1\n2 sort bitvec 64\n3 sort bitvec 5\n4 sort array 3 2\n");

  // the segments of rotor's model: as many words as the data has and the
  // allowances allow, two at least, addressed by word

  bits = log_two(data_size / WORDSIZE);

  if (two_to_the_power_of(bits) < data_size / WORDSIZE)
    bits = bits + 1;

  if (bits == 0)
    bits = 1;

  dprintf(output_fd, "5 sort bitvec %lu\n6 sort array 5 2\n", bits);

  bits = log_two(heap_allowance / WORDSIZE);

  if (two_to_the_power_of(bits) < heap_allowance / WORDSIZE)
    bits = bits + 1;

  if (bits == 0)
    bits = 1;

  dprintf(output_fd, "7 sort bitvec %lu\n8 sort array 7 2\n", bits);

  bits = log_two(stack_allowance / WORDSIZE);

  if (two_to_the_power_of(bits) < stack_allowance / WORDSIZE)
    bits = bits + 1;

  if (bits == 0)
    bits = 1;

  dprintf(output_fd, "9 sort bitvec %lu\n10 sort array 9 2\n", bits);

  dprintf(output_fd, "11 sort bitvec 32\n12 sort bitvec 2\n13 sort array 12 2\n");
  dprintf(output_fd, "14 sort bitvec %lu\n15 sort array 14 2\n", log_two(NUMBER_OF_TAPES * TAPE_WORDS));

  // the grid

  dprintf(output_fd, "20 sort bitvec %lu\n21 sort bitvec %lu\n", log_two(grid_width), log_two(grid_height));
  dprintf(output_fd, "22 sort bitvec 8\n23 sort bitvec %lu\n", log_two(grid_size));
  dprintf(output_fd, "24 sort array 23 22\n25 sort array 23 2\n26 sort bitvec 3\n\n");

  // rotor's states: a segment is loaded if the boot loader put a word into it

  dprintf(output_fd, "30 state 2 core-0-pc\n31 state 4 core-0-initialized-register-file\n");

  loaded = 0;

  i = 0;

  while (i < data_size / WORDSIZE) {
    if (load_data(i * WORDSIZE) != 0)
      loaded = 1;

    i = i + 1;
  }

  if (loaded)
    dprintf(output_fd, "32 state 6 core-0-loaded-data-segment\n");
  else
    dprintf(output_fd, "32 state 6 core-0-zeroed-data-segment\n");

  dprintf(output_fd, "33 state 8 core-0-zeroed-heap-segment\n34 state 10 core-0-loaded-stack-segment\n");
  dprintf(output_fd, "35 state 11 core-0-program-break\n36 state 2 open-files\n");
  dprintf(output_fd, "37 state 13 tape-heads\n38 state 13 tape-ends\n39 state 13 tape-inputs\n40 state 13 tape-opens\n");
  dprintf(output_fd, "41 state 15 input-tapes\n42 state 15 output-tapes\n\n");

  // cellfie's states

  dprintf(output_fd, "43 state 20 token-x\n44 state 21 token-y\n45 state 12 token-heading\n");
  dprintf(output_fd, "46 state 2 token-pc\n47 state 2 token-address\n48 state 2 token-data\n");
  dprintf(output_fd, "49 state 2 token-break\n50 state 2 token-open-files\n51 state 12 token-leg\n52 state 2 token-word\n");
  dprintf(output_fd, "53 state 4 token-registers\n");
  dprintf(output_fd, "54 state 13 token-tape-heads\n57 state 13 token-tape-ends\n58 state 13 token-tape-inputs\n59 state 13 token-tape-opens\n");
  dprintf(output_fd, "55 state 24 cell-kinds\n56 state 25 cell-words\n\n");

  // step: the token is on the path of an instruction cell

  dprintf(output_fd, "60 concat 23 44 43\n61 read 22 55 60\n62 slice 26 61 2 0\n63 constd 26 %lu\n64 eq 1 62 63\n", CELL_INSTRUCTION);
  dprintf(output_fd, "65 slice 12 61 4 3\n66 eq 1 45 65\n67 and 1 64 66\n68 output 67 step\n\n");

  abstraction_step = 67;

  // nothing is in transit

  dprintf(output_fd, "70 zero 2\n71 zero 12\n72 neq 1 47 70\n73 neq 1 48 70\n74 neq 1 51 71\n75 neq 1 52 70\n");
  dprintf(output_fd, "76 or 1 72 73\n77 or 1 74 75\n78 or 1 76 77\n79 and 1 67 78\n80 bad 79 token-in-transit\n\n");

  // pc, program break, next file descriptor

  dprintf(output_fd, "81 neq 1 30 46\n82 and 1 67 81\n83 bad 82 pc-differs\n");
  dprintf(output_fd, "84 uext 2 35 32\n85 neq 1 84 49\n86 and 1 67 85\n87 bad 86 program-break-differs\n");
  dprintf(output_fd, "88 neq 1 36 50\n89 and 1 67 88\n90 bad 89 open-files-differ\n\n");

  abstraction_nid = 100;

  // registers and tapes by the same index in both models

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    print_difference(3, 31, i, 53, 0);

    dprintf(output_fd, "register-%lu-differs\n", i);

    i = i + 1;
  }

  i = 0;

  while (i < NUMBER_OF_TAPES) {
    print_difference(12, 37, i, 54, 0);

    dprintf(output_fd, "head-of-tape-%lu-differs\n", i);

    print_difference(12, 38, i, 57, 0);

    dprintf(output_fd, "end-of-tape-%lu-differs\n", i);

    print_difference(12, 39, i, 58, 0);

    dprintf(output_fd, "kind-of-tape-%lu-differs\n", i);

    print_difference(12, 40, i, 59, 0);

    dprintf(output_fd, "host-flag-of-tape-%lu-differs\n", i);

    i = i + 1;
  }

  // the words of memory and tapes, each in its segment or on its tape

  stack_start_address = VIRTUALMEMORYSIZE * GIGABYTE - stack_allowance;

  i = 0;

  while (i < number_of_words) {
    address = *(word_addresses + i);

    if (address >= INPUT_TAPES) {
      // tape of standard input
      print_difference(14, 41, (address - INPUT_TAPES) / WORDSIZE, 56, *(word_cells + i));

      dprintf(output_fd, "input-word-%lu-differs\n", (address - INPUT_TAPES) / WORDSIZE);
    } else if (address >= OUTPUT_TAPES) {
      // tape of the file descriptor times 4GB
      address = address - OUTPUT_TAPES;

      print_difference(14, 42, address / two_to_the_power_of(32) * TAPE_WORDS + address % two_to_the_power_of(32) / WORDSIZE, 56, *(word_cells + i));

      dprintf(output_fd, "output-word-%lu-of-tape-%lu-differs\n", address % two_to_the_power_of(32) / WORDSIZE, address / two_to_the_power_of(32));
    } else {
      if (address >= stack_start_address)
        print_difference(9, 34, (address - stack_start_address) / WORDSIZE, 56, *(word_cells + i));
      else if (address >= heap_start_address) {
        if (address - heap_start_address >= heap_allowance) {
          output_fd = STDOUT_FD;

          printf("%s: the word at 0x%lX is beyond the heap allowance of %lu bytes\n", selfie_name, address, heap_allowance);

          exit(EXITCODE_BADARGUMENTS);
        }

        print_difference(7, 33, (address - heap_start_address) / WORDSIZE, 56, *(word_cells + i));
      } else
        print_difference(5, 32, (address - data_start) / WORDSIZE, 56, *(word_cells + i));

      dprintf(output_fd, "word-at-0x%lX-differs\n", address);
    }

    i = i + 1;
  }

  output_name = (char*) 0;
  output_fd   = STDOUT_FD;

  printf("%s: abstraction for %lu words of memory and tapes written to %s\n", selfie_name, number_of_words, name);
}

// -----------------------------------------------------------------
// ---------------------------- HYBRID -----------------------------
// -----------------------------------------------------------------

// The hybrid simulator runs a RISC-R binary on the layout that the
// compiler would write, without laying it out: the instruction cells
// and the cells of the words act on the token by the procedures of the
// cell rule, and the wire in between is not followed but measured. The
// compiler lays wire on which the token never turns back, so the ticks
// of a transfer are the distance along its wire. With strips of the
// path of n instructions and p rows, of which S is the row in which
// control enters, strips of words whose combs have h rows, and c and
// a the first strips of the path that transfer control and access
// memory:
//
//   from an instruction to the next: 2 ticks, or 2 * n + 4 + p if
//   the next is in the next strip
//
//   from an instruction in strip s and column x to the one after the
//   come-from in strip t and column y: 2 * S + x + y + 4 ticks, and
//   (s + t - 2 * c) * p for the rows in between
//
//   from an instruction in strip s and column x to the word in column
//   w and row v and back to its side: 2 * x + 2 * w + 2 * v + 2 * h - 4
//   ticks, and 2 * (s - 2 * a) * p for the rows in between, and 2 more
//   to the next instruction after the last such leg
//
// See cellfie.md. Words are allocated when first accessed. Files are
// the host's, as in riscr: openat opens the file, read moves its bytes
// onto the input tape before the token gets there, write also writes
// the bytes to the file. Forward only.

uint64_t* word_in_store(uint64_t address) {
  uint64_t table;
  uint64_t offset;
  uint64_t* pages;
  uint64_t* page;

  // the word of memory or of a tape at address; assert: it has a cell

  if (address >= INPUT_TAPES)
    table = 1 + right_shift(address - INPUT_TAPES, 32);
  else if (address >= OUTPUT_TAPES)
    table = 1 + NUMBER_OF_TAPES + right_shift(address - OUTPUT_TAPES, 32);
  else
    table = 0;

  offset = get_bits(address, 3, 29);

  pages = (uint64_t*) *(store + table);

  if (pages == (uint64_t*) 0) {
    pages = zmalloc(STORE_PAGES * sizeof(uint64_t*));

    *(store + table) = (uint64_t) pages;
  }

  page = (uint64_t*) *(pages + offset / PAGE_WORDS);

  if (page == (uint64_t*) 0) {
    page = zmalloc(PAGE_WORDS * sizeof(uint64_t));

    *(pages + offset / PAGE_WORDS) = (uint64_t) page;
  }

  return page + offset % PAGE_WORDS;
}

void boot_store() {
  uint64_t i;
  uint64_t address;
  uint64_t value;

  // the words as the boot loader left the machine: the data segment, the
  // arguments on the stack, and the input on the tape of standard input

  store = zmalloc((1 + 2 * NUMBER_OF_TAPES) * sizeof(uint64_t*));

  i = 0;

  while (i < data_size / WORDSIZE) {
    *(word_in_store(data_start + i * WORDSIZE)) = initial_word(data_start + i * WORDSIZE);

    i = i + 1;
  }

  i = 0;

  while (i < stack_words) {
    address = VIRTUALMEMORYSIZE * GIGABYTE - (stack_words - i) * WORDSIZE;

    value = initial_word(address);

    if (value != 0)
      *(word_in_store(address)) = value;

    i = i + 1;
  }

  i = 0;

  while (i * WORDSIZE < input_size) {
    *(word_in_store(INPUT_TAPES + i * WORDSIZE)) = initial_word(INPUT_TAPES + i * WORDSIZE);

    i = i + 1;
  }

  // standard output and standard error are the host's

  host_fds = zmalloc(NUMBER_OF_TAPES * sizeof(uint64_t));

  *(host_fds + 1) = 1;
  *(host_fds + 2) = 2;
}

uint64_t* allocate_host_buffer(uint64_t words) {
  uint64_t i;

  // a buffer of that many words, all zero

  if (words > host_buffer_words) {
    host_buffer = smalloc(words * sizeof(uint64_t));

    host_buffer_words = words;
  }

  i = 0;

  while (i < words) {
    *(host_buffer + i) = 0;

    i = i + 1;
  }

  return host_buffer;
}

void host_openat() {
  uint64_t fd;
  uint64_t* filename;
  uint64_t address;
  uint64_t word;
  uint64_t flags;
  uint64_t i;
  uint64_t j;
  uint64_t found;
  uint64_t host_fd;

  // openat: whether the host can open the file whose name is in memory
  // at a1 is what the cell of the ecall goes by; the file descriptor of
  // the host is remembered, and the end of the file is not known yet

  fd = token_open_files % NUMBER_OF_TAPES;

  *(token_opens + fd) = 0;

  filename = allocate_host_buffer(MAX_FILENAME_LENGTH / WORDSIZE);

  address = get_token_register(REG_A1);

  found = 0;

  i = 0;

  while (and(found == 0, i < MAX_FILENAME_LENGTH / WORDSIZE)) {
    if (find_region(address + i * WORDSIZE) == number_of_regions)
      // the name is not in words that have a cell
      return;

    word = *(word_in_store(address + i * WORDSIZE));

    *(filename + i) = word;

    j = 0;

    while (j < WORDSIZE) {
      if (get_bits(word, j * 8, 8) == 0)
        found = 1;

      j = j + 1;
    }

    i = i + 1;
  }

  if (found == 0)
    return;

  flags = get_token_register(REG_A2);

  if (flags == LINUX_O_CREAT_TRUNC_WRONLY)
    // use correct flags for host operating system
    flags = O_CREAT_TRUNC_WRONLY;

  host_fd = sign_extend(open((char*) filename, flags, get_token_register(REG_A3)), SYSCALL_BITWIDTH);

  if (signed_less_than(host_fd, 0))
    return;

  *(host_fds + fd) = host_fd;

  *(token_opens + fd) = 1;
  *(token_ends + fd)  = -1;
}

void host_read() {
  uint64_t fd;
  uint64_t words;
  uint64_t size;
  uint64_t head;
  uint64_t* buffer;
  uint64_t bytes;
  uint64_t address;
  uint64_t i;

  // read: the bytes that the token is about to read from a file of the
  // host go onto its input tape at the head, zero beyond the end of the
  // file, which is known when fewer bytes are there than asked for

  if (not(is_transfer()))
    return;

  fd    = get_token_register(REG_A1) % NUMBER_OF_TAPES;
  words = transfer_words();
  size  = get_token_register(REG_A3);
  head  = *(token_heads + fd);

  if (fd < 3)
    // the input of standard input is on its tape
    return;
  else if (*(token_ends + fd) != (uint64_t) -1)
    return;

  buffer = allocate_host_buffer(words);

  bytes = sign_extend(read(*(host_fds + fd), buffer, size), SYSCALL_BITWIDTH);

  if (signed_less_than(bytes, 0))
    bytes = 0;

  i = 0;

  while (i < words) {
    address = INPUT_TAPES + left_shift(fd, 32) + (head + i) * WORDSIZE;

    // the token stops at a word of the tape that has no cell

    if (find_region(address) < number_of_regions)
      *(word_in_store(address)) = *(buffer + i);

    i = i + 1;
  }

  if (bytes < size)
    *(token_ends + fd) = head * WORDSIZE + bytes;
}

void host_write() {
  uint64_t fd;
  uint64_t words;
  uint64_t* buffer;
  uint64_t address;
  uint64_t i;

  // write: the bytes that the token is about to copy from memory onto
  // an output tape are written to the file of the host as well

  if (not(is_transfer()))
    return;

  fd    = get_token_register(REG_A1) % NUMBER_OF_TAPES;
  words = transfer_words();

  buffer = allocate_host_buffer(words);

  i = 0;

  while (i < words) {
    address = get_token_register(REG_A2) + i * WORDSIZE;

    if (find_region(address) == number_of_regions)
      // the token stops at a word of the buffer that has no cell
      return;

    *(buffer + i) = *(word_in_store(address));

    i = i + 1;
  }

  write(*(host_fds + fd), buffer, get_token_register(REG_A3));
}

void host_system_call() {
  uint64_t a7;

  // what the host does for a token on the path of an ecall cell

  a7 = get_token_register(REG_A7);

  if (a7 == SYSCALL_OPENAT)
    host_openat();
  else if (a7 == SYSCALL_READ)
    host_read();
  else if (a7 == SYSCALL_WRITE)
    host_write();
}

void run_hybrid(char* name) {
  uint64_t n;
  uint64_t i;
  uint64_t j;
  uint64_t x;
  uint64_t r;
  uint64_t address;
  uint64_t word;
  uint64_t property;
  uint64_t at;
  uint64_t strip;

  word  = 0;
  at    = 0;
  strip = 0;

  boot_binary(name, 1);

  plan_path();
  plan_regions();
  plan_rows();

  n = code_size / INSTRUCTIONSIZE;

  x = path_column + 2 * path_width + 2;

  if (x < word_column + two_to_the_power_of(strip_bits + 1) + 1)
    x = word_column + two_to_the_power_of(strip_bits + 1) + 1;

  set_grid_size(x, memory_in_row + memory_rows);

  boot_token();
  boot_store();

  printf("%s: %lu instructions of %s on a grid of %lux%lu cells, not laid out: %lu transfer control, %lu access memory, %lu words\n", selfie_name,
    n, name, grid_width, grid_height, controls, accesses, number_of_region_words);

  reverse = 0;

  property = PROPERTY_NONE;

  while (property == PROPERTY_NONE) {
    // the token is on the path of the instruction cell of its pc, if there is one

    i = (token_pc - code_start) / INSTRUCTIONSIZE;

    if (token_pc < code_start)
      property = PROPERTY_INVALID_PC;
    else if (token_pc % INSTRUCTIONSIZE != 0)
      property = PROPERTY_INVALID_PC;
    else if (i >= n)
      property = PROPERTY_INVALID_PC;
    else {
      at = i;

      strip = i / path_width;

      x = path_column + 2 * (i % path_width);

      token_x = x;
      token_y = strip * path_pitch + path_row;

      word = load_instruction(i * INSTRUCTIONSIZE);

      property = instruction_property(word);
    }

    if (property == PROPERTY_NONE) {
      if (is == ECALL)
        host_system_call();

      if (*(instruction_classes + i) == CLASS_ACCESS) {
        act_instruction(EAST, BACKSLASH, word);

        while (token_heading == SOUTH) {
          // a leg to the word at the address of the token and back to the side of the cell

          address = token_address;

          r = find_region(address);

          if (r == number_of_regions) {
            property = PROPERTY_INVALID_ADDRESS;

            token_heading = EAST;
          } else {
            if (*(region_kinds + r) == CELL_TAPE)
              act_tape(word_in_store(address));
            else
              act_memory(word_in_store(address));

            // the column and the row of the word

            j = get_word_strip(address, r);
            j = get_word_column(address, j) + get_word_row(j);

            executed_ticks = executed_ticks + 2 * x + 2 * j + 2 * strip_height - 4;

            // the rows of the strips of the path on the way

            executed_ticks = executed_ticks + 2 * (strip - first_access_strip) * path_pitch;
            executed_ticks = executed_ticks - 2 * first_access_strip * path_pitch;

            act_instruction(EAST, BACKSLASH, word);
          }
        }
      } else {
        act_instruction(EAST, SLASH, word);

        if (token_heading == NORTH) {
          // to the come-from at the pc of the token, which must be one

          j = (token_pc - code_start) / INSTRUCTIONSIZE;

          if (token_pc < code_start)
            property = PROPERTY_INVALID_PC;
          else if (token_pc % INSTRUCTIONSIZE != 0)
            property = PROPERTY_INVALID_PC;
          else if (j >= n)
            property = PROPERTY_INVALID_PC;
          else if (*(instruction_classes + j) != CLASS_CONTROL)
            property = PROPERTY_INVALID_PC;
          else {
            at = j;

            token_x = path_column + 2 * (j % path_width);
            token_y = j / path_width * path_pitch + path_row;

            executed_ticks = executed_ticks + 2 * control_spine_row + x + token_x + 2;

            // the rows of the strips of the path on the way

            j = strip + j / path_width - 2 * first_control_strip;

            executed_ticks = executed_ticks + j * path_pitch;

            j = at;

            act_instruction(EAST, SLASH, load_instruction(j * INSTRUCTIONSIZE));

            if (token_heading != EAST)
              // the come-from does not take the token
              property = PROPERTY_INVALID_PC;
          }
        }
      }

      if (property == PROPERTY_NONE) {
        // to the next instruction on the path, which may be in the next strip

        executed_ticks = executed_ticks + 2;

        if (at % path_width == path_width - 1)
          if (at + 1 < n)
            executed_ticks = executed_ticks + 2 * path_width + 2 + path_pitch;
      }
    }
  }

  token_heading = EAST;

  print_stop(property);
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
    else if (string_compare(argument, "-c"))
      compile_layout(get_argument());
    else if (string_compare(argument, "-i"))
      input_name = get_argument();
    else if (string_compare(argument, "-h"))
      run_hybrid(get_argument());
    else if (string_compare(argument, "-tapes")) {
      NUMBER_OF_TAPES = atoi(get_argument());

      if (NUMBER_OF_TAPES < 4)
        return EXITCODE_BADARGUMENTS;
      else if (NUMBER_OF_TAPES != two_to_the_power_of(log_two(NUMBER_OF_TAPES)))
        return EXITCODE_BADARGUMENTS;
      else if (token_registers != (uint64_t*) 0)
        // the token has its tapes already
        return EXITCODE_BADARGUMENTS;

      tape_files = NUMBER_OF_TAPES;
    } else if (string_compare(argument, "-tapewords"))
      TAPE_WORDS = atoi(get_argument());
    else if (string_compare(argument, "-stack"))
      stack_words = atoi(get_argument());
    else if (string_compare(argument, "-heap")) {
      if (number_of_remaining_arguments() < 2)
        return EXITCODE_BADARGUMENTS;
      else if (number_of_heap_regions >= MAX_HEAP_REGIONS)
        return EXITCODE_BADARGUMENTS;

      if (heap_offsets == (uint64_t*) 0) {
        heap_offsets = zmalloc(MAX_HEAP_REGIONS * sizeof(uint64_t));
        heap_words   = zmalloc(MAX_HEAP_REGIONS * sizeof(uint64_t));
      }

      *(heap_offsets + number_of_heap_regions) = atoi(get_argument());
      *(heap_words + number_of_heap_regions)   = atoi(get_argument());

      number_of_heap_regions = number_of_heap_regions + 1;
    } else if (string_compare(argument, "-a")) {
      if (number_of_remaining_arguments() < 3)
        return EXITCODE_BADARGUMENTS;

      name = get_argument();

      width  = atoi(get_argument());
      height = atoi(get_argument());

      write_abstraction(name, width, height);
    }
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
  init_kernel();

  // the layout compiler uses selfie's binary and boot loader
  init_register();
  init_interpreter();
  init_disassembler();

  init_model();

  INPUT_TAPES  = two_to_the_power_of(63);
  OUTPUT_TAPES = two_to_the_power_of(62);

  exit_code = cellfie();

  // selfie's strings are short, the options are in the comment at the top
  return exit_selfie(exit_code, " { -l layout | -c binary | -o layout | -f ticks | -b ticks | -rev ticks | -btor2 width height | -check states | -h binary ... }");
}
