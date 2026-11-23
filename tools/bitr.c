/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

Bitr is a bounded model checker for BTOR2 models in C*, built up in
layers, see projects/reversible.md. It reads BTOR2 and nothing else:
models come from rotor or cellfie, programs and input enter only as
initial state through its loaders. The first layer (M4) is a parser
for the BTOR2 subset rotor emits, loaders that put an ELF binary into
the code and data segments and a file onto the input tape of a model,
and a concrete simulator that runs a model step by step until it
halts, hits a bad state, or violates a constraint. The model data
structure and the evaluator are tools/btor2.h, shared with rotor.

The second layer (M5) is symbolic: a bit-blaster from BTOR2 to an
and-inverter graph with constant folding and structural hashing, a
CDCL SAT solver, a bounded model checker that follows the control
flow of the model path by path and asks the solver only where a path
forks or may reach a bad state, and a prover that one model undoes
another, by cases over all choices the two models make.

Usage: bitr model.btor2 [ -l binary ] [ -i file ] [ -grid layout ] [ -k steps ] [ -p ]
       bitr model.btor2 [ -l binary ] -bmc steps [ -all ] [ -w file ] [ -dimacs prefix limit ] [ -v ]
       bitr model.btor2 -identity inverse.btor2 [ -k steps ] [ -all ] [ -v ]
       bitr model.btor2 [ -l binary ] -product other.btor2 [ -grid layout ] -abstraction map.btor2 [ -k steps ]
       bitr -sat file.cnf

-l loads the code and data of binary into the model's code and data
segment states, checking them against words the model holds already;
-i puts file onto the model's input tape (RISC-R) or input buffer
(RISC-U); -grid loads the cells and the token of a cellfie layout
into the states of cellfie's model; -k bounds the number of steps;
-p prints the program counter at every step. Bitr reports the first bad state or violated
constraint and the number of instructions executed until then.

-bmc checks all inputs at once: state that the model leaves
uninitialized and no loader fills is free. Bitr reports the first
bad state reachable within the given number of steps with an input
that reaches it, which -w writes to a file to replay in an emulator;
-all reports a bad state for every such input and whether all other
inputs halt; -dimacs writes each SAT instance with at most limit
variables as prefix-n.cnf; -v reports progress.

-identity proves that steps of the model followed by as many steps
of the inverse model lead back to the state they started in, for
every state that satisfies the constraints of the model and is not
bad; the models share their states by name. One step is the default.
Bitr reports the first state it finds not restored, with -all all.

-product runs the model and another model together, concretely: the
other model step by step, the model only in the steps in which the
output step of the abstraction holds. The abstraction is a third
BTOR2 file whose states are states of the two models by name and
whose bad states are where the two differ. Bitr reports the first
step in which they differ or only one of them stops, or that they
agree until both stop together. This is how cellfie's cell rule on
a layout is compared with rotor's RISC-R model of a binary.

-sat runs the CDCL solver on a DIMACS CNF file.
*/

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------------- BITR ------------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- PARSER -----------------------------
// -----------------------------------------------------------------

uint64_t* read_whole_file(char* name);

uint64_t  model_character();
void      next_model_character();
void      skip_blanks();
uint64_t  at_end_of_line();
void      skip_line();
char*     scan_token();
char*     scan_comment();

uint64_t  parse_decimal(char* token);
uint64_t  parse_hexadecimal(char* token);
uint64_t  parse_binary(char* token);

uint64_t* line_of_nid(uint64_t nid);
void      set_line_of_nid(uint64_t nid, uint64_t* line);
uint64_t* line_of_token(char* token);

char*     canonical_op(char* token);

void      parse_error(char* message);
void      parse_model();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t READ_CHUNK = 1048576; // 1MB per read

// ------------------------ GLOBAL VARIABLES -----------------------

char*    model_name = (char*) 0;

char*    model_text = (char*) 0; // model file in memory
uint64_t model_size = 0;         // in bytes
uint64_t model_pos  = 0;         // current character
uint64_t model_line = 1;         // current line number

uint64_t* nid_lines = (uint64_t*) 0; // line of each nid
uint64_t  nid_limit = 0;             // size of nid_lines
uint64_t  max_nid   = 0;

uint64_t* init_lines = (uint64_t*) 0; // init line of each state nid

uint64_t number_of_sorts      = 0;
uint64_t number_of_states     = 0;
uint64_t number_of_inits      = 0;
uint64_t number_of_nexts      = 0;
uint64_t number_of_bads       = 0;
uint64_t number_of_constraints = 0;

// -----------------------------------------------------------------
// ---------------------------- LOADERS ----------------------------
// -----------------------------------------------------------------

uint64_t* find_state(char* symbol);
uint64_t  array_elements(uint64_t* state_nid);
uint64_t  array_element_size(uint64_t* state_nid);

void load_words(uint64_t* state_nid, uint64_t start, uint64_t size, uint64_t binary);
void load_binary(char* name);
void load_input(char* name);

uint64_t layout_character();
void     layout_error(char* message);
void     skip_layout_blanks(uint64_t lines);
uint64_t scan_layout_decimal();
uint64_t scan_layout_hexadecimal(uint64_t digits);
uint64_t scan_layout_mirror();
uint64_t scan_layout_heading(uint64_t c);

uint64_t* find_layout_state(char* symbol);

void load_layout(char* name);

void load_files();

// ------------------------ GLOBAL VARIABLES -----------------------

char* binary_file = (char*) 0;
char* input_file  = (char*) 0;
char* layout_file = (char*) 0;

uint64_t* layout_text = (uint64_t*) 0; // layout file in memory
uint64_t  layout_size = 0;             // in bytes
uint64_t  layout_pos  = 0;             // current character
uint64_t  layout_line = 1;             // current line number

uint64_t loaded_words   = 0;
uint64_t checked_words  = 0;
uint64_t mismatched_words = 0;

// -----------------------------------------------------------------
// --------------------------- SIMULATOR ---------------------------
// -----------------------------------------------------------------

void     init_states();
uint64_t check_properties();
uint64_t simulate();

uint64_t* violated_property();

void parse_next_model(char* name);

void bind_abstraction();
void eval_nexts();
void apply_nexts();
void skip_nexts();

uint64_t product();

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t max_steps   = 0; // bound on steps, 0 for none
uint64_t printing_pc = 0; // print pc at every step

uint64_t* pc_state_nid = (uint64_t*) 0;

// product of two models: the second model, the abstraction that relates
// its states to the states of the first, and the models as records

char* OP_OUTPUT = (char*) 0; // output lines name what an abstraction computes

char* product_model_name     = (char*) 0;
char* abstraction_model_name = (char*) 0;

uint64_t MODEL_RECORD_SIZE = 16;

uint64_t* abstraction_states = (uint64_t*) 0; // states of the abstraction
uint64_t* abstracted_states  = (uint64_t*) 0; // and the states of the models they stand for

uint64_t number_of_abstraction_states = 0;

// -----------------------------------------------------------------
// -------------------------- BIT BLASTER --------------------------
// -----------------------------------------------------------------

uint64_t* grow_words(uint64_t* words, uint64_t old_size, uint64_t new_size);

void     init_aig();
uint64_t aig_not(uint64_t l);
uint64_t aig_new_node(uint64_t left, uint64_t right);
uint64_t aig_input();
uint64_t aig_is_input(uint64_t node);
uint64_t aig_hash(uint64_t a, uint64_t b);
void     aig_rehash();
uint64_t aig_and(uint64_t a, uint64_t b);
uint64_t aig_or(uint64_t a, uint64_t b);
uint64_t aig_xor(uint64_t a, uint64_t b);
uint64_t aig_mux(uint64_t s, uint64_t a, uint64_t b);

void      init_bit_vectors();
uint64_t  bv_width(uint64_t* bv);
uint64_t  bv_lit(uint64_t* bv, uint64_t i);
void      bv_set(uint64_t* bv, uint64_t i, uint64_t l);
uint64_t* bv_new(uint64_t w);
uint64_t  bv_hash(uint64_t* bv);
uint64_t  bv_equal(uint64_t* a, uint64_t* b);
void      bv_rehash();
uint64_t* bv_intern(uint64_t* bv);
uint64_t* bv_constant(uint64_t value, uint64_t w);
uint64_t  bv_is_constant(uint64_t* a);
uint64_t  bv_value(uint64_t* a);
uint64_t* bv_fresh(uint64_t w);
uint64_t* bv_bool(uint64_t l);
uint64_t* bv_not(uint64_t* a);
uint64_t* bv_bitwise(uint64_t* a, uint64_t* b, uint64_t op);
uint64_t* bv_ite(uint64_t c, uint64_t* a, uint64_t* b);
uint64_t* bv_add(uint64_t* a, uint64_t* b, uint64_t carry);
uint64_t* bv_sub(uint64_t* a, uint64_t* b);
uint64_t* bv_neg(uint64_t* a);
uint64_t  bv_eq(uint64_t* a, uint64_t* b);
uint64_t  bv_uge(uint64_t* a, uint64_t* b, uint64_t is_signed);
uint64_t* bv_shift(uint64_t* a, uint64_t* s, uint64_t kind);
uint64_t* bv_mul(uint64_t* a, uint64_t* b);
uint64_t* bv_udivrem(uint64_t* a, uint64_t* b, uint64_t remainder);
uint64_t* bv_sdivrem(uint64_t* a, uint64_t* b, uint64_t remainder);
uint64_t* bv_ext(uint64_t* a, uint64_t extra, uint64_t is_signed);
uint64_t* bv_slice(uint64_t* a, uint64_t u, uint64_t l);
uint64_t* bv_concat(uint64_t* a, uint64_t* b);

void      init_arrays();
uint64_t  arr_new(uint64_t kind, uint64_t x, uint64_t y, uint64_t z, uint64_t iw, uint64_t ew);
uint64_t  arr_base(uint64_t* state_nid, uint64_t symbolic);
uint64_t  arr_write(uint64_t a, uint64_t* index, uint64_t* value);
uint64_t  arr_ite(uint64_t c, uint64_t a, uint64_t b);
uint64_t* arr_element(uint64_t a, uint64_t index);
uint64_t* arr_base_read(uint64_t a, uint64_t* index, uint64_t bit, uint64_t prefix);
uint64_t  memo_hash(uint64_t a, uint64_t* index);
void      memo_rehash();
uint64_t* arr_read(uint64_t a, uint64_t* index);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t AIG_FALSE = 0;
uint64_t AIG_TRUE  = 1;
uint64_t AIG_INPUT = -1; // left child of an input node

uint64_t BV_SCRATCH_SIZE = 1048576; // in words
uint64_t BV_STORE_CHUNK  = 1048576; // in words

uint64_t ARR_BASE  = 1;
uint64_t ARR_WRITE = 2;
uint64_t ARR_ITE   = 3;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* aig_left  = (uint64_t*) 0; // left child of each node
uint64_t* aig_right = (uint64_t*) 0; // right child of each node

uint64_t aig_nodes    = 0;
uint64_t aig_capacity = 0;

uint64_t* aig_table      = (uint64_t*) 0; // structural hash table of and-nodes
uint64_t  aig_table_size = 0;

uint64_t aig_ands   = 0;
uint64_t aig_inputs = 0;

uint64_t* aig_mark = (uint64_t*) 0; // cone a node was last part of
uint64_t* aig_var  = (uint64_t*) 0; // its variable in that cone

uint64_t* aig_assumed = (uint64_t*) 0; // per node: 1 if assumed true on the current path, 2 if false

uint64_t* assumed_nodes = (uint64_t*) 0; // nodes assumed, in order
uint64_t  assumed_count = 0;
uint64_t  assumed_capacity = 0;

uint64_t deciding      = 0; // evaluating on a path: choices are decided by what the path assumes
uint64_t pending_split = 0; // first literal met that the path does not decide yet
uint64_t cofactoring   = 0; // building the cofactor of a literal by what the path assumes

uint64_t* cofactor_stamps = (uint64_t*) 0; // per node: the assumptions its cofactor was built for
uint64_t* cofactor_values = (uint64_t*) 0; // and that cofactor

uint64_t assumption_epoch = 1; // changes whenever what the path assumes changes

uint64_t UNDO_ADD = 1;
uint64_t UNDO_SUB = 2;
uint64_t UNDO_XOR = 3;

uint64_t* undo_results = (uint64_t*) 0; // results of additions, subtractions, exclusive ors,
uint64_t* undo_kinds   = (uint64_t*) 0; // their kind,
uint64_t* undo_lefts   = (uint64_t*) 0; // and their operands,
uint64_t* undo_rights  = (uint64_t*) 0; // so that the inverse operation finds the operand back

uint64_t undo_size  = 0;
uint64_t undo_count = 0;

uint64_t* bv_scratch     = (uint64_t*) 0;
uint64_t  bv_scratch_top = 0;

uint64_t* bv_store     = (uint64_t*) 0;
uint64_t  bv_store_top = 0;

uint64_t* bv_table      = (uint64_t*) 0;
uint64_t  bv_table_size = 0;
uint64_t  bv_count      = 0;

uint64_t bv_carry = 0; // carry out of the most recent addition

uint64_t* arr_kind = (uint64_t*) 0;
uint64_t* arr_x    = (uint64_t*) 0;
uint64_t* arr_y    = (uint64_t*) 0;
uint64_t* arr_z    = (uint64_t*) 0;
uint64_t* arr_iw   = (uint64_t*) 0; // index width
uint64_t* arr_ew   = (uint64_t*) 0; // element width

uint64_t arr_count    = 0;
uint64_t arr_capacity = 0;

uint64_t* memo_array = (uint64_t*) 0; // reads done: array,
uint64_t* memo_index = (uint64_t*) 0; // index,
uint64_t* memo_value = (uint64_t*) 0; // and result

uint64_t memo_size  = 0;
uint64_t memo_count = 0;

// -----------------------------------------------------------------
// ----------------------------- CDCL ------------------------------
// -----------------------------------------------------------------

uint64_t sat_negate(uint64_t l);
uint64_t sat_lit_value(uint64_t l);
void     sat_reset(uint64_t variables);
void     sat_heap_up(uint64_t position);
void     sat_heap_down(uint64_t position);
void     sat_heap_insert(uint64_t v);
uint64_t sat_heap_pop();
void     sat_bump(uint64_t v);
void     sat_watch(uint64_t l, uint64_t clause);
void     sat_enqueue(uint64_t l, uint64_t reason);
uint64_t sat_new_clause(uint64_t* literals, uint64_t n);
void     sat_add_clause(uint64_t* literals, uint64_t n);
uint64_t sat_propagate();
void     sat_cancel_until(uint64_t level);
uint64_t sat_analyze(uint64_t conflict);
uint64_t sat_luby(uint64_t i);
void     sat_reduce();
uint64_t sat_solve();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t SAT_UNASSIGNED = 0;
uint64_t SAT_TRUE       = 1;
uint64_t SAT_FALSE      = 2;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t sat_variables = 0;
uint64_t sat_capacity  = 0; // variables the solver has memory for, plus one

uint64_t* sat_values     = (uint64_t*) 0; // per variable
uint64_t* sat_levels     = (uint64_t*) 0; // decision level of its assignment
uint64_t* sat_reasons    = (uint64_t*) 0; // clause that implied it, 0 if decided
uint64_t* sat_activities = (uint64_t*) 0;
uint64_t* sat_phases     = (uint64_t*) 0; // its most recent value
uint64_t* sat_seen       = (uint64_t*) 0;
uint64_t* sat_positions  = (uint64_t*) 0; // its position in the heap plus one

uint64_t* sat_trail  = (uint64_t*) 0; // assigned literals in order
uint64_t* sat_starts = (uint64_t*) 0; // trail size at each decision
uint64_t* sat_heap   = (uint64_t*) 0; // variables by activity
uint64_t* sat_learnt = (uint64_t*) 0; // most recent learnt clause
uint64_t* sat_keep   = (uint64_t*) 0; // which of its literals are not redundant

uint64_t sat_first_learnt = 0; // first learnt clause
uint64_t sat_reductions   = 0;

uint64_t sat_learnt_size = 0;

uint64_t* sat_watches          = (uint64_t*) 0; // per literal: clauses watching it
uint64_t* sat_watch_sizes      = (uint64_t*) 0;
uint64_t* sat_watch_capacities = (uint64_t*) 0;

uint64_t* sat_db          = (uint64_t*) 0; // clauses: size followed by literals
uint64_t  sat_db_size     = 0;
uint64_t  sat_db_capacity = 0;

uint64_t sat_trail_size = 0;
uint64_t sat_head       = 0; // next literal on the trail to propagate
uint64_t sat_level      = 0;
uint64_t sat_heap_size  = 0;
uint64_t sat_increment  = 1;

uint64_t sat_inconsistent = 0;

uint64_t sat_clauses   = 0;
uint64_t sat_conflicts = 0;
uint64_t sat_decisions = 0;
uint64_t sat_restarts  = 0;

// -----------------------------------------------------------------
// ------------------------------ CNF ------------------------------
// -----------------------------------------------------------------

uint64_t cnf_build(uint64_t root);
uint64_t cnf_literal(uint64_t l);
void     cnf_solver(uint64_t root);
void     cnf_print_literal(uint64_t fd, uint64_t l);
void     cnf_dimacs(uint64_t root);

uint64_t aig_model(uint64_t l);
uint64_t aig_solve(uint64_t root);

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* cone_nodes  = (uint64_t*) 0; // nodes of the current cone in post-order
uint64_t* cone_stack  = (uint64_t*) 0;
uint64_t* cone_values = (uint64_t*) 0; // value of each variable in the model

uint64_t cone_capacity = 0;
uint64_t cone_size     = 0;
uint64_t cone_id       = 0;

uint64_t* cnf_clause = (uint64_t*) 0;

uint64_t model_is_trivial = 0;

char*    dimacs_prefix = (char*) 0; // write each CNF as prefix-n.cnf
uint64_t dimacs_limit  = 0;         // if it has at most this many variables, 0 for no limit
uint64_t dimacs_files  = 0;

uint64_t sat_calls           = 0;
uint64_t sat_max_variables   = 0;
uint64_t sat_total_variables = 0;
uint64_t sat_total_clauses   = 0;
uint64_t sat_total_conflicts = 0;
uint64_t sat_total_decisions = 0;

// -----------------------------------------------------------------
// --------------------- BOUNDED MODEL CHECKER ---------------------
// -----------------------------------------------------------------

uint64_t assumed_value(uint64_t l);
uint64_t assume_literal(uint64_t l);
void     undo_assumptions(uint64_t mark);
uint64_t decide(uint64_t l);

uint64_t aig_cofactor(uint64_t l);

void      undo_record(uint64_t* result, uint64_t kind, uint64_t* a, uint64_t* b);
uint64_t  undo_find(uint64_t* result);
uint64_t* bv_add_normal(uint64_t* a, uint64_t* b);
uint64_t* bv_sub_normal(uint64_t* a, uint64_t* b);
uint64_t* bv_xor_normal(uint64_t* a, uint64_t* b);
uint64_t  bv_eq_normal(uint64_t* a, uint64_t* b);

uint64_t* arr_probe(uint64_t a, uint64_t* index);

uint64_t width_of(uint64_t* line);
uint64_t sym_bit(uint64_t* line);
uint64_t sym_eval(uint64_t* line);
void     sym_init(uint64_t all_symbolic);

uint64_t bv_model(uint64_t* a);
uint64_t sym_element_model(uint64_t* state_nid, uint64_t index);
uint64_t sym_block_model(uint64_t limit);
void     write_witness();

void     sym_cases(uint64_t* line, uint64_t guard);
void     init_paths();
void     add_next_path(uint64_t guard, uint64_t* states);
uint64_t check_bads(uint64_t guard, uint64_t t);

uint64_t bmc();
void     print_bmc_statistics();

void     save_model(uint64_t* model);
void     restore_model(uint64_t* model);
void     assume(uint64_t l);
void     sym_assume_frame();
uint64_t aig_evaluate(uint64_t l);
uint64_t bv_evaluate(uint64_t* a);
uint64_t solve_on_path(uint64_t goal);
void     check_state_at(uint64_t* line, uint64_t* index);
void     sym_step_frame();
uint64_t evaluate_path();
void     check_state(uint64_t* line);
void     check_path();
void     prove_paths();
uint64_t prove_identity();

uint64_t dimacs_pass(uint64_t checking);
uint64_t solve_dimacs();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t MAX_CASES = 64; // constants a bit-vector state may choose between when forking

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* uninitialized_states = (uint64_t*) 0; // per nid: state without init and not loaded

uint64_t* state_slots = (uint64_t*) 0; // per state nid: its slot in the states of a path
uint64_t* slot_nids   = (uint64_t*) 0; // per slot: its state nid

uint64_t number_of_slots = 0;

uint64_t* path_guards = (uint64_t*) 0; // per path: literal that is true on the path
uint64_t* path_states = (uint64_t*) 0; // per path: value of each state
uint64_t* next_guards = (uint64_t*) 0; // the same for the paths of the next frame
uint64_t* next_states = (uint64_t*) 0;

uint64_t path_capacity        = 0;
uint64_t number_of_paths      = 0;
uint64_t number_of_next_paths = 0;

uint64_t* case_guards = (uint64_t*) 0; // cases of the most recent decomposition
uint64_t* case_values = (uint64_t*) 0;

uint64_t number_of_cases = 0;
uint64_t cases_constant  = 0;
uint64_t cases_visited   = 0;

uint64_t* fork_slots  = (uint64_t*) 0; // forking states of a frame and their cases
uint64_t* fork_firsts = (uint64_t*) 0;
uint64_t* fork_counts = (uint64_t*) 0;
uint64_t* fork_guards = (uint64_t*) 0;
uint64_t* fork_values = (uint64_t*) 0;

uint64_t blocked = 1; // literal that excludes all witnesses found so far

uint64_t forked_paths = 0;
uint64_t halted_paths = 0;
uint64_t max_paths    = 1;

uint64_t* sym_values = (uint64_t*) 0; // per nid: value in the frame of its stamp
uint64_t* sym_stamps = (uint64_t*) 0;
uint64_t* sym_states = (uint64_t*) 0; // per state nid: current value
uint64_t* sym_nexts  = (uint64_t*) 0; // per next nid: next value
uint64_t* sym_bases  = (uint64_t*) 0; // per state nid: initial value
uint64_t* sym_free   = (uint64_t*) 0; // per state nid: initial value is free
uint64_t* bad_lits   = (uint64_t*) 0; // per bad nid: literal in the current frame

uint64_t sym_frame = 0;

uint64_t checking_bmc  = 0; // bounded model checking instead of simulating
uint64_t verbose       = 0; // report progress per frame
uint64_t stop_at_first = 1; // stop at the first bad state found

uint64_t PATH_INFEASIBLE = 0;
uint64_t PATH_SPLIT      = 1;
uint64_t PATH_COMPLETE   = 2;

uint64_t* state_map          = (uint64_t*) 0; // state of the first model per state of the second
uint64_t* difference_indices = (uint64_t*) 0; // per array state: the free index at which it is compared
uint64_t* solved_paths       = (uint64_t*) 0; // per state: paths on which the solver had to prove it
uint64_t* failed_paths       = (uint64_t*) 0; // per state: paths on which it is not restored

uint64_t complete_paths   = 0;
uint64_t infeasible_paths = 0;
uint64_t solver_conflicts = 0;
uint64_t counterexamples  = 0;

char* second_model_name = (char*) 0; // model that undoes the first, for proving identity

uint64_t* assumptions = (uint64_t*) 0; // literals assumed: constraints, and bad states negated

uint64_t number_of_assumptions = 0;
uint64_t assumption_capacity   = 0;

uint64_t* eval_marks  = (uint64_t*) 0; // per node: evaluation it was last part of
uint64_t* eval_values = (uint64_t*) 0; // and its value then
uint64_t* eval_stack  = (uint64_t*) 0;

uint64_t eval_capacity = 0;
uint64_t eval_id       = 0;

uint64_t* first_model  = (uint64_t*) 0; // parser and symbolic tables of the first model
uint64_t* second_model = (uint64_t*) 0; // and of the second

char*    witness_file = (char*) 0; // file to write the input of a bad state to
uint64_t witnesses    = 0;

uint64_t* dimacs_clause = (uint64_t*) 0;

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

uint64_t bitr();

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------------- PARSER -----------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t* read_whole_file(char* name) {
  uint64_t fd;
  uint64_t* buffer;
  uint64_t capacity;
  uint64_t* bigger;
  uint64_t bytes;

  // reads the file into a word-aligned buffer, model_size is its length in bytes

  fd = open_read_only(name);

  if (signed_less_than(fd, 0)) {
    printf("%s: could not open %s\n", selfie_name, name);

    exit(EXITCODE_IOERROR);
  }

  capacity = READ_CHUNK;
  buffer   = touch(zmalloc(capacity + READ_CHUNK), capacity + READ_CHUNK);

  model_size = 0;

  // mipster only reads into mapped memory at word-aligned addresses, so
  // the buffer is touched, and a short read is the end of the file

  bytes = READ_CHUNK;

  while (bytes == READ_CHUNK) {
    bytes = sign_extend(read(fd, (uint64_t*) ((uint64_t) buffer + model_size), READ_CHUNK), SYSCALL_BITWIDTH);

    if (signed_less_than(0, bytes)) {
      model_size = model_size + bytes;

      if (model_size + READ_CHUNK > capacity) {
        bigger = touch(zmalloc(2 * capacity + READ_CHUNK), 2 * capacity + READ_CHUNK);

        memcopy(bigger, buffer, round_up(model_size, sizeof(uint64_t)));

        buffer   = bigger;
        capacity = 2 * capacity;
      }
    }
  }

  return buffer;
}

uint64_t model_character() {
  if (model_pos < model_size)
    return load_character(model_text, model_pos);
  else
    return 0;
}

void next_model_character() {
  if (model_character() == 10)
    model_line = model_line + 1;

  model_pos = model_pos + 1;
}

void skip_blanks() {
  while (model_pos < model_size) {
    if (model_character() == 32)
      next_model_character();
    else if (model_character() == 9)
      next_model_character();
    else if (model_character() == 13)
      next_model_character();
    else
      return;
  }
}

uint64_t at_end_of_line() {
  if (model_pos >= model_size)
    return 1;
  else
    return model_character() == 10;
}

void skip_line() {
  while (not(at_end_of_line()))
    next_model_character();

  if (model_pos < model_size)
    next_model_character();
}

char* scan_token() {
  uint64_t start;
  uint64_t scanning;
  uint64_t c;
  uint64_t length;
  char* token;
  uint64_t i;

  // the next blank-separated token on the current line, or 0

  skip_blanks();

  start = model_pos;

  scanning = not(at_end_of_line());

  while (scanning) {
    c = model_character();

    if (c == 32)
      scanning = 0;
    else if (c == 9)
      scanning = 0;
    else if (c == 13)
      scanning = 0;
    else if (c == 59)
      // semicolon starts a comment
      scanning = 0;
    else {
      next_model_character();

      scanning = not(at_end_of_line());
    }
  }

  length = model_pos - start;

  if (length == 0)
    return (char*) 0;

  token = (char*) zmalloc(round_up(length + 1, sizeof(uint64_t)));

  i = 0;

  while (i < length) {
    store_character(token, i, load_character(model_text, start + i));

    i = i + 1;
  }

  return token;
}

char* scan_comment() {
  uint64_t start;
  uint64_t length;
  char* comment;
  uint64_t i;

  // the rest of the line after a semicolon, or 0

  skip_blanks();

  if (at_end_of_line())
    return (char*) 0;

  if (model_character() != 59)
    parse_error("comment expected");

  next_model_character();

  skip_blanks();

  start = model_pos;

  while (not(at_end_of_line()))
    next_model_character();

  length = model_pos - start;

  comment = (char*) zmalloc(round_up(length + 1, sizeof(uint64_t)));

  i = 0;

  while (i < length) {
    store_character(comment, i, load_character(model_text, start + i));

    i = i + 1;
  }

  return comment;
}

uint64_t parse_decimal(char* token) {
  uint64_t negative;
  uint64_t value;
  uint64_t i;
  uint64_t c;

  negative = 0;
  value    = 0;
  i        = 0;

  if (load_character(token, 0) == 45) {
    negative = 1;

    i = 1;
  }

  c = load_character(token, i);

  if (c == 0)
    parse_error("decimal number expected");

  while (c != 0) {
    if (c < 48)
      parse_error("decimal digit expected");
    else if (c > 57)
      parse_error("decimal digit expected");

    value = value * 10 + (c - 48);

    i = i + 1;

    c = load_character(token, i);
  }

  if (negative)
    return -value;
  else
    return value;
}

uint64_t parse_hexadecimal(char* token) {
  uint64_t value;
  uint64_t i;
  uint64_t c;

  value = 0;
  i     = 0;

  c = load_character(token, 0);

  if (c == 0)
    parse_error("hexadecimal number expected");

  while (c != 0) {
    if (c >= 48)
      if (c <= 57)
        value = value * 16 + (c - 48);
      else if (c >= 65)
        if (c <= 70)
          value = value * 16 + (c - 55);
        else if (c >= 97)
          if (c <= 102)
            value = value * 16 + (c - 87);
          else
            parse_error("hexadecimal digit expected");
        else
          parse_error("hexadecimal digit expected");
      else
        parse_error("hexadecimal digit expected");
    else
      parse_error("hexadecimal digit expected");

    i = i + 1;

    c = load_character(token, i);
  }

  return value;
}

uint64_t parse_binary(char* token) {
  uint64_t value;
  uint64_t i;
  uint64_t c;

  value = 0;
  i     = 0;

  c = load_character(token, 0);

  if (c == 0)
    parse_error("binary number expected");

  while (c != 0) {
    if (c == 48)
      value = value * 2;
    else if (c == 49)
      value = value * 2 + 1;
    else
      parse_error("binary digit expected");

    i = i + 1;

    c = load_character(token, i);
  }

  return value;
}

uint64_t* line_of_nid(uint64_t nid) {
  if (nid < nid_limit)
    if (nid > 0)
      return (uint64_t*) *(nid_lines + nid);

  return UNUSED;
}

void set_line_of_nid(uint64_t nid, uint64_t* line) {
  uint64_t* bigger;
  uint64_t  bigger_limit;

  if (nid == 0)
    parse_error("nid must be positive");

  if (nid >= nid_limit) {
    bigger_limit = nid_limit;

    if (bigger_limit == 0)
      bigger_limit = 1024;

    while (bigger_limit <= nid)
      bigger_limit = bigger_limit * 2;

    bigger = zmalloc(bigger_limit * sizeof(uint64_t*));

    if (nid_limit > 0)
      memcopy(bigger, nid_lines, nid_limit * sizeof(uint64_t*));

    nid_lines = bigger;

    bigger = zmalloc(bigger_limit * sizeof(uint64_t*));

    if (nid_limit > 0)
      memcopy(bigger, init_lines, nid_limit * sizeof(uint64_t*));

    init_lines = bigger;

    nid_limit = bigger_limit;
  }

  if (*(nid_lines + nid) != 0)
    parse_error("nid defined twice");

  *(nid_lines + nid) = (uint64_t) line;

  if (nid > max_nid)
    max_nid = nid;
}

uint64_t* line_of_token(char* token) {
  uint64_t* line;

  if (token == (char*) 0)
    parse_error("nid expected");

  line = line_of_nid(parse_decimal(token));

  if (line == UNUSED)
    parse_error("undefined nid");

  return line;
}

char* canonical_op(char* token) {
  if (string_compare(token, OP_SORT)) return OP_SORT;
  if (string_compare(token, OP_ZERO)) return OP_ZERO;
  if (string_compare(token, OP_ONE)) return OP_ONE;
  if (string_compare(token, OP_CONST)) return OP_CONST;
  if (string_compare(token, OP_CONSTD)) return OP_CONSTD;
  if (string_compare(token, OP_CONSTH)) return OP_CONSTH;
  if (string_compare(token, OP_INPUT)) return OP_INPUT;
  if (string_compare(token, OP_STATE)) return OP_STATE;
  if (string_compare(token, OP_INIT)) return OP_INIT;
  if (string_compare(token, OP_NEXT)) return OP_NEXT;
  if (string_compare(token, OP_SEXT)) return OP_SEXT;
  if (string_compare(token, OP_UEXT)) return OP_UEXT;
  if (string_compare(token, OP_SLICE)) return OP_SLICE;
  if (string_compare(token, OP_NOT)) return OP_NOT;
  if (string_compare(token, OP_INC)) return OP_INC;
  if (string_compare(token, OP_DEC)) return OP_DEC;
  if (string_compare(token, OP_NEG)) return OP_NEG;
  if (string_compare(token, OP_IMPLIES)) return OP_IMPLIES;
  if (string_compare(token, OP_EQ)) return OP_EQ;
  if (string_compare(token, OP_NEQ)) return OP_NEQ;
  if (string_compare(token, OP_SGT)) return OP_SGT;
  if (string_compare(token, OP_UGT)) return OP_UGT;
  if (string_compare(token, OP_SGTE)) return OP_SGTE;
  if (string_compare(token, OP_UGTE)) return OP_UGTE;
  if (string_compare(token, OP_SLT)) return OP_SLT;
  if (string_compare(token, OP_ULT)) return OP_ULT;
  if (string_compare(token, OP_SLTE)) return OP_SLTE;
  if (string_compare(token, OP_ULTE)) return OP_ULTE;
  if (string_compare(token, OP_AND)) return OP_AND;
  if (string_compare(token, OP_OR)) return OP_OR;
  if (string_compare(token, OP_XOR)) return OP_XOR;
  if (string_compare(token, OP_SLL)) return OP_SLL;
  if (string_compare(token, OP_SRL)) return OP_SRL;
  if (string_compare(token, OP_SRA)) return OP_SRA;
  if (string_compare(token, OP_ADD)) return OP_ADD;
  if (string_compare(token, OP_SUB)) return OP_SUB;
  if (string_compare(token, OP_MUL)) return OP_MUL;
  if (string_compare(token, OP_SDIV)) return OP_SDIV;
  if (string_compare(token, OP_UDIV)) return OP_UDIV;
  if (string_compare(token, OP_SREM)) return OP_SREM;
  if (string_compare(token, OP_UREM)) return OP_UREM;
  if (string_compare(token, OP_CONCAT)) return OP_CONCAT;
  if (string_compare(token, OP_READ)) return OP_READ;
  if (string_compare(token, OP_ITE)) return OP_ITE;
  if (string_compare(token, OP_WRITE)) return OP_WRITE;
  if (string_compare(token, OP_BAD)) return OP_BAD;
  if (string_compare(token, OP_CONSTRAINT)) return OP_CONSTRAINT;
  if (string_compare(token, OP_OUTPUT)) return OP_OUTPUT;

  return (char*) 0;
}

void parse_error(char* message) {
  printf("%s: syntax error in %s in line %lu: %s\n", selfie_name, model_name, model_line, message);

  exit(EXITCODE_PARSERERROR);
}

void parse_model() {
  char* token;
  uint64_t nid;
  char* op;
  uint64_t* sid;
  uint64_t* line;
  uint64_t* arg1;
  uint64_t* arg2;
  uint64_t* arg3;
  uint64_t  value;
  uint64_t  u;
  uint64_t  l;
  char* symbol;
  char* comment;

  model_text = (char*) read_whole_file(model_name);
  model_pos  = 0;
  model_line = 1;

  // keep the model as written: no structural sharing
  reuse_lines = 0;

  while (model_pos < model_size) {
    skip_blanks();

    if (at_end_of_line()) {
      skip_line();
    } else if (model_character() == 59) {
      // comment line
      skip_line();
    } else {
      token = scan_token();

      nid = parse_decimal(token);

      token = scan_token();

      if (token == (char*) 0)
        parse_error("operator expected");

      op = canonical_op(token);

      if (op == (char*) 0)
        parse_error("unknown operator");

      line = UNUSED;

      if (op == OP_SORT) {
        token = scan_token();

        if (token == (char*) 0)
          parse_error("sort kind expected");

        if (string_compare(token, "bitvec")) {
          value = parse_decimal(scan_token());

          comment = scan_comment();

          line = new_bitvec(value, comment);

          if (value == 1)
            if (SID_BOOLEAN == UNUSED)
              SID_BOOLEAN = line;
        } else if (string_compare(token, "array")) {
          arg2 = line_of_token(scan_token());
          arg3 = line_of_token(scan_token());

          comment = scan_comment();

          line = new_array(arg2, arg3, comment);
        } else
          parse_error("bitvec or array expected");

        number_of_sorts = number_of_sorts + 1;
      } else if (or(is_constant_op(op), or(op == OP_ZERO, op == OP_ONE))) {
        sid = line_of_token(scan_token());

        if (op == OP_ZERO) {
          // zero and one are decimal constants in the model
          op = OP_CONSTD;

          value = 0;
        } else if (op == OP_ONE) {
          op = OP_CONSTD;

          value = 1;
        } else {
          token = scan_token();

          if (token == (char*) 0)
            parse_error("constant expected");

          if (op == OP_CONSTD)
            value = parse_decimal(token);
          else if (op == OP_CONSTH)
            value = parse_hexadecimal(token);
          else
            value = parse_binary(token);
        }

        comment = scan_comment();

        line = new_constant(op, sid, value, comment);
      } else if (is_input_op(op)) {
        sid = line_of_token(scan_token());

        symbol = scan_token();

        comment = scan_comment();

        line = new_input(op, sid, symbol, comment);

        if (op == OP_STATE)
          number_of_states = number_of_states + 1;
      } else if (op == OP_INIT) {
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());
        arg2 = line_of_token(scan_token());

        comment = scan_comment();

        line = new_init(sid, arg1, arg2, comment);

        if (get_op(arg1) != OP_STATE)
          parse_error("init of non-state");

        *(init_lines + get_nid(arg1)) = (uint64_t) line;

        number_of_inits = number_of_inits + 1;
      } else if (op == OP_NEXT) {
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());
        arg2 = line_of_token(scan_token());

        comment = scan_comment();

        line = new_next(sid, arg1, arg2, comment);

        number_of_nexts = number_of_nexts + 1;
      } else if (is_property_op(op)) {
        arg1 = line_of_token(scan_token());

        symbol = scan_token();

        comment = scan_comment();

        line = new_property(op, arg1, symbol, comment);

        if (op == OP_BAD)
          number_of_bads = number_of_bads + 1;
        else
          number_of_constraints = number_of_constraints + 1;
      } else if (op == OP_OUTPUT) {
        // a named value, of an abstraction
        arg1 = line_of_token(scan_token());

        symbol = scan_token();

        comment = scan_comment();

        line = new_property(op, arg1, symbol, comment);
      } else if (op == OP_SEXT) {
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());

        value = parse_decimal(scan_token());

        comment = scan_comment();

        line = new_ext(op, sid, arg1, value, comment);
      } else if (op == OP_UEXT) {
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());

        value = parse_decimal(scan_token());

        comment = scan_comment();

        line = new_ext(op, sid, arg1, value, comment);
      } else if (op == OP_SLICE) {
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());

        u = parse_decimal(scan_token());
        l = parse_decimal(scan_token());

        comment = scan_comment();

        line = new_slice(sid, arg1, u, l, comment);
      } else if (is_unary_op(op)) {
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());

        comment = scan_comment();

        line = new_unary(op, sid, arg1, comment);
      } else if (op == OP_ITE) {
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());
        arg2 = line_of_token(scan_token());
        arg3 = line_of_token(scan_token());

        comment = scan_comment();

        line = new_ternary(op, sid, arg1, arg2, arg3, comment);
      } else if (op == OP_WRITE) {
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());
        arg2 = line_of_token(scan_token());
        arg3 = line_of_token(scan_token());

        comment = scan_comment();

        line = new_ternary(op, sid, arg1, arg2, arg3, comment);
      } else {
        // read, concat, and binary operators
        sid  = line_of_token(scan_token());
        arg1 = line_of_token(scan_token());
        arg2 = line_of_token(scan_token());

        comment = scan_comment();

        line = new_binary(op, sid, arg1, arg2, comment);
      }

      set_line_of_nid(nid, line);

      set_nid(line, nid);

      skip_line();
    }
  }

  printf("%s: %lu lines with %lu sorts, %lu states, %lu inits, %lu nexts, %lu bads, and %lu constraints parsed from %s\n", selfie_name,
    number_of_lines, number_of_sorts, number_of_states, number_of_inits, number_of_nexts, number_of_bads, number_of_constraints, model_name);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------------- LOADERS ----------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t* find_state(char* symbol) {
  uint64_t nid;
  uint64_t* line;

  // the state with the given symbol, or 0

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED)
      if (get_op(line) == OP_STATE)
        if ((char*) get_arg1(line) != (char*) 0)
          if (string_compare((char*) get_arg1(line), symbol))
            return line;

    nid = nid + 1;
  }

  return UNUSED;
}

uint64_t array_elements(uint64_t* state_nid) {
  return two_to_the_power_of(eval_array_size(get_sid(state_nid)));
}

uint64_t array_element_size(uint64_t* state_nid) {
  return eval_element_size(get_sid(state_nid));
}

void load_words(uint64_t* state_nid, uint64_t start, uint64_t size, uint64_t binary) {
  uint64_t element_bytes;
  uint64_t elements;
  uint64_t offset;
  uint64_t index;
  uint64_t word;

  // writes the words of a loaded code (binary == 1) or data (binary == 0)
  // segment of size bytes into the array state, element by element, and
  // checks the words the state already holds

  element_bytes = array_element_size(state_nid) / 8;
  elements      = array_elements(state_nid);

  offset = 0;

  while (offset < size) {
    index = offset / element_bytes;

    if (index >= elements) {
      printf("%s: %s does not fit the %lu elements of %s\n", selfie_name, binary_file, elements, (char*) get_arg1(state_nid));

      exit(EXITCODE_BADARGUMENTS);
    }

    if (binary)
      word = load_instruction(offset);
    else
      word = load_data(offset);

    if (read_array_raw(state_nid, index) != 0)
      if (read_array_raw(state_nid, index) != word)
        mismatched_words = mismatched_words + 1;

    if (read_array_raw(state_nid, index) == word)
      checked_words = checked_words + 1;

    write_array_raw(state_nid, index, word);

    loaded_words = loaded_words + 1;

    offset = offset + element_bytes;
  }

  // unused since linear addresses are relative to the segment start
  start = start + 0;
}

void load_binary(char* name) {
  uint64_t* code_nid;
  uint64_t* data_nid;

  // code and data of the binary go into the live code and data segment states;
  // a model generated for the binary holds the same words already, which checks
  // the loader against rotor's initialization, see projects/reversible.md

  selfie_load(name);

  code_nid = find_state("core-0-loaded-code-segment");

  if (code_nid == UNUSED)
    code_nid = find_state("core-0-code-segment");

  data_nid = find_state("core-0-loaded-data-segment");

  if (data_nid == UNUSED)
    data_nid = find_state("core-0-zeroed-data-segment");

  if (code_nid == UNUSED) {
    printf("%s: no code segment state in %s\n", selfie_name, model_name);

    exit(EXITCODE_BADARGUMENTS);
  }

  load_words(code_nid, code_start, code_size, 1);

  *(uninitialized_states + get_nid(code_nid)) = 0;

  if (data_nid != UNUSED) {
    load_words(data_nid, data_start, data_size, 0);

    *(uninitialized_states + get_nid(data_nid)) = 0;
  }

  printf("%s: %lu words of %s loaded into %s, %lu words agreed, %lu words mismatched\n", selfie_name,
    loaded_words, name, model_name, checked_words, mismatched_words);

  if (mismatched_words > 0)
    exit(EXITCODE_SYSTEMERROR);
}

void load_input(char* name) {
  uint64_t* tapes_nid;
  uint64_t* ends_nid;
  uint64_t* heads_nid;
  uint64_t* buffer_nid;
  uint64_t* buffer;
  uint64_t  size;
  uint64_t  tape_words;
  uint64_t  words;
  uint64_t  i;

  // the file goes onto the input tape of standard input, with its size as
  // the file end; a RISC-U model reads its first byte from the input buffer

  buffer = read_whole_file(name);
  size   = model_size;

  tapes_nid = find_state("input-tapes");
  ends_nid  = find_state("tape-ends");
  heads_nid = find_state("tape-heads");

  if (tapes_nid != UNUSED) {
    // words per tape: all tape words over the number of tapes
    tape_words = array_elements(tapes_nid) / array_elements(heads_nid);

    words = round_up(size, WORDSIZE) / WORDSIZE;

    if (words > tape_words) {
      // reads beyond the tape are bad states, so only the beginning matters
      printf("%s: only the first %lu of %lu words of %s fit the input tape in %s\n", selfie_name, tape_words, words, name, model_name);

      words = tape_words;
    }

    i = 0;

    while (i < words) {
      write_array_raw(tapes_nid, i, *(buffer + i));

      i = i + 1;
    }

    write_array_raw(ends_nid, 0, size);

    // loaded input is not free
    *(uninitialized_states + get_nid(tapes_nid)) = 0;
    *(uninitialized_states + get_nid(ends_nid))  = 0;

    printf("%s: %lu bytes of %s put onto the input tape of %s\n", selfie_name, size, name, model_name);
  } else {
    buffer_nid = find_state("input-buffer");

    if (buffer_nid == UNUSED) {
      printf("%s: no input tape or buffer in %s\n", selfie_name, model_name);

      exit(EXITCODE_BADARGUMENTS);
    }

    if (size > 0)
      current_input = load_character((char*) buffer, 0);
    else
      current_input = 0;

    printf("%s: first byte %lu of %s put into the input buffer of %s\n", selfie_name, current_input, name, model_name);
  }
}

// a layout is a grid of cells and a token as text, see cellfie.md; it goes
// into the states of cellfie's model: the token into token-x, token-y,
// token-heading, token-pc, token-address, token-data, and token-registers,
// the state of its system calls into token-break, token-open-files,
// token-leg, token-word, token-tape-heads, token-tape-ends,
// token-tape-inputs, and token-tape-opens, and the cells into cell-kinds
// and cell-words, row by row

uint64_t layout_character() {
  if (layout_pos < layout_size)
    return load_character((char*) layout_text, layout_pos);
  else
    return 0;
}

void layout_error(char* message) {
  printf("%s: %s in line %lu of %s\n", selfie_name, message, layout_line, layout_file);

  exit(EXITCODE_SCANNERERROR);
}

void skip_layout_blanks(uint64_t lines) {
  uint64_t c;

  // spaces and tabs, and line ends as well if lines is set

  while (1) {
    c = layout_character();

    if (c == 10) {
      if (lines)
        layout_line = layout_line + 1;
      else
        return;
    } else if (c == 13) {
      if (not(lines))
        return;
    } else if (c != ' ')
      if (c != 9)
        return;

    layout_pos = layout_pos + 1;
  }
}

uint64_t scan_layout_decimal() {
  uint64_t n;
  uint64_t c;

  skip_layout_blanks(0);

  c = layout_character();

  if (or(c < '0', c > '9'))
    layout_error("decimal number expected");

  n = 0;

  while (and(c >= '0', c <= '9')) {
    n = n * 10 + c - '0';

    layout_pos = layout_pos + 1;

    c = layout_character();
  }

  return n;
}

uint64_t scan_layout_hexadecimal(uint64_t digits) {
  uint64_t n;
  uint64_t i;
  uint64_t c;

  // a number of exactly that many hexadecimal digits, or, with 0 digits,
  // of as many as there are, at least one

  if (digits == 0)
    skip_layout_blanks(0);

  n = 0;
  i = 0;

  while (1) {
    c = layout_character();

    if (and(c >= '0', c <= '9'))
      c = c - '0';
    else if (and(c >= 'a', c <= 'f'))
      c = c - 'a' + 10;
    else if (and(c >= 'A', c <= 'F'))
      c = c - 'A' + 10;
    else if (or(i == 0, digits != 0))
      layout_error("hexadecimal digit expected");
    else
      return n;

    n = n * 16 + c;

    layout_pos = layout_pos + 1;

    i = i + 1;

    if (i == digits)
      return n;
  }
}

uint64_t scan_layout_mirror() {
  uint64_t c;

  // slash is 0, backslash is 1

  c = layout_character();

  layout_pos = layout_pos + 1;

  if (c == '/')
    return 0;
  else if (c != 92)
    layout_error("mirror expected");

  return 1;
}

uint64_t scan_layout_heading(uint64_t c) {
  // east is 0, north is 1, west is 2, south is 3

  if (c == 'E')
    return 0;
  else if (c == 'N')
    return 1;
  else if (c == 'W')
    return 2;
  else if (c != 'S')
    layout_error("heading E, N, W, or S expected");

  return 3;
}

uint64_t* find_layout_state(char* symbol) {
  uint64_t* state_nid;

  state_nid = find_state(symbol);

  if (state_nid == UNUSED) {
    printf("%s: no state %s for %s in %s\n", selfie_name, symbol, layout_file, model_name);

    exit(EXITCODE_BADARGUMENTS);
  }

  // a loaded state is not free
  *(uninitialized_states + get_nid(state_nid)) = 0;

  return state_nid;
}

void load_layout(char* name) {
  uint64_t* registers_nid;
  uint64_t* kinds_nid;
  uint64_t* words_nid;
  uint64_t* heads_nid;
  uint64_t* ends_nid;
  uint64_t* inputs_nid;
  uint64_t* opens_nid;
  uint64_t width;
  uint64_t height;
  uint64_t x;
  uint64_t y;
  uint64_t n;
  uint64_t c;
  uint64_t cell;
  uint64_t word;

  layout_text = read_whole_file(name);
  layout_size = model_size;

  layout_pos  = 0;
  layout_line = 1;

  registers_nid = find_layout_state("token-registers");
  kinds_nid     = find_layout_state("cell-kinds");
  words_nid     = find_layout_state("cell-words");

  heads_nid  = find_layout_state("token-tape-heads");
  ends_nid   = find_layout_state("token-tape-ends");
  inputs_nid = find_layout_state("token-tape-inputs");
  opens_nid  = find_layout_state("token-tape-opens");

  // the token: at the northwestern cell heading east with all words zero,
  // unless a line #T x y heading pc address data says otherwise; a line
  // #R register value sets a register; the three standard files are open
  // with standard input the only input tape, unless a line #S break
  // open-files leg word or #F descriptor head end input open says
  // otherwise; all other lines with # are comments

  set_state(find_layout_state("token-break"), 0);
  set_state(find_layout_state("token-open-files"), 3);
  set_state(find_layout_state("token-leg"), 0);
  set_state(find_layout_state("token-word"), 0);

  n = 0;

  while (n < array_elements(heads_nid)) {
    write_array_raw(heads_nid, n, 0);
    write_array_raw(ends_nid, n, 0);
    write_array_raw(inputs_nid, n, n == 0);
    write_array_raw(opens_nid, n, 0);

    n = n + 1;
  }

  set_state(find_layout_state("token-x"), 0);
  set_state(find_layout_state("token-y"), 0);
  set_state(find_layout_state("token-heading"), 0);
  set_state(find_layout_state("token-pc"), 0);
  set_state(find_layout_state("token-address"), 0);
  set_state(find_layout_state("token-data"), 0);

  skip_layout_blanks(1);

  while (layout_character() == '#') {
    layout_pos = layout_pos + 1;

    c = layout_character();

    if (c == 'T') {
      layout_pos = layout_pos + 1;

      set_state(find_state("token-x"), scan_layout_decimal());
      set_state(find_state("token-y"), scan_layout_decimal());

      skip_layout_blanks(0);

      set_state(find_state("token-heading"), scan_layout_heading(layout_character()));

      layout_pos = layout_pos + 1;

      set_state(find_state("token-pc"), scan_layout_hexadecimal(0));
      set_state(find_state("token-address"), scan_layout_hexadecimal(0));
      set_state(find_state("token-data"), scan_layout_hexadecimal(0));
    } else if (c == 'R') {
      layout_pos = layout_pos + 1;

      n = scan_layout_decimal();

      if (n >= array_elements(registers_nid))
        layout_error("no such register");

      c = scan_layout_hexadecimal(0);

      // register zero is always 0
      if (n != 0)
        write_array_raw(registers_nid, n, c);
    } else if (c == 'S') {
      layout_pos = layout_pos + 1;

      set_state(find_state("token-break"), scan_layout_hexadecimal(0));
      set_state(find_state("token-open-files"), scan_layout_hexadecimal(0));

      n = scan_layout_hexadecimal(0);

      if (n > 3)
        layout_error("no such leg");

      set_state(find_state("token-leg"), n);
      set_state(find_state("token-word"), scan_layout_hexadecimal(0));
    } else if (c == 'F') {
      layout_pos = layout_pos + 1;

      n = scan_layout_decimal();

      if (n >= array_elements(heads_nid))
        layout_error("no such file descriptor");

      write_array_raw(heads_nid, n, scan_layout_hexadecimal(0));
      write_array_raw(ends_nid, n, scan_layout_hexadecimal(0));
      write_array_raw(inputs_nid, n, scan_layout_hexadecimal(0));
      write_array_raw(opens_nid, n, scan_layout_hexadecimal(0));
    }

    while (and(layout_character() != 10, layout_pos < layout_size))
      layout_pos = layout_pos + 1;

    skip_layout_blanks(1);
  }

  // x = width, y = height, rule = RISC-R: the grid of the model has the
  // powers of two as sides that width and height fit in, 2 at least

  if (layout_character() != 'x')
    layout_error("x = width, y = height, rule = RISC-R expected");

  layout_pos = layout_pos + 1;

  skip_layout_blanks(0);

  layout_pos = layout_pos + 1;

  width = scan_layout_decimal();

  while (or(layout_character() < '0', layout_character() > '9')) {
    if (layout_pos >= layout_size)
      layout_error("x = width, y = height, rule = RISC-R expected");

    layout_pos = layout_pos + 1;
  }

  height = scan_layout_decimal();

  // reversibility is a switch, the rule says which way it is set

  while (layout_character() != '=') {
    if (layout_pos >= layout_size)
      layout_error("x = width, y = height, rule = RISC-R expected");

    layout_pos = layout_pos + 1;
  }

  layout_pos = layout_pos + 1;

  skip_layout_blanks(0);

  n = 0;

  while (n < 6) {
    // RISC-R

    if (n == 0)
      c = 'R';
    else if (n == 1)
      c = 'I';
    else if (n == 2)
      c = 'S';
    else if (n == 3)
      c = 'C';
    else if (n == 4)
      c = '-';
    else
      c = 'R';

    if (layout_character() != c)
      layout_error("the rule of the layout is not RISC-R");

    layout_pos = layout_pos + 1;

    n = n + 1;
  }

  x = two_to_the_power_of(eval_bitvec_size(get_sid(find_state("token-x"))));
  y = two_to_the_power_of(eval_bitvec_size(get_sid(find_state("token-y"))));

  if (or(width > x, or(height > y, or(and(2 * width <= x, x > 2), and(2 * height <= y, y > 2))))) {
    printf("%s: the grid of %lux%lu cells of %s is not the grid of %lux%lu cells of %s\n", selfie_name,
      width, height, name, x, y, model_name);

    exit(EXITCODE_BADARGUMENTS);
  }

  width  = x;
  height = y;

  if (or(get_state(find_state("token-x")) >= width, get_state(find_state("token-y")) >= height))
    layout_error("token is not on the grid");

  // the cells, row by row: a cell is its kind, plus orientation times 8 for
  // an instruction cell, plus 32 for a backslash mirror; the word of a router
  // is its bit, plus 64 if it is a bit of the address

  n = 0;

  while (n < width * height) {
    write_array_raw(kinds_nid, n, 0);
    write_array_raw(words_nid, n, 0);

    n = n + 1;
  }

  x = 0;
  y = 0;

  while (1) {
    skip_layout_blanks(1);

    n = 1;

    c = layout_character();

    if (and(c >= '0', c <= '9'))
      n = scan_layout_decimal();

    c = layout_character();

    layout_pos = layout_pos + 1;

    cell = 0;
    word = 0;

    if (c == '!') {
      printf("%s: grid of %lux%lu cells and token of %s loaded into %s\n", selfie_name, width, height, name, model_name);

      return;
    } else if (c == '$') {
      x = 0;
      y = y + n;

      n = 0;
    } else if (c == '/')
      cell = 1;
    else if (c == 92)
      cell = 1 + 32;
    else if (c == 'R') {
      cell = 2 + scan_layout_mirror() * 32;

      c = layout_character();

      if (c == 'a')
        word = 64;
      else if (c != 'p')
        layout_error("router field p or a expected");

      layout_pos = layout_pos + 1;

      c = scan_layout_hexadecimal(2);

      // two decimal digits read as hexadecimal ones

      if (or(c / 16 > 6, c % 16 > 9))
        layout_error("router bit expected");

      c = c / 16 * 10 + c % 16;

      if (c > 63)
        layout_error("router bit beyond 63");

      word = word + c;
    } else if (c == 'M') {
      cell = 3;

      word = scan_layout_hexadecimal(16);
    } else if (c == 'T') {
      cell = 5;

      word = scan_layout_hexadecimal(16);
    } else if (c != '.') {
      if (c == 0)
        layout_error("layout does not end with !");

      cell = 4 + scan_layout_heading(c) * 8;

      cell = cell + scan_layout_mirror() * 32;

      word = scan_layout_hexadecimal(8);
    }

    while (n > 0) {
      if (x >= width)
        layout_error("row is wider than the grid");
      else if (y >= height)
        layout_error("more rows than the grid has");

      write_array_raw(kinds_nid, y * width + x, cell);
      write_array_raw(words_nid, y * width + x, word);

      x = x + 1;

      n = n - 1;
    }
  }
}

void load_files() {
  // each file goes into the model that has the states for it

  if (binary_file != (char*) 0) {
    if (find_state("core-0-loaded-code-segment") != UNUSED)
      load_binary(binary_file);
    else if (find_state("core-0-code-segment") != UNUSED)
      load_binary(binary_file);
  }

  if (input_file != (char*) 0) {
    if (find_state("input-tapes") != UNUSED)
      load_input(input_file);
    else if (find_state("input-buffer") != UNUSED)
      load_input(input_file);
  }

  if (layout_file != (char*) 0)
    if (find_state("cell-kinds") != UNUSED)
      load_layout(layout_file);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// --------------------------- SIMULATOR ---------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

void init_states() {
  uint64_t nid;
  uint64_t* line;
  uint64_t* sid;
  uint64_t* init_nid;

  // states are initialized in the order of their nids, states without
  // init to zero; the input buffer of RISC-U models and the code segment
  // are arrays the evaluator never copies

  uninitialized_states = zmalloc((nid_limit + 1) * sizeof(uint64_t));

  line = find_state("input-buffer");

  if (line != UNUSED)
    SID_INPUT_BUFFER = get_sid(line);

  line = find_state("core-0-code-segment");

  if (line != UNUSED)
    SID_CODE_STATE = get_sid(line);

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED)
      if (get_op(line) == OP_STATE) {
        init_nid = (uint64_t*) *(init_lines + nid);

        if (init_nid == UNUSED) {
          // free for bounded model checking, zero for simulation
          *(uninitialized_states + nid) = 1;

          sid = get_sid(line);

          if (is_bitvector(sid))
            init_nid = new_init(sid, line, new_constant(OP_CONSTD, sid, 0, "zero"), "uninitialized state zeroed");
          else
            init_nid = new_init(sid, line, new_constant(OP_CONSTD, get_arg3(sid), 0, "zero"), "uninitialized state zeroed");
        }

        eval_init(init_nid);
      }

    nid = nid + 1;
  }

  pc_state_nid = find_state("core-0-pc");
}

uint64_t check_properties() {
  uint64_t nid;
  uint64_t* line;
  uint64_t  condition;

  // reports the first bad state or violated constraint, returns 1 if any

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED) {
      if (get_op(line) == OP_BAD) {
        condition = eval_line(get_arg1(line));

        if (condition) {
          printf("%s: bad %s after %lu instructions\n", selfie_name, (char*) get_arg2(line), current_step + 1);

          return 1;
        }
      } else if (get_op(line) == OP_CONSTRAINT) {
        condition = eval_line(get_arg1(line));

        if (not(condition)) {
          printf("%s: constraint %s violated after %lu instructions\n", selfie_name, (char*) get_arg2(line), current_step + 1);

          return 1;
        }
      }
    }

    nid = nid + 1;
  }

  return 0;
}

uint64_t simulate() {
  uint64_t nid;
  uint64_t* line;
  uint64_t  halt;

  // runs the model from its initial state until it halts, reaches a bad
  // state, or violates a constraint; the number of instructions executed
  // is the number of steps taken, counting the step a property stops

  printf("%s: ********************************************************************************\n", selfie_name);

  current_step = 0;
  next_step    = 0;

  while (1) {
    next_step = next_step + 1;

    if (printing_pc)
      if (pc_state_nid != UNUSED)
        printf("%s: pc 0x%lX at instruction %lu\n", selfie_name, get_state(pc_state_nid), current_step + 1);

    if (check_properties())
      return 1;

    if (max_steps > 0)
      if (current_step >= max_steps) {
        printf("%s: %lu instructions executed, bound reached\n", selfie_name, current_step);

        return 0;
      }

    halt = 1;

    nid = 1;

    while (nid <= max_nid) {
      line = line_of_nid(nid);

      if (line != UNUSED)
        if (get_op(line) == OP_NEXT)
          halt = halt * eval_next(line);

      nid = nid + 1;
    }

    if (halt) {
      printf("%s: halted after %lu instructions\n", selfie_name, current_step + 1);

      return 0;
    }

    nid = 1;

    while (nid <= max_nid) {
      line = line_of_nid(nid);

      if (line != UNUSED)
        if (get_op(line) == OP_NEXT)
          apply_next(line);

      nid = nid + 1;
    }

    current_step = next_step;
  }
}

// The product of two models runs both, the second step by step and the
// first only in the steps in which an abstraction says so: the second
// model may take many steps where the first takes one, as cellfie's cell
// rule takes many ticks for one RISC-R instruction. The abstraction is a
// third model without initial or next states. Its states are the states
// of the two models by name, its output step says whether the first model
// takes a step, and its bad states are where the two models differ.

uint64_t* violated_property() {
  uint64_t nid;
  uint64_t* line;

  // the first bad state or violated constraint of the current model, or 0

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED) {
      if (get_op(line) == OP_BAD) {
        if (eval_line(get_arg1(line)))
          return line;
      } else if (get_op(line) == OP_CONSTRAINT)
        if (not(eval_line(get_arg1(line))))
          return line;
    }

    nid = nid + 1;
  }

  return UNUSED;
}

void parse_next_model(char* name) {
  // another model, with its own lines and sorts

  nid_lines  = (uint64_t*) 0;
  init_lines = (uint64_t*) 0;
  nid_limit  = 0;
  max_nid    = 0;

  number_of_sorts       = 0;
  number_of_states      = 0;
  number_of_inits       = 0;
  number_of_nexts       = 0;
  number_of_bads        = 0;
  number_of_constraints = 0;

  SID_BOOLEAN      = UNUSED;
  SID_INPUT_BUFFER = UNUSED;
  SID_CODE_STATE   = UNUSED;

  model_name = name;

  parse_model();
}

void bind_abstraction() {
  uint64_t i;
  uint64_t* state_nid;

  // the states of the abstraction are the states of the models: bit vectors
  // by value, arrays by reference

  i = 0;

  while (i < number_of_abstraction_states) {
    state_nid = (uint64_t*) *(abstraction_states + i);

    set_state(state_nid, get_state((uint64_t*) *(abstracted_states + i)));

    set_step(state_nid, current_step);

    i = i + 1;
  }
}

void eval_nexts() {
  uint64_t nid;
  uint64_t* line;

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED)
      if (get_op(line) == OP_NEXT)
        eval_next(line);

    nid = nid + 1;
  }
}

void apply_nexts() {
  uint64_t nid;
  uint64_t* line;

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED)
      if (get_op(line) == OP_NEXT)
        apply_next(line);

    nid = nid + 1;
  }
}

void skip_nexts() {
  uint64_t nid;
  uint64_t* line;

  // the current model does not take this step: its states keep their
  // values and move to the next step with all others

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED) {
      if (get_op(line) == OP_NEXT)
        set_step(line, next_step);
      else if (get_op(line) == OP_STATE)
        set_step(line, next_step);
    }

    nid = nid + 1;
  }
}

uint64_t product() {
  uint64_t* first;
  uint64_t* second;
  uint64_t* abstraction;
  uint64_t* step_nid;
  uint64_t* line;
  uint64_t* other;
  uint64_t* first_stop;
  uint64_t* second_stop;
  uint64_t nid;
  uint64_t step;
  uint64_t first_steps;
  uint64_t second_steps;

  // returns 1 if the models do not differ until both stop in the same step
  // or the bound on the steps of the second model is reached, 0 otherwise

  first       = zmalloc(MODEL_RECORD_SIZE * sizeof(uint64_t));
  second      = zmalloc(MODEL_RECORD_SIZE * sizeof(uint64_t));
  abstraction = zmalloc(MODEL_RECORD_SIZE * sizeof(uint64_t));

  init_states();
  load_files();

  save_model(first);

  parse_next_model(product_model_name);

  init_states();
  load_files();

  save_model(second);

  parse_next_model(abstraction_model_name);

  init_states();

  save_model(abstraction);

  // the states of the abstraction are states of the two models by name

  abstraction_states = zmalloc((max_nid + 1) * sizeof(uint64_t*));
  abstracted_states  = zmalloc((max_nid + 1) * sizeof(uint64_t*));

  step_nid = UNUSED;

  nid = 1;

  while (nid <= *(abstraction + 3)) {
    restore_model(abstraction);

    line = line_of_nid(nid);

    if (line != UNUSED) {
      if (get_op(line) == OP_STATE) {
        restore_model(first);

        other = find_state((char*) get_arg1(line));

        if (other == UNUSED) {
          restore_model(second);

          other = find_state((char*) get_arg1(line));
        }

        if (other == UNUSED) {
          printf("%s: state %s of %s is neither in %s nor in %s\n", selfie_name, (char*) get_arg1(line),
            abstraction_model_name, (char*) *(first + 10), product_model_name);

          exit(EXITCODE_BADARGUMENTS);
        }

        if (is_bitvector(get_sid(line))) {
          step = 0;

          if (is_bitvector(get_sid(other)))
            step = eval_bitvec_size(get_sid(line)) == eval_bitvec_size(get_sid(other));
        } else {
          step = 0;

          if (is_array(get_sid(other)))
            if (eval_array_size(get_sid(line)) == eval_array_size(get_sid(other)))
              step = eval_element_size(get_sid(line)) == eval_element_size(get_sid(other));
        }

        if (not(step)) {
          printf("%s: state %s of %s has another sort in %s\n", selfie_name, (char*) get_arg1(line),
            abstraction_model_name, model_name);

          exit(EXITCODE_BADARGUMENTS);
        }

        *(abstraction_states + number_of_abstraction_states) = (uint64_t) line;
        *(abstracted_states + number_of_abstraction_states)  = (uint64_t) other;

        number_of_abstraction_states = number_of_abstraction_states + 1;
      } else if (get_op(line) == OP_OUTPUT)
        if (string_compare((char*) get_arg2(line), "step"))
          step_nid = get_arg1(line);
    }

    nid = nid + 1;
  }

  if (step_nid == UNUSED) {
    printf("%s: no output step in %s\n", selfie_name, abstraction_model_name);

    exit(EXITCODE_BADARGUMENTS);
  }

  printf("%s: ********************************************************************************\n", selfie_name);

  current_step = 0;
  next_step    = 0;

  first_steps  = 0;
  second_steps = 0;

  while (1) {
    next_step = next_step + 1;

    restore_model(abstraction);

    bind_abstraction();

    step = eval_line(step_nid);

    restore_model(second);

    second_stop = violated_property();

    if (step) {
      // the first model is to take a step: the models must not differ, and
      // either both stop here or neither

      restore_model(first);

      first_stop = violated_property();

      restore_model(abstraction);

      line = violated_property();

      if (line != UNUSED) {
        printf("%s: %s %s: %s after %lu steps and %s after %lu steps differ\n", selfie_name,
          get_op(line), (char*) get_arg2(line), (char*) *(first + 10), first_steps, product_model_name, second_steps);

        return 0;
      }

      if (first_stop != UNUSED) {
        if (second_stop != UNUSED) {
          printf("%s: %s %s after %lu instructions in %s\n", selfie_name,
            get_op(first_stop), (char*) get_arg2(first_stop), first_steps + 1, (char*) *(first + 10));
          printf("%s: %s %s after %lu instructions in %s\n", selfie_name,
            get_op(second_stop), (char*) get_arg2(second_stop), second_steps + 1, product_model_name);
          printf("%s: %s and %s agree at all %lu steps of %s, in %lu steps of %s, and stop together\n", selfie_name,
            (char*) *(first + 10), product_model_name, first_steps, (char*) *(first + 10), second_steps, product_model_name);

          return 1;
        }

        printf("%s: %s %s after %lu instructions in %s but %s goes on after %lu steps\n", selfie_name,
          get_op(first_stop), (char*) get_arg2(first_stop), first_steps + 1, (char*) *(first + 10), product_model_name, second_steps);

        return 0;
      }
    }

    if (second_stop != UNUSED) {
      printf("%s: %s %s after %lu instructions in %s but %s goes on after %lu steps\n", selfie_name,
        get_op(second_stop), (char*) get_arg2(second_stop), second_steps + 1, product_model_name, (char*) *(first + 10), first_steps);

      return 0;
    }

    if (max_steps > 0)
      if (second_steps >= max_steps) {
        printf("%s: %s and %s agree at all %lu steps of %s, in %lu steps of %s, bound reached\n", selfie_name,
          (char*) *(first + 10), product_model_name, first_steps, (char*) *(first + 10), second_steps, product_model_name);

        return 1;
      }

    // all next states are evaluated before any is applied

    restore_model(second);

    eval_nexts();

    if (step) {
      restore_model(first);

      eval_nexts();
      apply_nexts();

      first_steps = first_steps + 1;
    } else {
      restore_model(first);

      skip_nexts();
    }

    restore_model(second);

    apply_nexts();

    second_steps = second_steps + 1;

    restore_model(abstraction);

    skip_nexts();

    current_step = next_step;
  }
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------------- BIT BLASTER --------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t* grow_words(uint64_t* words, uint64_t old_size, uint64_t new_size) {
  uint64_t* bigger;

  bigger = zmalloc(new_size * sizeof(uint64_t));

  if (old_size > 0)
    memcopy(bigger, words, old_size * sizeof(uint64_t));

  return bigger;
}

// -----------------------------------------------------------------
// ------------------------------ AIG ------------------------------
// -----------------------------------------------------------------

// and-inverter graph: node 0 is the constant, literal 2 * node + sign,
// so literal 0 is false and literal 1 is true; and-nodes are hashed
// structurally and folded over constants, which is what collapses
// the model wherever the state is concrete

void init_aig() {
  aig_capacity = 65536;

  aig_left  = zmalloc(aig_capacity * sizeof(uint64_t));
  aig_right = zmalloc(aig_capacity * sizeof(uint64_t));

  aig_assumed = zmalloc(aig_capacity * sizeof(uint64_t));

  cofactor_stamps = zmalloc(aig_capacity * sizeof(uint64_t));
  cofactor_values = zmalloc(aig_capacity * sizeof(uint64_t));

  aig_table_size = 131072;

  aig_table = zmalloc(aig_table_size * sizeof(uint64_t));

  aig_nodes = 1;
}

uint64_t aig_not(uint64_t l) {
  if (l % 2)
    return l - 1;
  else
    return l + 1;
}

uint64_t aig_new_node(uint64_t left, uint64_t right) {
  if (aig_nodes == aig_capacity) {
    aig_left  = grow_words(aig_left, aig_capacity, 2 * aig_capacity);
    aig_right = grow_words(aig_right, aig_capacity, 2 * aig_capacity);

    if (aig_mark != (uint64_t*) 0) {
      aig_mark = grow_words(aig_mark, aig_capacity, 2 * aig_capacity);
      aig_var  = grow_words(aig_var, aig_capacity, 2 * aig_capacity);
    }

    aig_assumed = grow_words(aig_assumed, aig_capacity, 2 * aig_capacity);

    cofactor_stamps = grow_words(cofactor_stamps, aig_capacity, 2 * aig_capacity);
    cofactor_values = grow_words(cofactor_values, aig_capacity, 2 * aig_capacity);

    aig_capacity = 2 * aig_capacity;
  }

  *(aig_left + aig_nodes)  = left;
  *(aig_right + aig_nodes) = right;

  aig_nodes = aig_nodes + 1;

  return aig_nodes - 1;
}

uint64_t aig_input() {
  aig_inputs = aig_inputs + 1;

  return 2 * aig_new_node(AIG_INPUT, 0);
}

uint64_t aig_is_input(uint64_t node) {
  return *(aig_left + node) == AIG_INPUT;
}

uint64_t aig_hash(uint64_t a, uint64_t b) {
  return ((a * 6364136223846793005 + b * 1442695040888963407) / 65536) % aig_table_size;
}

void aig_rehash() {
  uint64_t n;
  uint64_t h;

  aig_table_size = 2 * aig_table_size;

  aig_table = zmalloc(aig_table_size * sizeof(uint64_t));

  n = 1;

  while (n < aig_nodes) {
    if (not(aig_is_input(n))) {
      h = aig_hash(*(aig_left + n), *(aig_right + n));

      while (*(aig_table + h) != 0) {
        h = h + 1;

        if (h == aig_table_size)
          h = 0;
      }

      *(aig_table + h) = n;
    }

    n = n + 1;
  }
}

uint64_t aig_and(uint64_t a, uint64_t b) {
  uint64_t h;
  uint64_t n;

  if (a == AIG_FALSE)
    return AIG_FALSE;
  else if (b == AIG_FALSE)
    return AIG_FALSE;
  else if (a == AIG_TRUE)
    return b;
  else if (b == AIG_TRUE)
    return a;
  else if (a == b)
    return a;
  else if (a == aig_not(b))
    return AIG_FALSE;

  if (a > b) {
    h = a;
    a = b;
    b = h;
  }

  h = aig_hash(a, b);

  n = *(aig_table + h);

  while (n != 0) {
    if (*(aig_left + n) == a)
      if (*(aig_right + n) == b) {
        if (cofactoring)
          // what the path assumes is constant
          return assumed_value(2 * n);

        return 2 * n;
      }

    h = h + 1;

    if (h == aig_table_size)
      h = 0;

    n = *(aig_table + h);
  }

  n = aig_new_node(a, b);

  *(aig_table + h) = n;

  aig_ands = aig_ands + 1;

  if (2 * aig_ands > aig_table_size)
    aig_rehash();

  return 2 * n;
}

uint64_t aig_or(uint64_t a, uint64_t b) {
  return aig_not(aig_and(aig_not(a), aig_not(b)));
}

uint64_t aig_xor(uint64_t a, uint64_t b) {
  if (a == AIG_FALSE)
    return b;
  else if (b == AIG_FALSE)
    return a;
  else if (a == AIG_TRUE)
    return aig_not(b);
  else if (b == AIG_TRUE)
    return aig_not(a);
  else if (a == b)
    return AIG_FALSE;
  else if (a == aig_not(b))
    return AIG_TRUE;

  return aig_or(aig_and(a, aig_not(b)), aig_and(aig_not(a), b));
}

uint64_t aig_mux(uint64_t s, uint64_t a, uint64_t b) {
  // s ? a : b
  if (s == AIG_TRUE)
    return a;
  else if (s == AIG_FALSE)
    return b;
  else if (a == b)
    return a;

  return aig_or(aig_and(s, a), aig_and(aig_not(s), b));
}

// path assumptions: evaluating on a path, literals the path assumes are
// constants, and the first literal that a choice depends on but that
// the path does not assume yet is remembered as the place to split

uint64_t assumed_value(uint64_t l) {
  uint64_t v;

  v = *(aig_assumed + l / 2);

  if (v == 0)
    return l;
  else if (v == 1)
    return AIG_TRUE - l % 2;
  else
    return l % 2;
}

uint64_t assume_literal(uint64_t l) {
  uint64_t n;
  uint64_t v;

  // assumes l true; a true and-node makes its children true;
  // returns 0 if that contradicts the path

  if (l == AIG_TRUE)
    return 1;
  else if (l == AIG_FALSE)
    return 0;

  n = l / 2;

  if (l % 2)
    v = 2;
  else
    v = 1;

  if (*(aig_assumed + n) != 0)
    return *(aig_assumed + n) == v;

  if (assumed_count == assumed_capacity) {
    if (assumed_capacity == 0)
      assumed_capacity = 1024;
    else
      assumed_capacity = 2 * assumed_capacity;

    assumed_nodes = grow_words(assumed_nodes, assumed_count, assumed_capacity);
  }

  *(aig_assumed + n) = v;

  *(assumed_nodes + assumed_count) = n;

  assumed_count = assumed_count + 1;

  assumption_epoch = assumption_epoch + 1;

  if (not(aig_is_input(n))) {
    if (v == 1) {
      if (not(assume_literal(*(aig_left + n))))
        return 0;

      return assume_literal(*(aig_right + n));
    } else if (assumed_value(*(aig_left + n)) == AIG_TRUE)
      return assume_literal(aig_not(*(aig_right + n)));
    else if (assumed_value(*(aig_right + n)) == AIG_TRUE)
      return assume_literal(aig_not(*(aig_left + n)));
  }

  return 1;
}

void undo_assumptions(uint64_t mark) {
  if (assumed_count > mark)
    assumption_epoch = assumption_epoch + 1;

  while (assumed_count > mark) {
    assumed_count = assumed_count - 1;

    *(aig_assumed + *(assumed_nodes + assumed_count)) = 0;
  }
}

uint64_t aig_cofactor(uint64_t l) {
  uint64_t n;
  uint64_t a;
  uint64_t b;
  uint64_t r;

  // the literal as the path sees it: equal to l wherever what the path
  // assumes holds, with all that the path assumes replaced by constants

  n = l / 2;

  if (n == 0)
    return l;

  if (*(aig_assumed + n) != 0)
    return assumed_value(l);

  if (*(cofactor_stamps + n) == assumption_epoch)
    r = *(cofactor_values + n);
  else {
    if (aig_is_input(n))
      r = 2 * n;
    else {
      a = aig_cofactor(*(aig_left + n));

      if (a == AIG_FALSE)
        r = AIG_FALSE;
      else {
        b = aig_cofactor(*(aig_right + n));

        cofactoring = 1;

        r = aig_and(a, b);

        cofactoring = 0;
      }
    }

    // the nodes may have moved

    *(cofactor_stamps + n) = assumption_epoch;
    *(cofactor_values + n) = r;
  }

  if (l % 2)
    return aig_not(r);
  else
    return r;
}

uint64_t decide(uint64_t l) {
  // the literal a choice depends on, as the path sees it

  if (deciding) {
    l = aig_cofactor(l);

    if (l > AIG_TRUE)
      if (pending_split == 0)
        pending_split = l;
  }

  return l;
}

// -----------------------------------------------------------------
// -------------------------- BIT VECTORS --------------------------
// -----------------------------------------------------------------

// a bit vector is its width followed by one literal per bit, least
// significant first; bit vectors are built on a scratch stack and
// then interned, so that equal bit vectors are the same pointer

void init_bit_vectors() {
  bv_scratch = zmalloc(BV_SCRATCH_SIZE * sizeof(uint64_t));

  bv_store     = zmalloc(BV_STORE_CHUNK * sizeof(uint64_t));
  bv_store_top = 0;

  bv_table_size = 131072;

  bv_table = zmalloc(bv_table_size * sizeof(uint64_t));
}

uint64_t bv_width(uint64_t* bv) {
  return *bv;
}

uint64_t bv_lit(uint64_t* bv, uint64_t i) {
  return *(bv + 1 + i);
}

void bv_set(uint64_t* bv, uint64_t i, uint64_t l) {
  *(bv + 1 + i) = l;
}

uint64_t* bv_new(uint64_t w) {
  uint64_t* bv;

  if (bv_scratch_top + w + 1 > BV_SCRATCH_SIZE) {
    printf("%s: bit vector scratch stack overflow\n", selfie_name);

    exit(EXITCODE_OUTOFVIRTUALMEMORY);
  }

  bv = bv_scratch + bv_scratch_top;

  bv_scratch_top = bv_scratch_top + w + 1;

  *bv = w;

  return bv;
}

uint64_t bv_hash(uint64_t* bv) {
  uint64_t w;
  uint64_t h;
  uint64_t i;

  w = *bv;
  h = w;
  i = 0;

  while (i < w) {
    h = h * 1099511628211 + bv_lit(bv, i);

    i = i + 1;
  }

  return (h / 65536) % bv_table_size;
}

uint64_t bv_equal(uint64_t* a, uint64_t* b) {
  uint64_t w;
  uint64_t i;

  w = *a;

  if (*b != w)
    return 0;

  i = 0;

  while (i < w) {
    if (bv_lit(a, i) != bv_lit(b, i))
      return 0;

    i = i + 1;
  }

  return 1;
}

void bv_rehash() {
  uint64_t* old_table;
  uint64_t old_size;
  uint64_t i;
  uint64_t* e;
  uint64_t h;

  old_table = bv_table;
  old_size  = bv_table_size;

  bv_table_size = 2 * bv_table_size;

  bv_table = zmalloc(bv_table_size * sizeof(uint64_t));

  i = 0;

  while (i < old_size) {
    e = (uint64_t*) *(old_table + i);

    if (e != (uint64_t*) 0) {
      h = bv_hash(e);

      while (*(bv_table + h) != 0) {
        h = h + 1;

        if (h == bv_table_size)
          h = 0;
      }

      *(bv_table + h) = (uint64_t) e;
    }

    i = i + 1;
  }
}

uint64_t* bv_intern(uint64_t* bv) {
  uint64_t h;
  uint64_t* e;
  uint64_t w;
  uint64_t i;

  // bv is the top of the scratch stack: pop it

  bv_scratch_top = ((uint64_t) bv - (uint64_t) bv_scratch) / sizeof(uint64_t);

  h = bv_hash(bv);

  e = (uint64_t*) *(bv_table + h);

  while (e != (uint64_t*) 0) {
    if (bv_equal(e, bv))
      return e;

    h = h + 1;

    if (h == bv_table_size)
      h = 0;

    e = (uint64_t*) *(bv_table + h);
  }

  w = *bv;

  if (bv_store_top + w + 1 > BV_STORE_CHUNK) {
    bv_store     = zmalloc(BV_STORE_CHUNK * sizeof(uint64_t));
    bv_store_top = 0;
  }

  e = bv_store + bv_store_top;

  bv_store_top = bv_store_top + w + 1;

  i = 0;

  while (i <= w) {
    *(e + i) = *(bv + i);

    i = i + 1;
  }

  *(bv_table + h) = (uint64_t) e;

  bv_count = bv_count + 1;

  if (2 * bv_count > bv_table_size)
    bv_rehash();

  return e;
}

uint64_t* bv_constant(uint64_t value, uint64_t w) {
  uint64_t* r;
  uint64_t i;

  r = bv_new(w);

  i = 0;

  while (i < w) {
    bv_set(r, i, value % 2);

    value = value / 2;

    i = i + 1;
  }

  return bv_intern(r);
}

uint64_t bv_is_constant(uint64_t* a) {
  uint64_t w;
  uint64_t i;

  w = *a;
  i = 0;

  while (i < w) {
    if (bv_lit(a, i) > AIG_TRUE)
      return 0;

    i = i + 1;
  }

  return 1;
}

uint64_t bv_value(uint64_t* a) {
  uint64_t i;
  uint64_t value;

  // assert: a is constant

  i     = *a;
  value = 0;

  while (i > 0) {
    i = i - 1;

    value = value * 2 + bv_lit(a, i);
  }

  return value;
}

uint64_t* bv_fresh(uint64_t w) {
  uint64_t* r;
  uint64_t i;

  r = bv_new(w);

  i = 0;

  while (i < w) {
    bv_set(r, i, aig_input());

    i = i + 1;
  }

  return bv_intern(r);
}

uint64_t* bv_bool(uint64_t l) {
  uint64_t* r;

  r = bv_new(1);

  bv_set(r, 0, l);

  return bv_intern(r);
}

uint64_t* bv_not(uint64_t* a) {
  uint64_t* r;
  uint64_t w;
  uint64_t i;

  w = *a;
  r = bv_new(w);
  i = 0;

  while (i < w) {
    bv_set(r, i, aig_not(bv_lit(a, i)));

    i = i + 1;
  }

  return bv_intern(r);
}

uint64_t* bv_bitwise(uint64_t* a, uint64_t* b, uint64_t op) {
  uint64_t* r;
  uint64_t w;
  uint64_t i;

  // op: 0 and, 1 or, 2 xor

  w = *a;
  r = bv_new(w);
  i = 0;

  while (i < w) {
    if (op == 0)
      bv_set(r, i, aig_and(bv_lit(a, i), bv_lit(b, i)));
    else if (op == 1)
      bv_set(r, i, aig_or(bv_lit(a, i), bv_lit(b, i)));
    else
      bv_set(r, i, aig_xor(bv_lit(a, i), bv_lit(b, i)));

    i = i + 1;
  }

  return bv_intern(r);
}

uint64_t* bv_ite(uint64_t c, uint64_t* a, uint64_t* b) {
  uint64_t* r;
  uint64_t w;
  uint64_t i;

  if (c == AIG_TRUE)
    return a;
  else if (c == AIG_FALSE)
    return b;
  else if (a == b)
    return a;

  w = *a;
  r = bv_new(w);
  i = 0;

  while (i < w) {
    bv_set(r, i, aig_mux(c, bv_lit(a, i), bv_lit(b, i)));

    i = i + 1;
  }

  return bv_intern(r);
}

uint64_t* bv_add(uint64_t* a, uint64_t* b, uint64_t carry) {
  uint64_t* r;
  uint64_t w;
  uint64_t i;
  uint64_t x;
  uint64_t y;
  uint64_t z;

  // ripple-carry adder, bv_carry is the carry out

  w = *a;
  r = bv_new(w);
  i = 0;

  while (i < w) {
    x = bv_lit(a, i);
    y = bv_lit(b, i);

    z = aig_xor(x, y);

    bv_set(r, i, aig_xor(z, carry));

    carry = aig_or(aig_and(x, y), aig_and(z, carry));

    i = i + 1;
  }

  bv_carry = carry;

  return bv_intern(r);
}

uint64_t* bv_sub(uint64_t* a, uint64_t* b) {
  return bv_add(a, bv_not(b), AIG_TRUE);
}

uint64_t* bv_neg(uint64_t* a) {
  return bv_add(bv_not(a), bv_constant(0, *a), AIG_TRUE);
}

uint64_t bv_eq(uint64_t* a, uint64_t* b) {
  uint64_t w;
  uint64_t i;
  uint64_t e;

  if (a == b)
    return AIG_TRUE;

  w = *a;
  e = AIG_TRUE;
  i = 0;

  while (i < w) {
    e = aig_and(e, aig_not(aig_xor(bv_lit(a, i), bv_lit(b, i))));

    if (e == AIG_FALSE)
      return AIG_FALSE;

    i = i + 1;
  }

  return e;
}

uint64_t bv_uge(uint64_t* a, uint64_t* b, uint64_t is_signed) {
  uint64_t w;
  uint64_t i;
  uint64_t x;
  uint64_t y;
  uint64_t carry;

  // a >= b iff a + ~b + 1 carries out; signed by flipping the sign bits

  w = *a;
  i = 0;

  carry = AIG_TRUE;

  while (i < w) {
    x = bv_lit(a, i);
    y = aig_not(bv_lit(b, i));

    if (is_signed)
      if (i == w - 1) {
        x = aig_not(x);
        y = aig_not(y);
      }

    carry = aig_or(aig_and(x, y), aig_and(aig_xor(x, y), carry));

    i = i + 1;
  }

  return carry;
}

uint64_t* bv_shift(uint64_t* a, uint64_t* s, uint64_t kind) {
  uint64_t w;
  uint64_t* r;
  uint64_t* t;
  uint64_t fill;
  uint64_t stage;
  uint64_t distance;
  uint64_t i;
  uint64_t overflow;

  // barrel shifter, kind: 0 sll, 1 srl, 2 sra; shifting by the width or more
  // leaves only the fill bit

  w = *a;

  if (kind == 2)
    fill = bv_lit(a, w - 1);
  else
    fill = AIG_FALSE;

  r = a;

  stage    = 0;
  distance = 1;

  while (distance < w) {
    if (bv_lit(s, stage) != AIG_FALSE) {
      t = bv_new(w);

      i = 0;

      while (i < w) {
        if (kind == 0) {
          if (i >= distance)
            bv_set(t, i, aig_mux(bv_lit(s, stage), bv_lit(r, i - distance), bv_lit(r, i)));
          else
            bv_set(t, i, aig_mux(bv_lit(s, stage), fill, bv_lit(r, i)));
        } else if (i + distance < w)
          bv_set(t, i, aig_mux(bv_lit(s, stage), bv_lit(r, i + distance), bv_lit(r, i)));
        else
          bv_set(t, i, aig_mux(bv_lit(s, stage), fill, bv_lit(r, i)));

        i = i + 1;
      }

      r = bv_intern(t);
    }

    stage    = stage + 1;
    distance = distance * 2;
  }

  overflow = AIG_FALSE;

  while (stage < w) {
    overflow = aig_or(overflow, bv_lit(s, stage));

    stage = stage + 1;
  }

  if (overflow != AIG_FALSE) {
    t = bv_new(w);

    i = 0;

    while (i < w) {
      bv_set(t, i, aig_mux(overflow, fill, bv_lit(r, i)));

      i = i + 1;
    }

    r = bv_intern(t);
  }

  return r;
}

uint64_t* bv_mul(uint64_t* a, uint64_t* b) {
  uint64_t w;
  uint64_t* r;
  uint64_t* t;
  uint64_t i;
  uint64_t j;

  // shift and add

  w = *a;

  r = bv_constant(0, w);

  i = 0;

  while (i < w) {
    if (bv_lit(b, i) != AIG_FALSE) {
      t = bv_new(w);

      j = 0;

      while (j < w) {
        if (j < i)
          bv_set(t, j, AIG_FALSE);
        else
          bv_set(t, j, aig_and(bv_lit(a, j - i), bv_lit(b, i)));

        j = j + 1;
      }

      t = bv_intern(t);

      r = bv_add(r, t, AIG_FALSE);
    }

    i = i + 1;
  }

  return r;
}

uint64_t* bv_udivrem(uint64_t* a, uint64_t* b, uint64_t remainder) {
  uint64_t w;
  uint64_t* q;
  uint64_t* r;
  uint64_t* s;
  uint64_t* d;
  uint64_t top;
  uint64_t ge;
  uint64_t i;
  uint64_t j;

  // restoring division; dividing by zero gives all ones and the dividend
  // as remainder, as BTOR2 defines it

  w = *a;

  q = bv_new(w);

  r = bv_constant(0, w);

  i = w;

  while (i > 0) {
    i = i - 1;

    // shift the remainder left by one, the bit shifted out is top

    top = bv_lit(r, w - 1);

    s = bv_new(w);

    bv_set(s, 0, bv_lit(a, i));

    j = 1;

    while (j < w) {
      bv_set(s, j, bv_lit(r, j - 1));

      j = j + 1;
    }

    s = bv_intern(s);

    d = bv_sub(s, b);

    ge = aig_or(top, bv_carry);

    bv_set(q, i, ge);

    r = bv_ite(ge, d, s);
  }

  q = bv_intern(q);

  if (remainder)
    return r;
  else
    return q;
}

uint64_t* bv_sdivrem(uint64_t* a, uint64_t* b, uint64_t remainder) {
  uint64_t w;
  uint64_t sa;
  uint64_t sb;
  uint64_t* r;

  // signed through absolute values; the remainder has the sign of the dividend

  w = *a;

  sa = bv_lit(a, w - 1);
  sb = bv_lit(b, w - 1);

  r = bv_udivrem(bv_ite(sa, bv_neg(a), a), bv_ite(sb, bv_neg(b), b), remainder);

  if (remainder)
    return bv_ite(sa, bv_neg(r), r);
  else
    return bv_ite(aig_xor(sa, sb), bv_neg(r), r);
}

uint64_t* bv_ext(uint64_t* a, uint64_t extra, uint64_t is_signed) {
  uint64_t w;
  uint64_t* r;
  uint64_t i;

  w = *a;
  r = bv_new(w + extra);
  i = 0;

  while (i < w + extra) {
    if (i < w)
      bv_set(r, i, bv_lit(a, i));
    else if (is_signed)
      bv_set(r, i, bv_lit(a, w - 1));
    else
      bv_set(r, i, AIG_FALSE);

    i = i + 1;
  }

  return bv_intern(r);
}

uint64_t* bv_slice(uint64_t* a, uint64_t u, uint64_t l) {
  uint64_t* r;
  uint64_t i;

  r = bv_new(u - l + 1);
  i = l;

  while (i <= u) {
    bv_set(r, i - l, bv_lit(a, i));

    i = i + 1;
  }

  return bv_intern(r);
}

uint64_t* bv_concat(uint64_t* a, uint64_t* b) {
  uint64_t wa;
  uint64_t wb;
  uint64_t* r;
  uint64_t i;

  // a is the upper part, b the lower

  wa = *a;
  wb = *b;

  r = bv_new(wa + wb);
  i = 0;

  while (i < wa + wb) {
    if (i < wb)
      bv_set(r, i, bv_lit(b, i));
    else
      bv_set(r, i, bv_lit(a, i - wb));

    i = i + 1;
  }

  return bv_intern(r);
}

// what an operation undoes is found by structure, not by the solver:
// (x + v) - v, (x - v) + v, and (x ^ v) ^ v are x, constants added in
// a row add up; this is what makes a step followed by its inverse
// collapse where the model is reversible by construction

void undo_record(uint64_t* result, uint64_t kind, uint64_t* a, uint64_t* b) {
  uint64_t* old_results;
  uint64_t* old_kinds;
  uint64_t* old_lefts;
  uint64_t* old_rights;
  uint64_t old_size;
  uint64_t i;
  uint64_t h;

  if (2 * undo_count >= undo_size) {
    old_results = undo_results;
    old_kinds   = undo_kinds;
    old_lefts   = undo_lefts;
    old_rights  = undo_rights;
    old_size    = undo_size;

    if (undo_size == 0)
      undo_size = 65536;
    else
      undo_size = 2 * undo_size;

    undo_results = zmalloc(undo_size * sizeof(uint64_t));
    undo_kinds   = zmalloc(undo_size * sizeof(uint64_t));
    undo_lefts   = zmalloc(undo_size * sizeof(uint64_t));
    undo_rights  = zmalloc(undo_size * sizeof(uint64_t));

    undo_count = 0;

    i = 0;

    while (i < old_size) {
      if (*(old_results + i) != 0)
        undo_record((uint64_t*) *(old_results + i), *(old_kinds + i), (uint64_t*) *(old_lefts + i), (uint64_t*) *(old_rights + i));

      i = i + 1;
    }
  }

  h = (((uint64_t) result * 6364136223846793005) / 65536) % undo_size;

  while (*(undo_results + h) != 0) {
    if (*(undo_results + h) == (uint64_t) result)
      // keep the first way the result was made
      return;

    h = h + 1;

    if (h == undo_size)
      h = 0;
  }

  *(undo_results + h) = (uint64_t) result;
  *(undo_kinds + h)   = kind;
  *(undo_lefts + h)   = (uint64_t) a;
  *(undo_rights + h)  = (uint64_t) b;

  undo_count = undo_count + 1;
}

uint64_t undo_find(uint64_t* result) {
  uint64_t h;

  // index of the record of result plus one, or 0

  if (undo_size == 0)
    return 0;

  h = (((uint64_t) result * 6364136223846793005) / 65536) % undo_size;

  while (*(undo_results + h) != 0) {
    if (*(undo_results + h) == (uint64_t) result)
      return h + 1;

    h = h + 1;

    if (h == undo_size)
      h = 0;
  }

  return 0;
}

uint64_t* bv_add_normal(uint64_t* a, uint64_t* b) {
  uint64_t* r;
  uint64_t h;
  uint64_t c;

  // the constant, if any, is b

  if (bv_is_constant(a)) {
    r = a;
    a = b;
    b = r;
  }

  if (bv_is_constant(b)) {
    if (bv_is_constant(a))
      return bv_add(a, b, AIG_FALSE);

    c = bv_value(b);

    if (c == 0)
      return a;

    h = undo_find(a);

    if (h != 0)
      if (*(undo_kinds + h - 1) == UNDO_ADD)
        if (bv_is_constant((uint64_t*) *(undo_rights + h - 1))) {
          // (u + c0) + c is u + (c0 + c)

          b = bv_constant(bv_value((uint64_t*) *(undo_rights + h - 1)) + c, *a);

          a = (uint64_t*) *(undo_lefts + h - 1);

          if (bv_value(b) == 0)
            return a;
        }
  } else {
    h = undo_find(a);

    if (h != 0)
      if (*(undo_kinds + h - 1) == UNDO_SUB)
        if (*(undo_rights + h - 1) == (uint64_t) b)
          // (u - b) + b
          return (uint64_t*) *(undo_lefts + h - 1);

    h = undo_find(b);

    if (h != 0)
      if (*(undo_kinds + h - 1) == UNDO_SUB)
        if (*(undo_rights + h - 1) == (uint64_t) a)
          // a + (u - a)
          return (uint64_t*) *(undo_lefts + h - 1);
  }

  r = bv_add(a, b, AIG_FALSE);

  undo_record(r, UNDO_ADD, a, b);

  return r;
}

uint64_t* bv_sub_normal(uint64_t* a, uint64_t* b) {
  uint64_t* r;
  uint64_t h;

  if (bv_is_constant(b))
    if (not(bv_is_constant(a)))
      // subtracting a constant is adding its negation
      return bv_add_normal(a, bv_constant(0 - bv_value(b), *a));

  h = undo_find(a);

  if (h != 0)
    if (*(undo_kinds + h - 1) == UNDO_ADD) {
      if (*(undo_rights + h - 1) == (uint64_t) b)
        // (u + b) - b
        return (uint64_t*) *(undo_lefts + h - 1);
      else if (*(undo_lefts + h - 1) == (uint64_t) b)
        // (b + w) - b
        return (uint64_t*) *(undo_rights + h - 1);
    }

  r = bv_sub(a, b);

  undo_record(r, UNDO_SUB, a, b);

  return r;
}

uint64_t* bv_xor_normal(uint64_t* a, uint64_t* b) {
  uint64_t* r;
  uint64_t h;

  h = undo_find(a);

  if (h != 0)
    if (*(undo_kinds + h - 1) == UNDO_XOR) {
      if (*(undo_rights + h - 1) == (uint64_t) b)
        // (u ^ b) ^ b
        return (uint64_t*) *(undo_lefts + h - 1);
      else if (*(undo_lefts + h - 1) == (uint64_t) b)
        return (uint64_t*) *(undo_rights + h - 1);
    }

  h = undo_find(b);

  if (h != 0)
    if (*(undo_kinds + h - 1) == UNDO_XOR) {
      if (*(undo_rights + h - 1) == (uint64_t) a)
        // a ^ (u ^ a)
        return (uint64_t*) *(undo_lefts + h - 1);
      else if (*(undo_lefts + h - 1) == (uint64_t) a)
        return (uint64_t*) *(undo_rights + h - 1);
    }

  r = bv_bitwise(a, b, 2);

  undo_record(r, UNDO_XOR, a, b);

  return r;
}

uint64_t bv_eq_normal(uint64_t* a, uint64_t* b) {
  uint64_t h;
  uint64_t c;
  uint64_t d;

  // u + c and u + d are equal iff c and d are

  c = 0;
  d = 0;

  h = undo_find(a);

  if (h != 0)
    if (*(undo_kinds + h - 1) == UNDO_ADD)
      if (bv_is_constant((uint64_t*) *(undo_rights + h - 1))) {
        c = bv_value((uint64_t*) *(undo_rights + h - 1));

        a = (uint64_t*) *(undo_lefts + h - 1);
      }

  h = undo_find(b);

  if (h != 0)
    if (*(undo_kinds + h - 1) == UNDO_ADD)
      if (bv_is_constant((uint64_t*) *(undo_rights + h - 1))) {
        d = bv_value((uint64_t*) *(undo_rights + h - 1));

        b = (uint64_t*) *(undo_lefts + h - 1);
      }

  if (a == b) {
    if (c == d)
      return AIG_TRUE;
    else
      return AIG_FALSE;
  }

  if (c == d)
    return bv_eq(a, b);

  // the sums as they were

  if (c != 0)
    a = bv_add_normal(a, bv_constant(c, *a));

  if (d != 0)
    b = bv_add_normal(b, bv_constant(d, *b));

  return bv_eq(a, b);
}

// -----------------------------------------------------------------
// ---------------------------- ARRAYS -----------------------------
// -----------------------------------------------------------------

// an array value is a base, the array a state holds initially, or a
// write on top of an array, or a choice between two arrays; reads
// eliminate writes and choices, which is finite since k is bounded

void init_arrays() {
  arr_capacity = 65536;

  arr_kind = zmalloc(arr_capacity * sizeof(uint64_t));
  arr_x    = zmalloc(arr_capacity * sizeof(uint64_t));
  arr_y    = zmalloc(arr_capacity * sizeof(uint64_t));
  arr_z    = zmalloc(arr_capacity * sizeof(uint64_t));
  arr_iw   = zmalloc(arr_capacity * sizeof(uint64_t));
  arr_ew   = zmalloc(arr_capacity * sizeof(uint64_t));

  arr_count = 1;

  memo_size = 131072;

  memo_array = zmalloc(memo_size * sizeof(uint64_t));
  memo_index = zmalloc(memo_size * sizeof(uint64_t));
  memo_value = zmalloc(memo_size * sizeof(uint64_t));
}

uint64_t arr_new(uint64_t kind, uint64_t x, uint64_t y, uint64_t z, uint64_t iw, uint64_t ew) {
  if (arr_count == arr_capacity) {
    arr_kind = grow_words(arr_kind, arr_capacity, 2 * arr_capacity);
    arr_x    = grow_words(arr_x, arr_capacity, 2 * arr_capacity);
    arr_y    = grow_words(arr_y, arr_capacity, 2 * arr_capacity);
    arr_z    = grow_words(arr_z, arr_capacity, 2 * arr_capacity);
    arr_iw   = grow_words(arr_iw, arr_capacity, 2 * arr_capacity);
    arr_ew   = grow_words(arr_ew, arr_capacity, 2 * arr_capacity);

    arr_capacity = 2 * arr_capacity;
  }

  *(arr_kind + arr_count) = kind;
  *(arr_x + arr_count)    = x;
  *(arr_y + arr_count)    = y;
  *(arr_z + arr_count)    = z;
  *(arr_iw + arr_count)   = iw;
  *(arr_ew + arr_count)   = ew;

  arr_count = arr_count + 1;

  return arr_count - 1;
}

uint64_t arr_base(uint64_t* state_nid, uint64_t symbolic) {
  uint64_t iw;
  uint64_t* elements;

  // x: the state, y: 1 if its elements are free, z: the free elements, allocated on demand

  iw = eval_array_size(get_sid(state_nid));

  elements = (uint64_t*) 0;

  if (symbolic) {
    if (iw > 24) {
      printf("%s: symbolic array %s with %lu-bit addresses is too large\n", selfie_name, (char*) get_arg1(state_nid), iw);

      exit(EXITCODE_OUTOFVIRTUALMEMORY);
    }

    elements = zmalloc(two_to_the_power_of(iw) * sizeof(uint64_t));
  }

  return arr_new(ARR_BASE, (uint64_t) state_nid, symbolic, (uint64_t) elements, iw, eval_element_size(get_sid(state_nid)));
}

uint64_t* arr_probe(uint64_t a, uint64_t* index) {
  uint64_t h;

  // what a read of a at index is known to return without evaluating
  // anything: the value of a write at that index, or a read done before

  if (*(arr_kind + a) == ARR_WRITE)
    if (*(arr_y + a) == (uint64_t) index)
      return (uint64_t*) *(arr_z + a);

  h = memo_hash(a, index);

  while (*(memo_array + h) != 0) {
    if (*(memo_array + h) == a)
      if (*(memo_index + h) == (uint64_t) index)
        return (uint64_t*) *(memo_value + h);

    h = h + 1;

    if (h == memo_size)
      h = 0;
  }

  return (uint64_t*) 0;
}

uint64_t arr_write(uint64_t a, uint64_t* index, uint64_t* value) {
  // a write to the index of the write below replaces that write

  if (*(arr_kind + a) == ARR_WRITE)
    if (*(arr_y + a) == (uint64_t) index)
      a = *(arr_x + a);

  // writing back what is there changes nothing

  if (arr_probe(a, index) == value)
    return a;

  return arr_new(ARR_WRITE, a, (uint64_t) index, (uint64_t) value, *(arr_iw + a), *(arr_ew + a));
}

uint64_t arr_ite(uint64_t c, uint64_t a, uint64_t b) {
  if (c == AIG_TRUE)
    return a;
  else if (c == AIG_FALSE)
    return b;
  else if (a == b)
    return a;

  return arr_new(ARR_ITE, c, a, b, *(arr_iw + a), *(arr_ew + a));
}

uint64_t* arr_element(uint64_t a, uint64_t index) {
  uint64_t* elements;
  uint64_t* element;

  // element of a base: free bits, allocated on first use, or the state's value

  if (*(arr_y + a)) {
    elements = (uint64_t*) *(arr_z + a);

    element = (uint64_t*) *(elements + index);

    if (element == (uint64_t*) 0) {
      element = bv_fresh(*(arr_ew + a));

      *(elements + index) = (uint64_t) element;
    }

    return element;
  } else
    return bv_constant(read_array_raw((uint64_t*) *(arr_x + a), index), *(arr_ew + a));
}

uint64_t* arr_base_read(uint64_t a, uint64_t* index, uint64_t bit, uint64_t prefix) {
  uint64_t l;

  // multiplexer tree over the index bits that are not constant

  if (bit == 0)
    return arr_element(a, prefix);

  l = bv_lit(index, bit - 1);

  if (l == AIG_FALSE)
    return arr_base_read(a, index, bit - 1, prefix * 2);
  else if (l == AIG_TRUE)
    return arr_base_read(a, index, bit - 1, prefix * 2 + 1);
  else
    return bv_ite(l,
      arr_base_read(a, index, bit - 1, prefix * 2 + 1),
      arr_base_read(a, index, bit - 1, prefix * 2));
}

uint64_t memo_hash(uint64_t a, uint64_t* index) {
  return ((a * 6364136223846793005 + (uint64_t) index * 1442695040888963407) / 65536) % memo_size;
}

void memo_rehash() {
  uint64_t* old_array;
  uint64_t* old_index;
  uint64_t* old_value;
  uint64_t old_size;
  uint64_t i;
  uint64_t h;

  old_array = memo_array;
  old_index = memo_index;
  old_value = memo_value;
  old_size  = memo_size;

  memo_size = 2 * memo_size;

  memo_array = zmalloc(memo_size * sizeof(uint64_t));
  memo_index = zmalloc(memo_size * sizeof(uint64_t));
  memo_value = zmalloc(memo_size * sizeof(uint64_t));

  i = 0;

  while (i < old_size) {
    if (*(old_array + i) != 0) {
      h = memo_hash(*(old_array + i), (uint64_t*) *(old_index + i));

      while (*(memo_array + h) != 0) {
        h = h + 1;

        if (h == memo_size)
          h = 0;
      }

      *(memo_array + h) = *(old_array + i);
      *(memo_index + h) = *(old_index + i);
      *(memo_value + h) = *(old_value + i);
    }

    i = i + 1;
  }
}

uint64_t* arr_read(uint64_t a, uint64_t* index) {
  uint64_t index_is_constant;
  uint64_t skipping;
  uint64_t h;
  uint64_t e;
  uint64_t* r;

  // writes at other constant indices are skipped

  index_is_constant = bv_is_constant(index);

  skipping = 1;

  while (skipping) {
    if (*(arr_kind + a) == ARR_WRITE) {
      if (*(arr_y + a) == (uint64_t) index)
        return (uint64_t*) *(arr_z + a);
      else if (index_is_constant) {
        if (bv_is_constant((uint64_t*) *(arr_y + a)))
          a = *(arr_x + a);
        else
          skipping = 0;
      } else
        skipping = 0;
    } else
      skipping = 0;
  }

  h = memo_hash(a, index);

  while (*(memo_array + h) != 0) {
    if (*(memo_array + h) == a)
      if (*(memo_index + h) == (uint64_t) index)
        if (or(not(deciding), *(arr_kind + a) == ARR_BASE))
          return (uint64_t*) *(memo_value + h);

    h = h + 1;

    if (h == memo_size)
      h = 0;
  }

  if (*(arr_kind + a) == ARR_BASE)
    r = arr_base_read(a, index, *(arr_iw + a), 0);
  else if (*(arr_kind + a) == ARR_WRITE) {
    e = decide(bv_eq_normal(index, (uint64_t*) *(arr_y + a)));

    if (e == AIG_TRUE)
      r = (uint64_t*) *(arr_z + a);
    else if (e == AIG_FALSE)
      r = arr_read(*(arr_x + a), index);
    else
      r = bv_ite(e, (uint64_t*) *(arr_z + a), arr_read(*(arr_x + a), index));
  } else {
    e = decide(*(arr_x + a));

    if (e == AIG_TRUE)
      r = arr_read(*(arr_y + a), index);
    else if (e == AIG_FALSE)
      r = arr_read(*(arr_z + a), index);
    else
      r = bv_ite(e, arr_read(*(arr_y + a), index), arr_read(*(arr_z + a), index));
  }

  // on a path only reads of bases are independent of the path

  if (deciding)
    if (*(arr_kind + a) != ARR_BASE)
      return r;

  // the table may have been rehashed by nested reads

  h = memo_hash(a, index);

  while (*(memo_array + h) != 0) {
    h = h + 1;

    if (h == memo_size)
      h = 0;
  }

  *(memo_array + h) = a;
  *(memo_index + h) = (uint64_t) index;
  *(memo_value + h) = (uint64_t) r;

  memo_count = memo_count + 1;

  if (2 * memo_count > memo_size)
    memo_rehash();

  return r;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------------- CDCL ------------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// conflict-driven clause learning next to babysat's enumeration:
// two watched literals, first-UIP learning, activities, restarts;
// variables are 1 to n, literal 2 * variable + 1 if negative

uint64_t sat_negate(uint64_t l) {
  if (l % 2)
    return l - 1;
  else
    return l + 1;
}

uint64_t sat_lit_value(uint64_t l) {
  uint64_t v;

  // SAT_TRUE, SAT_FALSE, or SAT_UNASSIGNED

  v = *(sat_values + l / 2);

  if (v == SAT_UNASSIGNED)
    return SAT_UNASSIGNED;
  else if (l % 2)
    return 3 - v;
  else
    return v;
}

void sat_reset(uint64_t variables) {
  uint64_t n;
  uint64_t i;

  // prepares the solver for a new instance, reusing its memory

  n = variables + 1;

  if (n > sat_capacity) {
    sat_values     = zmalloc(n * sizeof(uint64_t));
    sat_levels     = zmalloc(n * sizeof(uint64_t));
    sat_reasons    = zmalloc(n * sizeof(uint64_t));
    sat_trail      = zmalloc(n * sizeof(uint64_t));
    sat_starts     = zmalloc(n * sizeof(uint64_t));
    sat_activities = zmalloc(n * sizeof(uint64_t));
    sat_phases     = zmalloc(n * sizeof(uint64_t));
    sat_seen       = zmalloc(n * sizeof(uint64_t));
    sat_heap       = zmalloc(n * sizeof(uint64_t));
    sat_positions  = zmalloc(n * sizeof(uint64_t));
    sat_learnt     = zmalloc(n * sizeof(uint64_t));
    sat_keep       = zmalloc(n * sizeof(uint64_t));

    sat_watches         = grow_words(sat_watches, 2 * sat_capacity, 2 * n);
    sat_watch_sizes     = zmalloc(2 * n * sizeof(uint64_t));
    sat_watch_capacities = grow_words(sat_watch_capacities, 2 * sat_capacity, 2 * n);

    sat_capacity = n;
  } else {
    i = 0;

    while (i < n) {
      *(sat_values + i)     = SAT_UNASSIGNED;
      *(sat_activities + i) = 0;
      *(sat_phases + i)     = 0;
      *(sat_seen + i)       = 0;
      *(sat_positions + i)  = 0;

      *(sat_watch_sizes + 2 * i)     = 0;
      *(sat_watch_sizes + 2 * i + 1) = 0;

      i = i + 1;
    }
  }

  sat_variables = variables;

  sat_db_size = 1; // clause reference 0 means no clause

  if (sat_db_capacity == 0) {
    sat_db_capacity = 1048576;

    sat_db = zmalloc(sat_db_capacity * sizeof(uint64_t));
  }

  sat_trail_size = 0;
  sat_head       = 0;
  sat_level      = 0;
  sat_heap_size  = 0;

  sat_increment = 1;

  sat_inconsistent = 0;

  sat_clauses   = 0;
  sat_conflicts = 0;
  sat_decisions = 0;
  sat_restarts  = 0;

  i = 1;

  while (i <= variables) {
    sat_heap_insert(i);

    i = i + 1;
  }
}

// activity heap: the variable with the highest activity is on top

void sat_heap_up(uint64_t position) {
  uint64_t v;
  uint64_t parent;
  uint64_t moving;

  // positions are stored plus one, zero means not in heap

  v = *(sat_heap + position);

  moving = position > 0;

  while (moving) {
    parent = (position - 1) / 2;

    if (*(sat_activities + *(sat_heap + parent)) < *(sat_activities + v)) {
      *(sat_heap + position) = *(sat_heap + parent);

      *(sat_positions + *(sat_heap + position)) = position + 1;

      position = parent;

      moving = position > 0;
    } else
      moving = 0;
  }

  *(sat_heap + position) = v;

  *(sat_positions + v) = position + 1;
}

void sat_heap_down(uint64_t position) {
  uint64_t v;
  uint64_t child;
  uint64_t moving;

  v = *(sat_heap + position);

  moving = 2 * position + 1 < sat_heap_size;

  while (moving) {
    child = 2 * position + 1;

    if (child + 1 < sat_heap_size)
      if (*(sat_activities + *(sat_heap + child + 1)) > *(sat_activities + *(sat_heap + child)))
        child = child + 1;

    if (*(sat_activities + *(sat_heap + child)) > *(sat_activities + v)) {
      *(sat_heap + position) = *(sat_heap + child);

      *(sat_positions + *(sat_heap + position)) = position + 1;

      position = child;

      moving = 2 * position + 1 < sat_heap_size;
    } else
      moving = 0;
  }

  *(sat_heap + position) = v;

  *(sat_positions + v) = position + 1;
}

void sat_heap_insert(uint64_t v) {
  if (*(sat_positions + v) == 0) {
    *(sat_heap + sat_heap_size) = v;

    sat_heap_size = sat_heap_size + 1;

    sat_heap_up(sat_heap_size - 1);
  }
}

uint64_t sat_heap_pop() {
  uint64_t v;

  v = *sat_heap;

  *(sat_positions + v) = 0;

  sat_heap_size = sat_heap_size - 1;

  if (sat_heap_size > 0) {
    *sat_heap = *(sat_heap + sat_heap_size);

    sat_heap_down(0);
  }

  return v;
}

void sat_bump(uint64_t v) {
  uint64_t i;

  *(sat_activities + v) = *(sat_activities + v) + sat_increment;

  if (*(sat_activities + v) > 1152921504606846976) {
    // rescale all activities by 2^30, which keeps their order
    i = 1;

    while (i <= sat_variables) {
      *(sat_activities + i) = *(sat_activities + i) / 1073741824;

      i = i + 1;
    }

    sat_increment = sat_increment / 1073741824;

    if (sat_increment == 0)
      sat_increment = 1;
  }

  if (*(sat_positions + v) != 0)
    sat_heap_up(*(sat_positions + v) - 1);
}

void sat_watch(uint64_t l, uint64_t clause) {
  uint64_t n;
  uint64_t capacity;

  n        = *(sat_watch_sizes + l);
  capacity = *(sat_watch_capacities + l);

  if (n == capacity) {
    if (capacity == 0)
      capacity = 4;
    else
      capacity = 2 * capacity;

    *(sat_watches + l) = (uint64_t) grow_words((uint64_t*) *(sat_watches + l), n, capacity);

    *(sat_watch_capacities + l) = capacity;
  }

  *((uint64_t*) *(sat_watches + l) + n) = clause;

  *(sat_watch_sizes + l) = n + 1;
}

void sat_enqueue(uint64_t l, uint64_t reason) {
  uint64_t v;

  v = l / 2;

  if (l % 2)
    *(sat_values + v) = SAT_FALSE;
  else
    *(sat_values + v) = SAT_TRUE;

  *(sat_levels + v)  = sat_level;
  *(sat_reasons + v) = reason;

  *(sat_trail + sat_trail_size) = l;

  sat_trail_size = sat_trail_size + 1;
}

uint64_t sat_new_clause(uint64_t* literals, uint64_t n) {
  uint64_t clause;
  uint64_t i;

  // stores the clause and watches its first two literals

  if (sat_db_size + n + 1 > sat_db_capacity) {
    while (sat_db_size + n + 1 > sat_db_capacity)
      sat_db_capacity = 2 * sat_db_capacity;

    sat_db = grow_words(sat_db, sat_db_size, sat_db_capacity);
  }

  clause = sat_db_size;

  *(sat_db + clause) = n;

  i = 0;

  while (i < n) {
    *(sat_db + clause + 1 + i) = *(literals + i);

    i = i + 1;
  }

  sat_db_size = sat_db_size + n + 1;

  sat_watch(*literals, clause);
  sat_watch(*(literals + 1), clause);

  return clause;
}

void sat_add_clause(uint64_t* literals, uint64_t n) {
  uint64_t i;
  uint64_t j;
  uint64_t l;
  uint64_t keep;
  uint64_t m;

  // adds a clause of the instance before solving: tautologies are dropped,
  // repeated literals removed, units go onto the trail without propagating

  m = 0;
  i = 0;

  while (i < n) {
    l = *(literals + i);

    keep = 1;

    j = 0;

    while (j < m) {
      if (*(literals + j) == l)
        keep = 0;
      else if (*(literals + j) == sat_negate(l))
        return;

      j = j + 1;
    }

    if (keep) {
      *(literals + m) = l;

      m = m + 1;
    }

    i = i + 1;
  }

  sat_clauses = sat_clauses + 1;

  if (m == 0)
    sat_inconsistent = 1;
  else if (m == 1) {
    l = *literals;

    if (sat_lit_value(l) == SAT_FALSE)
      sat_inconsistent = 1;
    else if (sat_lit_value(l) == SAT_UNASSIGNED)
      sat_enqueue(l, 0);
  } else
    sat_new_clause(literals, m);
}

uint64_t sat_propagate() {
  uint64_t false_literal;
  uint64_t* watches;
  uint64_t n;
  uint64_t i;
  uint64_t j;
  uint64_t clause;
  uint64_t first;
  uint64_t size;
  uint64_t k;
  uint64_t l;
  uint64_t found;
  uint64_t conflict;

  // unit propagation, returns a conflicting clause or 0

  conflict = 0;

  while (sat_head < sat_trail_size) {
    false_literal = sat_negate(*(sat_trail + sat_head));

    sat_head = sat_head + 1;

    watches = (uint64_t*) *(sat_watches + false_literal);

    n = *(sat_watch_sizes + false_literal);

    i = 0;
    j = 0;

    while (i < n) {
      clause = *(watches + i);

      i = i + 1;

      // the false literal goes second

      if (*(sat_db + clause + 1) == false_literal) {
        *(sat_db + clause + 1) = *(sat_db + clause + 2);
        *(sat_db + clause + 2) = false_literal;
      }

      first = *(sat_db + clause + 1);

      if (sat_lit_value(first) == SAT_TRUE) {
        *(watches + j) = clause;

        j = j + 1;
      } else {
        // look for another literal to watch

        size = *(sat_db + clause);

        found = 0;

        k = 2;

        while (k < size) {
          l = *(sat_db + clause + 1 + k);

          if (sat_lit_value(l) != SAT_FALSE) {
            *(sat_db + clause + 2)     = l;
            *(sat_db + clause + 1 + k) = false_literal;

            sat_watch(l, clause);

            found = 1;

            k = size;
          } else
            k = k + 1;
        }

        if (found == 0) {
          *(watches + j) = clause;

          j = j + 1;

          if (sat_lit_value(first) == SAT_FALSE) {
            // conflict: keep the remaining watches and stop

            conflict = clause;

            while (i < n) {
              *(watches + j) = *(watches + i);

              i = i + 1;
              j = j + 1;
            }

            sat_head = sat_trail_size;
          } else
            sat_enqueue(first, clause);
        }
      }
    }

    *(sat_watch_sizes + false_literal) = j;
  }

  return conflict;
}

void sat_cancel_until(uint64_t level) {
  uint64_t v;

  if (sat_level > level) {
    while (sat_trail_size > *(sat_starts + level)) {
      sat_trail_size = sat_trail_size - 1;

      v = *(sat_trail + sat_trail_size) / 2;

      // remember the phase

      *(sat_phases + v) = *(sat_values + v);

      *(sat_values + v) = SAT_UNASSIGNED;

      sat_heap_insert(v);
    }

    sat_head  = sat_trail_size;
    sat_level = level;
  }
}

uint64_t sat_analyze(uint64_t conflict) {
  uint64_t n;
  uint64_t paths;
  uint64_t p;
  uint64_t index;
  uint64_t size;
  uint64_t i;
  uint64_t q;
  uint64_t v;
  uint64_t level;
  uint64_t analyzing;

  // first unique implication point: resolves the conflicting clause with
  // reasons until one literal of the current level is left; the learnt
  // clause is in sat_learnt with that literal first, its size in
  // sat_learnt_size; returns the level to backjump to

  n     = 1;
  paths = 0;
  p     = 0;

  index = sat_trail_size;

  analyzing = 1;

  while (analyzing) {
    size = *(sat_db + conflict);

    // the first literal of a reason is the implied literal p

    if (p == 0)
      i = 0;
    else
      i = 1;

    while (i < size) {
      q = *(sat_db + conflict + 1 + i);

      v = q / 2;

      if (*(sat_seen + v) == 0)
        if (*(sat_levels + v) > 0) {
          sat_bump(v);

          *(sat_seen + v) = 1;

          if (*(sat_levels + v) >= sat_level)
            paths = paths + 1;
          else {
            *(sat_learnt + n) = q;

            n = n + 1;
          }
        }

      i = i + 1;
    }

    // next literal on the trail to resolve

    index = index - 1;

    while (*(sat_seen + *(sat_trail + index) / 2) == 0)
      index = index - 1;

    p = *(sat_trail + index);

    conflict = *(sat_reasons + p / 2);

    *(sat_seen + p / 2) = 0;

    paths = paths - 1;

    if (paths == 0)
      analyzing = 0;
  }

  *sat_learnt = sat_negate(p);

  // minimize: a literal is redundant if its reason only has literals that
  // are in the clause or false at level 0

  *(sat_seen + p / 2) = 1;

  i = 1;

  while (i < n) {
    q = *(sat_learnt + i);

    conflict = *(sat_reasons + q / 2);

    *(sat_keep + i) = 1;

    if (conflict != 0) {
      *(sat_keep + i) = 0;

      size = *(sat_db + conflict);

      v = 1;

      while (v < size) {
        index = *(sat_db + conflict + 1 + v) / 2;

        if (*(sat_seen + index) == 0)
          if (*(sat_levels + index) > 0) {
            *(sat_keep + i) = 1;

            v = size;
          }

        v = v + 1;
      }
    }

    i = i + 1;
  }

  *(sat_seen + p / 2) = 0;

  // backjump to the highest level among the other literals, that literal goes second

  level = 0;

  size = 1;

  i = 1;

  while (i < n) {
    q = *(sat_learnt + i);

    *(sat_seen + q / 2) = 0;

    if (*(sat_keep + i)) {
      *(sat_learnt + size) = q;

      if (*(sat_levels + q / 2) > level) {
        level = *(sat_levels + q / 2);

        *(sat_learnt + size) = *(sat_learnt + 1);
        *(sat_learnt + 1)    = q;
      }

      size = size + 1;
    }

    i = i + 1;
  }

  sat_learnt_size = size;

  return level;
}

uint64_t sat_luby(uint64_t i) {
  uint64_t size;
  uint64_t sequence;

  // i-th element of the Luby sequence 1 1 2 1 1 2 4 ..., counting from 0

  size     = 1;
  sequence = 0;

  while (size < i + 1) {
    sequence = sequence + 1;

    size = 2 * size + 1;
  }

  while (size - 1 != i) {
    size = (size - 1) / 2;

    sequence = sequence - 1;

    i = i % size;
  }

  return two_to_the_power_of(sequence);
}

void sat_reduce() {
  uint64_t from;
  uint64_t to;
  uint64_t size;
  uint64_t middle;
  uint64_t keep;
  uint64_t clause;
  uint64_t i;
  uint64_t j;
  uint64_t l;

  // at level 0: forgets the older half of the long learnt clauses, compacts
  // the clauses, and watches all clauses anew

  middle = sat_first_learnt + (sat_db_size - sat_first_learnt) / 2;

  from = sat_first_learnt;
  to   = sat_first_learnt;

  while (from < sat_db_size) {
    size = *(sat_db + from);

    keep = 1;

    if (from < middle)
      if (size > 8)
        keep = 0;

    if (keep) {
      i = 0;

      while (i <= size) {
        *(sat_db + to + i) = *(sat_db + from + i);

        i = i + 1;
      }

      to = to + size + 1;
    }

    from = from + size + 1;
  }

  sat_db_size = to;

  // no reasons at level 0

  i = 0;

  while (i < sat_trail_size) {
    *(sat_reasons + *(sat_trail + i) / 2) = 0;

    i = i + 1;
  }

  i = 0;

  while (i < 2 * sat_variables + 2) {
    *(sat_watch_sizes + i) = 0;

    i = i + 1;
  }

  clause = 1;

  while (clause < sat_db_size) {
    size = *(sat_db + clause);

    // two literals that are not false go first; there are two unless the
    // clause is true, since level 0 is propagated

    j = 0;

    i = 0;

    while (i < size) {
      l = *(sat_db + clause + 1 + i);

      if (sat_lit_value(l) != SAT_FALSE) {
        *(sat_db + clause + 1 + i) = *(sat_db + clause + 1 + j);
        *(sat_db + clause + 1 + j) = l;

        j = j + 1;

        if (j == 2)
          i = size;
      }

      i = i + 1;
    }

    sat_watch(*(sat_db + clause + 1), clause);
    sat_watch(*(sat_db + clause + 2), clause);

    clause = clause + size + 1;
  }

  sat_reductions = sat_reductions + 1;
}

uint64_t sat_solve() {
  uint64_t conflict;
  uint64_t level;
  uint64_t clause;
  uint64_t limit;
  uint64_t since;
  uint64_t budget;
  uint64_t v;
  uint64_t picking;

  // returns SAT_TRUE if satisfiable, with the model in sat_values, else SAT_FALSE

  if (sat_inconsistent)
    return SAT_FALSE;

  limit = 64 * sat_luby(0);
  since = 0;

  sat_first_learnt = sat_db_size;

  budget = sat_db_size;

  if (budget < 4194304)
    budget = 4194304;

  while (1) {
    conflict = sat_propagate();

    if (conflict != 0) {
      sat_conflicts = sat_conflicts + 1;

      since = since + 1;

      if (verbose)
        if (sat_conflicts % 10000 == 0)
          printf("%s: %lu conflicts, %lu decisions, %lu restarts, %lu words of clauses\n", selfie_name,
            sat_conflicts, sat_decisions, sat_restarts, sat_db_size);

      if (sat_level == 0)
        return SAT_FALSE;

      level = sat_analyze(conflict);

      sat_cancel_until(level);

      if (sat_learnt_size == 1)
        sat_enqueue(*sat_learnt, 0);
      else {
        clause = sat_new_clause(sat_learnt, sat_learnt_size);

        sat_enqueue(*sat_learnt, clause);
      }

      // newer conflicts weigh more

      sat_increment = sat_increment + sat_increment / 16 + 1;
    } else if (since >= limit) {
      // restart

      sat_restarts = sat_restarts + 1;

      sat_cancel_until(0);

      since = 0;
      limit = 64 * sat_luby(sat_restarts);

      // at most a conflict at level 0 is left to find

      if (sat_propagate() != 0)
        return SAT_FALSE;

      if (sat_db_size - sat_first_learnt > budget) {
        sat_reduce();

        budget = budget + budget / 2;
      }
    } else {
      // decide the unassigned variable with the highest activity

      v = 0;

      picking = 1;

      while (picking) {
        if (sat_heap_size == 0)
          picking = 0;
        else {
          v = sat_heap_pop();

          if (*(sat_values + v) == SAT_UNASSIGNED)
            picking = 0;
          else
            v = 0;
        }
      }

      if (v == 0)
        return SAT_TRUE;

      sat_decisions = sat_decisions + 1;

      *(sat_starts + sat_level) = sat_trail_size;

      sat_level = sat_level + 1;

      if (*(sat_phases + v) == SAT_TRUE)
        sat_enqueue(2 * v, 0);
      else
        sat_enqueue(2 * v + 1, 0);
    }
  }
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ------------------------------ CNF ------------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t cnf_build(uint64_t root) {
  uint64_t top;
  uint64_t e;
  uint64_t n;
  uint64_t child;

  // numbers the nodes in the cone of influence of root in post-order, so that
  // every and-node has a higher variable than its children; babysat, which
  // assigns variables in order, then only ever chooses inputs

  if (aig_mark == (uint64_t*) 0) {
    aig_mark = zmalloc(aig_capacity * sizeof(uint64_t));
    aig_var  = zmalloc(aig_capacity * sizeof(uint64_t));
  }

  if (cone_capacity < aig_nodes) {
    cone_capacity = aig_capacity;

    cone_nodes  = zmalloc(cone_capacity * sizeof(uint64_t));
    cone_stack  = zmalloc(3 * cone_capacity * sizeof(uint64_t));
    cone_values = zmalloc((cone_capacity + 1) * sizeof(uint64_t));
  }

  cone_id = cone_id + 1;

  cone_size = 0;

  *cone_stack = 2 * (root / 2);

  top = 1;

  while (top > 0) {
    top = top - 1;

    e = *(cone_stack + top);

    n = e / 2;

    if (e % 2) {
      *(cone_nodes + cone_size) = n;

      cone_size = cone_size + 1;

      *(aig_var + n) = cone_size;
    } else if (*(aig_mark + n) != cone_id) {
      *(aig_mark + n) = cone_id;

      *(cone_stack + top) = e + 1;

      top = top + 1;

      if (not(aig_is_input(n))) {
        child = *(aig_left + n) / 2;

        if (*(aig_mark + child) != cone_id) {
          *(cone_stack + top) = 2 * child;

          top = top + 1;
        }

        child = *(aig_right + n) / 2;

        if (*(aig_mark + child) != cone_id) {
          *(cone_stack + top) = 2 * child;

          top = top + 1;
        }
      }
    }
  }

  return cone_size;
}

uint64_t cnf_literal(uint64_t l) {
  return 2 * *(aig_var + l / 2) + l % 2;
}

void cnf_solver(uint64_t root) {
  uint64_t i;
  uint64_t n;
  uint64_t v;
  uint64_t a;
  uint64_t b;

  // Tseitin encoding of the cone into the solver: v <-> a and b

  sat_reset(cone_size);

  i = 0;

  while (i < cone_size) {
    n = *(cone_nodes + i);

    if (not(aig_is_input(n))) {
      v = 2 * *(aig_var + n);

      a = cnf_literal(*(aig_left + n));
      b = cnf_literal(*(aig_right + n));

      *cnf_clause       = v + 1;
      *(cnf_clause + 1) = a;

      sat_add_clause(cnf_clause, 2);

      *cnf_clause       = v + 1;
      *(cnf_clause + 1) = b;

      sat_add_clause(cnf_clause, 2);

      *cnf_clause       = v;
      *(cnf_clause + 1) = sat_negate(a);
      *(cnf_clause + 2) = sat_negate(b);

      sat_add_clause(cnf_clause, 3);
    }

    i = i + 1;
  }

  *cnf_clause = cnf_literal(root);

  sat_add_clause(cnf_clause, 1);
}

void cnf_print_literal(uint64_t fd, uint64_t l) {
  if (l % 2)
    dprintf(fd, "-%lu ", l / 2);
  else
    dprintf(fd, "%lu ", l / 2);
}

void cnf_dimacs(uint64_t root) {
  uint64_t fd;
  char* name;
  uint64_t ands;
  uint64_t i;
  uint64_t n;
  uint64_t v;
  uint64_t a;
  uint64_t b;

  // the same encoding as DIMACS CNF file, for babysat and other solvers

  name = string_alloc(MAX_FILENAME_LENGTH);

  sprintf(name, "%s-%lu.cnf", dimacs_prefix, sat_calls);

  fd = open_write_only(name, S_IRUSR_IWUSR_IRGRP_IROTH);

  if (signed_less_than(fd, 0)) {
    printf("%s: could not create %s\n", selfie_name, name);

    exit(EXITCODE_IOERROR);
  }

  ands = 0;

  i = 0;

  while (i < cone_size) {
    if (not(aig_is_input(*(cone_nodes + i))))
      ands = ands + 1;

    i = i + 1;
  }

  dprintf(fd, "c generated by bitr from %s\n", model_name);
  dprintf(fd, "p cnf %lu %lu\n", cone_size, 3 * ands + 1);

  i = 0;

  while (i < cone_size) {
    n = *(cone_nodes + i);

    if (not(aig_is_input(n))) {
      v = 2 * *(aig_var + n);

      a = cnf_literal(*(aig_left + n));
      b = cnf_literal(*(aig_right + n));

      cnf_print_literal(fd, v + 1);
      cnf_print_literal(fd, a);
      dprintf(fd, "0\n");

      cnf_print_literal(fd, v + 1);
      cnf_print_literal(fd, b);
      dprintf(fd, "0\n");

      cnf_print_literal(fd, v);
      cnf_print_literal(fd, sat_negate(a));
      cnf_print_literal(fd, sat_negate(b));
      dprintf(fd, "0\n");
    }

    i = i + 1;
  }

  cnf_print_literal(fd, cnf_literal(root));
  dprintf(fd, "0\n");

  dimacs_files = dimacs_files + 1;
}

uint64_t aig_model(uint64_t l) {
  uint64_t n;

  // value of a literal in the most recent model: nodes outside of the
  // cone of the solved formula are inputs that do not matter, false

  n = l / 2;

  if (n == 0)
    return l % 2;
  else if (model_is_trivial)
    return l % 2;
  else if (*(aig_mark + n) == cone_id)
    return (*(cone_values + *(aig_var + n)) + l % 2) % 2;
  else
    return l % 2;
}

uint64_t aig_solve(uint64_t root) {
  uint64_t i;
  uint64_t n;
  uint64_t result;

  // is root satisfiable? if so, aig_model gives a model

  if (root == AIG_FALSE)
    return 0;

  if (root == AIG_TRUE) {
    model_is_trivial = 1;

    return 1;
  }

  model_is_trivial = 0;

  sat_calls = sat_calls + 1;

  cnf_build(root);

  if (dimacs_prefix != (char*) 0)
    if (or(dimacs_limit == 0, cone_size <= dimacs_limit))
      cnf_dimacs(root);

  cnf_solver(root);

  result = sat_solve();

  sat_total_variables = sat_total_variables + sat_variables;
  sat_total_clauses   = sat_total_clauses + sat_clauses;
  sat_total_conflicts = sat_total_conflicts + sat_conflicts;
  sat_total_decisions = sat_total_decisions + sat_decisions;

  if (sat_variables > sat_max_variables)
    sat_max_variables = sat_variables;

  if (result == SAT_FALSE)
    return 0;

  // simulate the cone on the model's inputs: checks encoding and solver

  i = 0;

  while (i < cone_size) {
    n = *(cone_nodes + i);

    if (aig_is_input(n))
      *(cone_values + i + 1) = *(sat_values + i + 1) == SAT_TRUE;
    else
      *(cone_values + i + 1) = aig_model(*(aig_left + n)) * aig_model(*(aig_right + n));

    if (*(cone_values + i + 1) != (*(sat_values + i + 1) == SAT_TRUE)) {
      printf("%s: model of solver disagrees with circuit at variable %lu\n", selfie_name, i + 1);

      exit(EXITCODE_SYSTEMERROR);
    }

    i = i + 1;
  }

  if (aig_model(root) == 0) {
    printf("%s: model of solver does not satisfy formula\n", selfie_name);

    exit(EXITCODE_SYSTEMERROR);
  }

  return 1;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ------------------------- BOUNDED MODEL CHECKER -----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t width_of(uint64_t* line) {
  return eval_bitvec_size(get_sid(line));
}

uint64_t sym_bit(uint64_t* line) {
  // literal of a Boolean line in the current frame
  return bv_lit((uint64_t*) sym_eval(line), 0);
}

uint64_t sym_eval(uint64_t* line) {
  uint64_t nid;
  char* op;
  uint64_t value;
  uint64_t c;
  uint64_t* a;
  uint64_t* b;

  // value of a line in the current frame: a bit vector, or an array for
  // lines of array sort; evaluated once per frame, and only if needed,
  // so that the untaken side of a decided choice costs nothing

  nid = get_nid(line);

  if (*(sym_stamps + nid) == sym_frame)
    return *(sym_values + nid);

  op = get_op(line);

  if (op == OP_STATE)
    value = *(sym_states + nid);
  else if (op == OP_INPUT)
    value = (uint64_t) bv_fresh(width_of(line));
  else if (is_constant_op(op))
    value = (uint64_t) bv_constant((uint64_t) get_arg1(line), width_of(line));
  else if (op == OP_ITE) {
    c = decide(sym_bit(get_arg1(line)));

    if (c == AIG_TRUE)
      value = sym_eval(get_arg2(line));
    else if (c == AIG_FALSE)
      value = sym_eval(get_arg3(line));
    else if (is_array(get_sid(line)))
      value = arr_ite(c, sym_eval(get_arg2(line)), sym_eval(get_arg3(line)));
    else
      value = (uint64_t) bv_ite(c, (uint64_t*) sym_eval(get_arg2(line)), (uint64_t*) sym_eval(get_arg3(line)));
  } else if (op == OP_READ)
    value = (uint64_t) arr_read(sym_eval(get_arg1(line)), (uint64_t*) sym_eval(get_arg2(line)));
  else if (op == OP_WRITE)
    value = arr_write(sym_eval(get_arg1(line)), (uint64_t*) sym_eval(get_arg2(line)), (uint64_t*) sym_eval(get_arg3(line)));
  else if (op == OP_SEXT)
    value = (uint64_t) bv_ext((uint64_t*) sym_eval(get_arg1(line)), (uint64_t) get_arg2(line), 1);
  else if (op == OP_UEXT)
    value = (uint64_t) bv_ext((uint64_t*) sym_eval(get_arg1(line)), (uint64_t) get_arg2(line), 0);
  else if (op == OP_SLICE)
    value = (uint64_t) bv_slice((uint64_t*) sym_eval(get_arg1(line)), (uint64_t) get_arg2(line), (uint64_t) get_arg3(line));
  else if (op == OP_NOT)
    value = (uint64_t) bv_not((uint64_t*) sym_eval(get_arg1(line)));
  else if (op == OP_INC) {
    a = (uint64_t*) sym_eval(get_arg1(line));

    value = (uint64_t) bv_add_normal(a, bv_constant(1, *a));
  } else if (op == OP_DEC) {
    a = (uint64_t*) sym_eval(get_arg1(line));

    value = (uint64_t) bv_add_normal(a, bv_constant(-1, *a));
  } else if (op == OP_NEG)
    value = (uint64_t) bv_neg((uint64_t*) sym_eval(get_arg1(line)));
  else {
    // binary operators; Boolean connectives are decided by their left side if possible

    a = (uint64_t*) sym_eval(get_arg1(line));

    value = 0;

    if (*a == 1) {
      c = bv_lit(a, 0);

      if (deciding)
        c = aig_cofactor(c);

      if (op == OP_AND) {
        if (c == AIG_FALSE)
          value = (uint64_t) a;
      } else if (op == OP_OR) {
        if (c == AIG_TRUE)
          value = (uint64_t) a;
      } else if (op == OP_IMPLIES)
        if (c == AIG_FALSE)
          value = (uint64_t) bv_bool(AIG_TRUE);
    }

    if (value == 0) {
      b = (uint64_t*) sym_eval(get_arg2(line));

      if (op == OP_AND)
        value = (uint64_t) bv_bitwise(a, b, 0);
      else if (op == OP_OR)
        value = (uint64_t) bv_bitwise(a, b, 1);
      else if (op == OP_XOR)
        value = (uint64_t) bv_xor_normal(a, b);
      else if (op == OP_IMPLIES)
        value = (uint64_t) bv_bitwise(bv_not(a), b, 1);
      else if (op == OP_EQ)
        value = (uint64_t) bv_bool(bv_eq(a, b));
      else if (op == OP_NEQ)
        value = (uint64_t) bv_bool(aig_not(bv_eq(a, b)));
      else if (op == OP_UGTE)
        value = (uint64_t) bv_bool(bv_uge(a, b, 0));
      else if (op == OP_ULT)
        value = (uint64_t) bv_bool(aig_not(bv_uge(a, b, 0)));
      else if (op == OP_ULTE)
        value = (uint64_t) bv_bool(bv_uge(b, a, 0));
      else if (op == OP_UGT)
        value = (uint64_t) bv_bool(aig_not(bv_uge(b, a, 0)));
      else if (op == OP_SGTE)
        value = (uint64_t) bv_bool(bv_uge(a, b, 1));
      else if (op == OP_SLT)
        value = (uint64_t) bv_bool(aig_not(bv_uge(a, b, 1)));
      else if (op == OP_SLTE)
        value = (uint64_t) bv_bool(bv_uge(b, a, 1));
      else if (op == OP_SGT)
        value = (uint64_t) bv_bool(aig_not(bv_uge(b, a, 1)));
      else if (op == OP_ADD)
        value = (uint64_t) bv_add_normal(a, b);
      else if (op == OP_SUB)
        value = (uint64_t) bv_sub_normal(a, b);
      else if (op == OP_MUL)
        value = (uint64_t) bv_mul(a, b);
      else if (op == OP_UDIV)
        value = (uint64_t) bv_udivrem(a, b, 0);
      else if (op == OP_UREM)
        value = (uint64_t) bv_udivrem(a, b, 1);
      else if (op == OP_SDIV)
        value = (uint64_t) bv_sdivrem(a, b, 0);
      else if (op == OP_SREM)
        value = (uint64_t) bv_sdivrem(a, b, 1);
      else if (op == OP_SLL)
        value = (uint64_t) bv_shift(a, b, 0);
      else if (op == OP_SRL)
        value = (uint64_t) bv_shift(a, b, 1);
      else if (op == OP_SRA)
        value = (uint64_t) bv_shift(a, b, 2);
      else if (op == OP_CONCAT)
        value = (uint64_t) bv_concat(a, b);
      else {
        printf("%s: operator %s is not supported symbolically\n", selfie_name, op);

        exit(EXITCODE_SYSTEMERROR);
      }
    }
  }

  *(sym_values + nid) = value;
  *(sym_stamps + nid) = sym_frame;

  return value;
}

void sym_init(uint64_t all_symbolic) {
  uint64_t nid;
  uint64_t* line;

  // the symbolic state starts as the concrete initial state, except for states
  // the model leaves uninitialized and no loader filled: those are free, they
  // are the input; with all_symbolic every state is free

  sym_values  = zmalloc((max_nid + 1) * sizeof(uint64_t));
  sym_stamps  = zmalloc((max_nid + 1) * sizeof(uint64_t));
  sym_states  = zmalloc((max_nid + 1) * sizeof(uint64_t));
  sym_nexts   = zmalloc((max_nid + 1) * sizeof(uint64_t));
  sym_bases   = zmalloc((max_nid + 1) * sizeof(uint64_t));
  sym_free    = zmalloc((max_nid + 1) * sizeof(uint64_t));
  bad_lits    = zmalloc((max_nid + 1) * sizeof(uint64_t));

  sym_frame = 1;

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED)
      if (get_op(line) == OP_STATE) {
        if (all_symbolic)
          *(sym_free + nid) = 1;
        else
          *(sym_free + nid) = *(uninitialized_states + nid);

        if (is_bitvector(get_sid(line))) {
          if (*(sym_free + nid))
            *(sym_states + nid) = (uint64_t) bv_fresh(width_of(line));
          else
            *(sym_states + nid) = (uint64_t) bv_constant(get_state(line), width_of(line));

          *(sym_bases + nid) = *(sym_states + nid);
        } else {
          *(sym_states + nid) = arr_base(line, *(sym_free + nid));

          *(sym_bases + nid) = *(sym_states + nid);
        }
      }

    nid = nid + 1;
  }
}

uint64_t bv_model(uint64_t* a) {
  uint64_t i;
  uint64_t value;

  i     = *a;
  value = 0;

  while (i > 0) {
    i = i - 1;

    value = value * 2 + aig_model(bv_lit(a, i));
  }

  return value;
}

uint64_t sym_element_model(uint64_t* state_nid, uint64_t index) {
  uint64_t a;
  uint64_t* elements;
  uint64_t* element;

  // value of an element of a free array state in the model, 0 if never read

  a = *(sym_bases + get_nid(state_nid));

  elements = (uint64_t*) *(arr_z + a);

  element = (uint64_t*) *(elements + index);

  if (element == (uint64_t*) 0)
    return 0;
  else
    return bv_model(element);
}

uint64_t sym_block_model(uint64_t limit) {
  uint64_t nid;
  uint64_t* line;
  uint64_t block;
  uint64_t a;
  uint64_t* elements;
  uint64_t* element;
  uint64_t n;
  uint64_t i;
  uint64_t j;

  // prints the model of all free state read so far, of arrays only if they have
  // at most limit elements unless limit is 0, and returns the literal that is
  // true iff that state has exactly the model's values

  block = AIG_TRUE;

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED)
      if (get_op(line) == OP_STATE)
        if (*(sym_free + nid)) {
          if (is_bitvector(get_sid(line))) {
            element = (uint64_t*) *(sym_bases + nid);

            printf("%s: witness %s = %lu\n", selfie_name, (char*) get_arg1(line), bv_model(element));

            j = 0;

            while (j < *element) {
              if (aig_model(bv_lit(element, j)))
                block = aig_and(block, bv_lit(element, j));
              else
                block = aig_and(block, aig_not(bv_lit(element, j)));

              j = j + 1;
            }
          } else {
            a = *(sym_bases + nid);

            elements = (uint64_t*) *(arr_z + a);

            n = two_to_the_power_of(*(arr_iw + a));

            i = 0;

            while (i < n) {
              element = (uint64_t*) *(elements + i);

              if (element != (uint64_t*) 0) {
                if (or(limit == 0, n <= limit))
                  printf("%s: witness %s[%lu] = %lu\n", selfie_name, (char*) get_arg1(line), i, bv_model(element));

                j = 0;

                while (j < *element) {
                  if (aig_model(bv_lit(element, j)))
                    block = aig_and(block, bv_lit(element, j));
                  else
                    block = aig_and(block, aig_not(bv_lit(element, j)));

                  j = j + 1;
                }
              }

              i = i + 1;
            }
          }
        }

    nid = nid + 1;
  }

  return block;
}

void write_witness() {
  uint64_t* buffer_nid;
  uint64_t* tapes_nid;
  uint64_t* ends_nid;
  uint64_t* heads_nid;
  uint64_t fd;
  uint64_t n;
  uint64_t i;
  uint64_t end;
  uint64_t* bytes;
  char* name;

  // the inverse of the input loader: the model of the input buffer, or of
  // the input tape of standard input up to the end of its file, as file

  buffer_nid = find_state("input-buffer");
  tapes_nid  = find_state("input-tapes");

  n = 0;

  bytes = (uint64_t*) 0;

  if (tapes_nid != UNUSED) {
    if (*(sym_free + get_nid(tapes_nid))) {
      ends_nid  = find_state("tape-ends");
      heads_nid = find_state("tape-heads");

      // words per tape, tape 0 is standard input

      n = array_elements(tapes_nid) / array_elements(heads_nid);

      bytes = zmalloc(n * sizeof(uint64_t));

      i = 0;

      while (i < n) {
        *(bytes + i) = sym_element_model(tapes_nid, i);

        i = i + 1;
      }

      n = n * sizeof(uint64_t);

      if (*(sym_free + get_nid(ends_nid))) {
        end = sym_element_model(ends_nid, 0);

        if (end < n)
          n = end;
      }
    }
  } else if (buffer_nid != UNUSED)
    if (*(sym_free + get_nid(buffer_nid))) {
      n = array_elements(buffer_nid);

      bytes = zmalloc(round_up(n, sizeof(uint64_t)));

      i = 0;

      while (i < n) {
        store_character((char*) bytes, i, sym_element_model(buffer_nid, i));

        i = i + 1;
      }
    }

  if (bytes == (uint64_t*) 0) {
    printf("%s: no free input state in %s to write a witness for\n", selfie_name, model_name);

    return;
  }

  name = string_alloc(MAX_FILENAME_LENGTH);

  if (witnesses == 0)
    sprintf(name, "%s", witness_file);
  else
    sprintf(name, "%s.%lu", witness_file, witnesses);

  fd = open_write_only(name, S_IRUSR_IWUSR_IRGRP_IROTH);

  if (signed_less_than(fd, 0)) {
    printf("%s: could not create %s\n", selfie_name, name);

    exit(EXITCODE_IOERROR);
  }

  write(fd, bytes, n);

  printf("%s: %lu bytes of input written into %s\n", selfie_name, n, name);
}

void sym_cases(uint64_t* line, uint64_t guard) {
  uint64_t c;
  uint64_t value;
  uint64_t i;

  // decomposes a bit-vector line into the constants it chooses between, by
  // descending through its choices: guard and value of each case end up in
  // case_guards and case_values; cases_constant is 0 if some case is not
  // a constant or there are too many cases

  if (guard == AIG_FALSE)
    return;

  if (cases_constant == 0)
    return;

  if (get_op(line) == OP_ITE) {
    c = sym_bit(get_arg1(line));

    if (c == AIG_TRUE)
      sym_cases(get_arg2(line), guard);
    else if (c == AIG_FALSE)
      sym_cases(get_arg3(line), guard);
    else {
      sym_cases(get_arg2(line), aig_and(guard, c));
      sym_cases(get_arg3(line), aig_and(guard, aig_not(c)));
    }
  } else {
    value = sym_eval(line);

    cases_visited = cases_visited + 1;

    if (not(bv_is_constant((uint64_t*) value)))
      cases_constant = 0;
    else if (cases_visited > MAX_CASES)
      cases_constant = 0;
    else {
      i = 0;

      while (i < number_of_cases) {
        if (*(case_values + i) == value) {
          // same constant on another way: either way
          *(case_guards + i) = aig_or(*(case_guards + i), guard);

          return;
        }

        i = i + 1;
      }

      *(case_guards + number_of_cases) = guard;
      *(case_values + number_of_cases) = value;

      number_of_cases = number_of_cases + 1;
    }
  }
}

void init_paths() {
  uint64_t nid;
  uint64_t* line;
  uint64_t* states;
  uint64_t i;

  // one path with the initial state; states get slots 0, 1, 2, ...

  state_slots = zmalloc((max_nid + 1) * sizeof(uint64_t));
  slot_nids   = zmalloc((max_nid + 1) * sizeof(uint64_t));

  number_of_slots = 0;

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED)
      if (get_op(line) == OP_STATE) {
        *(state_slots + nid) = number_of_slots;

        *(slot_nids + number_of_slots) = nid;

        number_of_slots = number_of_slots + 1;
      }

    nid = nid + 1;
  }

  path_capacity = 64;

  path_guards = zmalloc(path_capacity * sizeof(uint64_t));
  path_states = zmalloc(path_capacity * sizeof(uint64_t));
  next_guards = zmalloc(path_capacity * sizeof(uint64_t));
  next_states = zmalloc(path_capacity * sizeof(uint64_t));

  case_guards = zmalloc((MAX_CASES + 1) * sizeof(uint64_t));
  case_values = zmalloc((MAX_CASES + 1) * sizeof(uint64_t));

  fork_slots  = zmalloc(number_of_slots * sizeof(uint64_t));
  fork_firsts = zmalloc(number_of_slots * sizeof(uint64_t));
  fork_counts = zmalloc(number_of_slots * sizeof(uint64_t));
  fork_guards = zmalloc(number_of_slots * (MAX_CASES + 1) * sizeof(uint64_t));
  fork_values = zmalloc(number_of_slots * (MAX_CASES + 1) * sizeof(uint64_t));

  states = zmalloc(number_of_slots * sizeof(uint64_t));

  i = 0;

  while (i < number_of_slots) {
    *(states + i) = *(sym_states + *(slot_nids + i));

    i = i + 1;
  }

  *path_guards = AIG_TRUE;
  *path_states = (uint64_t) states;

  number_of_paths = 1;
}

void add_next_path(uint64_t guard, uint64_t* states) {
  if (number_of_next_paths == path_capacity) {
    path_guards = grow_words(path_guards, path_capacity, 2 * path_capacity);
    path_states = grow_words(path_states, path_capacity, 2 * path_capacity);
    next_guards = grow_words(next_guards, path_capacity, 2 * path_capacity);
    next_states = grow_words(next_states, path_capacity, 2 * path_capacity);

    path_capacity = 2 * path_capacity;
  }

  *(next_guards + number_of_next_paths) = guard;
  *(next_states + number_of_next_paths) = (uint64_t) states;

  number_of_next_paths = number_of_next_paths + 1;
}

uint64_t check_bads(uint64_t guard, uint64_t t) {
  uint64_t nid;
  uint64_t* line;
  uint64_t any;
  uint64_t b;
  uint64_t found;
  uint64_t searching;

  // looks for bad states in the current frame of a path, once without
  // enumerating; returns the number of witnesses found

  found = 0;

  searching = 1;

  while (searching) {
    any = AIG_FALSE;

    nid = 1;

    while (nid <= max_nid) {
      line = line_of_nid(nid);

      if (line != UNUSED)
        if (get_op(line) == OP_BAD) {
          b = sym_bit(get_arg1(line));

          *(bad_lits + nid) = b;

          any = aig_or(any, b);
        }

      nid = nid + 1;
    }

    if (aig_solve(aig_and(aig_and(guard, blocked), any))) {
      nid = 1;

      while (nid <= max_nid) {
        line = line_of_nid(nid);

        if (line != UNUSED)
          if (get_op(line) == OP_BAD)
            if (aig_model(*(bad_lits + nid)))
              printf("%s: bad %s after %lu instructions\n", selfie_name, (char*) get_arg2(line), t + 1);

        nid = nid + 1;
      }

      // the witness is excluded from now on

      blocked = aig_and(blocked, aig_not(sym_block_model(0)));

      if (witness_file != (char*) 0)
        write_witness();

      witnesses = witnesses + 1;

      found = found + 1;

      if (stop_at_first)
        searching = 0;
      else if (blocked == AIG_FALSE)
        // no free state: the bad state is reached on every run
        searching = 0;
    } else
      searching = 0;
  }

  return found;
}

uint64_t bmc() {
  uint64_t nid;
  uint64_t* line;
  uint64_t p;
  uint64_t guard;
  uint64_t* states;
  uint64_t* successor;
  uint64_t slot;
  uint64_t value;
  uint64_t changed;
  uint64_t forks;
  uint64_t found;
  uint64_t n;
  uint64_t t;
  uint64_t i;
  uint64_t j;
  uint64_t f;
  uint64_t first;
  uint64_t last;
  uint64_t* swap;

  // forward bounded model checking: unrolls the model frame by frame over
  // symbolic state and asks in every frame whether a bad state is reachable
  // under all constraints so far. Where the next value of a bit-vector
  // state is a choice between constants, such as the program counter after
  // a branch on input, the path forks, one path per constant that the
  // solver finds reachable, so that control stays concrete on every path
  // and only data is symbolic. Returns the number of witnesses found.

  printf("%s: ********************************************************************************\n", selfie_name);

  sym_init(0);

  init_paths();

  blocked = AIG_TRUE;

  found = 0;

  t = 0;

  while (number_of_paths > 0) {
    number_of_next_paths = 0;

    p = 0;

    while (p < number_of_paths) {
      guard  = *(path_guards + p);
      states = (uint64_t*) *(path_states + p);

      // the frame of this path

      i = 0;

      while (i < number_of_slots) {
        *(sym_states + *(slot_nids + i)) = *(states + i);

        i = i + 1;
      }

      sym_frame = sym_frame + 1;

      // constraints

      nid = 1;

      while (nid <= max_nid) {
        line = line_of_nid(nid);

        if (line != UNUSED)
          if (get_op(line) == OP_CONSTRAINT)
            guard = aig_and(guard, sym_bit(get_arg1(line)));

        nid = nid + 1;
      }

      // bad states

      n = 0;

      if (guard != AIG_FALSE)
        n = check_bads(guard, t);

      found = found + n;

      if (n > 0) {
        if (stop_at_first)
          return found;

        // is there input left on this path?

        if (not(aig_solve(aig_and(guard, blocked))))
          guard = AIG_FALSE;
      }

      if (guard != AIG_FALSE) {
        // next states: one successor, or several where a bit-vector state forks

        successor = zmalloc(number_of_slots * sizeof(uint64_t));

        changed = 0;
        forks   = 0;
        last    = 0;

        nid = 1;

        while (nid <= max_nid) {
          line = line_of_nid(nid);

          if (line != UNUSED)
            if (get_op(line) == OP_NEXT) {
              slot = *(state_slots + get_nid(get_arg1(line)));

              number_of_cases = 0;

              if (is_bitvector(get_sid(line))) {
                cases_constant = 1;
                cases_visited  = 0;

                sym_cases(get_arg2(line), AIG_TRUE);

                if (cases_constant == 0)
                  number_of_cases = 0;
              }

              if (number_of_cases > 1) {
                *(fork_slots + forks)  = slot;
                *(fork_firsts + forks) = last;
                *(fork_counts + forks) = number_of_cases;

                i = 0;

                while (i < number_of_cases) {
                  *(fork_guards + last + i) = *(case_guards + i);
                  *(fork_values + last + i) = *(case_values + i);

                  i = i + 1;
                }

                last = last + number_of_cases;

                forks = forks + 1;

                changed = 1;
              } else {
                value = sym_eval(get_arg2(line));

                *(successor + slot) = value;

                if (value != *(states + slot))
                  changed = 1;
              }
            }

          nid = nid + 1;
        }

        // states without next keep their value

        i = 0;

        while (i < number_of_slots) {
          if (*(successor + i) == 0)
            *(successor + i) = *(states + i);

          i = i + 1;
        }

        if (changed == 0)
          // the machine halted on this path
          halted_paths = halted_paths + 1;
        else if (forks == 0)
          add_next_path(guard, successor);
        else {
          // one successor per combination of cases that is reachable

          first = number_of_next_paths;

          add_next_path(guard, successor);

          f = 0;

          while (f < forks) {
            slot = *(fork_slots + f);

            last = number_of_next_paths;

            i = first;

            while (i < last) {
              j = 0;

              while (j < *(fork_counts + f)) {
                guard = aig_and(*(next_guards + i), *(fork_guards + *(fork_firsts + f) + j));

                if (j + 1 < *(fork_counts + f)) {
                  // a copy for all cases but the last, which takes the original

                  successor = zmalloc(number_of_slots * sizeof(uint64_t));

                  memcopy(successor, (uint64_t*) *(next_states + i), number_of_slots * sizeof(uint64_t));

                  *(successor + slot) = *(fork_values + *(fork_firsts + f) + j);

                  if (aig_solve(aig_and(guard, blocked))) {
                    add_next_path(guard, successor);

                    forked_paths = forked_paths + 1;
                  }
                } else {
                  successor = (uint64_t*) *(next_states + i);

                  *(successor + slot) = *(fork_values + *(fork_firsts + f) + j);

                  if (aig_solve(aig_and(guard, blocked)))
                    *(next_guards + i) = guard;
                  else
                    *(next_guards + i) = AIG_FALSE;
                }

                j = j + 1;
              }

              i = i + 1;
            }

            f = f + 1;
          }

          // drop unreachable originals

          i = first;
          j = first;

          while (i < number_of_next_paths) {
            if (*(next_guards + i) != AIG_FALSE) {
              *(next_guards + j) = *(next_guards + i);
              *(next_states + j) = *(next_states + i);

              j = j + 1;
            }

            i = i + 1;
          }

          number_of_next_paths = j;
        }
      }

      p = p + 1;
    }

    if (verbose)
      printf("%s: %lu instructions: %lu paths, %lu and-nodes, %lu bit vectors, %lu array nodes, %lu reads, %lu SAT calls, %lu conflicts\n", selfie_name,
        t + 1, number_of_next_paths, aig_ands, bv_count, arr_count - 1, memo_count, sat_calls, sat_total_conflicts);

    swap = path_guards;

    path_guards = next_guards;
    next_guards = swap;

    swap = path_states;

    path_states = next_states;
    next_states = swap;

    number_of_paths = number_of_next_paths;

    if (number_of_paths > max_paths)
      max_paths = number_of_paths;

    t = t + 1;

    if (number_of_paths == 0)
      printf("%s: halted after %lu instructions on all inputs that reach no bad state\n", selfie_name, t);
    else if (max_steps > 0)
      if (t >= max_steps) {
        printf("%s: bound of %lu instructions reached on %lu paths\n", selfie_name, max_steps, number_of_paths);

        number_of_paths = 0;
      }
  }

  return found;
}

void print_bmc_statistics() {
  printf("%s: %lu and-nodes over %lu inputs, %lu bit vectors, %lu array nodes\n", selfie_name,
    aig_ands, aig_inputs, bv_count, arr_count - 1);
  printf("%s: %lu paths forked, %lu paths at most, %lu paths halted\n", selfie_name,
    forked_paths, max_paths, halted_paths);
  printf("%s: %lu SAT calls with %lu variables at most, %lu clauses, %lu decisions, and %lu conflicts in total\n", selfie_name,
    sat_calls, sat_max_variables, sat_total_clauses, sat_total_decisions, sat_total_conflicts);

  if (dimacs_prefix != (char*) 0)
    printf("%s: %lu CNF files written with prefix %s\n", selfie_name, dimacs_files, dimacs_prefix);
}

// -----------------------------------------------------------------
// --------------------------- IDENTITY ----------------------------
// -----------------------------------------------------------------

void save_model(uint64_t* model) {
  // the parser's and the symbolic evaluator's tables are per model

  *model       = (uint64_t) nid_lines;
  *(model + 1) = (uint64_t) init_lines;
  *(model + 2) = nid_limit;
  *(model + 3) = max_nid;
  *(model + 4) = (uint64_t) sym_values;
  *(model + 5) = (uint64_t) sym_stamps;
  *(model + 6) = (uint64_t) sym_states;
  *(model + 7) = (uint64_t) sym_nexts;
  *(model + 8) = (uint64_t) sym_bases;
  *(model + 9) = (uint64_t) sym_free;
  *(model + 10) = (uint64_t) model_name;

  // and what the concrete evaluator needs per model

  *(model + 11) = (uint64_t) SID_BOOLEAN;
  *(model + 12) = (uint64_t) SID_INPUT_BUFFER;
  *(model + 13) = (uint64_t) SID_CODE_STATE;
  *(model + 14) = (uint64_t) uninitialized_states;
  *(model + 15) = (uint64_t) pc_state_nid;
}

void restore_model(uint64_t* model) {
  nid_lines  = (uint64_t*) *model;
  init_lines = (uint64_t*) *(model + 1);
  nid_limit  = *(model + 2);
  max_nid    = *(model + 3);
  sym_values = (uint64_t*) *(model + 4);
  sym_stamps = (uint64_t*) *(model + 5);
  sym_states = (uint64_t*) *(model + 6);
  sym_nexts  = (uint64_t*) *(model + 7);
  sym_bases  = (uint64_t*) *(model + 8);
  sym_free   = (uint64_t*) *(model + 9);
  model_name = (char*) *(model + 10);

  SID_BOOLEAN      = (uint64_t*) *(model + 11);
  SID_INPUT_BUFFER = (uint64_t*) *(model + 12);
  SID_CODE_STATE   = (uint64_t*) *(model + 13);

  uninitialized_states = (uint64_t*) *(model + 14);

  pc_state_nid = (uint64_t*) *(model + 15);
}

void assume(uint64_t l) {
  if (number_of_assumptions == assumption_capacity) {
    if (assumption_capacity == 0)
      assumption_capacity = 64;
    else
      assumption_capacity = 2 * assumption_capacity;

    assumptions = grow_words(assumptions, number_of_assumptions, assumption_capacity);
  }

  *(assumptions + number_of_assumptions) = l;

  number_of_assumptions = number_of_assumptions + 1;
}

uint64_t aig_evaluate(uint64_t l) {
  uint64_t top;
  uint64_t e;
  uint64_t n;
  uint64_t child;
  uint64_t value;

  // value of any literal under the most recent model, whose inputs outside
  // of the solved cone are false; evaluates nodes outside of that cone

  if (eval_capacity < aig_nodes) {
    eval_capacity = aig_capacity;

    eval_marks  = zmalloc(eval_capacity * sizeof(uint64_t));
    eval_values = zmalloc(eval_capacity * sizeof(uint64_t));
    eval_stack  = zmalloc(3 * eval_capacity * sizeof(uint64_t));

    eval_id = 0;
  }

  if (l / 2 == 0)
    return l % 2;

  // values are valid for one model, the caller advances eval_id per model

  *eval_stack = 2 * (l / 2);

  top = 1;

  while (top > 0) {
    top = top - 1;

    e = *(eval_stack + top);

    n = e / 2;

    if (*(eval_marks + n) != eval_id) {
      value = 2;

      if (not(model_is_trivial))
        if (*(aig_mark + n) == cone_id)
          value = *(cone_values + *(aig_var + n));

      if (value == 2) {
        if (aig_is_input(n))
          value = 0;
        else if (e % 2) {
          // both children are evaluated

          child = *(aig_left + n);

          value = (*(eval_values + child / 2) + child % 2) % 2;

          child = *(aig_right + n);

          value = value * ((*(eval_values + child / 2) + child % 2) % 2);
        } else {
          *(eval_stack + top) = e + 1;

          top = top + 1;

          child = *(aig_left + n) / 2;

          if (*(eval_marks + child) != eval_id) {
            *(eval_stack + top) = 2 * child;

            top = top + 1;
          }

          child = *(aig_right + n) / 2;

          if (*(eval_marks + child) != eval_id) {
            *(eval_stack + top) = 2 * child;

            top = top + 1;
          }
        }
      }

      if (value != 2) {
        *(eval_values + n) = value;
        *(eval_marks + n)  = eval_id;
      }
    }
  }

  return (*(eval_values + l / 2) + l % 2) % 2;
}

void sym_step_frame() {
  uint64_t nid;
  uint64_t* line;

  // one frame of the current model on its current states, the states advance

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED)
      if (get_op(line) == OP_NEXT)
        *(sym_nexts + nid) = sym_eval(get_arg2(line));

    nid = nid + 1;
  }

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED)
      if (get_op(line) == OP_NEXT)
        *(sym_states + get_nid(get_arg1(line))) = *(sym_nexts + nid);

    nid = nid + 1;
  }
}

void sym_assume_frame() {
  uint64_t nid;
  uint64_t* line;

  // one frame of the current model on its current states: the constraints
  // and the absence of bad states become assumptions, the states advance

  sym_frame = sym_frame + 1;

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED) {
      if (get_op(line) == OP_CONSTRAINT)
        assume(aig_cofactor(sym_bit(get_arg1(line))));
      else if (get_op(line) == OP_BAD)
        assume(aig_cofactor(aig_not(sym_bit(get_arg1(line)))));
    }

    nid = nid + 1;
  }

  sym_step_frame();
}

uint64_t evaluate_path() {
  uint64_t nid;
  uint64_t k;
  uint64_t i;

  // k steps of the first model and then k steps of the second on the
  // current path, from free states: returns PATH_INFEASIBLE if the path
  // violates a constraint of the first model or reaches one of its bad
  // states, PATH_SPLIT if a choice depends on a literal the path does
  // not decide yet, and PATH_COMPLETE otherwise

  pending_split = 0;

  number_of_assumptions = 0;

  restore_model(first_model);

  nid = 1;

  while (nid <= max_nid) {
    *(sym_states + nid) = *(sym_bases + nid);

    nid = nid + 1;
  }

  i = 0;

  k = 0;

  while (k < max_steps) {
    sym_assume_frame();

    while (i < number_of_assumptions) {
      if (*(assumptions + i) == AIG_FALSE)
        return PATH_INFEASIBLE;

      i = i + 1;
    }

    if (pending_split != 0)
      return PATH_SPLIT;

    k = k + 1;
  }

  // the path may assume what the first model assumes

  i = 0;

  while (i < number_of_assumptions) {
    if (not(assume_literal(*(assumptions + i))))
      return PATH_INFEASIBLE;

    i = i + 1;
  }

  // hand the states over by name, its constraints and bad states do not
  // matter for the second model

  nid = 1;

  while (nid <= *(second_model + 3)) {
    if (*(state_map + nid) != 0)
      *((uint64_t*) *(second_model + 6) + nid) = *(sym_states + *(state_map + nid));

    nid = nid + 1;
  }

  restore_model(second_model);

  k = 0;

  while (k < max_steps) {
    sym_frame = sym_frame + 1;

    sym_step_frame();

    if (pending_split != 0)
      return PATH_SPLIT;

    k = k + 1;
  }

  return PATH_COMPLETE;
}

uint64_t bv_evaluate(uint64_t* a) {
  uint64_t i;
  uint64_t value;

  // value of any bit vector under the most recent model

  i     = *a;
  value = 0;

  while (i > 0) {
    i = i - 1;

    value = value * 2 + aig_evaluate(bv_lit(a, i));
  }

  return value;
}

uint64_t solve_on_path(uint64_t goal) {
  uint64_t selected;
  uint64_t violated;
  uint64_t i;
  uint64_t n;

  // is goal satisfiable together with what the path assumes? Starts
  // without the path and adds what a model of goal violates, until there
  // is no model, or a model that satisfies all the path assumes

  selected = AIG_TRUE;

  while (1) {
    if (not(aig_solve(aig_and(selected, goal))))
      return 0;

    solver_conflicts = solver_conflicts + sat_conflicts;

    eval_id = eval_id + 1;

    violated = 0;

    i = 0;

    while (i < assumed_count) {
      n = *(assumed_nodes + i);

      if (aig_evaluate(2 * n) != (*(aig_assumed + n) == 1)) {
        if (*(aig_assumed + n) == 1)
          selected = aig_and(selected, 2 * n);
        else
          selected = aig_and(selected, 2 * n + 1);

        violated = violated + 1;
      }

      i = i + 1;
    }

    if (violated == 0)
      return 1;
  }
}

void check_state_at(uint64_t* line, uint64_t* index) {
  uint64_t nid;
  uint64_t* before;
  uint64_t* after;
  uint64_t difference;
  uint64_t mark;

  // on a complete path a state is restored, at an index if it is an
  // array, by construction if its values before and after are the same,
  // and otherwise if they cannot differ given what the path assumes;
  // reading an array at an index that may or may not be one that was
  // written splits the path, for this check only

  nid = get_nid(line);

  pending_split = 0;

  if (index == (uint64_t*) 0) {
    before = (uint64_t*) *(sym_bases + nid);
    after  = (uint64_t*) *(sym_states + nid);
  } else {
    before = arr_read(*(sym_bases + nid), index);
    after  = arr_read(*(sym_states + nid), index);
  }

  if (pending_split != 0) {
    difference = pending_split;

    mark = assumed_count;

    if (assume_literal(difference))
      check_state_at(line, index);

    undo_assumptions(mark);

    if (assume_literal(aig_not(difference)))
      check_state_at(line, index);

    undo_assumptions(mark);

    return;
  }

  if (before == after)
    return;

  // their difference as the path sees it

  difference = aig_cofactor(aig_not(bv_eq(before, after)));

  if (difference == AIG_FALSE)
    return;

  *(solved_paths + nid) = *(solved_paths + nid) + 1;

  deciding = 0;

  if (solve_on_path(difference)) {
    if (*(failed_paths + nid) == 0) {
      if (index == (uint64_t*) 0)
        printf("%s: %s is %lu instead of %lu on path %lu with\n", selfie_name, (char*) get_arg1(line),
          bv_evaluate(after), bv_evaluate(before), complete_paths);
      else
        printf("%s: %s[%lu] is %lu instead of %lu on path %lu with\n", selfie_name, (char*) get_arg1(line),
          bv_evaluate(index), bv_evaluate(after), bv_evaluate(before), complete_paths);

      restore_model(first_model);

      sym_block_model(32);

      restore_model(second_model);
    }

    *(failed_paths + nid) = *(failed_paths + nid) + 1;

    counterexamples = counterexamples + 1;
  }

  deciding = 1;
}

void check_state(uint64_t* line) {
  uint64_t nid;
  uint64_t a;

  // an array that is the array before with elements written is restored
  // iff it is at all indices written, any other array iff it is at a
  // free index

  nid = get_nid(line);

  if (*(sym_states + nid) == *(sym_bases + nid))
    return;

  if (is_bitvector(get_sid(line))) {
    check_state_at(line, (uint64_t*) 0);

    return;
  }

  a = *(sym_states + nid);

  while (*(arr_kind + a) == ARR_WRITE)
    a = *(arr_x + a);

  if (a == *(sym_bases + nid)) {
    a = *(sym_states + nid);

    while (*(arr_kind + a) == ARR_WRITE) {
      check_state_at(line, (uint64_t*) *(arr_y + a));

      a = *(arr_x + a);
    }
  } else {
    if (*(difference_indices + nid) == 0)
      *(difference_indices + nid) = (uint64_t) bv_fresh(eval_array_size(get_sid(line)));

    check_state_at(line, (uint64_t*) *(difference_indices + nid));
  }
}

void check_path() {
  uint64_t nid;
  uint64_t* line;

  // every state must be back at its initial value

  complete_paths = complete_paths + 1;

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED)
      if (get_op(line) == OP_STATE)
        check_state(line);

    nid = nid + 1;
  }
}

void prove_paths() {
  uint64_t mark;
  uint64_t outcome;
  uint64_t split;

  // depth-first over all paths: a path that is not decided yet is split
  // on the first literal it does not decide; stops at the first path on
  // which a state is not restored, unless all are asked for

  if (stop_at_first)
    if (counterexamples > 0)
      return;

  mark = assumed_count;

  outcome = evaluate_path();

  if (outcome == PATH_SPLIT) {
    split = pending_split;

    outcome = assumed_count;

    if (assume_literal(split))
      prove_paths();
    else
      infeasible_paths = infeasible_paths + 1;

    undo_assumptions(outcome);

    if (assume_literal(aig_not(split)))
      prove_paths();
    else
      infeasible_paths = infeasible_paths + 1;
  } else if (outcome == PATH_COMPLETE) {
    check_path();

    if (verbose)
      if (complete_paths % 1000 == 0)
        printf("%s: %lu paths complete, %lu infeasible, %lu and-nodes\n", selfie_name, complete_paths, infeasible_paths, aig_ands);
  } else
    infeasible_paths = infeasible_paths + 1;

  undo_assumptions(mark);
}

uint64_t prove_identity() {
  uint64_t nid;
  uint64_t* line;
  uint64_t* other;
  uint64_t failed;
  uint64_t proven;

  // proves that the second model undoes the first: from any state that
  // satisfies the constraints of the first model and is not bad, k steps of
  // the first followed by k steps of the second lead back to that state.
  // All states are free, the models share their states by name. The proof
  // is by cases: every choice in the models, between instructions, between
  // aliased and distinct registers and addresses, between taken and not
  // taken, splits the path, and on a path without choices most states are
  // restored by construction. Returns the number of states for which a
  // counterexample exists.

  printf("%s: ********************************************************************************\n", selfie_name);

  if (max_steps == 0)
    max_steps = 1;

  first_model  = zmalloc(MODEL_RECORD_SIZE * sizeof(uint64_t));
  second_model = zmalloc(MODEL_RECORD_SIZE * sizeof(uint64_t));

  sym_init(1);

  save_model(first_model);

  // the second model

  nid_lines  = (uint64_t*) 0;
  init_lines = (uint64_t*) 0;
  nid_limit  = 0;
  max_nid    = 0;

  number_of_sorts       = 0;
  number_of_states      = 0;
  number_of_inits       = 0;
  number_of_nexts       = 0;
  number_of_bads        = 0;
  number_of_constraints = 0;

  model_name = second_model_name;

  parse_model();

  sym_values = zmalloc((max_nid + 1) * sizeof(uint64_t));
  sym_stamps = zmalloc((max_nid + 1) * sizeof(uint64_t));
  sym_states = zmalloc((max_nid + 1) * sizeof(uint64_t));
  sym_nexts  = zmalloc((max_nid + 1) * sizeof(uint64_t));
  sym_bases  = zmalloc((max_nid + 1) * sizeof(uint64_t));
  sym_free   = zmalloc((max_nid + 1) * sizeof(uint64_t));

  state_map          = zmalloc((max_nid + 1) * sizeof(uint64_t));
  difference_indices = zmalloc((max_nid + 1) * sizeof(uint64_t));
  solved_paths       = zmalloc((max_nid + 1) * sizeof(uint64_t));
  failed_paths       = zmalloc((max_nid + 1) * sizeof(uint64_t));

  save_model(second_model);

  // the states of the second model are the states of the first by name

  nid = 1;

  while (nid <= *(second_model + 3)) {
    restore_model(second_model);

    line = line_of_nid(nid);

    if (line != UNUSED)
      if (get_op(line) == OP_STATE) {
        restore_model(first_model);

        other = find_state((char*) get_arg1(line));

        if (other == UNUSED) {
          printf("%s: state %s of %s is not in %s\n", selfie_name, (char*) get_arg1(line), second_model_name, model_name);

          exit(EXITCODE_BADARGUMENTS);
        }

        *(state_map + nid) = get_nid(other);

        *((uint64_t*) *(second_model + 8) + nid) = *(sym_bases + get_nid(other));
      }

    nid = nid + 1;
  }

  deciding = 1;

  prove_paths();

  deciding = 0;

  restore_model(second_model);

  printf("%s: %s and then %s on %lu paths, %lu more are infeasible, steps: %lu\n", selfie_name,
    (char*) *(first_model + 10), model_name, complete_paths, infeasible_paths, max_steps);
  printf("%s: %lu and-nodes over %lu inputs, %lu SAT calls with %lu variables at most and %lu conflicts in total\n", selfie_name,
    aig_ands, aig_inputs, sat_calls, sat_max_variables, solver_conflicts);

  failed = 0;
  proven = 0;

  nid = 1;

  while (nid <= max_nid) {
    line = line_of_nid(nid);

    if (line != UNUSED)
      if (get_op(line) == OP_STATE) {
        if (*(failed_paths + nid) > 0) {
          printf("%s: %s is not restored on %lu paths\n", selfie_name, (char*) get_arg1(line), *(failed_paths + nid));

          failed = failed + 1;
        } else if (counterexamples == 0) {
          if (*(solved_paths + nid) == 0)
            printf("%s: %s is restored, by construction on all paths\n", selfie_name, (char*) get_arg1(line));
          else
            printf("%s: %s is restored, by construction on all but %lu paths, proven by CDCL\n", selfie_name,
              (char*) get_arg1(line), *(solved_paths + nid));

          proven = proven + 1;
        }
      }

    nid = nid + 1;
  }

  if (failed == 0)
    printf("%s: %s after %s is the identity on all %lu states, steps: %lu\n", selfie_name,
      second_model_name, (char*) *(first_model + 10), proven, max_steps);
  else
    printf("%s: %s after %s is not the identity: %lu states are not restored on the paths taken\n", selfie_name,
      second_model_name, (char*) *(first_model + 10), failed);

  return failed;
}

// -----------------------------------------------------------------
// ---------------------------- DIMACS -----------------------------
// -----------------------------------------------------------------

uint64_t dimacs_pass(uint64_t checking) {
  char* token;
  uint64_t n;
  uint64_t l;
  uint64_t satisfied;
  uint64_t clauses;

  // first pass: loads the clauses into the solver; second pass: counts the
  // clauses the model does not satisfy

  model_pos  = 0;
  model_line = 1;

  n = 0;

  satisfied = 0;
  clauses   = 0;

  while (model_pos < model_size) {
    skip_blanks();

    if (at_end_of_line())
      skip_line();
    else if (model_character() == 99)
      // comment
      skip_line();
    else if (model_character() == 37)
      // end marker of some benchmarks
      model_pos = model_size;
    else if (model_character() == 112) {
      scan_token();
      scan_token();

      l = parse_decimal(scan_token());

      if (not(checking)) {
        sat_reset(l);

        dimacs_clause = zmalloc((2 * l + 2) * sizeof(uint64_t));
      }

      skip_line();
    } else {
      token = scan_token();

      while (token != (char*) 0) {
        if (load_character(token, 0) == 45)
          l = 2 * (0 - parse_decimal(token)) + 1;
        else
          l = 2 * parse_decimal(token);

        if (l / 2 == 0) {
          if (checking) {
            if (satisfied == 0)
              clauses = clauses + 1;
          } else
            sat_add_clause(dimacs_clause, n);

          n = 0;

          satisfied = 0;
        } else if (l / 2 > sat_variables)
          parse_error("variable exceeds number of variables");
        else if (checking) {
          if (sat_lit_value(l) == SAT_TRUE)
            satisfied = 1;
        } else if (n < 2 * sat_variables + 2) {
          *(dimacs_clause + n) = l;

          n = n + 1;
        }

        token = scan_token();
      }

      skip_line();
    }
  }

  return clauses;
}

uint64_t solve_dimacs() {
  uint64_t v;

  // CDCL on a DIMACS CNF file, reporting as babysat does

  model_text = (char*) read_whole_file(model_name);

  dimacs_pass(0);

  if (sat_solve() == SAT_TRUE) {
    if (dimacs_pass(1) > 0) {
      printf("%s: model does not satisfy %s\n", selfie_name, model_name);

      return EXITCODE_SYSTEMERROR;
    }

    printf("%s: %s is satisfiable with ", selfie_name, model_name);

    v = 1;

    while (v <= sat_variables) {
      if (*(sat_values + v) == SAT_TRUE)
        printf("%lu ", v);
      else
        printf("-%lu ", v);

      v = v + 1;
    }
  } else
    printf("%s: %s is unsatisfiable", selfie_name, model_name);

  println();

  printf("%s: %lu variables, %lu clauses, %lu decisions, %lu conflicts, %lu restarts\n", selfie_name,
    sat_variables, sat_clauses, sat_decisions, sat_conflicts, sat_restarts);

  return EXITCODE_NOERROR;
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

uint64_t bitr() {
  if (number_of_remaining_arguments() == 0)
    return EXITCODE_BADARGUMENTS;

  model_name = get_argument();

  if (string_compare(model_name, "-sat")) {
    // CDCL on a DIMACS CNF file
    if (number_of_remaining_arguments() == 0)
      return EXITCODE_BADARGUMENTS;

    model_name = get_argument();

    return solve_dimacs();
  }

  while (number_of_remaining_arguments() > 0) {
    get_argument();

    if (string_compare(argument, "-bmc")) {
      checking_bmc = 1;

      if (number_of_remaining_arguments() > 0)
        max_steps = atoi(get_argument());
      else
        return EXITCODE_BADARGUMENTS;
    } else if (string_compare(argument, "-identity")) {
      if (number_of_remaining_arguments() > 0)
        second_model_name = get_argument();
      else
        return EXITCODE_BADARGUMENTS;
    } else if (string_compare(argument, "-product")) {
      if (number_of_remaining_arguments() > 0)
        product_model_name = get_argument();
      else
        return EXITCODE_BADARGUMENTS;
    } else if (string_compare(argument, "-abstraction")) {
      if (number_of_remaining_arguments() > 0)
        abstraction_model_name = get_argument();
      else
        return EXITCODE_BADARGUMENTS;
    } else if (string_compare(argument, "-grid")) {
      if (number_of_remaining_arguments() > 0)
        layout_file = get_argument();
      else
        return EXITCODE_BADARGUMENTS;
    } else if (string_compare(argument, "-all"))
      stop_at_first = 0;
    else if (string_compare(argument, "-v"))
      verbose = 1;
    else if (string_compare(argument, "-w")) {
      if (number_of_remaining_arguments() > 0)
        witness_file = get_argument();
      else
        return EXITCODE_BADARGUMENTS;
    } else if (string_compare(argument, "-dimacs")) {
      if (number_of_remaining_arguments() > 1) {
        dimacs_prefix = get_argument();
        dimacs_limit  = atoi(get_argument());
      } else
        return EXITCODE_BADARGUMENTS;
    } else if (string_compare(argument, "-l")) {
      if (number_of_remaining_arguments() > 0)
        binary_file = get_argument();
      else
        return EXITCODE_BADARGUMENTS;
    } else if (string_compare(argument, "-i")) {
      if (number_of_remaining_arguments() > 0)
        input_file = get_argument();
      else
        return EXITCODE_BADARGUMENTS;
    } else if (string_compare(argument, "-k")) {
      if (number_of_remaining_arguments() > 0)
        max_steps = atoi(get_argument());
      else
        return EXITCODE_BADARGUMENTS;
    } else if (string_compare(argument, "-p"))
      printing_pc = 1;
    else
      return EXITCODE_BADARGUMENTS;
  }

  // concrete simulation: inputs and states are values, not symbols
  inputs_are_symbolic = 0;
  states_are_symbolic = 0;

  parse_model();

  if (second_model_name != (char*) 0) {
    if (prove_identity() > 0)
      return EXITCODE_SYSTEMERROR;

    printf("%s: ################################################################################\n", selfie_name);

    return EXITCODE_NOERROR;
  }

  if (product_model_name != (char*) 0) {
    if (abstraction_model_name == (char*) 0)
      return EXITCODE_BADARGUMENTS;

    if (not(product()))
      return EXITCODE_SYSTEMERROR;

    printf("%s: ################################################################################\n", selfie_name);

    return EXITCODE_NOERROR;
  }

  init_states();

  if (binary_file != (char*) 0)
    load_binary(binary_file);

  if (input_file != (char*) 0)
    load_input(input_file);

  if (layout_file != (char*) 0)
    load_layout(layout_file);

  if (checking_bmc) {
    bmc();

    print_bmc_statistics();
  } else
    simulate();

  printf("%s: ################################################################################\n", selfie_name);

  return EXITCODE_NOERROR;
}

int main(int argc, char** argv) {
  uint64_t exit_code;

  init_selfie((uint64_t) argc, (uint64_t*) argv);

  init_library();
  init_system();
  init_target();
  init_kernel();

  // the loader uses selfie's binary loader
  init_register();
  init_interpreter();
  init_disassembler();

  init_model();

  OP_OUTPUT = "output";

  init_aig();
  init_bit_vectors();
  init_arrays();

  cnf_clause = zmalloc(3 * sizeof(uint64_t));

  exit_code = bitr();

  return exit_selfie(exit_code, " model.btor2 [ -l binary ] [ -i file ] [ -grid layout ] [ -k steps ] [ -p ]");
}
