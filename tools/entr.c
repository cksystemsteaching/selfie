/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

Entr counts. A BTOR2 model with some bits of its initial state open has
a world per value of these bits, and a question, here whether a bad state
is reached within a number of steps, marks some of the worlds. Their
number is the count of the question and the logarithm of the count its
entropy. See projects/entropy.md for the plan and the story.

This file has, from milestone E1, the arithmetic of counts and the
reference, which is the specification of every count that entr will ever
report. The reference enumerates the worlds and runs the concrete
evaluator of tools/btor2.h on each, or for a formula evaluates its clauses.
It is exponential in the bits counted over, on purpose.

From milestone E2 it has the loop, for formulas in DIMACS format: bracket
a region, and if the bracket is undecided split the region and bracket the
halves. The bracket is what is concluded without a split, the estimate
picks the split, and every other technique is a switch of one of the two.
A ledger says how many worlds each rule disposed of and must account for
all of them, and a trace is the run as a file that tests/entr-trace.c
replays to the count.

Every count is a count over a declared set of bits. An open bit of the
model that is neither counted over nor fixed is refused: it would double
the count without being asked to.

Entr reads BTOR2 and nothing else. Parser, loaders, and the lines of a
model are bitr's, through bitr.h, which is tools/bitr.c with its main
renamed, as riscr.h is tools/riscr.c. Entr uses nothing of bitr's
symbolic layer.
*/

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------------- ENTR ------------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------------- COUNT -----------------------------
// -----------------------------------------------------------------

uint64_t* new_count(uint64_t value);

uint64_t count_mantissa(uint64_t* count);
uint64_t count_exponent(uint64_t* count);
uint64_t count_is_exact(uint64_t* count);

void count_normalize(uint64_t* count);
void count_add(uint64_t* count, uint64_t* addend);

uint64_t entropy_in_hundredths(uint64_t* count);

void print_count(uint64_t* count);
void print_entropy(uint64_t* count);

// a count is mantissa * 2^exponent, the mantissa odd or zero, so that
// open bits only add to the exponent; a count whose mantissa did not
// fit is not exact, and is then a lower bound
//
// +---+----------+
// | 0 | mantissa |
// | 1 | exponent |
// | 2 | exact    | 1 if the count is exact, 0 if it is a lower bound
// +---+----------+

uint64_t COUNT_SIZE = 3;

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t ENTROPY_FRACTION_BITS = 16; // bits of the binary logarithm after the point

// -----------------------------------------------------------------
// ----------------------------- WORLDS ----------------------------
// -----------------------------------------------------------------

void declare_over(char* symbol, uint64_t index, uint64_t bits);
void declare_fixed(char* symbol, uint64_t index, uint64_t value);
void declare_zero(char* symbol);

uint64_t* state_of_declaration(char* symbol);
uint64_t  bits_of_state(uint64_t* state_nid);
uint64_t  elements_of_state(uint64_t* state_nid);

void check_declarations();

uint64_t read_element(uint64_t* state_nid, uint64_t index);
void     write_element(uint64_t* state_nid, uint64_t index, uint64_t value);

void take_snapshot();
void set_world(uint64_t world);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t MAX_DECLARATIONS = 64;

uint64_t MAX_BITS_OVER = 24; // the reference enumerates up to 2^24 worlds

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* over_symbols = (uint64_t*) 0; // states with bits counted over
uint64_t* over_states  = (uint64_t*) 0; // their lines
uint64_t* over_indices = (uint64_t*) 0; // the element, 0 for a bit vector
uint64_t* over_bits    = (uint64_t*) 0; // the number of its lowest bits counted over

uint64_t number_of_overs = 0;

uint64_t* fixed_symbols = (uint64_t*) 0; // states with an element fixed to a value
uint64_t* fixed_states  = (uint64_t*) 0;
uint64_t* fixed_indices = (uint64_t*) 0;
uint64_t* fixed_values  = (uint64_t*) 0;

uint64_t number_of_fixed = 0;

uint64_t* zero_symbols = (uint64_t*) 0; // states whose open bits are zero unless declared otherwise
uint64_t* zero_states  = (uint64_t*) 0;

uint64_t number_of_zeros = 0;

uint64_t bits_over = 0; // number of bits counted over

uint64_t* snapshot = (uint64_t*) 0; // per state: its value, or a copy of its array, before the first step

// -----------------------------------------------------------------
// --------------------------- REFERENCE ---------------------------
// -----------------------------------------------------------------

uint64_t property_index(uint64_t* line);

uint64_t run_world();

void print_world(uint64_t world, uint64_t outcome);

void reference();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t WORLD_BAD      = 1; // a bad state is reached
uint64_t WORLD_HALTED   = 2; // no state changes any more
uint64_t WORLD_OPEN     = 3; // the bound on steps is reached
uint64_t WORLD_EXCLUDED = 4; // a constraint is violated: not a world

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t printing_worlds = 0; // print the outcome of every world that is not halted

uint64_t* world_property = (uint64_t*) 0; // the property that ended the most recent world
uint64_t  world_steps    = 0;             // and the number of instructions executed

uint64_t* bad_counts = (uint64_t*) 0; // per property: number of worlds it ended
uint64_t* bad_firsts = (uint64_t*) 0; // the smallest number of instructions after which it did
uint64_t* bad_lasts  = (uint64_t*) 0; // and the largest

// -----------------------------------------------------------------
// ---------------------------- FORMULA ----------------------------
// -----------------------------------------------------------------

uint64_t formula_character();
void     skip_formula_blanks();
void     skip_formula_line();
uint64_t scan_formula_number();
void     formula_error(char* message);

void load_formula(char* name);

uint64_t literal_variable(uint64_t literal);
uint64_t literal_is_negative(uint64_t literal);
uint64_t literal_value(uint64_t literal);

void print_literal(uint64_t fd, uint64_t literal);

void add_clause(uint64_t* literals, uint64_t size);

uint64_t negation(uint64_t literal);

void assign_literal(uint64_t literal);
void suppose_literal(uint64_t literal);
void imply_literal(uint64_t literal, uint64_t clause);
void unassign_to(uint64_t mark);

void formula_reference();

// a formula is a conjunction of clauses over variables 0 to n - 1; a
// literal is twice its variable, plus one if it is negative; a region is
// the values of the variables, on a trail in the order they were given;
// a literal on the trail is assumed, by a split, or implied by a clause,
// its reason, and its level is the number of literals assumed up to it;
// clauses that follow from the formula may be added behind its own

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t VALUE_OPEN  = 0;
uint64_t VALUE_TRUE  = 1;
uint64_t VALUE_FALSE = 2;

uint64_t MAX_REFERENCE_VARIABLES = 24; // the reference enumerates up to 2^24 worlds

// ------------------------ GLOBAL VARIABLES -----------------------

char* formula_name = (char*) 0;

char*    formula_text = (char*) 0; // formula file in memory
uint64_t formula_size = 0;         // in bytes
uint64_t formula_pos  = 0;         // current character
uint64_t formula_line = 1;         // current line number

uint64_t number_of_variables   = 0;
uint64_t number_of_clauses     = 0; // clauses of the formula
uint64_t number_of_all_clauses = 0; // and with the clauses added

uint64_t* clause_starts   = (uint64_t*) 0; // per clause: its first literal, and one more for the end
uint64_t* clause_literals = (uint64_t*) 0;

uint64_t clause_capacity  = 0; // clauses there is memory for
uint64_t literal_capacity = 0; // literals there is memory for

uint64_t* variable_values  = (uint64_t*) 0; // per variable: open, true, or false
uint64_t* variable_levels  = (uint64_t*) 0; // number of literals assumed when it got its value
uint64_t* variable_reasons = (uint64_t*) 0; // clause that implied its value, plus one, or 0

uint64_t* trail       = (uint64_t*) 0; // literals made true, in order
uint64_t  trail_size  = 0;
uint64_t  trail_level = 0; // number of literals assumed on the trail

// -----------------------------------------------------------------
// ----------------------------- LOOP ------------------------------
// -----------------------------------------------------------------

uint64_t* count_of_power(uint64_t exponent);

uint64_t* new_ledger();
void      enter(uint64_t* ledger, uint64_t exponent);
uint64_t* count_of_ledger(uint64_t* ledger);
uint64_t  ledgers_account();

uint64_t open_variables();

void trace(char* event, uint64_t literal, uint64_t clause);

uint64_t is_answered();

void count_region();

void print_model();
void print_interval(uint64_t* total);
void print_ledger();
void print_measure();

void loop();

// the loop of the story: bracket a region; if the bracket is undecided,
// split the region on the bit the estimate picks and bracket the halves

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t asking_whether = 0; // the question is whether the count is zero: stop at the first world found

uint64_t found_regions = 0; // regions that are full so far

// the ledger: how many worlds each rule disposed of, as the number of
// regions of each size, so that no world is lost to rounding: a region
// with f open bits is entered as one region at exponent f

uint64_t* ledger_empty     = (uint64_t*) 0; // regions that violate a clause
uint64_t* ledger_full      = (uint64_t*) 0; // regions that satisfy all clauses
uint64_t* ledger_propagate = (uint64_t*) 0; // halves that unit propagation found empty
uint64_t* ledger_pure      = (uint64_t*) 0; // halves that pure literals make irrelevant
uint64_t* ledger_learn     = (uint64_t*) 0; // regions and halves that a learned clause found empty
uint64_t* ledger_open      = (uint64_t*) 0; // regions not looked at since the question was answered

// the measure: what the search cost

uint64_t undecided_regions = 0; // regions split
uint64_t brackets_taken    = 0; // regions bracketed
uint64_t clauses_visited   = 0; // clauses looked at by all brackets

uint64_t* model_values = (uint64_t*) 0; // per variable: its value in the first world found

uint64_t model_found = 0;

char*    trace_name = (char*) 0; // file to write the trace to
uint64_t trace_fd   = 0;

// -----------------------------------------------------------------
// ---------------------------- BRACKET ----------------------------
// -----------------------------------------------------------------

uint64_t scan_clauses();
uint64_t find_pure_literal();

uint64_t bracket();

void learn(uint64_t conflict);

// the bracket of a region: empty, full, or undecided; a bracket that
// propagates makes the region smaller before it says undecided

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t BRACKET_EMPTY     = 0; // lo = hi = 0
uint64_t BRACKET_FULL      = 1; // lo = hi = 2^(open variables)
uint64_t BRACKET_UNDECIDED = 2; // lo = 0, hi = 2^(open variables)
uint64_t BRACKET_UNIT      = 3; // a clause has one open literal and no true one

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t bracket_propagates = 1; // switch propagate: unit propagation
uint64_t bracket_pure       = 1; // switch pure: pure literals, only if asking whether
uint64_t bracket_learns     = 1; // switch learn: a clause from every region found empty

uint64_t* variable_seen = (uint64_t*) 0; // per variable: part of the clause being learned
uint64_t* seen_stack    = (uint64_t*) 0; // the variables seen, to forget them again
uint64_t* learned       = (uint64_t*) 0; // the clause being learned

uint64_t learned_clauses  = 0; // clauses learned
uint64_t learned_literals = 0; // and their literals

uint64_t bracket_clause  = 0; // the clause that makes the region empty, or is unit
uint64_t bracket_literal = 0; // the open literal of the unit clause

uint64_t* literal_occurs = (uint64_t*) 0; // per literal: whether it occurs in a clause not yet satisfied

// -----------------------------------------------------------------
// --------------------------- ESTIMATE ----------------------------
// -----------------------------------------------------------------

uint64_t estimate();

// the estimate of a region: the literal to make true first, for the
// variable to split on; it changes the cost and never the answer

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

uint64_t set_switch(char* name, uint64_t value);

uint64_t entr_formula();

uint64_t entr();

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------------- COUNT -----------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t* new_count(uint64_t value) {
  uint64_t* count;

  count = smalloc(COUNT_SIZE * sizeof(uint64_t));

  *count       = value;
  *(count + 1) = 0;
  *(count + 2) = 1;

  count_normalize(count);

  return count;
}

uint64_t count_mantissa(uint64_t* count) { return *count; }
uint64_t count_exponent(uint64_t* count) { return *(count + 1); }
uint64_t count_is_exact(uint64_t* count) { return *(count + 2); }

void count_normalize(uint64_t* count) {
  // the mantissa is odd, or the count is zero with exponent zero

  if (*count == 0) {
    *(count + 1) = 0;

    return;
  }

  while (*count % 2 == 0) {
    *count       = *count / 2;
    *(count + 1) = *(count + 1) + 1;
  }
}

void count_add(uint64_t* count, uint64_t* addend) {
  uint64_t m;
  uint64_t e;
  uint64_t n;
  uint64_t f;

  // count = count + addend: the sum of the counts of two halves

  if (count_is_exact(addend) == 0)
    *(count + 2) = 0;

  if (count_mantissa(addend) == 0)
    return;

  if (count_mantissa(count) == 0) {
    *count       = count_mantissa(addend);
    *(count + 1) = count_exponent(addend);

    return;
  }

  // m * 2^e is the summand with the smaller exponent

  if (count_exponent(count) <= count_exponent(addend)) {
    m = count_mantissa(count);
    e = count_exponent(count);
    n = count_mantissa(addend);
    f = count_exponent(addend);
  } else {
    m = count_mantissa(addend);
    e = count_exponent(addend);
    n = count_mantissa(count);
    f = count_exponent(count);
  }

  // n * 2^f becomes n * 2^(f - e) * 2^e as far as that fits

  while (f > e) {
    if (n >= two_to_the_power_of(SIZEOFUINT64INBITS - 1)) {
      // it does not: the smaller summand loses its lowest bits instead,
      // and the sum is a lower bound
      while (f > e) {
        if (m % 2 == 1)
          *(count + 2) = 0;

        m = m / 2;
        e = e + 1;
      }
    } else {
      n = n * 2;
      f = f - 1;
    }
  }

  if (m + n < m) {
    // the sum does not fit: halved, it does, and loses its lowest bit
    if ((m % 2 + n % 2) % 2 == 1)
      *(count + 2) = 0;

    *count       = m / 2 + n / 2 + (m % 2 + n % 2) / 2;
    *(count + 1) = e + 1;
  } else {
    *count       = m + n;
    *(count + 1) = e;
  }

  count_normalize(count);
}

uint64_t entropy_in_hundredths(uint64_t* count) {
  uint64_t m;
  uint64_t p;
  uint64_t x;
  uint64_t fraction;
  uint64_t i;

  // the binary logarithm of a count that is not zero, times 100, rounded
  // down: the exponent plus the logarithm of the mantissa, whose bits
  // after the point come from squaring the mantissa scaled to [1,2)

  // p is the position of the highest bit of the mantissa

  m = count_mantissa(count);

  p = 0;

  while (m > 1) {
    m = m / 2;

    p = p + 1;
  }

  m = count_mantissa(count);

  // x = m / 2^p * 2^31, in [2^31, 2^32)

  if (p >= 31)
    x = m / two_to_the_power_of(p - 31);
  else
    x = m * two_to_the_power_of(31 - p);

  fraction = 0;

  i = 0;

  while (i < ENTROPY_FRACTION_BITS) {
    x = x * x / two_to_the_power_of(31);

    fraction = fraction * 2;

    if (x >= two_to_the_power_of(32)) {
      x = x / 2;

      fraction = fraction + 1;
    }

    i = i + 1;
  }

  return (count_exponent(count) + p) * 100 + fraction * 100 / two_to_the_power_of(ENTROPY_FRACTION_BITS);
}

void print_count(uint64_t* count) {
  if (count_is_exact(count) == 0) {
    // a lower bound, as a power of two
    if (count_mantissa(count) == 0)
      printf("at least 0");
    else {
      printf("at least 2^");
      print_entropy(count);
    }

    return;
  }

  if (count_exponent(count) == 0)
    printf("%lu", count_mantissa(count));
  else if (count_exponent(count) + log_two(count_mantissa(count)) < SIZEOFUINT64INBITS - 1)
    printf("%lu", count_mantissa(count) * two_to_the_power_of(count_exponent(count)));
  else if (count_mantissa(count) == 1)
    printf("2^%lu", count_exponent(count));
  else
    printf("%lu * 2^%lu", count_mantissa(count), count_exponent(count));
}

void print_entropy(uint64_t* count) {
  uint64_t h;

  // entropy in bits with two digits after the point

  if (count_mantissa(count) == 0) {
    printf("none");

    return;
  }

  h = entropy_in_hundredths(count);

  printf("%lu.", h / 100);

  if (h % 100 < 10)
    printf("0");

  printf("%lu", h % 100);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------------- WORLDS ----------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

void declare_over(char* symbol, uint64_t index, uint64_t bits) {
  if (over_symbols == (uint64_t*) 0) {
    over_symbols = smalloc(MAX_DECLARATIONS * sizeof(uint64_t));
    over_states  = smalloc(MAX_DECLARATIONS * sizeof(uint64_t));
    over_indices = smalloc(MAX_DECLARATIONS * sizeof(uint64_t));
    over_bits    = smalloc(MAX_DECLARATIONS * sizeof(uint64_t));
  }

  if (number_of_overs >= MAX_DECLARATIONS) {
    printf("%s: more than %lu elements counted over\n", selfie_name, MAX_DECLARATIONS);

    exit(EXITCODE_BADARGUMENTS);
  }

  *(over_symbols + number_of_overs) = (uint64_t) symbol;
  *(over_indices + number_of_overs) = index;
  *(over_bits + number_of_overs)    = bits;

  number_of_overs = number_of_overs + 1;
}

void declare_fixed(char* symbol, uint64_t index, uint64_t value) {
  if (fixed_symbols == (uint64_t*) 0) {
    fixed_symbols = smalloc(MAX_DECLARATIONS * sizeof(uint64_t));
    fixed_states  = smalloc(MAX_DECLARATIONS * sizeof(uint64_t));
    fixed_indices = smalloc(MAX_DECLARATIONS * sizeof(uint64_t));
    fixed_values  = smalloc(MAX_DECLARATIONS * sizeof(uint64_t));
  }

  if (number_of_fixed >= MAX_DECLARATIONS) {
    printf("%s: more than %lu elements fixed\n", selfie_name, MAX_DECLARATIONS);

    exit(EXITCODE_BADARGUMENTS);
  }

  *(fixed_symbols + number_of_fixed) = (uint64_t) symbol;
  *(fixed_indices + number_of_fixed) = index;
  *(fixed_values + number_of_fixed)  = value;

  number_of_fixed = number_of_fixed + 1;
}

void declare_zero(char* symbol) {
  if (zero_symbols == (uint64_t*) 0) {
    zero_symbols = smalloc(MAX_DECLARATIONS * sizeof(uint64_t));
    zero_states  = smalloc(MAX_DECLARATIONS * sizeof(uint64_t));
  }

  if (number_of_zeros >= MAX_DECLARATIONS) {
    printf("%s: more than %lu states zeroed\n", selfie_name, MAX_DECLARATIONS);

    exit(EXITCODE_BADARGUMENTS);
  }

  *(zero_symbols + number_of_zeros) = (uint64_t) symbol;

  number_of_zeros = number_of_zeros + 1;
}

uint64_t* state_of_declaration(char* symbol) {
  uint64_t* state_nid;

  state_nid = find_state(symbol);

  if (state_nid == UNUSED) {
    printf("%s: no state %s in %s\n", selfie_name, symbol, model_name);

    exit(EXITCODE_BADARGUMENTS);
  }

  if (*(uninitialized_states + get_nid(state_nid)) == 0) {
    // an initialized or loaded state has no open bits
    printf("%s: state %s in %s is not open\n", selfie_name, symbol, model_name);

    exit(EXITCODE_BADARGUMENTS);
  }

  return state_nid;
}

uint64_t bits_of_state(uint64_t* state_nid) {
  // the number of bits of a bit vector, or of an element of an array

  if (is_bitvector(get_sid(state_nid)))
    return eval_bitvec_size(get_sid(state_nid));
  else
    return array_element_size(state_nid);
}

uint64_t elements_of_state(uint64_t* state_nid) {
  if (is_bitvector(get_sid(state_nid)))
    return 1;
  else
    return array_elements(state_nid);
}

void check_declarations() {
  uint64_t i;
  uint64_t j;
  uint64_t* state_nid;
  uint64_t declared;
  uint64_t covered;

  // binds the declarations to the states of the model, and refuses the
  // model if a state is open that is neither zeroed nor counted over in
  // all bits of all its elements

  bits_over = 0;

  i = 0;

  while (i < number_of_overs) {
    state_nid = state_of_declaration((char*) *(over_symbols + i));

    if (*(over_indices + i) >= elements_of_state(state_nid)) {
      printf("%s: state %s in %s has no element %lu\n", selfie_name, (char*) *(over_symbols + i), model_name, *(over_indices + i));

      exit(EXITCODE_BADARGUMENTS);
    }

    if (*(over_bits + i) > bits_of_state(state_nid)) {
      printf("%s: state %s in %s has %lu and not %lu bits\n", selfie_name, (char*) *(over_symbols + i), model_name, bits_of_state(state_nid), *(over_bits + i));

      exit(EXITCODE_BADARGUMENTS);
    }

    j = 0;

    while (j < i) {
      if (*(over_states + j) == (uint64_t) state_nid)
        if (*(over_indices + j) == *(over_indices + i)) {
          printf("%s: element %lu of state %s is counted over twice\n", selfie_name, *(over_indices + i), (char*) *(over_symbols + i));

          exit(EXITCODE_BADARGUMENTS);
        }

      j = j + 1;
    }

    *(over_states + i) = (uint64_t) state_nid;

    bits_over = bits_over + *(over_bits + i);

    i = i + 1;
  }

  if (bits_over > MAX_BITS_OVER) {
    printf("%s: %lu bits are more than the %lu the reference counts over\n", selfie_name, bits_over, MAX_BITS_OVER);

    exit(EXITCODE_BADARGUMENTS);
  }

  i = 0;

  while (i < number_of_fixed) {
    state_nid = state_of_declaration((char*) *(fixed_symbols + i));

    if (*(fixed_indices + i) >= elements_of_state(state_nid)) {
      printf("%s: state %s in %s has no element %lu\n", selfie_name, (char*) *(fixed_symbols + i), model_name, *(fixed_indices + i));

      exit(EXITCODE_BADARGUMENTS);
    }

    *(fixed_states + i) = (uint64_t) state_nid;

    i = i + 1;
  }

  i = 0;

  while (i < number_of_zeros) {
    *(zero_states + i) = (uint64_t) state_of_declaration((char*) *(zero_symbols + i));

    i = i + 1;
  }

  i = 0;

  while (i < number_of_state_lines) {
    state_nid = (uint64_t*) *(state_lines + i);

    if (*(uninitialized_states + get_nid(state_nid))) {
      declared = 0;

      j = 0;

      while (j < number_of_zeros) {
        if (*(zero_states + j) == (uint64_t) state_nid)
          declared = 1;

        j = j + 1;
      }

      if (declared == 0) {
        // not zeroed: all bits of all elements must be counted over
        covered = 0;

        j = 0;

        while (j < number_of_overs) {
          if (*(over_states + j) == (uint64_t) state_nid)
            covered = covered + *(over_bits + j);

          j = j + 1;
        }

        if (covered < elements_of_state(state_nid) * bits_of_state(state_nid)) {
          printf("%s: state %s in %s is open: %lu of its %lu bits are neither counted over nor fixed\n", selfie_name,
            (char*) get_arg1(state_nid),
            model_name,
            elements_of_state(state_nid) * bits_of_state(state_nid) - covered,
            elements_of_state(state_nid) * bits_of_state(state_nid));

          exit(EXITCODE_BADARGUMENTS);
        }
      }
    }

    i = i + 1;
  }
}

uint64_t read_element(uint64_t* state_nid, uint64_t index) {
  if (is_bitvector(get_sid(state_nid)))
    return get_state(state_nid);
  else
    return read_array_raw(state_nid, index);
}

void write_element(uint64_t* state_nid, uint64_t index, uint64_t value) {
  if (is_bitvector(get_sid(state_nid)))
    set_state(state_nid, value);
  else
    write_array_raw(state_nid, index, value);
}

void take_snapshot() {
  uint64_t i;
  uint64_t* state_nid;
  uint64_t* sid;

  // the state before the first step, as initialized and loaded, with all
  // open bits zero; the code segment never changes and is not copied

  snapshot = smalloc(number_of_state_lines * sizeof(uint64_t));

  i = 0;

  while (i < number_of_state_lines) {
    state_nid = (uint64_t*) *(state_lines + i);

    sid = get_sid(state_nid);

    if (is_bitvector(sid))
      *(snapshot + i) = get_state(state_nid);
    else if (sid != SID_CODE_STATE) {
      // a state that only initializes another one has no array of its own
      if (get_state(state_nid) != 0)
        *(snapshot + i) = (uint64_t) copy_array(sid, (uint64_t*) get_state(state_nid), allocate_array(sid));
      else
        *(snapshot + i) = 0;
    }

    i = i + 1;
  }
}

void set_world(uint64_t world) {
  uint64_t i;
  uint64_t* state_nid;
  uint64_t* sid;
  uint64_t worlds;

  // all states are as before the first step, but for the elements fixed
  // and the bits counted over, which are the digits of the world; the
  // bits of an element above the ones counted over stay as fixed

  i = 0;

  while (i < number_of_state_lines) {
    state_nid = (uint64_t*) *(state_lines + i);

    sid = get_sid(state_nid);

    if (is_bitvector(sid))
      set_state(state_nid, *(snapshot + i));
    else if (sid != SID_CODE_STATE)
      if (*(snapshot + i) != 0)
        copy_array(sid, (uint64_t*) *(snapshot + i), (uint64_t*) get_state(state_nid));

    set_step(state_nid, current_step);

    i = i + 1;
  }

  i = 0;

  while (i < number_of_fixed) {
    write_element((uint64_t*) *(fixed_states + i), *(fixed_indices + i), *(fixed_values + i));

    i = i + 1;
  }

  i = 0;

  while (i < number_of_overs) {
    state_nid = (uint64_t*) *(over_states + i);

    worlds = two_to_the_power_of(*(over_bits + i));

    write_element(state_nid, *(over_indices + i),
      read_element(state_nid, *(over_indices + i)) / worlds * worlds + world % worlds);

    world = world / worlds;

    i = i + 1;
  }
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// --------------------------- REFERENCE ---------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t property_index(uint64_t* line) {
  uint64_t i;

  i = 0;

  while (i < number_of_property_lines) {
    if (*(property_lines + i) == (uint64_t) line)
      return i;

    i = i + 1;
  }

  return i;
}

uint64_t run_world() {
  uint64_t i;
  uint64_t halt;

  // runs the model from the state it is in until a bad state is reached,
  // a constraint is violated, no state changes any more, or the bound on
  // steps is reached; a step that a property stops is counted, as bitr
  // counts it; all lines are left in the step the next world begins in

  world_steps = 0;

  while (1) {
    next_step = next_step + 1;

    world_property = violated_property();

    if (world_property != UNUSED) {
      skip_nexts();

      current_step = next_step;

      world_steps = world_steps + 1;

      if (get_op(world_property) == OP_BAD)
        return WORLD_BAD;
      else
        return WORLD_EXCLUDED;
    }

    if (max_steps > 0)
      if (world_steps >= max_steps) {
        skip_nexts();

        current_step = next_step;

        return WORLD_OPEN;
      }

    halt = 1;

    i = 0;

    while (i < number_of_next_lines) {
      halt = halt * eval_next((uint64_t*) *(next_lines + i));

      i = i + 1;
    }

    apply_nexts();

    current_step = next_step;

    world_steps = world_steps + 1;

    if (halt)
      return WORLD_HALTED;
  }
}

void print_world(uint64_t world, uint64_t outcome) {
  if (outcome == WORLD_BAD)
    printf("%s: world %lu: bad %s after %lu instructions\n", selfie_name, world, (char*) get_arg2(world_property), world_steps);
  else if (outcome == WORLD_EXCLUDED)
    printf("%s: world %lu: constraint %s violated after %lu instructions\n", selfie_name, world, (char*) get_arg2(world_property), world_steps);
  else if (outcome == WORLD_OPEN)
    printf("%s: world %lu: open after %lu instructions\n", selfie_name, world, world_steps);
}

void reference() {
  uint64_t worlds;
  uint64_t world;
  uint64_t outcome;
  uint64_t i;
  uint64_t* found;
  uint64_t* open;
  uint64_t* total;
  uint64_t* one;
  uint64_t halted;
  uint64_t excluded;
  uint64_t last_halt;

  // the count by enumeration: every world is run, and is bad, halted,
  // open at the bound, or excluded by a constraint; the count of the
  // question is between found and found plus open

  bad_counts = zmalloc(number_of_property_lines * sizeof(uint64_t));
  bad_firsts = zmalloc(number_of_property_lines * sizeof(uint64_t));
  bad_lasts  = zmalloc(number_of_property_lines * sizeof(uint64_t));

  found = new_count(0);
  open  = new_count(0);
  total = new_count(0);
  one   = new_count(1);

  halted    = 0;
  excluded  = 0;
  last_halt = 0;

  worlds = two_to_the_power_of(bits_over);

  world = 0;

  while (world < worlds) {
    set_world(world);

    outcome = run_world();

    if (printing_worlds)
      print_world(world, outcome);

    if (outcome == WORLD_EXCLUDED)
      excluded = excluded + 1;
    else {
      count_add(total, one);

      if (outcome == WORLD_BAD) {
        count_add(found, one);

        i = property_index(world_property);

        if (*(bad_counts + i) == 0)
          *(bad_firsts + i) = world_steps;
        else if (world_steps < *(bad_firsts + i))
          *(bad_firsts + i) = world_steps;

        if (world_steps > *(bad_lasts + i))
          *(bad_lasts + i) = world_steps;

        *(bad_counts + i) = *(bad_counts + i) + 1;
      } else if (outcome == WORLD_OPEN)
        count_add(open, one);
      else {
        halted = halted + 1;

        if (world_steps > last_halt)
          last_halt = world_steps;
      }
    }

    world = world + 1;
  }

  i = 0;

  while (i < number_of_property_lines) {
    if (*(bad_counts + i) > 0)
      printf("%s: %lu worlds reach bad %s after %lu to %lu instructions\n", selfie_name,
        *(bad_counts + i),
        (char*) get_arg2((uint64_t*) *(property_lines + i)),
        *(bad_firsts + i),
        *(bad_lasts + i));

    i = i + 1;
  }

  if (halted > 0)
    printf("%s: %lu worlds halt after at most %lu instructions\n", selfie_name, halted, last_halt);

  if (excluded > 0)
    printf("%s: %lu assignments violate a constraint and are no worlds\n", selfie_name, excluded);

  if (count_mantissa(open) > 0) {
    printf("%s: ", selfie_name);
    print_count(open);
    printf(" worlds are open after %lu instructions\n", max_steps);
  }

  printf("%s: count ", selfie_name);
  print_count(found);

  if (count_mantissa(open) > 0) {
    count_add(open, found);

    printf(" to ");
    print_count(open);
  }

  printf(" of ");
  print_count(total);
  printf(" worlds, entropy ");
  print_entropy(found);

  if (count_mantissa(open) > 0) {
    printf(" to ");
    print_entropy(open);
  }

  printf(" of ");
  print_entropy(total);
  printf(" bits\n");
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------------- FORMULA ----------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t formula_character() {
  if (formula_pos < formula_size)
    return load_character(formula_text, formula_pos);
  else
    // the end of the file
    return 0;
}

void skip_formula_blanks() {
  uint64_t c;

  // blanks, tabs, and ends of lines: 32, 9, 13, and 10

  c = formula_character();

  while (1) {
    if (c == 10)
      formula_line = formula_line + 1;
    else if (c != 32)
      if (c != 9)
        if (c != 13)
          return;

    formula_pos = formula_pos + 1;

    c = formula_character();
  }
}

void skip_formula_line() {
  uint64_t c;

  c = formula_character();

  while (c != 10) {
    if (c == 0)
      return;

    formula_pos = formula_pos + 1;

    c = formula_character();
  }
}

uint64_t scan_formula_number() {
  uint64_t c;
  uint64_t n;

  c = formula_character();

  if (c < '0')
    formula_error("number expected");
  else if (c > '9')
    formula_error("number expected");

  n = 0;

  while (c >= '0') {
    if (c > '9')
      return n;

    n = n * 10 + c - '0';

    formula_pos = formula_pos + 1;

    c = formula_character();
  }

  return n;
}

void formula_error(char* message) {
  printf("%s: %s in line %lu of %s\n", selfie_name, message, formula_line, formula_name);

  exit(EXITCODE_SCANNERERROR);
}

void load_formula(char* name) {
  uint64_t c;
  uint64_t clause;
  uint64_t literals;
  uint64_t negative;
  uint64_t variable;

  // a formula in DIMACS format: comment lines that begin with c, a line
  // p cnf with the numbers of variables and clauses, and the clauses, each
  // a list of variables from 1 on, negated by a minus, that ends with 0

  formula_name = name;

  formula_text = (char*) read_whole_file(name);
  formula_size = model_size;
  formula_pos  = 0;
  formula_line = 1;

  skip_formula_blanks();

  while (formula_character() == 'c') {
    skip_formula_line();
    skip_formula_blanks();
  }

  if (formula_character() != 'p')
    formula_error("p cnf expected");

  formula_pos = formula_pos + 1;

  skip_formula_blanks();

  if (formula_character() != 'c')
    formula_error("p cnf expected");

  // c, n, f
  formula_pos = formula_pos + 3;

  skip_formula_blanks();

  number_of_variables = scan_formula_number();

  skip_formula_blanks();

  number_of_clauses = scan_formula_number();

  // the clauses have no more literals than there are characters left
  clause_capacity  = number_of_clauses + 1;
  literal_capacity = formula_size - formula_pos + 1;

  clause_starts   = smalloc((clause_capacity + 1) * sizeof(uint64_t));
  clause_literals = smalloc(literal_capacity * sizeof(uint64_t));

  variable_values  = zmalloc(number_of_variables * sizeof(uint64_t));
  variable_levels  = zmalloc(number_of_variables * sizeof(uint64_t));
  variable_reasons = zmalloc(number_of_variables * sizeof(uint64_t));
  variable_seen    = zmalloc(number_of_variables * sizeof(uint64_t));

  seen_stack = smalloc(number_of_variables * sizeof(uint64_t));
  learned    = smalloc((number_of_variables + 1) * sizeof(uint64_t));

  model_values    = zmalloc(number_of_variables * sizeof(uint64_t));
  literal_occurs  = zmalloc(2 * number_of_variables * sizeof(uint64_t));

  trail       = smalloc(number_of_variables * sizeof(uint64_t));
  trail_size  = 0;
  trail_level = 0;

  clause   = 0;
  literals = 0;

  *clause_starts = 0;

  while (clause < number_of_clauses) {
    skip_formula_blanks();

    c = formula_character();

    while (c == 'c') {
      skip_formula_line();
      skip_formula_blanks();

      c = formula_character();
    }

    negative = 0;

    if (c == '-') {
      negative = 1;

      formula_pos = formula_pos + 1;
    }

    variable = scan_formula_number();

    if (variable == 0) {
      // the end of a clause is the start of the next
      clause = clause + 1;

      *(clause_starts + clause) = literals;
    } else if (variable > number_of_variables)
      formula_error("variable is not declared");
    else {
      *(clause_literals + literals) = 2 * (variable - 1) + negative;

      literals = literals + 1;
    }
  }

  number_of_all_clauses = number_of_clauses;

  printf("%s: %lu clauses over %lu variables with %lu literals loaded from %s\n", selfie_name,
    number_of_clauses, number_of_variables, literals, formula_name);
}

void add_clause(uint64_t* literals, uint64_t size) {
  uint64_t* bigger;
  uint64_t first;
  uint64_t i;

  // a clause that follows from the formula, behind the clauses there are

  first = *(clause_starts + number_of_all_clauses);

  if (number_of_all_clauses + 1 > clause_capacity) {
    clause_capacity = 2 * clause_capacity;

    bigger = smalloc((clause_capacity + 1) * sizeof(uint64_t));

    i = 0;

    while (i <= number_of_all_clauses) {
      *(bigger + i) = *(clause_starts + i);

      i = i + 1;
    }

    clause_starts = bigger;
  }

  if (first + size > literal_capacity) {
    literal_capacity = 2 * (first + size);

    bigger = smalloc(literal_capacity * sizeof(uint64_t));

    i = 0;

    while (i < first) {
      *(bigger + i) = *(clause_literals + i);

      i = i + 1;
    }

    clause_literals = bigger;
  }

  i = 0;

  while (i < size) {
    *(clause_literals + first + i) = *(literals + i);

    i = i + 1;
  }

  number_of_all_clauses = number_of_all_clauses + 1;

  *(clause_starts + number_of_all_clauses) = first + size;
}

uint64_t negation(uint64_t literal) {
  if (literal_is_negative(literal))
    return literal - 1;
  else
    return literal + 1;
}

uint64_t literal_variable(uint64_t literal)    { return literal / 2; }
uint64_t literal_is_negative(uint64_t literal) { return literal % 2; }

uint64_t literal_value(uint64_t literal) {
  uint64_t value;

  // open, true, or false

  value = *(variable_values + literal_variable(literal));

  if (value == VALUE_OPEN)
    return VALUE_OPEN;
  else if (literal_is_negative(literal)) {
    if (value == VALUE_TRUE)
      return VALUE_FALSE;
    else
      return VALUE_TRUE;
  } else
    return value;
}

void print_literal(uint64_t fd, uint64_t literal) {
  // as in DIMACS: variables from 1 on, negated by a minus

  if (literal_is_negative(literal))
    dprintf(fd, "-%lu", literal_variable(literal) + 1);
  else
    dprintf(fd, "%lu", literal_variable(literal) + 1);
}

void assign_literal(uint64_t literal) {
  // the region becomes its half in which the literal is true

  if (literal_is_negative(literal))
    *(variable_values + literal_variable(literal)) = VALUE_FALSE;
  else
    *(variable_values + literal_variable(literal)) = VALUE_TRUE;

  *(variable_levels + literal_variable(literal))  = trail_level;
  *(variable_reasons + literal_variable(literal)) = 0;

  *(trail + trail_size) = literal;

  trail_size = trail_size + 1;
}

void suppose_literal(uint64_t literal) {
  // a half that no clause singles out: by a split, or by a pure literal

  trail_level = trail_level + 1;

  assign_literal(literal);
}

void imply_literal(uint64_t literal, uint64_t clause) {
  // the half that a clause leaves: its other half is empty by the clause

  assign_literal(literal);

  *(variable_reasons + literal_variable(literal)) = clause + 1;
}

void unassign_to(uint64_t mark) {
  // the region becomes what it was when the trail had mark literals

  while (trail_size > mark) {
    trail_size = trail_size - 1;

    *(variable_values + literal_variable(*(trail + trail_size))) = VALUE_OPEN;
  }

  if (trail_size == 0)
    trail_level = 0;
  else
    trail_level = *(variable_levels + literal_variable(*(trail + trail_size - 1)));
}

void formula_reference() {
  uint64_t worlds;
  uint64_t world;
  uint64_t bits;
  uint64_t variable;
  uint64_t clause;
  uint64_t i;
  uint64_t satisfied;
  uint64_t* found;
  uint64_t* total;
  uint64_t* one;

  // the count by enumeration: every assignment is a world, and is counted
  // if every clause has a true literal

  if (number_of_variables > MAX_REFERENCE_VARIABLES) {
    printf("%s: %lu variables are more than the %lu the reference counts over\n", selfie_name, number_of_variables, MAX_REFERENCE_VARIABLES);

    exit(EXITCODE_BADARGUMENTS);
  }

  found = new_count(0);
  one   = new_count(1);

  worlds = two_to_the_power_of(number_of_variables);

  world = 0;

  while (world < worlds) {
    bits = world;

    variable = 0;

    while (variable < number_of_variables) {
      if (bits % 2)
        *(variable_values + variable) = VALUE_TRUE;
      else
        *(variable_values + variable) = VALUE_FALSE;

      bits = bits / 2;

      variable = variable + 1;
    }

    satisfied = 1;

    clause = 0;

    while (clause < number_of_clauses) {
      satisfied = 0;

      i = *(clause_starts + clause);

      while (i < *(clause_starts + clause + 1)) {
        if (literal_value(*(clause_literals + i)) == VALUE_TRUE) {
          satisfied = 1;

          i = *(clause_starts + clause + 1);
        } else
          i = i + 1;
      }

      if (satisfied)
        clause = clause + 1;
      else
        clause = number_of_clauses;
    }

    if (satisfied)
      count_add(found, one);

    world = world + 1;
  }

  total = count_of_power(number_of_variables);

  printf("%s: count ", selfie_name);
  print_count(found);
  printf(" of ");
  print_count(total);
  printf(" worlds, entropy ");
  print_entropy(found);
  printf(" of ");
  print_entropy(total);
  printf(" bits\n");
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------------- LOOP ------------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t* count_of_power(uint64_t exponent) {
  uint64_t* count;

  // 2^exponent: the number of worlds of a region with that many open bits

  count = new_count(1);

  *(count + 1) = exponent;

  return count;
}

uint64_t* new_ledger() {
  return zmalloc((number_of_variables + 1) * sizeof(uint64_t));
}

void enter(uint64_t* ledger, uint64_t exponent) {
  // one more region of 2^exponent worlds

  *(ledger + exponent) = *(ledger + exponent) + 1;
}

uint64_t* count_of_ledger(uint64_t* ledger) {
  uint64_t* count;
  uint64_t* regions;
  uint64_t exponent;

  // the worlds of a ledger as a count, from the largest regions down, so
  // that a count that does not fit loses its smallest regions

  count = new_count(0);

  exponent = number_of_variables + 1;

  while (exponent > 0) {
    exponent = exponent - 1;

    if (*(ledger + exponent) > 0) {
      regions = new_count(*(ledger + exponent));

      *(regions + 1) = *(regions + 1) + exponent;

      count_add(count, regions);
    }
  }

  return count;
}

uint64_t ledgers_account() {
  uint64_t exponent;
  uint64_t regions;

  // the regions of all ledgers are all 2^n worlds, each once: two regions
  // of a size are one region of the next size, from the smallest up, and
  // what is left is one region of all worlds

  regions = 0;

  exponent = 0;

  while (exponent < number_of_variables) {
    regions = regions
      + *(ledger_empty + exponent)
      + *(ledger_full + exponent)
      + *(ledger_propagate + exponent)
      + *(ledger_pure + exponent)
      + *(ledger_learn + exponent)
      + *(ledger_open + exponent);

    if (regions % 2 == 1)
      return 0;

    regions = regions / 2;

    exponent = exponent + 1;
  }

  regions = regions
    + *(ledger_empty + exponent)
    + *(ledger_full + exponent)
    + *(ledger_propagate + exponent)
    + *(ledger_pure + exponent)
    + *(ledger_learn + exponent)
    + *(ledger_open + exponent);

  return regions == 1;
}

uint64_t open_variables() {
  return number_of_variables - trail_size;
}

void trace(char* event, uint64_t literal, uint64_t clause) {
  // the trace is the run of the loop in the order it happened: s for a
  // split on a literal, followed by the half in which it is true and the
  // half in which it is false; u for a literal that a clause makes true,
  // p for a pure literal, each followed by the half in which it is true;
  // e for a region that a clause makes empty; f for a full region; o for
  // a region not looked at; and, between regions, l for a clause learned,
  // see learn(), which is from then on a clause as the others, numbered
  // after them

  if (trace_name == (char*) 0)
    return;

  dprintf(trace_fd, "%s", event);

  if (string_compare(event, "f") == 0)
    if (string_compare(event, "o") == 0) {
      if (string_compare(event, "e") == 0) {
        dprintf(trace_fd, " ");

        print_literal(trace_fd, literal);
      }

      if (string_compare(event, "s") == 0)
        if (string_compare(event, "p") == 0)
          dprintf(trace_fd, " %lu", clause + 1);
    }

  dprintf(trace_fd, "\n");
}

uint64_t is_answered() {
  // whether is answered by the first world found

  if (asking_whether)
    return found_regions > 0;
  else
    return 0;
}

void count_region() {
  uint64_t mark;
  uint64_t split;
  uint64_t outcome;
  uint64_t literal;
  uint64_t variable;

  // brackets the region the trail describes and, if the bracket is
  // undecided, splits it; leaves the trail as it found it

  mark = trail_size;

  outcome = bracket();

  // the trail of the region as the bracket left it
  split = trail_size;

  if (outcome == BRACKET_EMPTY) {
    if (bracket_clause < number_of_clauses)
      enter(ledger_empty, open_variables());
    else
      // empty by a clause that was learned
      enter(ledger_learn, open_variables());

    trace("e", 0, bracket_clause);

    if (bracket_learns)
      learn(bracket_clause);
  } else if (outcome == BRACKET_FULL) {
    enter(ledger_full, open_variables());

    found_regions = found_regions + 1;

    trace("f", 0, 0);

    if (model_found == 0) {
      // the first world found, with the open variables true
      model_found = 1;

      variable = 0;

      while (variable < number_of_variables) {
        if (*(variable_values + variable) == VALUE_FALSE)
          *(model_values + variable) = VALUE_FALSE;
        else
          *(model_values + variable) = VALUE_TRUE;

        variable = variable + 1;
      }
    }
  } else {
    undecided_regions = undecided_regions + 1;

    literal = estimate();

    trace("s", literal, 0);

    suppose_literal(literal);

    count_region();

    unassign_to(split);

    if (is_answered()) {
      // the other half is not looked at
      enter(ledger_open, open_variables() - 1);

      trace("o", 0, 0);
    } else {
      // the other half: the literal is false
      suppose_literal(negation(literal));

      count_region();
    }
  }

  unassign_to(mark);
}

void print_model() {
  uint64_t variable;

  printf("%s: %s is satisfiable with ", selfie_name, formula_name);

  variable = 0;

  while (variable < number_of_variables) {
    if (*(model_values + variable) == VALUE_FALSE)
      printf("-%lu ", variable + 1);
    else
      printf("%lu ", variable + 1);

    variable = variable + 1;
  }

  printf("\n");
}

void print_interval(uint64_t* total) {
  uint64_t* found;
  uint64_t* open;
  uint64_t* top;

  // the count is between the worlds found and the worlds found plus the
  // worlds not looked at

  found = count_of_ledger(ledger_full);
  open  = count_of_ledger(ledger_open);

  printf("%s: count ", selfie_name);
  print_count(found);

  if (count_mantissa(open) > 0) {
    top = count_of_ledger(ledger_full);

    count_add(top, open);

    printf(" to ");
    print_count(top);
  } else
    top = found;

  printf(" of ");
  print_count(total);
  printf(" worlds, entropy ");
  print_entropy(found);

  if (top != found) {
    printf(" to ");
    print_entropy(top);
  }

  printf(" of ");
  print_entropy(total);
  printf(" bits\n");
}

void print_ledger() {
  // every world is disposed of by exactly one rule: a conservation law

  printf("%s: ledger: ", selfie_name);
  print_count(count_of_ledger(ledger_empty));
  printf(" empty, ");
  print_count(count_of_ledger(ledger_full));
  printf(" full, ");
  print_count(count_of_ledger(ledger_propagate));
  printf(" by propagation, ");
  print_count(count_of_ledger(ledger_pure));
  printf(" by pure literals, ");
  print_count(count_of_ledger(ledger_learn));
  printf(" by learned clauses, ");
  print_count(count_of_ledger(ledger_open));
  printf(" open: ");

  if (ledgers_account())
    printf("all ");
  else
    printf("ledger error: not all ");

  print_count(count_of_power(number_of_variables));
  printf(" worlds\n");

  if (ledgers_account() == 0)
    exit(EXITCODE_SYSTEMERROR);
}

void print_measure() {
  printf("%s: %lu regions undecided, %lu brackets, %lu clauses visited, %lu clauses learned with %lu literals\n", selfie_name,
    undecided_regions, brackets_taken, clauses_visited, learned_clauses, learned_literals);
}

void loop() {
  ledger_empty     = new_ledger();
  ledger_full      = new_ledger();
  ledger_propagate = new_ledger();
  ledger_pure      = new_ledger();
  ledger_learn     = new_ledger();
  ledger_open      = new_ledger();

  if (trace_name != (char*) 0) {
    trace_fd = open_write_only(trace_name, S_IRUSR_IWUSR_IRGRP_IROTH);

    if (signed_less_than(trace_fd, 0)) {
      printf("%s: could not create trace file %s\n", selfie_name, trace_name);

      exit(EXITCODE_IOERROR);
    }
  }

  count_region();

  if (found_regions > 0) {
    if (asking_whether)
      print_model();
  } else
    // whether is only left open by a world found
    printf("%s: %s is unsatisfiable\n", selfie_name, formula_name);

  print_interval(count_of_power(number_of_variables));
  print_ledger();
  print_measure();
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------------- BRACKET ----------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t scan_clauses() {
  uint64_t clause;
  uint64_t i;
  uint64_t literal;
  uint64_t value;
  uint64_t satisfied;
  uint64_t open;
  uint64_t all_satisfied;

  // looks at the clauses in order: the first clause without a true or an
  // open literal makes the region empty; if all clauses have a true
  // literal the region is full; if the bracket propagates, the first
  // clause with no true and one open literal is unit

  all_satisfied = 1;

  clause = 0;

  while (clause < number_of_all_clauses) {
    clauses_visited = clauses_visited + 1;

    satisfied = 0;
    open      = 0;

    i = *(clause_starts + clause);

    while (i < *(clause_starts + clause + 1)) {
      literal = *(clause_literals + i);

      value = literal_value(literal);

      if (value == VALUE_TRUE) {
        satisfied = 1;

        i = *(clause_starts + clause + 1);
      } else {
        if (value == VALUE_OPEN) {
          open = open + 1;

          bracket_literal = literal;
        }

        i = i + 1;
      }
    }

    if (satisfied == 0) {
      all_satisfied = 0;

      if (open == 0) {
        bracket_clause = clause;

        return BRACKET_EMPTY;
      } else if (open == 1)
        if (bracket_propagates) {
          bracket_clause = clause;

          return BRACKET_UNIT;
        }
    }

    clause = clause + 1;
  }

  if (all_satisfied)
    return BRACKET_FULL;
  else
    return BRACKET_UNDECIDED;
}

uint64_t find_pure_literal() {
  uint64_t clause;
  uint64_t i;
  uint64_t literal;
  uint64_t satisfied;

  // a literal is pure if it is open and its negation occurs in no clause
  // that is not yet satisfied: making it true loses worlds, but not all,
  // unless there are none; returns 1 and the first pure literal, or 0

  literal = 0;

  while (literal < 2 * number_of_variables) {
    *(literal_occurs + literal) = 0;

    literal = literal + 1;
  }

  clause = 0;

  while (clause < number_of_all_clauses) {
    clauses_visited = clauses_visited + 1;

    satisfied = 0;

    i = *(clause_starts + clause);

    while (i < *(clause_starts + clause + 1)) {
      if (literal_value(*(clause_literals + i)) == VALUE_TRUE) {
        satisfied = 1;

        i = *(clause_starts + clause + 1);
      } else
        i = i + 1;
    }

    if (satisfied == 0) {
      i = *(clause_starts + clause);

      while (i < *(clause_starts + clause + 1)) {
        literal = *(clause_literals + i);

        if (literal_value(literal) == VALUE_OPEN)
          *(literal_occurs + literal) = 1;

        i = i + 1;
      }
    }

    clause = clause + 1;
  }

  literal = 0;

  while (literal < 2 * number_of_variables) {
    if (*(literal_occurs + literal)) {
      if (literal_is_negative(literal)) {
        if (*(literal_occurs + literal - 1) == 0) {
          bracket_literal = literal;

          return 1;
        }
      } else if (*(literal_occurs + literal + 1) == 0) {
        bracket_literal = literal;

        return 1;
      }
    }

    literal = literal + 1;
  }

  return 0;
}

uint64_t bracket() {
  uint64_t outcome;

  // the bracket of the region the trail describes; propagation and pure
  // literals make the region smaller, and the ledger and the trace say by
  // how much and why, until the region is empty, full, or left undecided

  brackets_taken = brackets_taken + 1;

  while (1) {
    outcome = scan_clauses();

    if (outcome == BRACKET_UNIT) {
      // the half in which the literal is false is empty
      if (bracket_clause < number_of_clauses)
        enter(ledger_propagate, open_variables() - 1);
      else
        // by a clause that was learned
        enter(ledger_learn, open_variables() - 1);

      trace("u", bracket_literal, bracket_clause);

      imply_literal(bracket_literal, bracket_clause);
    } else if (outcome == BRACKET_UNDECIDED) {
      if (bracket_pure == 0)
        return outcome;
      else if (asking_whether == 0)
        // pure literals are only right about zero
        return outcome;
      else if (find_pure_literal()) {
        // the half in which the literal is false is not looked at
        enter(ledger_pure, open_variables() - 1);

        trace("p", bracket_literal, 0);

        suppose_literal(bracket_literal);
      } else
        return outcome;
    } else
      return outcome;
  }
}

void learn(uint64_t conflict) {
  uint64_t level;
  uint64_t clause;
  uint64_t pivot;
  uint64_t i;
  uint64_t literal;
  uint64_t variable;
  uint64_t pending;
  uint64_t seen;
  uint64_t size;
  uint64_t t;
  uint64_t resolved;

  // the region is empty by the conflict clause, all of whose literals are
  // false. A literal that is false because a clause implied its negation
  // can be replaced by the other literals of that clause, which are false
  // as well: the result follows from the two clauses, by resolution, and
  // also makes the region empty. Replacing the literals of the highest
  // level, last implied first, until one is left, the first unique
  // implication point, gives a clause that makes more regions empty than
  // this one: all in which its literals are false, whatever was assumed
  // since. The clause is remembered; the count is not changed by it.

  level = 0;

  i = *(clause_starts + conflict);

  while (i < *(clause_starts + conflict + 1)) {
    variable = literal_variable(*(clause_literals + i));

    if (*(variable_levels + variable) > level)
      level = *(variable_levels + variable);

    i = i + 1;
  }

  if (level == 0)
    // nothing was assumed: the formula has no worlds, and nothing to learn
    return;

  pending  = 0; // literals of the highest level still to be replaced
  seen     = 0;
  size     = 1; // the first literal is the implication point
  resolved = 0;

  clause = conflict;
  pivot  = number_of_variables; // no variable

  t = trail_size;

  while (1) {
    i = *(clause_starts + clause);

    while (i < *(clause_starts + clause + 1)) {
      literal  = *(clause_literals + i);
      variable = literal_variable(literal);

      if (variable != pivot)
        if (*(variable_seen + variable) == 0)
          if (*(variable_levels + variable) > 0) {
            // literals implied before anything was assumed are false in all worlds
            *(variable_seen + variable) = 1;

            *(seen_stack + seen) = variable;

            seen = seen + 1;

            if (*(variable_levels + variable) == level)
              pending = pending + 1;
            else {
              *(learned + size) = literal;

              size = size + 1;
            }
          }

      i = i + 1;
    }

    // the literal of the highest level that was made true last

    t = t - 1;

    literal  = *(trail + t);
    variable = literal_variable(literal);

    while (*(variable_seen + variable) * (*(variable_levels + variable) == level) == 0) {
      t = t - 1;

      literal  = *(trail + t);
      variable = literal_variable(literal);
    }

    pending = pending - 1;

    if (pending == 0) {
      // the implication point: its negation is the first literal learned
      *learned = negation(literal);

      i = 0;

      while (i < seen) {
        *(variable_seen + *(seen_stack + i)) = 0;

        i = i + 1;
      }

      if (resolved == 0)
        // the conflict clause itself: nothing new
        return;

      add_clause(learned, size);

      learned_clauses  = learned_clauses + 1;
      learned_literals = learned_literals + size;

      if (trace_name != (char*) 0) {
        // l for a clause learned, its literals, and 0
        dprintf(trace_fd, "l ");

        i = 0;

        while (i < size) {
          print_literal(trace_fd, *(learned + i));

          dprintf(trace_fd, " ");

          i = i + 1;
        }

        dprintf(trace_fd, "0\n");
      }

      return;
    }

    // replace it by the other literals of the clause that implied it

    clause = *(variable_reasons + variable) - 1;
    pivot  = variable;

    resolved = resolved + 1;
  }
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// --------------------------- ESTIMATE ----------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t estimate() {
  uint64_t variable;

  // the weakest estimate: the first open variable, true first, which is
  // the order in which babysat goes through the assignments

  variable = 0;

  while (variable < number_of_variables) {
    if (*(variable_values + variable) == VALUE_OPEN)
      return 2 * variable;

    variable = variable + 1;
  }

  // not reached: an undecided region has an open variable
  return 0;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t set_switch(char* name, uint64_t value) {
  // a switch is a rule of the bracket or of the estimate, on or off

  if (string_compare(name, "propagate"))
    bracket_propagates = value;
  else if (string_compare(name, "pure"))
    bracket_pure = value;
  else if (string_compare(name, "learn"))
    bracket_learns = value;
  else
    return 0;

  return 1;
}

uint64_t entr_formula() {
  uint64_t referring;

  // -cnf formula { -first | -count | -reference | -O0 | -O switch | -no switch | -trace file }

  if (number_of_remaining_arguments() == 0)
    return EXITCODE_BADARGUMENTS;

  load_formula(get_argument());

  referring = 0;

  while (number_of_remaining_arguments() > 0) {
    get_argument();

    if (string_compare(argument, "-first"))
      asking_whether = 1;
    else if (string_compare(argument, "-count"))
      asking_whether = 0;
    else if (string_compare(argument, "-reference"))
      referring = 1;
    else if (string_compare(argument, "-O0")) {
      bracket_propagates = 0;
      bracket_pure       = 0;
      bracket_learns     = 0;
    } else if (string_compare(argument, "-O")) {
      if (number_of_remaining_arguments() == 0)
        return EXITCODE_BADARGUMENTS;

      if (set_switch(get_argument(), 1) == 0)
        return EXITCODE_BADARGUMENTS;
    } else if (string_compare(argument, "-no")) {
      if (number_of_remaining_arguments() == 0)
        return EXITCODE_BADARGUMENTS;

      if (set_switch(get_argument(), 0) == 0)
        return EXITCODE_BADARGUMENTS;
    } else if (string_compare(argument, "-trace")) {
      if (number_of_remaining_arguments() == 0)
        return EXITCODE_BADARGUMENTS;

      trace_name = get_argument();
    } else
      return EXITCODE_BADARGUMENTS;
  }

  printf("%s: ********************************************************************************\n", selfie_name);

  if (referring)
    formula_reference();
  else
    loop();

  printf("%s: ################################################################################\n", selfie_name);

  return EXITCODE_NOERROR;
}

uint64_t entr() {
  char* symbol;
  uint64_t index;
  uint64_t i;

  if (number_of_remaining_arguments() == 0)
    return EXITCODE_BADARGUMENTS;

  model_name = get_argument();

  if (string_compare(model_name, "-cnf"))
    // a formula instead of a model
    return entr_formula();

  while (number_of_remaining_arguments() > 0) {
    get_argument();

    if (string_compare(argument, "-l")) {
      if (number_of_remaining_arguments() == 0)
        return EXITCODE_BADARGUMENTS;

      binary_file = get_argument();
    } else if (string_compare(argument, "-i")) {
      if (number_of_remaining_arguments() == 0)
        return EXITCODE_BADARGUMENTS;

      input_file = get_argument();
    } else if (string_compare(argument, "-k")) {
      if (number_of_remaining_arguments() == 0)
        return EXITCODE_BADARGUMENTS;

      max_steps = atoi(get_argument());
    } else if (string_compare(argument, "-over")) {
      if (number_of_remaining_arguments() < 3)
        return EXITCODE_BADARGUMENTS;

      symbol = get_argument();
      index  = atoi(get_argument());

      declare_over(symbol, index, atoi(get_argument()));
    } else if (string_compare(argument, "-fix")) {
      if (number_of_remaining_arguments() < 3)
        return EXITCODE_BADARGUMENTS;

      symbol = get_argument();
      index  = atoi(get_argument());

      declare_fixed(symbol, index, atoi(get_argument()));
    } else if (string_compare(argument, "-zero")) {
      if (number_of_remaining_arguments() == 0)
        return EXITCODE_BADARGUMENTS;

      declare_zero(get_argument());
    } else if (string_compare(argument, "-v"))
      printing_worlds = 1;
    else
      return EXITCODE_BADARGUMENTS;
  }

  parse_model();

  current_step = 0;
  next_step    = 0;

  init_states();

  // the input buffer is a state as any other: the world says what it holds
  SID_INPUT_BUFFER = UNUSED;

  if (binary_file != (char*) 0)
    load_binary(binary_file);

  if (input_file != (char*) 0)
    load_input(input_file);

  collect_lines();

  check_declarations();

  take_snapshot();

  printf("%s: counting over %lu bits:", selfie_name, bits_over);

  i = 0;

  while (i < number_of_overs) {
    printf(" %lu of %s[%lu]", *(over_bits + i), (char*) *(over_symbols + i), *(over_indices + i));

    i = i + 1;
  }

  printf("\n");

  printf("%s: ********************************************************************************\n", selfie_name);

  reference();

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

  exit_code = entr();

  if (exit_code == EXITCODE_BADARGUMENTS)
    // selfie prints the usage of models after this
    printf("%s: for a formula: -cnf formula { -first | -count | -reference | -O0 | -O switch | -no switch | -trace file }\n", selfie_name);

  return exit_selfie(exit_code, " model.btor2 [ -l binary ] [ -i file ] [ -k steps ] { -over state index bits | -fix state index value | -zero state } [ -v ]");
}
