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

This file is the beginning, milestone E1: the arithmetic of counts and
the reference, which is the specification of every count that entr will
ever report. The reference enumerates the worlds and runs the concrete
evaluator of tools/btor2.h on each. It is exponential in the bits counted
over, on purpose.

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
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

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

  // n * 2^f becomes n * 2^(f - e) * 2^e if that fits

  while (f > e) {
    if (n >= two_to_the_power_of(SIZEOFUINT64INBITS - 1)) {
      // it does not: the smaller summand is dropped, the sum is a lower bound
      *count       = n;
      *(count + 1) = f;
      *(count + 2) = 0;

      return;
    }

    n = n * 2;
    f = f - 1;
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

  m = count_mantissa(count);

  p = 0;

  while (two_to_the_power_of(p + 1) <= m) {
    if (p + 1 == SIZEOFUINT64INBITS - 1) {
      // two_to_the_power_of(64) would be 0
      p = p + 1;

      m = 0;
    } else
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
  if (count_is_exact(count) == 0)
    printf("at least ");

  if (count_exponent(count) == 0)
    printf("%lu", count_mantissa(count));
  else if (count_exponent(count) + log_two(count_mantissa(count)) < SIZEOFUINT64INBITS - 1)
    printf("%lu", count_mantissa(count) * two_to_the_power_of(count_exponent(count)));
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
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t entr() {
  char* symbol;
  uint64_t index;
  uint64_t i;

  if (number_of_remaining_arguments() == 0)
    return EXITCODE_BADARGUMENTS;

  model_name = get_argument();

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

  return exit_selfie(exit_code, " model.btor2 [ -l binary ] [ -i file ] [ -k steps ] { -over state index bits | -fix state index value | -zero state } [ -v ]");
}
