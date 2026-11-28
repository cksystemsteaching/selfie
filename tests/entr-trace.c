/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

The checker of entr's traces. A trace is a run of entr's loop on a
formula as a file, see trace() in tools/entr.c. The checker replays it
and trusts nothing but the formula: a region that the trace says is empty
must violate the clause the trace names, a literal that the trace says a
clause makes true must be the one open literal of that clause with no true
literal, and a region that the trace says is full must satisfy all
clauses. The count is then the sum over the full regions, and exact
unless the trace has regions that were not looked at.

The checker is built on entr.h, which is tools/entr.c with its main
renamed, and uses its formula and its counts, not its loop or its bracket.
*/

// -----------------------------------------------------------------
// ---------------------------- CHECKER ----------------------------
// -----------------------------------------------------------------

uint64_t replay_character();
void     skip_replay_blanks();
uint64_t scan_replay_number();
uint64_t scan_replay_literal();
uint64_t scan_replay_clause();
void     replay_error(char* message);

void check_empty(uint64_t clause);
void check_unit(uint64_t literal, uint64_t clause);
void check_full();

void replay();

// ------------------------ GLOBAL VARIABLES -----------------------

char* replay_name = (char*) 0;

char*    replay_text = (char*) 0; // trace file in memory
uint64_t replay_size = 0;         // in bytes
uint64_t replay_pos  = 0;         // current character
uint64_t replay_line = 1;         // current line number

uint64_t* replayed_worlds = (uint64_t*) 0; // worlds in the full regions of the trace

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ---------------------------- CHECKER ----------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

uint64_t replay_character() {
  if (replay_pos < replay_size)
    return load_character(replay_text, replay_pos);
  else
    // the end of the file
    return 0;
}

void skip_replay_blanks() {
  uint64_t c;

  // blanks and ends of lines: 32 and 10

  c = replay_character();

  while (1) {
    if (c == 10)
      replay_line = replay_line + 1;
    else if (c != 32)
      return;

    replay_pos = replay_pos + 1;

    c = replay_character();
  }
}

uint64_t scan_replay_number() {
  uint64_t c;
  uint64_t n;

  c = replay_character();

  if (c < '0')
    replay_error("number expected");
  else if (c > '9')
    replay_error("number expected");

  n = 0;

  while (c >= '0') {
    if (c > '9')
      return n;

    n = n * 10 + c - '0';

    replay_pos = replay_pos + 1;

    c = replay_character();
  }

  return n;
}

uint64_t scan_replay_literal() {
  uint64_t negative;
  uint64_t variable;

  skip_replay_blanks();

  negative = 0;

  if (replay_character() == '-') {
    negative = 1;

    replay_pos = replay_pos + 1;
  }

  variable = scan_replay_number();

  if (variable == 0)
    replay_error("no variable");
  else if (variable > number_of_variables)
    replay_error("no variable");

  return 2 * (variable - 1) + negative;
}

uint64_t scan_replay_clause() {
  uint64_t clause;

  skip_replay_blanks();

  clause = scan_replay_number();

  if (clause == 0)
    replay_error("no clause");
  else if (clause > number_of_clauses)
    replay_error("no clause");

  return clause - 1;
}

void replay_error(char* message) {
  printf("%s: %s in line %lu of %s\n", selfie_name, message, replay_line, replay_name);

  exit(EXITCODE_SCANNERERROR);
}

void check_empty(uint64_t clause) {
  uint64_t i;

  // the region violates the clause: all its literals are false

  i = *(clause_starts + clause);

  while (i < *(clause_starts + clause + 1)) {
    if (literal_value(*(clause_literals + i)) != VALUE_FALSE)
      replay_error("region is not empty by the clause");

    i = i + 1;
  }
}

void check_unit(uint64_t literal, uint64_t clause) {
  uint64_t i;
  uint64_t found;

  // the clause makes the literal true: the literal is open and in the
  // clause, and all other literals of the clause are false

  found = 0;

  i = *(clause_starts + clause);

  while (i < *(clause_starts + clause + 1)) {
    if (*(clause_literals + i) == literal) {
      if (literal_value(literal) != VALUE_OPEN)
        replay_error("literal is not open");

      found = 1;
    } else if (literal_value(*(clause_literals + i)) != VALUE_FALSE)
      replay_error("clause does not make the literal true");

    i = i + 1;
  }

  if (found == 0)
    replay_error("literal is not in the clause");
}

void check_full() {
  uint64_t clause;
  uint64_t i;
  uint64_t satisfied;

  // the region satisfies all clauses: each has a true literal

  clause = 0;

  while (clause < number_of_clauses) {
    satisfied = 0;

    i = *(clause_starts + clause);

    while (i < *(clause_starts + clause + 1)) {
      if (literal_value(*(clause_literals + i)) == VALUE_TRUE)
        satisfied = 1;

      i = i + 1;
    }

    if (satisfied == 0)
      replay_error("region is not full");

    clause = clause + 1;
  }
}

void replay() {
  uint64_t event;
  uint64_t literal;
  uint64_t mark;

  // replays the events of one region and of all regions it is split into

  skip_replay_blanks();

  event = replay_character();

  replay_pos = replay_pos + 1;

  mark = trail_size;

  if (event == 'e')
    check_empty(scan_replay_clause());
  else if (event == 'f') {
    check_full();

    count_add(replayed_worlds, count_of_power(open_variables()));
  } else if (event == 'o')
    // a region not looked at: the count is a lower bound
    *(replayed_worlds + 2) = 0;
  else if (event == 'u') {
    literal = scan_replay_literal();

    check_unit(literal, scan_replay_clause());

    assign_literal(literal);

    replay();
  } else if (event == 'p') {
    literal = scan_replay_literal();

    if (literal_value(literal) != VALUE_OPEN)
      replay_error("literal is not open");

    // the half in which the literal is false is not looked at
    *(replayed_worlds + 2) = 0;

    assign_literal(literal);

    replay();
  } else if (event == 's') {
    literal = scan_replay_literal();

    if (literal_value(literal) != VALUE_OPEN)
      replay_error("literal is not open");

    assign_literal(literal);

    replay();

    unassign_to(mark);

    if (literal_is_negative(literal))
      assign_literal(literal - 1);
    else
      assign_literal(literal + 1);

    replay();
  } else
    replay_error("event expected");

  unassign_to(mark);
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

int main(int argc, char** argv) {
  init_selfie((uint64_t) argc, (uint64_t*) argv);

  init_library();

  if (number_of_remaining_arguments() != 2)
    return exit_selfie(EXITCODE_BADARGUMENTS, " formula trace");

  load_formula(get_argument());

  replay_name = get_argument();

  replay_text = (char*) read_whole_file(replay_name);
  replay_size = model_size;
  replay_pos  = 0;
  replay_line = 1;

  replayed_worlds = new_count(0);

  replay();

  skip_replay_blanks();

  if (replay_pos < replay_size)
    replay_error("end of trace expected");

  printf("%s: %s replays to count ", selfie_name, replay_name);
  print_count(replayed_worlds);
  printf(" of ");
  print_count(count_of_power(number_of_variables));
  printf(" worlds\n");

  return EXITCODE_NOERROR;
}
