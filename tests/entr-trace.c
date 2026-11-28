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
clauses. A clause that the trace says was learned must follow from the
clauses before it: with all its literals false, making true what clauses
imply must end in a clause that is violated. The count is then the sum
over the full regions, and exact unless the trace has regions that were
not looked at. After a restart the run begins again and so does the count;
the learned clauses stay, since they follow whatever the run.

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

uint64_t propagate_to_conflict();
void     check_learned();
void     replay_learned();

void replay();

// ------------------------ GLOBAL VARIABLES -----------------------

char* replay_name = (char*) 0;

char*    replay_text = (char*) 0; // trace file in memory
uint64_t replay_size = 0;         // in bytes
uint64_t replay_pos  = 0;         // current character
uint64_t replay_line = 1;         // current line number

uint64_t* replayed_worlds = (uint64_t*) 0; // worlds in the full regions of the trace

uint64_t* saved_trail   = (uint64_t*) 0; // the region, while a learned clause is checked
uint64_t* learned_check = (uint64_t*) 0; // the learned clause being checked

uint64_t replayed_clauses  = 0; // learned clauses checked
uint64_t replayed_restarts = 0; // restarts

uint64_t replay_restarting = 0; // the trace begins again

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
  else if (clause > number_of_all_clauses)
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

  // the clauses of the formula: the learned ones follow from them
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

uint64_t propagate_to_conflict() {
  uint64_t clause;
  uint64_t i;
  uint64_t literal;
  uint64_t value;
  uint64_t satisfied;
  uint64_t open;
  uint64_t unit;
  uint64_t changed;

  // makes true what clauses imply until a clause is violated, and returns
  // 1, or until no clause implies anything more, and returns 0

  changed = 1;

  while (changed) {
    changed = 0;

    clause = 0;

    while (clause < number_of_all_clauses) {
      satisfied = 0;
      open      = 0;
      unit      = 0;

      i = *(clause_starts + clause);

      while (i < *(clause_starts + clause + 1)) {
        literal = *(clause_literals + i);

        value = literal_value(literal);

        if (value == VALUE_TRUE)
          satisfied = 1;
        else if (value == VALUE_OPEN) {
          open = open + 1;

          unit = literal;
        }

        i = i + 1;
      }

      if (satisfied == 0) {
        if (open == 0)
          return 1;
        else if (open == 1) {
          assign_literal(unit);

          changed = 1;
        }
      }

      clause = clause + 1;
    }
  }

  return 0;
}

void check_learned() {
  uint64_t size;
  uint64_t saved;
  uint64_t i;
  uint64_t c;
  uint64_t literal;
  uint64_t tautology;

  // a learned clause, its literals and 0: it follows from the clauses so
  // far, whatever the region, and is a clause as the others from here on

  size = 0;

  skip_replay_blanks();

  c = replay_character();

  while (c != '0') {
    if (size > number_of_variables)
      replay_error("learned clause is too long");

    *(learned_check + size) = scan_replay_literal();

    size = size + 1;

    skip_replay_blanks();

    c = replay_character();
  }

  // the 0
  replay_pos = replay_pos + 1;

  // the region is put aside

  saved = trail_size;

  i = 0;

  while (i < saved) {
    *(saved_trail + i) = *(trail + i);

    i = i + 1;
  }

  unassign_to(0);

  tautology = 0;

  i = 0;

  while (i < size) {
    literal = *(learned_check + i);

    if (literal_value(literal) == VALUE_OPEN)
      assign_literal(negation(literal));
    else if (literal_value(literal) == VALUE_TRUE)
      // the clause has a literal and its negation
      tautology = 1;

    i = i + 1;
  }

  if (tautology == 0)
    if (propagate_to_conflict() == 0)
      replay_error("learned clause does not follow");

  unassign_to(0);

  i = 0;

  while (i < saved) {
    assign_literal(*(saved_trail + i));

    i = i + 1;
  }

  add_clause(learned_check, size);

  replayed_clauses = replayed_clauses + 1;
}

void replay_learned() {
  // the clauses learned before the next region

  skip_replay_blanks();

  while (replay_character() == 'l') {
    replay_pos = replay_pos + 1;

    check_learned();

    skip_replay_blanks();
  }
}

void replay() {
  uint64_t event;
  uint64_t literal;
  uint64_t mark;

  // replays the events of one region and of all regions it is split into

  replay_learned();

  event = replay_character();

  replay_pos = replay_pos + 1;

  mark = trail_size;

  if (event == 'r')
    // a restart: the regions that are open are given up
    replay_restarting = 1;
  else if (event == 'e')
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

    if (replay_restarting == 0) {
      assign_literal(negation(literal));

      replay();
    }
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

  saved_trail   = smalloc(number_of_variables * sizeof(uint64_t));
  learned_check = smalloc((number_of_variables + 1) * sizeof(uint64_t));

  replay();

  // the clauses learned from the last region
  replay_learned();

  if (replay_character() == 'r') {
    // a restart after the last region
    replay_pos = replay_pos + 1;

    replay_restarting = 1;
  }

  while (replay_restarting) {
    // the run begins again, with the clauses learned so far

    replay_restarting = 0;

    replayed_restarts = replayed_restarts + 1;

    unassign_to(0);

    replayed_worlds = new_count(0);

    replay();

    replay_learned();

    if (replay_character() == 'r') {
      replay_pos = replay_pos + 1;

      replay_restarting = 1;
    }
  }

  if (replay_pos < replay_size)
    replay_error("end of trace expected");

  printf("%s: %s replays to count ", selfie_name, replay_name);
  print_count(replayed_worlds);
  printf(" of ");
  print_count(count_of_power(number_of_variables));
  printf(" worlds, with %lu learned clauses that follow, after %lu restarts\n", replayed_clauses, replayed_restarts);

  return EXITCODE_NOERROR;
}
