/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

riscr-test is the check for milestone M1 of projects/reversible.md.
It emits hand-written RISC-R code using selfie's machine code
library, writes the code as RISC-R binary, loads it again, runs it
forward on mipster until it exits, runs the same number of
instructions backward, and checks that the initial machine state
(pc, registers, memory, tapes) is restored bit for bit. Programs
that violate the RISC-R rules must throw an irreversible instruction
exception instead. See riscr.md for the instruction set.

Usage: riscr-test scratch-binary < input (first byte must be 'R')
*/

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t MAX_SNAPSHOT_PAGES = 64;

char* message = (char*) 0; // written and read back by the io test, see main

// ------------------------ GLOBAL VARIABLES -----------------------

char* scratch_name = (char*) 0; // scratch file for RISC-R binaries

uint64_t* program_code = (uint64_t*) 0; // code of the tested program
uint64_t* program_data = (uint64_t*) 0; // data of the tested program

uint64_t number_of_tests        = 0;
uint64_t number_of_failed_tests = 0;

// snapshot of machine state

uint64_t  snapshot_pc        = 0;
uint64_t* snapshot_registers = (uint64_t*) 0;

uint64_t  snapshot_number_of_pages = 0;
uint64_t* snapshot_pages           = (uint64_t*) 0; // page numbers
uint64_t* snapshot_memory          = (uint64_t*) 0; // page contents

uint64_t  snapshot_input_tape_head  = 0;
uint64_t  snapshot_output_tape_head = 0;
uint64_t* snapshot_input_tape       = (uint64_t*) 0;
uint64_t* snapshot_output_tape      = (uint64_t*) 0;

// -----------------------------------------------------------------
// ------------------------- CODE EMISSION -------------------------
// -----------------------------------------------------------------

void begin_program() {
  // start a new RISC-R binary
  reset_binary();

  code_binary = program_code;
  data_binary = program_data;

  zero_memory(code_binary, MAX_CODE_SIZE);
  zero_memory(data_binary, MAX_DATA_SIZE);

  reset_binary_counters();

  code_start = PK_CODE_START;
  code_size  = 0;
  data_size  = 0;
}

void emit_exit_code(uint64_t exit_code) {
  // exit code must fit into 12-bit immediate
  emit_addi(REG_A0, REG_ZR, exit_code);
  emit_addi(REG_A7, REG_ZR, SYSCALL_EXIT);
  emit_ecall();
}

void end_program() {
  uint64_t i;

  // code segment must be word-aligned for loading binaries on mipster
  while (code_size % WORDSIZE != 0)
    emit_nop();

  // binaries need a data segment: emit message as data
  i = 0;

  while (i < 8) {
    store_data(i, load_word((uint64_t*) message, i, 1));

    i = i + WORDSIZE;
  }

  data_size  = 8;
  data_start = round_up(code_start + code_size, PAGESIZE);
}

// -----------------------------------------------------------------
// ------------------------- TEST PROGRAMS -------------------------
// -----------------------------------------------------------------

uint64_t emit_arithmetic() {
  // every arithmetic instruction once, see riscr.md for their semantics
  emit_lui(REG_T0, 1);                  // t0 += 4096
  emit_addi(REG_T1, REG_T0, 5);         // t1 += t0 + 5 == 4101
  emit_add(REG_T2, REG_T0, REG_T1);     // t2 += t0 + t1 == 8197
  emit_sub(REG_T3, REG_T1, REG_T0);     // t3 += t1 - t0 == 5
  emit_mul(REG_T4, REG_T3, REG_T3);     // t4 ^= t3 * t3 == 25
  emit_divu(REG_T5, REG_T4, REG_T3);    // t5 ^= t4 / t3 == 5
  emit_remu(REG_T6, REG_T4, REG_T1);    // t6 ^= t4 % t1 == 25
  emit_sltu(REG_A1, REG_T3, REG_T4);    // a1 ^= t3 < t4 == 1
  emit_add(REG_A0, REG_T5, REG_A1);     // a0 += t5 + a1 == 6
  emit_sub(REG_A0, REG_T3, REG_A1);     // a0 += t3 - a1 == 10
  emit_mul(REG_A0, REG_A1, REG_T3);     // a0 ^= a1 * t3 == 15
  emit_addi(REG_A7, REG_ZR, SYSCALL_EXIT);
  emit_ecall();

  return 15;
}

uint64_t emit_memory() {
  // ld exchanges a register with a memory word
  emit_addi(REG_SP, REG_ZR, -16);       // sp += -16
  emit_addi(REG_T0, REG_ZR, 42);        // t0 += 42
  emit_load(REG_T0, REG_SP, 0);         // t0 <-> mem[sp]: t0 == 0, mem[sp] == 42
  emit_addi(REG_T1, REG_ZR, 7);         // t1 += 7
  emit_load(REG_T1, REG_SP, 8);         // t1 <-> mem[sp + 8]: t1 == 0, mem[sp + 8] == 7
  emit_load(REG_T0, REG_SP, 8);         // t0 == 7, mem[sp + 8] == 0
  emit_load(REG_T1, REG_SP, 0);         // t1 == 42, mem[sp] == 0
  emit_add(REG_A0, REG_T0, REG_T1);     // a0 == 49
  emit_addi(REG_A7, REG_ZR, SYSCALL_EXIT);
  emit_ecall();

  return 49;
}

uint64_t emit_loop() {
  uint64_t head;
  uint64_t bottom;

  // sum of 1 to 5 with paired beq and all temporaries uncomputed:
  // t0 == i, t1 == c (continue flag), t2 scratch, t3 == 1, t4 == n
  emit_addi(REG_T3, REG_ZR, 1);
  emit_addi(REG_T4, REG_ZR, 5);

  head = code_size;

  emit_beq(REG_T1, REG_T3, 0);          // come-from of the back-edge, fixed up below

  emit_sltu(REG_T2, REG_ZR, REG_T0);    // t2 ^= 0 < i, 1 iff coming from the back-edge
  emit_sub(REG_T1, REG_ZR, REG_T2);     // c -= t2, c == 0
  emit_sltu(REG_T2, REG_ZR, REG_T0);    // t2 ^= 0 < i, t2 == 0
  emit_addi(REG_T0, REG_ZR, 1);         // i += 1
  emit_add(REG_A0, REG_T0, REG_ZR);     // a0 += i
  emit_sltu(REG_T1, REG_T0, REG_T4);    // c ^= i < n

  bottom = code_size;

  fixup_BFormat(head);                  // come-from points to the back-edge

  emit_beq(REG_T1, REG_T3, head - bottom); // back-edge, taken iff c == 1

  emit_addi(REG_A7, REG_ZR, SYSCALL_EXIT);
  emit_ecall();

  return 15;
}

uint64_t emit_call() {
  uint64_t call1;
  uint64_t call2;
  uint64_t procedure;
  uint64_t epilogue;

  // calling a procedure twice: jal links into zeroed ra, the come-from jalr
  // at the procedure uncomputes ra backward, the jalr returning to the
  // come-from jal after the call site uncomputes ra forward
  emit_addi(REG_A0, REG_ZR, 5);

  call1 = code_size;

  emit_jal(REG_RA, 0);                  // call, fixed up below
  emit_jal(REG_RA, 0);                  // return come-from, fixed up below

  call2 = code_size;

  emit_jal(REG_RA, 0);                  // call, fixed up below
  emit_jal(REG_RA, 0);                  // return come-from, fixed up below

  emit_addi(REG_A7, REG_ZR, SYSCALL_EXIT);
  emit_ecall();

  procedure = code_size;

  emit_jalr(REG_RA, REG_RA, 0);         // call come-from
  emit_addi(REG_A0, REG_ZR, 1);         // a0 += 1

  epilogue = code_size;

  emit_jalr(REG_RA, REG_RA, 0);         // return

  fixup_JFormat(call1, procedure);
  fixup_JFormat(call1 + INSTRUCTIONSIZE, epilogue);
  fixup_JFormat(call2, procedure);
  fixup_JFormat(call2 + INSTRUCTIONSIZE, epilogue);

  return 7;
}

uint64_t emit_io() {
  // write message from data segment to stdout, then read 8 bytes from
  // stdin onto the stack and exit with the first byte
  emit_lui(REG_A1, 17);                 // a1 += 0x11000 == data_start
  emit_addi(REG_A0, REG_ZR, 1);         // stdout
  emit_addi(REG_A2, REG_ZR, 7);         // 7 bytes
  emit_addi(REG_A7, REG_ZR, SYSCALL_WRITE);
  emit_ecall();                         // appends message to output tape
  emit_lui(REG_A1, -17);                // a1 -= 0x11000 == 0
  emit_addi(REG_SP, REG_ZR, -16);       // sp += -16
  emit_add(REG_A1, REG_SP, REG_ZR);     // a1 += sp
  emit_addi(REG_A0, REG_ZR, -1);        // stdin
  emit_addi(REG_A2, REG_ZR, 1);         // 8 bytes
  emit_addi(REG_A7, REG_ZR, SYSCALL_READ - SYSCALL_WRITE);
  emit_ecall();                         // exchanges mem[sp] with input tape
  emit_load(REG_A0, REG_SP, 0);         // a0 <-> mem[sp]: a0 == input word
  emit_addi(REG_T0, REG_ZR, 256);
  emit_remu(REG_T1, REG_A0, REG_T0);    // t1 ^= a0 % 256 == first byte
  emit_load(REG_A0, REG_SP, 0);         // a0 == 0, mem[sp] == input word
  emit_add(REG_A0, REG_T1, REG_ZR);     // a0 += t1
  emit_addi(REG_A7, REG_ZR, SYSCALL_EXIT - SYSCALL_READ);
  emit_ecall();

  return 'R';
}

void emit_aliasing() {
  // rd must be distinct from rs1 and rs2
  emit_addi(REG_T0, REG_ZR, 1);
  emit_add(REG_T0, REG_T0, REG_T1);
  emit_exit_code(0);
}

void emit_unpaired_branch() {
  // branch target must hold a come-from
  emit_beq(REG_ZR, REG_ZR, 2 * INSTRUCTIONSIZE);
  emit_nop();
  emit_exit_code(0);
}

void emit_sd() {
  // sd is not a RISC-R instruction
  emit_store(REG_SP, 0, REG_ZR);
  emit_exit_code(0);
}

void emit_nonzero_link() {
  uint64_t call;

  // ra must be zero when jal links into it
  emit_addi(REG_RA, REG_ZR, 1);

  call = code_size;

  emit_jal(REG_RA, 0);
  emit_jal(REG_RA, 0);
  emit_exit_code(0);

  fixup_JFormat(call, code_size);

  emit_jalr(REG_RA, REG_RA, 0);
  emit_jalr(REG_RA, REG_RA, 0);

  fixup_JFormat(call + INSTRUCTIONSIZE, code_size - INSTRUCTIONSIZE);
}

// -----------------------------------------------------------------
// ---------------------------- SNAPSHOT ---------------------------
// -----------------------------------------------------------------

void snapshot_page(uint64_t page) {
  uint64_t vaddr;
  uint64_t offset;

  if (snapshot_number_of_pages >= MAX_SNAPSHOT_PAGES) {
    printf("%s: too many mapped pages for snapshot\n", selfie_name);

    exit(EXITCODE_SYSTEMERROR);
  }

  *(snapshot_pages + snapshot_number_of_pages) = page;

  vaddr  = virtual_address_of_page(page);
  offset = snapshot_number_of_pages * PAGESIZE;

  while (offset < (snapshot_number_of_pages + 1) * PAGESIZE) {
    store_word(snapshot_memory, offset, 1, load_virtual_memory(get_pt(current_context), vaddr));

    vaddr  = vaddr + WORDSIZE;
    offset = offset + WORDSIZE;
  }

  snapshot_number_of_pages = snapshot_number_of_pages + 1;
}

void take_snapshot() {
  uint64_t r;
  uint64_t page;

  // assert: pages are mapped contiguously from code start up and from the top of memory down

  snapshot_pc = get_pc(current_context);

  r = 0;

  while (r < NUMBEROFREGISTERS) {
    *(snapshot_registers + r) = *(get_regs(current_context) + r);

    r = r + 1;
  }

  snapshot_number_of_pages = 0;

  page = page_of_virtual_address(code_start);

  while (is_page_mapped(get_pt(current_context), page)) {
    snapshot_page(page);

    page = page + 1;
  }

  page = NUMBEROFPAGES - 1;

  while (is_page_mapped(get_pt(current_context), page)) {
    snapshot_page(page);

    page = page - 1;
  }

  snapshot_input_tape_head  = input_tape_head;
  snapshot_output_tape_head = output_tape_head;

  zero_memory(snapshot_input_tape, MAX_TAPE_SIZE);
  zero_memory(snapshot_output_tape, MAX_TAPE_SIZE);

  r = 0;

  while (r < input_tape_head * WORDSIZE) {
    store_word(snapshot_input_tape, r, 1, load_word(input_tape, r, 1));

    r = r + WORDSIZE;
  }

  r = 0;

  while (r < output_tape_head * WORDSIZE) {
    store_word(snapshot_output_tape, r, 1, load_word(output_tape, r, 1));

    r = r + WORDSIZE;
  }
}

uint64_t find_snapshot_page(uint64_t page) {
  uint64_t i;

  i = 0;

  while (i < snapshot_number_of_pages) {
    if (*(snapshot_pages + i) == page)
      return i;

    i = i + 1;
  }

  return MAX_SNAPSHOT_PAGES;
}

uint64_t compare_page(uint64_t page) {
  uint64_t i;
  uint64_t vaddr;
  uint64_t offset;
  uint64_t expected;

  // pages mapped after the snapshot must be zero

  i = find_snapshot_page(page);

  vaddr  = virtual_address_of_page(page);
  offset = 0;

  while (offset < PAGESIZE) {
    if (i < MAX_SNAPSHOT_PAGES)
      expected = load_word(snapshot_memory, i * PAGESIZE + offset, 1);
    else
      expected = 0;

    if (load_virtual_memory(get_pt(current_context), vaddr) != expected) {
      printf("%s: memory at 0x%lX is 0x%lX, expected 0x%lX\n", selfie_name,
        vaddr, load_virtual_memory(get_pt(current_context), vaddr), expected);

      return 0;
    }

    vaddr  = vaddr + WORDSIZE;
    offset = offset + WORDSIZE;
  }

  return 1;
}

uint64_t compare_snapshot() {
  uint64_t r;
  uint64_t page;

  // returns 1 if the machine state is bit for bit the snapshot

  if (get_pc(current_context) != snapshot_pc) {
    printf("%s: pc is 0x%lX, expected 0x%lX\n", selfie_name, get_pc(current_context), snapshot_pc);

    return 0;
  }

  r = 0;

  while (r < NUMBEROFREGISTERS) {
    if (*(get_regs(current_context) + r) != *(snapshot_registers + r)) {
      printf("%s: register %s is 0x%lX, expected 0x%lX\n", selfie_name,
        get_register_name(r), *(get_regs(current_context) + r), *(snapshot_registers + r));

      return 0;
    }

    r = r + 1;
  }

  page = page_of_virtual_address(code_start);

  while (is_page_mapped(get_pt(current_context), page)) {
    if (not(compare_page(page)))
      return 0;

    page = page + 1;
  }

  page = NUMBEROFPAGES - 1;

  while (is_page_mapped(get_pt(current_context), page)) {
    if (not(compare_page(page)))
      return 0;

    page = page - 1;
  }

  if (input_tape_head != snapshot_input_tape_head) {
    printf("%s: input tape head is %lu, expected %lu\n", selfie_name, input_tape_head, snapshot_input_tape_head);

    return 0;
  }

  if (output_tape_head != snapshot_output_tape_head) {
    printf("%s: output tape head is %lu, expected %lu\n", selfie_name, output_tape_head, snapshot_output_tape_head);

    return 0;
  }

  r = 0;

  while (r < input_tape_head * WORDSIZE) {
    if (load_word(input_tape, r, 1) != load_word(snapshot_input_tape, r, 1)) {
      printf("%s: input tape differs at word %lu\n", selfie_name, r / WORDSIZE);

      return 0;
    }

    r = r + WORDSIZE;
  }

  r = 0;

  while (r < output_tape_head * WORDSIZE) {
    if (load_word(output_tape, r, 1) != load_word(snapshot_output_tape, r, 1)) {
      printf("%s: output tape differs at word %lu\n", selfie_name, r / WORDSIZE);

      return 0;
    }

    r = r + WORDSIZE;
  }

  return 1;
}

// -----------------------------------------------------------------
// ---------------------------- TESTING ----------------------------
// -----------------------------------------------------------------

void boot() {
  end_program();

  // write RISC-R binary and load it again, checking the ELF flag
  selfie_output(scratch_name);
  selfie_load(scratch_name);

  reset_interpreter();
  reset_profiler();
  reset_microkernel();

  init_memory(1);

  reset_tapes();

  current_context = create_context(MY_CONTEXT, 0);

  // assert: number_of_remaining_arguments() > 0

  boot_loader(current_context);

  run = 1;
}

void pass(char* name, char* reason) {
  printf("%s: %s: passed: %s\n", selfie_name, name, reason);
}

void fail(char* name, char* reason) {
  printf("%s: %s: FAILED: %s\n", selfie_name, name, reason);

  number_of_failed_tests = number_of_failed_tests + 1;
}

void test_reversibility(char* name, uint64_t expected_exit_code) {
  uint64_t exit_code;
  uint64_t steps;

  number_of_tests = number_of_tests + 1;

  boot();

  take_snapshot();

  exit_code = mipster(current_context);

  if (exit_code != expected_exit_code) {
    printf("%s: exit code is %ld, expected %ld\n", selfie_name,
      sign_extend(exit_code, SYSCALL_BITWIDTH), sign_extend(expected_exit_code, SYSCALL_BITWIDTH));

    fail(name, "wrong exit code");
  } else {
    // undo all executed instructions but the exit system call
    steps = get_total_number_of_instructions() - 1;

    mipster_backward(current_context, steps);

    printf("%s: %s: %lu instructions executed forward and backward\n", selfie_name, name, steps);

    if (compare_snapshot())
      pass(name, "initial state restored bit for bit");
    else
      fail(name, "initial state not restored");
  }

  run = 0;
}

void test_irreversibility(char* name) {
  uint64_t exit_code;

  number_of_tests = number_of_tests + 1;

  boot();

  exit_code = mipster(current_context);

  if (exit_code != EXITCODE_UNCAUGHTEXCEPTION)
    fail(name, "no exception thrown");
  else if (get_exception(current_context) != EXCEPTION_IRREVERSIBLEINSTRUCTION)
    fail(name, "wrong exception thrown");
  else
    pass(name, "irreversible instruction exception thrown");

  run = 0;
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

int main(int argc, char** argv) {
  init_selfie((uint64_t) argc, (uint64_t*) argv);

  init_library();
  init_system();
  init_target();
  init_kernel();

  init_register();
  init_interpreter();
  init_disassembler();

  if (number_of_remaining_arguments() == 0) {
    printf("%s { scratch binary }\n", selfie_name);

    return EXITCODE_BADARGUMENTS;
  }

  // the scratch binary name remains the argument of the tested programs
  scratch_name = peek_argument(0);

  RISCR = 1;

  message = "RISC-R\n";

  program_code = zmalloc(MAX_CODE_SIZE);
  program_data = zmalloc(MAX_DATA_SIZE);

  snapshot_registers  = zmalloc(NUMBEROFREGISTERS * sizeof(uint64_t));
  snapshot_pages      = zmalloc(MAX_SNAPSHOT_PAGES * sizeof(uint64_t));
  snapshot_memory     = zmalloc(MAX_SNAPSHOT_PAGES * PAGESIZE);
  snapshot_input_tape  = zmalloc(MAX_TAPE_SIZE);
  snapshot_output_tape = zmalloc(MAX_TAPE_SIZE);

  begin_program();
  emit_aliasing();
  test_irreversibility("aliasing");

  begin_program();
  emit_unpaired_branch();
  test_irreversibility("unpaired branch");

  begin_program();
  emit_sd();
  test_irreversibility("store");

  begin_program();
  emit_nonzero_link();
  test_irreversibility("nonzero link");

  begin_program();
  test_reversibility("arithmetic", emit_arithmetic());

  begin_program();
  test_reversibility("memory", emit_memory());

  begin_program();
  test_reversibility("loop", emit_loop());

  begin_program();
  test_reversibility("call", emit_call());

  begin_program();
  test_reversibility("io", emit_io());

  printf("%s: %lu of %lu tests passed\n", selfie_name, number_of_tests - number_of_failed_tests, number_of_tests);

  if (number_of_failed_tests > 0)
    return EXITCODE_SYSTEMERROR;
  else
    return EXITCODE_NOERROR;
}
