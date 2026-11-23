/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

cellfie-test writes the program that is laid out by hand on the grid
of tests/cellfie-test.rle as RISC-R binary, for milestone M7 of
projects/reversible.md: riscr runs the binary, rotor models it, and
bitr checks that cellfie's cell rule on the layout does, instruction
by instruction, what rotor's model of the binary does. The layout
and this program are written independently, the check is what ties
them. The program has a loop with a paired branch, three exchanges
with two words of the data segment, and a procedure call, see
riscr.md for the instruction set and cellfie.md for the grid.
cellfie-test is built like a tool with selfie.h as library.

Usage: cellfie-test binary
*/

// -----------------------------------------------------------------
// ---------------------------- PROGRAM ----------------------------
// -----------------------------------------------------------------

void emit_program() {
  uint64_t head;
  uint64_t bottom;
  uint64_t call;
  uint64_t procedure;
  uint64_t epilogue;

  // the data segment is at 0x11000: the words at 0x11000 and 0x11008

  store_data(0, 7);
  store_data(WORDSIZE, 0);

  data_size = 2 * WORDSIZE;

  emit_addi(REG_S4, REG_ZR, 1);            // 0x10000: one
  emit_addi(REG_T0, REG_ZR, 3);            // 0x10004: n = 3
  emit_lui(REG_S1, 17);                    // 0x10008: s1 = 0x11000, the data segment
  emit_addi(REG_A7, REG_ZR, SYSCALL_EXIT); // 0x1000C: exit

  head = code_size;

  emit_beq(REG_T2, REG_S4, 0);             // 0x10010: loop head, come-from of the branch at 0x10028

  emit_sltu(REG_T2, REG_ZR, REG_T1);       // 0x10014: uncompute the flag: it is 0 < i on both ways in
  emit_load(REG_A2, REG_S1, 0);            // 0x10018: exchange a2 with the word at 0x11000
  emit_add(REG_A0, REG_A2, REG_ZR);        // 0x1001C: a0 += a2
  emit_addi(REG_T1, REG_ZR, 1);            // 0x10020: i += 1
  emit_sltu(REG_T2, REG_T1, REG_T0);       // 0x10024: flag: i < n

  bottom = code_size;

  fixup_BFormat(head);                     // the come-from points at the branch

  emit_beq(REG_T2, REG_S4, head - bottom); // 0x10028: back to the loop head

  emit_load(REG_A0, REG_S1, WORDSIZE);     // 0x1002C: the word at 0x11008 becomes 7 + 0 + 7, a0 becomes 0

  call = code_size;

  emit_jal(REG_RA, 0);                     // 0x10030: call the procedure
  emit_jal(REG_RA, 0);                     // 0x10034: come-from of the return

  emit_ecall();                            // 0x10038: exit(a1), with a1 == 42

  emit_nop();                              // 0x1003C: never reached

  procedure = code_size;

  emit_jalr(REG_RA, REG_RA, 0);            // 0x10040: come-from of calls
  emit_load(REG_A3, REG_S1, WORDSIZE);     // 0x10044: a3 becomes 14, the word at 0x11008 becomes 0
  emit_add(REG_A1, REG_A3, REG_A3);        // 0x10048: a1 += 28
  emit_add(REG_A1, REG_A3, REG_ZR);        // 0x1004C: a1 += 14

  epilogue = code_size;

  emit_jalr(REG_RA, REG_RA, 0);            // 0x10050: return

  fixup_JFormat(call, procedure);
  fixup_JFormat(call + INSTRUCTIONSIZE, epilogue);

  // code segment must be word-aligned for loading binaries on mipster
  while (code_size % WORDSIZE != 0)
    emit_nop();

  data_start = round_up(code_start + code_size, PAGESIZE);
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
    printf("%s binary\n", selfie_name);

    return EXITCODE_BADARGUMENTS;
  }

  // start a new RISC-R binary

  reset_binary();

  code_binary = zmalloc(MAX_CODE_SIZE);
  data_binary = zmalloc(MAX_DATA_SIZE);

  reset_binary_counters();

  code_start = PK_CODE_START;
  code_size  = 0;
  data_size  = 0;

  emit_program();

  e_flags = EF_RISCR;

  selfie_output(get_argument());

  return EXITCODE_NOERROR;
}
