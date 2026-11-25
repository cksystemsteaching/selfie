/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

cellfie-build-test is a C* program that constructs a program on the
grid it runs on and starts it, by storing the parts of cells at the
addresses that they have on cellfie, see cellfie.md. It reads where
the grid is free from the word of the last cell of the grid, and
writes there that 64 columns and rows more are taken. It constructs
a mirror, a router, and a tagged memory cell, and three tagged
instruction cells in a row: a program that exits with exit code 42.
It stores the pc of that program in the pocket of its token, and
loads from the cell west of the three as no part of it: the token
lands there, with the pc, and runs the program. Compiled by selfie
and translated by riscr it runs on cellfie only: make construct
compiles it into a layout with room, runs it event-driven, forward
and backward, and on the hybrid simulator, and compares the two.
*/

uint64_t corner = 0; // 2^28 times the first free row plus the first free column of the grid

uint64_t* part_of_cell(uint64_t part, uint64_t x, uint64_t y) {
  // 2^61 plus part times 2^56 plus row times 2^28 plus column
  return (uint64_t*) (2305843009213693952 + part * 72057594037927936 + corner + y * 268435456 + x);
}

void construct_cell(uint64_t x, uint64_t y, uint64_t kind, uint64_t word, uint64_t tag) {
  uint64_t* part;

  part = part_of_cell(0, x, y);

  *part = kind;

  if (word != 0) {
    part = part_of_cell(1, x, y);

    *part = word;
  }

  if (tag != 0) {
    part = part_of_cell(2, x, y);

    *part = tag;
  }
}

uint64_t main() {
  uint64_t* part;

  // the word of the cell in the last column and row of the grid:
  // part 1 of the cell in row and column 2^28 - 1

  part = (uint64_t*) 2449958197289549823;

  corner = *part;

  if (corner == 0)
    return 1;

  *part = corner + 64 * 268435456 + 64;

  // a backslash mirror: kind 1, mirror 1 in bit 5

  construct_cell(0, 0, 33, 0, 0);

  // a router on bit 5 of the address, with a slash: kind 2, bit 5 and field 1 in bit 6

  construct_cell(3, 0, 2, 69, 0);

  // a memory cell with the word 42, tagged with the address 0x11000: kind 3, tagged in bit 6

  construct_cell(5, 2, 67, 42, 69632);

  // three instruction cells oriented east, tagged with the addresses
  // from 0x10000 on: addi a7,zero,93 and addi a1,zero,42 with a slash,
  // kind 4, and ecall with a backslash in bit 5

  construct_cell(9, 8, 68, 97519763, 65536);
  construct_cell(10, 8, 68, 44041619, 65540);
  construct_cell(11, 8, 100, 115, 65544);

  // the memory cell again: what is there is 42

  part = part_of_cell(1, 5, 2);

  if (*part != 42)
    return 1;

  // the pc of the token in the pocket, at 2^60: where the program begins

  part = (uint64_t*) 1152921504606846976;

  *part = 65536;

  // the token lands at the cell west of the program and does not return

  part = part_of_cell(3, 8, 8);

  return *part;
}
