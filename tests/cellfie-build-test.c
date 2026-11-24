/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

cellfie-build-test is a C* program that constructs four cells on the
grid it runs on, by storing their parts at the addresses that the
parts of cells have on cellfie, see cellfie.md: a mirror, a router,
a tagged memory cell, and a tagged instruction cell, in a window at
column 300 and row 1500. Compiled by selfie and translated by riscr
it runs on cellfie only: make construct compiles it into a layout
with that window, runs it event-driven and on the hybrid simulator,
and compares what the two find in the window.
*/

uint64_t* part_of_cell(uint64_t part, uint64_t x, uint64_t y) {
  // 2^61 plus part times 2^56 plus row times 2^28 plus column
  return (uint64_t*) (2305843009213693952 + part * 72057594037927936 + (1500 + y) * 268435456 + 300 + x);
}

uint64_t main() {
  uint64_t* part;

  // a backslash mirror: kind 1, mirror 1 in bit 5

  part = part_of_cell(0, 0, 0);

  *part = 33;

  // a router on bit 5 of the address, with a slash: kind 2, bit 5 and field 1 in bit 6

  part = part_of_cell(0, 3, 0);

  *part = 2;

  part = part_of_cell(1, 3, 0);

  *part = 69;

  // a memory cell with the word 42, tagged with the address 0x11000: kind 3, tagged in bit 6

  part = part_of_cell(0, 5, 2);

  *part = 67;

  part = part_of_cell(1, 5, 2);

  *part = 42;

  part = part_of_cell(2, 5, 2);

  *part = 69632;

  // an instruction cell oriented east with a slash and addi zero,zero,0,
  // tagged with the address 0x10000: kind 4, tagged

  part = part_of_cell(0, 63, 63);

  *part = 68;

  part = part_of_cell(1, 63, 63);

  *part = 19;

  part = part_of_cell(2, 63, 63);

  *part = 65536;

  // the memory cell again: what is there is 42

  part = part_of_cell(1, 5, 2);

  return *part;
}
