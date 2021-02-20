
#include <stdio.h>
#include "context.h"

#define PRINT_SIZE_DEF(prefix, name, stru) printf("#define %s%s %lu\n", #prefix, #name, sizeof(stru))
#define PRINT_OFFSET_DEF(prefix, name, stru, memb) printf("#define %s%s %lu\n", #prefix, #name, offsetof(stru, memb))

int main() {
  PRINT_SIZE_DEF(SIZEOF_, REGISTERS_STRUCT, struct registers);

  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, RA, struct registers, ra);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, SP, struct registers, sp);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, GP, struct registers, gp);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, TP, struct registers, tp);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, T0, struct registers, t0);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, T1, struct registers, t1);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, T2, struct registers, t2);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, S0, struct registers, s0);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, S1, struct registers, s1);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, A0, struct registers, a0);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, A1, struct registers, a1);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, A2, struct registers, a2);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, A3, struct registers, a3);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, A4, struct registers, a4);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, A5, struct registers, a5);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, A6, struct registers, a6);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, A7, struct registers, a7);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, S2, struct registers, s2);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, S3, struct registers, s3);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, S4, struct registers, s4);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, S5, struct registers, s5);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, S6, struct registers, s6);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, S7, struct registers, s7);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, S8, struct registers, s8);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, S9, struct registers, s9);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, S10, struct registers, s10);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, S11, struct registers, s11);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, T3, struct registers, t3);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, T4, struct registers, t4);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, T5, struct registers, t5);
  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, T6, struct registers, t6);

  PRINT_OFFSET_DEF(REGISTERS_OFFSET_, PC, struct registers, pc);
}
