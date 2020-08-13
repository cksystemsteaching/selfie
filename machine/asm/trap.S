#include "asm_offsets.h"

.extern temp_saved_regs

.text
  .global trap_handler_wrapper

.p2align 12
trap_handler_wrapper:
switch_to_kernel_pt:
  // at the moment sscratch stores what should be in
  // satp when we want to use the kernel's page table
  csrrw t6, sscratch, t6
  csrw satp, t6
  // flush TLB
  sfence.vma zero, zero

load_temp_saved_regs_address:
  // t6 can be used here since its value is still
  // saved in sscratch
  la t6, temp_saved_regs

save_regs:
  sd ra,  REGISTERS_OFFSET_RA(t6)
  sd sp,  REGISTERS_OFFSET_SP(t6)
  sd gp,  REGISTERS_OFFSET_GP(t6)
  sd tp,  REGISTERS_OFFSET_TP(t6)
  sd t0,  REGISTERS_OFFSET_T0(t6)
  sd t1,  REGISTERS_OFFSET_T1(t6)
  sd t2,  REGISTERS_OFFSET_T2(t6)
  sd s0,  REGISTERS_OFFSET_S0(t6)
  sd s1,  REGISTERS_OFFSET_S1(t6)
  sd a0,  REGISTERS_OFFSET_A0(t6)
  sd a1,  REGISTERS_OFFSET_A1(t6)
  sd a2,  REGISTERS_OFFSET_A2(t6)
  sd a3,  REGISTERS_OFFSET_A3(t6)
  sd a4,  REGISTERS_OFFSET_A4(t6)
  sd a5,  REGISTERS_OFFSET_A5(t6)
  sd a6,  REGISTERS_OFFSET_A6(t6)
  sd a7,  REGISTERS_OFFSET_A7(t6)
  sd s2,  REGISTERS_OFFSET_S2(t6)
  sd s3,  REGISTERS_OFFSET_S3(t6)
  sd s4,  REGISTERS_OFFSET_S4(t6)
  sd s5,  REGISTERS_OFFSET_S5(t6)
  sd s6,  REGISTERS_OFFSET_S6(t6)
  sd s7,  REGISTERS_OFFSET_S7(t6)
  sd s8,  REGISTERS_OFFSET_S8(t6)
  sd s9,  REGISTERS_OFFSET_S9(t6)
  sd s10, REGISTERS_OFFSET_S10(t6)
  sd s11, REGISTERS_OFFSET_S11(t6)
  sd t3,  REGISTERS_OFFSET_T3(t6)
  sd t4,  REGISTERS_OFFSET_T4(t6)
  sd t5,  REGISTERS_OFFSET_T5(t6)

  // save u-mode pc
  csrr t0, sepc
  sd t0, REGISTERS_OFFSET_PC(t6)

  // retrieve t6's content and save it
  add t0, zero, t6
  csrr t6, sscratch
  sd t6, REGISTERS_OFFSET_T6(t0)

call_trap_handler:
  call trap_handler
  // sscratch now stores the user process's satp value

restore_regs:
  la t6, temp_saved_regs

  // restore u-mode pc
  ld t0, REGISTERS_OFFSET_PC(t6)
  csrw sepc, t0

  ld ra,  REGISTERS_OFFSET_RA(t6)
  ld sp,  REGISTERS_OFFSET_SP(t6)
  ld gp,  REGISTERS_OFFSET_GP(t6)
  ld tp,  REGISTERS_OFFSET_TP(t6)
  ld t0,  REGISTERS_OFFSET_T0(t6)
  ld t1,  REGISTERS_OFFSET_T1(t6)
  ld t2,  REGISTERS_OFFSET_T2(t6)
  ld s0,  REGISTERS_OFFSET_S0(t6)
  ld s1,  REGISTERS_OFFSET_S1(t6)
  ld a0,  REGISTERS_OFFSET_A0(t6)
  ld a1,  REGISTERS_OFFSET_A1(t6)
  ld a2,  REGISTERS_OFFSET_A2(t6)
  ld a3,  REGISTERS_OFFSET_A3(t6)
  ld a4,  REGISTERS_OFFSET_A4(t6)
  ld a5,  REGISTERS_OFFSET_A5(t6)
  ld a6,  REGISTERS_OFFSET_A6(t6)
  ld a7,  REGISTERS_OFFSET_A7(t6)
  ld s2,  REGISTERS_OFFSET_S2(t6)
  ld s3,  REGISTERS_OFFSET_S3(t6)
  ld s4,  REGISTERS_OFFSET_S4(t6)
  ld s5,  REGISTERS_OFFSET_S5(t6)
  ld s6,  REGISTERS_OFFSET_S6(t6)
  ld s7,  REGISTERS_OFFSET_S7(t6)
  ld s8,  REGISTERS_OFFSET_S8(t6)
  ld s9,  REGISTERS_OFFSET_S9(t6)
  ld s10, REGISTERS_OFFSET_S10(t6)
  ld s11, REGISTERS_OFFSET_S11(t6)
  ld t3,  REGISTERS_OFFSET_T3(t6)
  ld t4,  REGISTERS_OFFSET_T4(t6)
  ld t5,  REGISTERS_OFFSET_T5(t6)
  ld t6,  REGISTERS_OFFSET_T6(t6)

switch_to_user_pt:
  // perform some trickery to swap the values of
  // sscratch and satp without losing t6's value
  csrrw t6, sscratch, t6
  csrrw t6, satp, t6
  csrrw t6, sscratch, t6
  // now we are in the user process's vaddr space
  // and sscratch contains the kernel's satp value

  // flush TLB
  sfence.vma zero, zero

return_to_umode:
  sret
