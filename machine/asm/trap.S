#include "asm_offsets.h"
#include "asm_context_switch_offsets.h"
#include "config.h"

.text

// trap_handler_wrapper expects the kernel stack to be set up
// like this. The kernel's stack pointer is saved in sscratch.
// :                      :
// +----------------------+
// | trap_handler address | -24
// |      kernel gp       | -16
// |     kernel satp      | -8
// |     [reserved]       |     <- kernel sp
// +----------------------+
  .p2align 12
  .global trap_handler_wrapper
trap_handler_wrapper:
switch_to_kernel_stack:
  // at the moment sscratch stores the kernel's sp
  csrrw sp, sscratch, sp

temp_store_s0:
  sd s0, CONTEXT_SWITCH_STACK_TEMP_REGISTER_BUFFER_OFFSET(sp)

switch_to_kernel_pt:
  ld s0, CONTEXT_SWITCH_STACK_KERNEL_SATP_OFFSET(sp)
  csrw satp, s0
  // flush TLB
  sfence.vma

setup_frame:
  mv s0, sp

allocate_registers_struct_space:
  addi sp, sp, -SIZEOF_REGISTERS_STRUCT

save_regs:
  sd ra,  REGISTERS_OFFSET_RA(sp)
  // sp will be saved later on
  sd gp,  REGISTERS_OFFSET_GP(sp)
  sd tp,  REGISTERS_OFFSET_TP(sp)
  sd t0,  REGISTERS_OFFSET_T0(sp)
  sd t1,  REGISTERS_OFFSET_T1(sp)
  sd t2,  REGISTERS_OFFSET_T2(sp)
  // s0 will be saved later on
  sd s1,  REGISTERS_OFFSET_S1(sp)
  sd a0,  REGISTERS_OFFSET_A0(sp)
  sd a1,  REGISTERS_OFFSET_A1(sp)
  sd a2,  REGISTERS_OFFSET_A2(sp)
  sd a3,  REGISTERS_OFFSET_A3(sp)
  sd a4,  REGISTERS_OFFSET_A4(sp)
  sd a5,  REGISTERS_OFFSET_A5(sp)
  sd a6,  REGISTERS_OFFSET_A6(sp)
  sd a7,  REGISTERS_OFFSET_A7(sp)
  sd s2,  REGISTERS_OFFSET_S2(sp)
  sd s3,  REGISTERS_OFFSET_S3(sp)
  sd s4,  REGISTERS_OFFSET_S4(sp)
  sd s5,  REGISTERS_OFFSET_S5(sp)
  sd s6,  REGISTERS_OFFSET_S6(sp)
  sd s7,  REGISTERS_OFFSET_S7(sp)
  sd s8,  REGISTERS_OFFSET_S8(sp)
  sd s9,  REGISTERS_OFFSET_S9(sp)
  sd s10, REGISTERS_OFFSET_S10(sp)
  sd s11, REGISTERS_OFFSET_S11(sp)
  sd t3,  REGISTERS_OFFSET_T3(sp)
  sd t4,  REGISTERS_OFFSET_T4(sp)
  sd t5,  REGISTERS_OFFSET_T5(sp)
  sd t6,  REGISTERS_OFFSET_T6(sp)

  // save s0
  ld t0, CONTEXT_SWITCH_STACK_TEMP_REGISTER_BUFFER_OFFSET(s0)
  sd t0, REGISTERS_OFFSET_S0(sp)

  // save sp
  csrr t0, sscratch
  sd t0, REGISTERS_OFFSET_SP(sp)

  // save u-mode pc
  csrr t0, sepc
  sd t0, REGISTERS_OFFSET_PC(sp)

restore_kernel_gp:
  ld gp, CONTEXT_SWITCH_STACK_KERNEL_GP_OFFSET(s0)

call_trap_handler:
  ld t0, CONTEXT_SWITCH_STACK_TRAP_HANDLER_ADDRESS_OFFSET(s0)
  mv a0, sp
  jalr t0

switch_to_user_pt:
  // trap_handler returns the satp value of the next context in a0
  csrw satp, a0
  sfence.vma

setup_sscratch:
  // sscratch must contain the kernel's old stack pointer
  // (i.e. what is currently the frame pointer)
  csrw sscratch, s0

restore_regs:
  // restore u-mode pc
  ld t0, REGISTERS_OFFSET_PC(sp)
  csrw sepc, t0

  ld ra,  REGISTERS_OFFSET_RA(sp)
  // restore sp later on
  ld gp,  REGISTERS_OFFSET_GP(sp)
  ld tp,  REGISTERS_OFFSET_TP(sp)
  ld t0,  REGISTERS_OFFSET_T0(sp)
  ld t1,  REGISTERS_OFFSET_T1(sp)
  ld t2,  REGISTERS_OFFSET_T2(sp)
  ld s0,  REGISTERS_OFFSET_S0(sp)
  ld s1,  REGISTERS_OFFSET_S1(sp)
  ld a0,  REGISTERS_OFFSET_A0(sp)
  ld a1,  REGISTERS_OFFSET_A1(sp)
  ld a2,  REGISTERS_OFFSET_A2(sp)
  ld a3,  REGISTERS_OFFSET_A3(sp)
  ld a4,  REGISTERS_OFFSET_A4(sp)
  ld a5,  REGISTERS_OFFSET_A5(sp)
  ld a6,  REGISTERS_OFFSET_A6(sp)
  ld a7,  REGISTERS_OFFSET_A7(sp)
  ld s2,  REGISTERS_OFFSET_S2(sp)
  ld s3,  REGISTERS_OFFSET_S3(sp)
  ld s4,  REGISTERS_OFFSET_S4(sp)
  ld s5,  REGISTERS_OFFSET_S5(sp)
  ld s6,  REGISTERS_OFFSET_S6(sp)
  ld s7,  REGISTERS_OFFSET_S7(sp)
  ld s8,  REGISTERS_OFFSET_S8(sp)
  ld s9,  REGISTERS_OFFSET_S9(sp)
  ld s10, REGISTERS_OFFSET_S10(sp)
  ld s11, REGISTERS_OFFSET_S11(sp)
  ld t3,  REGISTERS_OFFSET_T3(sp)
  ld t4,  REGISTERS_OFFSET_T4(sp)
  ld t5,  REGISTERS_OFFSET_T5(sp)
  ld t6,  REGISTERS_OFFSET_T6(sp)

  // restore sp
  ld sp, REGISTERS_OFFSET_SP(sp)

return_to_umode:
  sret

// [[noreturn]] void perform_initial_ctxt_switch(uint64_t satp, struct registers* regs)
// Performs the initial context switch by setting up the stack in a way switch_to_user_pt
// expects it to be
// :                      :
// +----------------------+
// | trap_handler address | -24
// |      kernel gp       | -16
// |     kernel satp      | -8
// |     [reserved]       |     <- s0
// +----------------------+
// |         t6           |
// :          :           :
// :          :           :
// |         ra           |     <- sp
// +----------------------+
// :                      :
  .global perform_initial_ctxt_switch
perform_initial_ctxt_switch:
  // Reserve space for kernel data

  addi s0, sp, -CONTEXT_SWITCH_STACK_SPACE_ALLOCATION
  addi sp, s0, -SIZEOF_REGISTERS_STRUCT

  csrr t0, satp
  la t1, trap_handler

  sd t0, CONTEXT_SWITCH_STACK_KERNEL_SATP_OFFSET(s0)
  sd gp, CONTEXT_SWITCH_STACK_KERNEL_GP_OFFSET(s0)
  sd t1, CONTEXT_SWITCH_STACK_TRAP_HANDLER_ADDRESS_OFFSET(s0)

  // Copy all registers (for now, use references later)
  // t0 is the source address (byte-wise, thus +8 for uint64_t)
  // t1 is the source address' last position (exit condition)
  // t2 is the destination address
  // t3 is the data to copy
  mv t0, a1
  mv t1, a1
  addi t1, t1, SIZEOF_REGISTERS_STRUCT
  mv t2, sp

copy_reg_loop:
  ld t3, (t0)
  sd t3, (t2)

  addi t0, t0, 8
  addi t2, t2, 8
  blt t0, t1, copy_reg_loop

switch_to_upper_half:
  // At first, calculate the offset of switch_to_user_pt relative to the trap handler page,
  // starting at trap_handler_wrapper
  la t0, trap_handler_wrapper
  la t1, switch_to_user_pt
  sub t0, t1, t0

  // Then, calculate the virtual address of the upper half mirror of switch_to_user_pt
  li t1, TRAMPOLINE_VADDR
  add t0, t0, t1

  // Do the jump
  jr t0
