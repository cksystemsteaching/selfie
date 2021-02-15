/*
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Copyright (c) 2019 Western Digital Corporation or its affiliates.
 *
 * Authors:
 *   Anup Patel <anup.patel@wdc.com>
 */

#include "config.h"

.text

  .section .entry, "ax", %progbits
  .p2align 2
  .global _start
_start:
  /* Set up the Global Pointer */
  .option push
  .option norelax

  la gp, __SDATA_BEGIN__

  .option pop

  /* Zero-out BSS */
  la a4, _bss_start
  la a5, _bss_end
_bss_zero:
  sd  zero, (a4)
  add a4, a4, __SIZEOF_POINTER__
  blt a4, a5, _bss_zero

_start_warm:
  /* Disable and clear all interrupts */
  csrw sie, zero
  csrw sip, zero

  /* Setup exception vectors */
  la a3, hang_machine
  csrw stvec, a3

  /* Setup stack */
  jal initial_stack_start
  mv sp, a0

  /* Jump to C main */
  call bootstrap

  /* We don't expect to reach here hence just hang */
  j hang_machine

  .section .entry, "ax", %progbits
  .p2align 2
  .global hang_machine
hang_machine:
  wfi
  j hang_machine

  .global initial_stack_start
initial_stack_start:
  la t0, _payload_end
  li a0, NUM_STACK_PAGES
  slli a0, a0, 12

  add a0, a0, t0
  ret
