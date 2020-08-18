/*
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Copyright (c) 2019 Western Digital Corporation or its affiliates.
 *
 * Authors:
 *   Anup Patel <anup.patel@wdc.com>
 */

#include <sbi/riscv_encoding.h>
#define __ASM_STR(x)	x

#if __riscv_xlen == 64
#define __REG_SEL(a, b)		__ASM_STR(a)
#define RISCV_PTR		.dword
#elif __riscv_xlen == 32
#define __REG_SEL(a, b)		__ASM_STR(b)
#define RISCV_PTR		.word
#else
#error "Unexpected __riscv_xlen"
#endif

#define REG_L		__REG_SEL(ld, lw)
#define REG_S		__REG_SEL(sd, sw)

#include "config.h"

    .section .entry, "ax", %progbits
    .align 3
    .globl _start
_start:
    /* Set up the Global Pointer */
    .option push
    .option norelax

    la gp, __SDATA_BEGIN__

    .option pop

    /* Pick one hart to run the main boot sequence */
    la	a3, _hart_lottery
    li	a2, 1
    amoadd.w a3, a2, (a3)
    bnez	a3, _start_hang

    /* Save a0 and a1 */
    la	a3, _boot_a0
    REG_S	a0, 0(a3)
    la	a3, _boot_a1
    REG_S	a1, 0(a3)

    /* Zero-out BSS */
    la a4, _bss_start
    la a5, _bss_end
_bss_zero:
    REG_S zero, (a4)
    add a4, a4, __SIZEOF_POINTER__
    blt a4, a5, _bss_zero

_start_warm:
    /* Disable and clear all interrupts */
    csrw	CSR_SIE, zero
    csrw	CSR_SIP, zero

    /* Setup exception vectors */
    la	a3, _start_hang
    csrw	CSR_STVEC, a3

    /* Setup early bump pointer for page allocator */
    /* An increment of one is necessary due to the pre-allocated stack page */
    la a3, _payload_end
    srli a3, a3, 12
    addi a3, a3, NUM_STACK_PAGES
    sd a3, ppn_bump, a4

    /* Setup stack */
    jal initial_stack_start
    add	sp, x0, a0

    /*
     * Setup heap bump pointer at the end of the preliminary stack
     * RISC-V uses full-stack semantics - sp points to the last pushed element
     */
    mv a3, sp
    sw a3, heap_head, a4


    /* Jump to C main */
    call	bootstrap

    /* We don't expect to reach here hence just hang */
    j	_start_hang

    .section .entry, "ax", %progbits
    .align 3
    .globl _start_hang
_start_hang:
    wfi
    j	_start_hang

.globl initial_stack_start
initial_stack_start:
    la	t0, _payload_end
    li	a0, NUM_STACK_PAGES
    slli a0, a0, 12

    add a0, a0, t0
    ret


    .section .entry, "ax", %progbits
    .align	3
_hart_lottery:
    RISCV_PTR	0
