/*
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Copyright (c) 2019 Western Digital Corporation or its affiliates.
 *
 * Authors:
 *   Anup Patel <anup.patel@wdc.com>
 */

OUTPUT_ARCH(riscv)
ENTRY(_start)

SECTIONS
{
  . = $SBI_START + $PAYLOAD_OFFSET;

  PROVIDE(_payload_start = .);

  . = ALIGN(0x1000); /* Need this to create proper sections */

  /* Beginning of the code section */

  .text :
  {
    PROVIDE(_text_start = .);
    *(.entry)
    *(.text)
    . = ALIGN(8);
    PROVIDE(_text_end = .);
  }

  . = ALIGN(0x1000); /* Ensure next section is page aligned */

  /* End of the code sections */

  /* Beginning of the read-only data sections */

  . = ALIGN(0x1000); /* Ensure next section is page aligned */

  .rodata :
  {
    PROVIDE(_rodata_start = .);
    *(.rodata .rodata.*)
    . = ALIGN(8);
    PROVIDE(_rodata_end = .);
  }

  /* End of the read-only data sections */


  /* Beginning of the read-write data sections */

  . = ALIGN(0x1000); /* Ensure next section is page aligned */

  PROVIDE(_data_start = .);
  .data :
  {
    *(.data)
    *(.data.*)
    *(.readmostly.data)
    *(*.data)
    . = ALIGN(8);
  }

  /* We want the small data sections together, so single-instruction offsets
     can access them all, and initialized data all before uninitialized, so
     we can shorten the on-disk segment size.
   */
  .sdata          :
  {
    __global_pointer$ = . + 0x800;
    __SDATA_BEGIN__ = . + 0x800;
    *(.srodata.cst16) *(.srodata.cst8) *(.srodata.cst4) *(.srodata.cst2) *(.srodata .srodata.*)
    *(.sdata .sdata.* .gnu.linkonce.s.*)
  }
  PROVIDE(_data_end = .);

  . = .;
  PROVIDE(_bss_start = .);
  .sbss           :
  {
    *(.dynsbss)
    *(.sbss .sbss.* .gnu.linkonce.sb.*)
    *(.scommon)
  }

  . = ALIGN(0x1000); /* Ensure next section is page aligned */

  .bss :
  {
    *(.bss)
    *(.bss.*)
    . = ALIGN(8);
  }
  PROVIDE(_bss_end = .);

  /* End of the read-write data sections */

  . = ALIGN(0x1000); /* Need this to create proper sections */

  PROVIDE(_payload_end = .);
}
