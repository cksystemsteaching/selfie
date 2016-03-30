0x0(~1): 0x24080278: addiu $t0,$zero,632   // the instructions @ 0x0 to 0x44
0x4(~1): 0x251C0000: addiu $gp,$t0,0       // initialize the global pointer
0x8(~1): 0x24080FFF: addiu $t0,$zero,4095  // $gp and the stack pointer $sp,
0xC(~1): 0x24094000: addiu $t1,$zero,16384 // and invoke the main function:
0x10(~1): 0x01090019: multu $t0,$t1        // $gp=632[0x278] which represents
0x14(~1): 0x00004012: mflo $t0             // the program break, that is,
0x18(~1): 0x00000000: nop                  // the first address after code,
0x1C(~1): 0x00000000: nop                  // strings, and global variables;
0x20(~1): 0x25083FFC: addiu $t0,$t0,16380  // $sp=mem[2^26-4] which is where
0x24(~1): 0x8D1D0000: lw $sp,0($t0)        // the loader stores the address
........: nop instructions removed         // of the top of the stack; and,
0x40(~1): 0x0C000067: jal 0x67[0x19C]      // finally, a jump to 0x19C which
0x44(~1): 0x00000000: nop                  // is where the code for main is.
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x48(~1): 0x27BDFFFC: addiu $sp,$sp,-4
0x4C(~1): 0xAFA20000: sw $v0,0($sp)
-------------------------------------------------------------------------------
0x50(~1): 0x8FA40000: lw $a0,0($sp)        // the exit function:
0x54(~1): 0x27BD0004: addiu $sp,$sp,4
0x58(~1): 0x24020FA1: addiu $v0,$zero,4001
0x5C(~1): 0x0000000C: syscall
-------------------------------------------------------------------------------
........: unused library code removed
-------------------------------------------------------------------------------
0x19C(~4): 0x27BDFFFC: addiu $sp,$sp,-4 // the prologue of the main function:
0x1A0(~4): 0xAFBF0000: sw $ra,0($sp)
0x1A4(~4): 0x27BDFFFC: addiu $sp,$sp,-4
0x1A8(~4): 0xAFBE0000: sw $fp,0($sp)
0x1AC(~4): 0x27BE0000: addiu $fp,$sp,0
-------------------------------------------------------------------------------
0x1B0(~4): 0x24080000: addiu $t0,$zero,0 // the x = 0 assignment:
0x1B4(~4): 0xAF88FFFC: sw $t0,-4($gp)
-------------------------------------------------------------------------------
0x1B8(~6): 0x8F88FFFC: lw $t0,-4($gp)    // the x = x + 1 assignment:
0x1BC(~6): 0x24090001: addiu $t1,$zero,1
0x1C0(~6): 0x01094021: addu $t0,$t0,$t1
0x1C4(~6): 0xAF88FFFC: sw $t0,-4($gp)
-------------------------------------------------------------------------------
0x1C8(~8): 0x8F88FFFC: lw $t0,-4($gp)         // the if statement:
0x1CC(~8): 0x24090001: addiu $t1,$zero,1
0x1D0(~8): 0x01094023: subu $t0,$t0,$t1
0x1D4(~8): 0x10080004: beq $zero,$t0,4[0x1E8]
0x1D8(~8): 0x00000000: nop
0x1DC(~8): 0x24080000: addiu $t0,$zero,0
0x1E0(~8): 0x10080002: beq $zero,$t0,2[0x1EC]
0x1E4(~8): 0x00000000: nop
0x1E8(~8): 0x24080001: addiu $t0,$zero,1
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x1EC(~8): 0x10080007: beq $zero,$t0,7[0x20C]
0x1F0(~8): 0x00000000: nop
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x1F4(~9): 0x8F88FFFC: lw $t0,-4($gp)    // the true case of the if statement
0x1F8(~9): 0x24090001: addiu $t1,$zero,1
0x1FC(~9): 0x01094021: addu $t0,$t0,$t1
0x200(~9): 0xAF88FFFC: sw $t0,-4($gp)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x204(~11): 0x10000005: beq $zero,$zero,5[0x21C]
0x208(~11): 0x00000000: nop
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x20C(~11): 0x8F88FFFC: lw $t0,-4($gp)    // the false case of the if statement
0x210(~11): 0x24090001: addiu $t1,$zero,1
0x214(~11): 0x01094023: subu $t0,$t0,$t1
0x218(~11): 0xAF88FFFC: sw $t0,-4($gp)
-------------------------------------------------------------------------------
0x21C(~13): 0x8F88FFFC: lw $t0,-4($gp)         // the while statement:
0x220(~13): 0x24090000: addiu $t1,$zero,0
0x224(~13): 0x0128402A: slt $t0,$t1,$t0
0x228(~13): 0x10080007: beq $zero,$t0,7[0x248]
0x22C(~13): 0x00000000: nop
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x230(~14): 0x8F88FFFC: lw $t0,-4($gp)
0x234(~14): 0x24090001: addiu $t1,$zero,1
0x238(~14): 0x01094023: subu $t0,$t0,$t1
0x23C(~14): 0xAF88FFFC: sw $t0,-4($gp)
0x240(~16): 0x1000FFF6: beq $zero,$zero,-10[0x21C]
0x244(~16): 0x00000000: nop
-------------------------------------------------------------------------------
0x248(~16): 0x8F88FFFC: lw $t0,-4($gp)     // the return statement:
0x24C(~16): 0x00081021: addu $v0,$zero,$t0
0x250(~16): 0x08000096: j 0x96[0x258]
0x254(~16): 0x00000000: nop
-------------------------------------------------------------------------------
0x258(~17): 0x27DD0000: addiu $sp,$fp,0 // the epilogue of the main function:
0x25C(~17): 0x8FBE0000: lw $fp,0($sp)
0x260(~17): 0x27BD0004: addiu $sp,$sp,4
0x264(~17): 0x8FBF0000: lw $ra,0($sp)
0x268(~17): 0x27BD0004: addiu $sp,$sp,4
0x26C(~17): 0x03E00008: jr $ra
0x270(~17): 0x00000000: nop