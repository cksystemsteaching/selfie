0x0(~1)-0x178(~1): initialization and library code removed
-------------------------------------------------------------------------------
0x17C(~2)-0x1E4(~8): unchanged code of f
-------------------------------------------------------------------------------
0x1E8(~11): 0x27BDFFFC: addiu $sp,$sp,-4 // the prologue of the main procedure:
0x1EC(~11): 0xAFBF0000: sw $ra,0($sp)    // the difference to the prologues we
0x1F0(~11): 0x27BDFFFC: addiu $sp,$sp,-4 // have seen before is the additional
0x1F4(~11): 0xAFBE0000: sw $fp,0($sp)    // sixth instruction which allocates
0x1F8(~11): 0x27BE0000: addiu $fp,$sp,0  // space on the stack for storing the
0x1FC(~11): 0x27BDFFFC: addiu $sp,$sp,-4 // value of x locally in main.
-------------------------------------------------------------------------------
0x200(~11): 0x24080000: addiu $t0,$zero,0 // the x = 0 assignment:
0x204(~11): 0xAFC8FFFC: sw $t0,-4($fp)    // now x is on the stack!
-------------------------------------------------------------------------------
0x208(~13): 0x8FC8FFFC: lw $t0,-4($fp)    // the x = x + 1 assignment:
0x20C(~13): 0x24090001: addiu $t1,$zero,1 // again, x is now on the stack.
0x210(~13): 0x01094021: addu $t0,$t0,$t1
0x214(~13): 0xAFC8FFFC: sw $t0,-4($fp)
-------------------------------------------------------------------------------
0x218(~15): 0x8FC8FFFC: lw $t0,-4($fp)         // the if statement:
0x21C(~15): 0x24090001: addiu $t1,$zero,1      // and again, no difference
0x220(~15): 0x01094023: subu $t0,$t0,$t1       // except that x is now loaded
0x224(~15): 0x10080004: beq $zero,$t0,4[0x238] // from the stack.
0x228(~15): 0x00000000: nop
0x22C(~15): 0x24080000: addiu $t0,$zero,0
0x230(~15): 0x10080002: beq $zero,$t0,2[0x23C]
0x234(~15): 0x00000000: nop
0x238(~15): 0x24080001: addiu $t0,$zero,1
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x23C(~15)-0x240(~15): unchanged code for selecting case by branching
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x244(~16): 0x8FC8FFFC: lw $t0,-4($fp)    // the true case of the if statement
0x248(~16): 0x24090001: addiu $t1,$zero,1 // now with x on the stack.
0x24C(~16): 0x01094021: addu $t0,$t0,$t1
0x250(~16): 0xAFC8FFFC: sw $t0,-4($fp)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x254(~18)-0x258(~18): unchanged code for avoiding false case by branching
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x25C(~18): 0x8FC8FFFC: lw $t0,-4($fp)    // the false case of the if statement
0x260(~18): 0x24090001: addiu $t1,$zero,1 // now with x on the stack.
0x264(~18): 0x01094023: subu $t0,$t0,$t1
0x268(~18): 0xAFC8FFFC: sw $t0,-4($fp)
-------------------------------------------------------------------------------
0x26C(~20): 0x8FC8FFFC: lw $t0,-4($fp)    // the return statement:
0x270(~20): 0x27BDFFFC: addiu $sp,$sp,-4  // again, the only difference is that
0x274(~20): 0xAFA80000: sw $t0,0($sp)     // x is now loaded from the stack.
0x278(~20): 0x0C00005F: jal 0x5F[0x17C]
0x27C(~20): 0x00000000: nop
0x280(~20): 0x24480000: addiu $t0,$v0,0
0x284(~20): 0x24020000: addiu $v0,$zero,0
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x288(~20)-0x290(~20): unchanged code for jumping to epilogue
-------------------------------------------------------------------------------
0x294(~21)-0x2AC(~21): unchanged epilogue of main