0x0(~1)-0xD4(~1): unchanged initialization and unused library code removed
-------------------------------------------------------------------------------
0xD8(~1): 0x8FA40000: lw $a0,0($sp)        // the malloc procedure:
0xDC(~1): 0x27BD0004: addiu $sp,$sp,4      // pop argument from the stack into
0xE0(~1): 0x24020FCD: addiu $v0,$zero,4045 // $a0 as argument for malloc system
0xE4(~1): 0x0000000C: syscall              // call identified by 4045; return
0xE8(~1): 0x03E00008: jr $ra               // after nop to caller with result
0xEC(~1): 0x00000000: nop                  // stored in $v0.
-------------------------------------------------------------------------------
0xF0(~1)-0x198(~1): unused library code removed
-------------------------------------------------------------------------------
0x19C(~4)-0x1B0(~4): unchanged prologue of main
-------------------------------------------------------------------------------
0x1B4(~4): 0x24080008: addiu $t0,$zero,8 // the x = malloc(8) assignment:
0x1B8(~4): 0x27BDFFFC: addiu $sp,$sp,-4  // push 8 onto the stack and invoke
0x1BC(~4): 0xAFA80000: sw $t0,0($sp)     // malloc by jumping, after nop, to
0x1C0(~4): 0x0C000036: jal 0x36[0xD8]    // 0xD8 where the code of malloc is;
0x1C4(~4): 0x00000000: nop               // after returning, store the result
0x1C8(~4): 0x24480000: addiu $t0,$v0,0   // returned in $v0 in x on the stack.
0x1CC(~4): 0x24020000: addiu $v0,$zero,0
0x1D0(~4): 0xAFC8FFFC: sw $t0,-4($fp)
-------------------------------------------------------------------------------
0x1D4(~6): 0x8FC8FFFC: lw $t0,-4($fp)    // the *x = 0 assignment:
0x1D8(~6): 0x24090000: addiu $t1,$zero,0 // load value of x from the stack and
0x1DC(~6): 0xAD090000: sw $t1,0($t0)     // store 0 in memory at address x.
-------------------------------------------------------------------------------
0x1E0(~8): 0x8FC8FFFC: lw $t0,-4($fp)    // the *x = *x + 1 assignment:
0x1E4(~8): 0x8FC9FFFC: lw $t1,-4($fp)    // load value of x from the stack;
0x1E8(~8): 0x8D290000: lw $t1,0($t1)     // load value from memory at address x
0x1EC(~8): 0x240A0001: addiu $t2,$zero,1 // and add 1 to it; finally, store the
0x1F0(~8): 0x012A4821: addu $t1,$t1,$t2  // result in memory at address x.
0x1F4(~8): 0xAD090000: sw $t1,0($t0)
-------------------------------------------------------------------------------
0x1F8(~10): 0x8FC8FFFC: lw $t0,-4($fp)    // the *(x + 1) = 0 assignment:
0x1FC(~10): 0x24090001: addiu $t1,$zero,1 // load value of x from the stack;
0x200(~10): 0x240A0004: addiu $t2,$zero,4 // compute the address for *(x + 1)
0x204(~10): 0x012A0019: multu $t1,$t2     // through pointer arithmetics; since
0x208(~10): 0x00004812: mflo $t1          // x points to int which is a signed
0x20C(~10): 0x00000000: nop               // 32-bit integer (4 bytes) the
0x210(~10): 0x00000000: nop               // address is computed by x + 1 * 4;
0x214(~10): 0x01094021: addu $t0,$t0,$t1  // finally, 0 is stored in memory
0x218(~10): 0x24090000: addiu $t1,$zero,0 // at address x + 1 * 4.
0x21C(~10): 0xAD090000: sw $t1,0($t0)
-------------------------------------------------------------------------------
0x220(~12): 0x8FC8FFFC: lw $t0,-4($fp)    // the x = x + 1 assignment:
0x224(~12): 0x24090001: addiu $t1,$zero,1 // load value of x from the stack
0x228(~12): 0x240A0004: addiu $t2,$zero,4 // and store the address x + 1 * 4
0x22C(~12): 0x012A0019: multu $t1,$t2     // in x on the stack.
0x230(~12): 0x00004812: mflo $t1
0x234(~12): 0x00000000: nop
0x238(~12): 0x00000000: nop
0x23C(~12): 0x01094021: addu $t0,$t0,$t1
0x240(~12): 0xAFC8FFFC: sw $t0,-4($fp)
-------------------------------------------------------------------------------
0x244(~14): 0x8FC8FFFC: lw $t0,-4($fp)     // the return statement:
0x248(~14): 0x8D080000: lw $t0,0($t0)      // load value of x from the stack;
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x24C(~14): 0x00081021: addu $v0,$zero,$t0 // load value from memory at address
0x250(~14): 0x08000096: j 0x96[0x258]      // x and store it in $v0; finally,
0x254(~14): 0x00000000: nop                // after nop, jump to epilogue.
-------------------------------------------------------------------------------
0x258(~15)-0x270(~15): unchanged epilogue of main