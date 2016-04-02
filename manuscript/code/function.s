0x0(~1)-0x198(~1): initialization and library code removed
-------------------------------------------------------------------------------
0x19C(~4)-0x1AC(~4): prologue of f unchanged from p
-------------------------------------------------------------------------------
0x1B0(~4): 0x8FC80008: lw $t0,8($fp)          // the while statement in f:
0x1B4(~4): 0x24090000: addiu $t1,$zero,0      // just like before, except that
0x1B8(~4): 0x0128402A: slt $t0,$t1,$t0        // now the value of x is on the
0x1BC(~4): 0x10080007: beq $zero,$t0,7[0x1DC] // stack and referenced by the
0x1C0(~4): 0x00000000: nop                    // frame pointer $fp!
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x1C4(~5): 0x8FC80008: lw $t0,8($fp)              // again, the value of x is
0x1C8(~5): 0x24090001: addiu $t1,$zero,1          // on the stack! this means
0x1CC(~5): 0x01094023: subu $t0,$t0,$t1           // that the x in f is not the
0x1D0(~5): 0xAFC80008: sw $t0,8($fp)              // x in main; they refer to
0x1D4(~7): 0x1000FFF6: beq $zero,$zero,-10[0x1B0] // two different variables
0x1D8(~7): 0x00000000: nop                        // with their own values.
-------------------------------------------------------------------------------
0x1DC(~7): 0x8FC80008: lw $t0,8($fp)      // the return statement in f:
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x1E0(~7): 0x00081021: addu $v0,$zero,$t0 // the key difference to the return
0x1E4(~7): 0x0800007B: j 0x7B[0x1EC]      // statement in main is that the
0x1E8(~7): 0x00000000: nop                // value of x is on the stack.
-------------------------------------------------------------------------------
0x1EC(~10)-0x204(~10): epilogue of f unchanged from p
-------------------------------------------------------------------------------
0x208(~11)-0x218(~11): unchanged prologue of main
-------------------------------------------------------------------------------
0x21C(~11)-0x220(~11): unchanged code for x = 0
-------------------------------------------------------------------------------
0x224(~13)-0x230(~13): unchanged code for x = x + 1
-------------------------------------------------------------------------------
0x234(~15)-0x284(~18): unchanged code for the if statement
-------------------------------------------------------------------------------
0x288(~20): 0x8F88FFFC: lw $t0,-4($gp)     // the return statement in main:
0x28C(~20): 0x27BDFFFC: addiu $sp,$sp,-4   // load the value of x from memory
0x290(~20): 0xAFA80000: sw $t0,0($sp)      // and push it onto the stack as
0x294(~20): 0x0C000067: jal 0x67[0x19C]    // argument for the procedure f;
0x298(~20): 0x00000000: nop                // after nop, jump to 0x19C where f
0x29C(~20): 0x24480000: addiu $t0,$v0,0    // is located; load result of f into
0x2A0(~20): 0x24020000: addiu $v0,$zero,0  // register $t0 and reset $v0; and,
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x2A4(~20): 0x00081021: addu $v0,$zero,$t0 // just like before, with the only
0x2A8(~20): 0x080000AC: j 0xAC[0x2B0]      // difference that the epilogue is
0x2AC(~20): 0x00000000: nop                // now at 0x2B0 rather than 0x294.
-------------------------------------------------------------------------------
0x2B0(~21)-0x2C8(~21): unchanged epilogue of main