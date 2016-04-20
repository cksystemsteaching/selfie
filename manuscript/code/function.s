0x0(~1)-0x178(~1): initialization and library code removed
-------------------------------------------------------------------------------
0x17C(~4)-0x18C(~4): prologue of f unchanged from p
-------------------------------------------------------------------------------
0x190(~4): 0x8FC80008: lw $t0,8($fp)          // the while statement in f:
0x194(~4): 0x24090000: addiu $t1,$zero,0      // just like before, except that
0x198(~4): 0x0128402A: slt $t0,$t1,$t0        // now the value of x is on the
0x19C(~4): 0x10080007: beq $zero,$t0,7[0x1BC] // stack and referenced by the
0x1A0(~4): 0x00000000: nop                    // frame pointer $fp!
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x1A4(~5): 0x8FC80008: lw $t0,8($fp)              // again, the value of x is
0x1A8(~5): 0x24090001: addiu $t1,$zero,1          // on the stack! this means
0x1AC(~5): 0x01094023: subu $t0,$t0,$t1           // that the x in f is not the
0x1B0(~5): 0xAFC80008: sw $t0,8($fp)              // x in main; they refer to
0x1B4(~7): 0x1000FFF6: beq $zero,$zero,-10[0x190] // two different variables
0x1B8(~7): 0x00000000: nop                        // with their own values.
-------------------------------------------------------------------------------
0x1BC(~7): 0x8FC80008: lw $t0,8($fp)      // the return statement in f:
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x1C0(~7): 0x00081021: addu $v0,$zero,$t0 // the key difference to the return
0x1C4(~7): 0x08000073: j 0x73[0x1CC]      // statement in main is that the
0x1C8(~7): 0x00000000: nop                // value of x is on the stack.
-------------------------------------------------------------------------------
0x1CC(~10)-0x1E4(~10): epilogue of f unchanged from p
-------------------------------------------------------------------------------
0x1E8(~11)-0x1F8(~11): unchanged prologue of main
-------------------------------------------------------------------------------
0x1FC(~11)-0x200(~11): unchanged code for x = 0
-------------------------------------------------------------------------------
0x204(~13)-0x210(~13): unchanged code for x = x + 1
-------------------------------------------------------------------------------
0x214(~15)-0x264(~18): unchanged code for the if statement
-------------------------------------------------------------------------------
0x268(~20): 0x8F88FFFC: lw $t0,-4($gp)     // the return statement in main:
0x26C(~20): 0x27BDFFFC: addiu $sp,$sp,-4   // load the value of x from memory
0x270(~20): 0xAFA80000: sw $t0,0($sp)      // and push it onto the stack as
0x274(~20): 0x0C00005F: jal 0x5F[0x17C]    // argument for the procedure f;
0x278(~20): 0x00000000: nop                // after nop, jump to 0x17C where f
0x27C(~20): 0x24480000: addiu $t0,$v0,0    // is located; load result of f into
0x280(~20): 0x24020000: addiu $v0,$zero,0  // register $t0 and reset $v0; and,
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x284(~20): 0x00081021: addu $v0,$zero,$t0 // just like before, with the only
0x288(~20): 0x080000A4: j 0xA4[0x290]      // difference that the epilogue is
0x28C(~20): 0x00000000: nop                // now at 0x290 rather than 0x274.
-------------------------------------------------------------------------------
0x290(~21)-0x2A8(~21): unchanged epilogue of main