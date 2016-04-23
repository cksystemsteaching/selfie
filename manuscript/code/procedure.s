0x0(~1): 0x24080294: addiu $t0,$zero,660   // the initialization works just
0x4(~1): 0x251C0000: addiu $gp,$t0,0       // like before except that the
0x8(~1): 0x24080FFF: addiu $t0,$zero,4095  // global pointer $gp is set to
0xC(~1): 0x24094000: addiu $t1,$zero,16384 // 660[0x294] rather than 600[0x258]
0x10(~1): 0x01090019: multu $t0,$t1        // because the code here is longer;
0x14(~1): 0x00004012: mflo $t0             // also, the jump to main is to
0x18(~1): 0x00000000: nop                  // 0x1D8 rather than 0x17C because
0x1C(~1): 0x00000000: nop                  // the code of the procedure p is
0x20(~1): 0x25083FFC: addiu $t0,$t0,16380  // located before the code of main.
0x24(~1): 0x8D1D0000: lw $sp,0($t0)
........: nop instructions removed
0x40(~1): 0x0C000076: jal 0x76[0x1D8]
0x44(~1): 0x00000000: nop
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x48(~1)-0x4C(~1): unchanged exit code handling
-------------------------------------------------------------------------------
0x50(~1)-0x5C(~1): unchanged exit procedure
-------------------------------------------------------------------------------
0x60(~1)-0x178(~1): unused library code removed
-------------------------------------------------------------------------------
0x17C(~4): 0x27BDFFFC: addiu $sp,$sp,-4 // the prologue of the procedure p,
0x180(~4): 0xAFBF0000: sw $ra,0($sp)    // just like the prologue of main.
0x184(~4): 0x27BDFFFC: addiu $sp,$sp,-4
0x188(~4): 0xAFBE0000: sw $fp,0($sp)
0x18C(~4): 0x27BE0000: addiu $fp,$sp,0
-------------------------------------------------------------------------------
0x190(~4): 0x8F88FFFC: lw $t0,-4($gp)         // the while statement in p:
0x194(~4): 0x24090000: addiu $t1,$zero,0      // this is the exact same code
0x198(~4): 0x0128402A: slt $t0,$t1,$t0        // as before except that the
0x19C(~4): 0x10080007: beq $zero,$t0,7[0x1BC] // branch goes to 0x1BC rather
0x1A0(~4): 0x00000000: nop                    // than 0x228.
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x1A4(~5): 0x8F88FFFC: lw $t0,-4($gp)             // the true case of the
0x1A8(~5): 0x24090001: addiu $t1,$zero,1          // while statement in p:
0x1AC(~5): 0x01094023: subu $t0,$t0,$t1           // again, this is the exact
0x1B0(~5): 0xAF88FFFC: sw $t0,-4($gp)             // same code as before except
0x1B4(~6): 0x1000FFF6: beq $zero,$zero,-10[0x190] // that the branch goes to
0x1B8(~6): 0x00000000: nop                        // 0x190 rather than 0x1FC.
-------------------------------------------------------------------------------
0x1BC(~8): 0x27DD0000: addiu $sp,$fp,0 // the epilogue of the procedure p,
0x1C0(~8): 0x8FBE0000: lw $fp,0($sp)   // just like the epilogue of main.
0x1C4(~8): 0x27BD0004: addiu $sp,$sp,4
0x1C8(~8): 0x8FBF0000: lw $ra,0($sp)
0x1CC(~8): 0x27BD0004: addiu $sp,$sp,4
0x1D0(~8): 0x03E00008: jr $ra
0x1D4(~8): 0x00000000: nop
-------------------------------------------------------------------------------
0x1D8(~9)-0x1E8(~9): unchanged prologue of main
-------------------------------------------------------------------------------
0x1EC(~9)-0x1F0(~9): unchanged code for x = 0
-------------------------------------------------------------------------------
0x1F4(~11)-0x200(~11): unchanged code for x = x + 1
-------------------------------------------------------------------------------
0x204(~13)-0x254(~16): unchanged code for the if statement
-------------------------------------------------------------------------------
0x258(~18): 0x0C00005F: jal 0x5F[0x17C]   // the invocation of the procedure p:
0x25C(~18): 0x00000000: nop               // jump to 0x17C which is where the
0x260(~18): 0x24020000: addiu $v0,$zero,0 // code of p is; reset register $v0.
-------------------------------------------------------------------------------
0x264(~20): 0x8F88FFFC: lw $t0,-4($gp)     // the return statement:
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
0x268(~20): 0x00081021: addu $v0,$zero,$t0 // the only difference here is the
0x26C(~20): 0x0800009D: j 0x9D[0x274]      // address of the epilogue is now
0x270(~20): 0x00000000: nop                // 0x274 rather than 0x238.
-------------------------------------------------------------------------------
0x274(~21)-0x28C(~21): unchanged epilogue of main