$pc=0x0(~1): 0x24080260: addiu $t0,$zero,608: $t0=0,$zero=0 -> $t0=608
$pc=0x4(~1): 0x251C0000: addiu $gp,$t0,0: $gp=0,$t0=608 -> $gp=608
$pc=0x8(~1): 0x24080FFF: addiu $t0,$zero,4095: $t0=608,$zero=0 -> $t0=4095
$pc=0xC(~1): 0x24094000: addiu $t1,$zero,16384: $t1=0,$zero=0 -> $t1=16384
$pc=0x10(~1): 0x01090019: multu $t0,$t1: $t0=4095,$t1=16384,$lo=0 -> $lo=67092480
$pc=0x14(~1): 0x00004012: mflo $t0: $t0=4095,$lo=67092480 -> $t0=67092480
$pc=0x18(~1): 0x00000000: nop
$pc=0x1C(~1): 0x00000000: nop
$pc=0x20(~1): 0x25083FFC: addiu $t0,$t0,16380: $t0=67092480,$t0=67092480 -> $t0=67108860
$pc=0x24(~1): 0x8D1D0000: lw $sp,0($t0): $sp=0,$t0=0x3FFFFFC -> $sp=67108816=memory[0x3FFFFFC]
$pc=0x28(~1): 0x00000000: nop
$pc=0x2C(~1): 0x00000000: nop
$pc=0x30(~1): 0x00000000: nop
$pc=0x34(~1): 0x00000000: nop
$pc=0x38(~1): 0x00000000: nop
$pc=0x3C(~1): 0x00000000: nop
$pc=0x40(~1): 0x0C000067: jal 0x67[0x19C]: $ra=0x0 -> $ra=0x48,$pc=0x19C
$pc=0x19C(~4): 0x27BDFFFC: addiu $sp,$sp,-4: $sp=67108816,$sp=67108816 -> $sp=67108812
$pc=0x1A0(~4): 0xAFBF0000: sw $ra,0($sp): $ra=72,$sp=0x3FFFFCC -> memory[0x3FFFFCC]=72=$ra
$pc=0x1A4(~4): 0x27BDFFFC: addiu $sp,$sp,-4: $sp=67108812,$sp=67108812 -> $sp=67108808
$pc=0x1A8(~4): 0xAFBE0000: sw $fp,0($sp): $fp=0,$sp=0x3FFFFC8 -> memory[0x3FFFFC8]=0=$fp
$pc=0x1AC(~4): 0x27BE0000: addiu $fp,$sp,0: $fp=0,$sp=67108808 -> $fp=67108808
$pc=0x1B0(~4): 0x24080000: addiu $t0,$zero,0: $t0=67108860,$zero=0 -> $t0=0
$pc=0x1B4(~4): 0xAF88FFFC: sw $t0,-4($gp): $t0=0,$gp=0x260 -> memory[0x25C]=0=$t0
$pc=0x1B8(~6): 0x8F88FFFC: lw $t0,-4($gp): $t0=0,$gp=0x260 -> $t0=0=memory[0x25C]
$pc=0x1BC(~6): 0x24090001: addiu $t1,$zero,1: $t1=16384,$zero=0 -> $t1=1
$pc=0x1C0(~6): 0x01094021: addu $t0,$t0,$t1: $t0=0,$t0=0,$t1=1 -> $t0=1
$pc=0x1C4(~6): 0xAF88FFFC: sw $t0,-4($gp): $t0=1,$gp=0x260 -> memory[0x25C]=1=$t0
$pc=0x1C8(~8): 0x8F88FFFC: lw $t0,-4($gp): $t0=1,$gp=0x260 -> $t0=1=memory[0x25C]
$pc=0x1CC(~8): 0x24090001: addiu $t1,$zero,1: $t1=1,$zero=0 -> $t1=1
$pc=0x1D0(~8): 0x01094023: subu $t0,$t0,$t1: $t0=1,$t0=1,$t1=1 -> $t0=0
$pc=0x1D4(~8): 0x10080004: beq $zero,$t0,4[0x1E8]: $zero=0,$t0=0 -> $pc=0x1E8
$pc=0x1E8(~8): 0x24080001: addiu $t0,$zero,1: $t0=0,$zero=0 -> $t0=1
$pc=0x1EC(~8): 0x10080005: beq $zero,$t0,5[0x204]: $zero=0,$t0=1 -> $pc=0x1F0
$pc=0x1F0(~8): 0x00000000: nop
$pc=0x1F4(~9): 0x8F88FFFC: lw $t0,-4($gp): $t0=1,$gp=0x260 -> $t0=1=memory[0x25C]
$pc=0x1F8(~9): 0x24090001: addiu $t1,$zero,1: $t1=1,$zero=0 -> $t1=1
$pc=0x1FC(~9): 0x01094021: addu $t0,$t0,$t1: $t0=1,$t0=1,$t1=1 -> $t0=2
$pc=0x200(~9): 0xAF88FFFC: sw $t0,-4($gp): $t0=2,$gp=0x260 -> memory[0x25C]=2=$t0
$pc=0x204(~11): 0x8F88FFFC: lw $t0,-4($gp): $t0=2,$gp=0x260 -> $t0=2=memory[0x25C]
$pc=0x208(~11): 0x24090000: addiu $t1,$zero,0: $t1=1,$zero=0 -> $t1=0
$pc=0x20C(~11): 0x0128402A: slt $t0,$t1,$t0: $t1=0,$t0=2 -> $t0=1
$pc=0x210(~11): 0x10080007: beq $zero,$t0,7[0x230]: $zero=0,$t0=1 -> $pc=0x214
$pc=0x214(~11): 0x00000000: nop
$pc=0x218(~12): 0x8F88FFFC: lw $t0,-4($gp): $t0=1,$gp=0x260 -> $t0=2=memory[0x25C]
$pc=0x21C(~12): 0x24090001: addiu $t1,$zero,1: $t1=0,$zero=0 -> $t1=1
$pc=0x220(~12): 0x01094023: subu $t0,$t0,$t1: $t0=2,$t0=2,$t1=1 -> $t0=1
$pc=0x224(~12): 0xAF88FFFC: sw $t0,-4($gp): $t0=1,$gp=0x260 -> memory[0x25C]=1=$t0
$pc=0x228(~14): 0x1000FFF6: beq $zero,$zero,-10[0x204]: $zero=0,$zero=0 -> $pc=0x204
$pc=0x204(~11): 0x8F88FFFC: lw $t0,-4($gp): $t0=1,$gp=0x260 -> $t0=1=memory[0x25C]
$pc=0x208(~11): 0x24090000: addiu $t1,$zero,0: $t1=1,$zero=0 -> $t1=0
$pc=0x20C(~11): 0x0128402A: slt $t0,$t1,$t0: $t1=0,$t0=1 -> $t0=1
$pc=0x210(~11): 0x10080007: beq $zero,$t0,7[0x230]: $zero=0,$t0=1 -> $pc=0x214
$pc=0x214(~11): 0x00000000: nop
$pc=0x218(~12): 0x8F88FFFC: lw $t0,-4($gp): $t0=1,$gp=0x260 -> $t0=1=memory[0x25C]
$pc=0x21C(~12): 0x24090001: addiu $t1,$zero,1: $t1=0,$zero=0 -> $t1=1
$pc=0x220(~12): 0x01094023: subu $t0,$t0,$t1: $t0=1,$t0=1,$t1=1 -> $t0=0
$pc=0x224(~12): 0xAF88FFFC: sw $t0,-4($gp): $t0=0,$gp=0x260 -> memory[0x25C]=0=$t0
$pc=0x228(~14): 0x1000FFF6: beq $zero,$zero,-10[0x204]: $zero=0,$zero=0 -> $pc=0x204
$pc=0x204(~11): 0x8F88FFFC: lw $t0,-4($gp): $t0=0,$gp=0x260 -> $t0=0=memory[0x25C]
$pc=0x208(~11): 0x24090000: addiu $t1,$zero,0: $t1=1,$zero=0 -> $t1=0
$pc=0x20C(~11): 0x0128402A: slt $t0,$t1,$t0: $t1=0,$t0=0 -> $t0=0
$pc=0x210(~11): 0x10080007: beq $zero,$t0,7[0x230]: $zero=0,$t0=0 -> $pc=0x230
$pc=0x230(~14): 0x8F88FFFC: lw $t0,-4($gp): $t0=0,$gp=0x260 -> $t0=0=memory[0x25C]
$pc=0x234(~14): 0x00081021: addu $v0,$zero,$t0: $v0=0,$zero=0,$t0=0 -> $v0=0
$pc=0x238(~14): 0x08000090: j 0x90[0x240]: -> $pc=0x240
$pc=0x240(~15): 0x27DD0000: addiu $sp,$fp,0: $sp=67108808,$fp=67108808 -> $sp=67108808
$pc=0x244(~15): 0x8FBE0000: lw $fp,0($sp): $fp=67108808,$sp=0x3FFFFC8 -> $fp=0=memory[0x3FFFFC8]
$pc=0x248(~15): 0x27BD0004: addiu $sp,$sp,4: $sp=67108808,$sp=67108808 -> $sp=67108812
$pc=0x24C(~15): 0x8FBF0000: lw $ra,0($sp): $ra=72,$sp=0x3FFFFCC -> $ra=72=memory[0x3FFFFCC]
$pc=0x250(~15): 0x27BD0004: addiu $sp,$sp,4: $sp=67108812,$sp=67108812 -> $sp=67108816
$pc=0x254(~15): 0x03E00008: jr $ra: $ra=0x48 -> $pc=0x48
$pc=0x48(~1): 0x27BDFFFC: addiu $sp,$sp,-4: $sp=67108816,$sp=67108816 -> $sp=67108812
$pc=0x4C(~1): 0xAFA20000: sw $v0,0($sp): $v0=0,$sp=0x3FFFFCC -> memory[0x3FFFFCC]=0=$v0
$pc=0x50(~1): 0x8FA40000: lw $a0,0($sp): $a0=0,$sp=0x3FFFFCC -> $a0=0=memory[0x3FFFFCC]
$pc=0x54(~1): 0x27BD0004: addiu $sp,$sp,4: $sp=67108812,$sp=67108812 -> $sp=67108816
$pc=0x58(~1): 0x24020FA1: addiu $v0,$zero,4001: $v0=0,$zero=0 -> $v0=4001
$pc=0x5C(~1): 0x0000000C: syscall
exiting with exit code 0
profile: total,max(ratio%)@addr(line#),2max(ratio%)@addr(line#),3max(ratio%)@addr(line#)
calls: 1,1(100.00%)@0x19C(~4),0(0.00%),0(0.00%)
loops: 2,2(100.00%)@0x204(~11),0(0.00%),0(0.00%)
loads: 13,3(23.09%)@0x204(~11),2(15.38%)@0x218(~12),1(7.69%)@0x24(~1)
stores: 8,2(25.00%)@0x224(~12),1(12.50%)@0x4C(~1),0(0.00%)