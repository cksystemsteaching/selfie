$pc=0x0(~1): addiu $t0,$zero,600: $t0=0,$zero=0 -> $t0=600
$pc=0x4(~1): addiu $gp,$t0,0: $gp=0,$t0=600 -> $gp=600
$pc=0x8(~1): addiu $t0,$zero,4095: $t0=600,$zero=0 -> $t0=4095
$pc=0xC(~1): addiu $t1,$zero,16384: $t1=0,$zero=0 -> $t1=16384
$pc=0x10(~1): multu $t0,$t1: $t0=4095,$t1=16384,$lo=0 -> $lo=67092480
$pc=0x14(~1): mflo $t0: $t0=4095,$lo=67092480 -> $t0=67092480
$pc=0x18(~1): nop
$pc=0x1C(~1): nop
$pc=0x20(~1): addiu $t0,$t0,16380: $t0=67092480,$t0=67092480 -> $t0=67108860
$pc=0x24(~1): lw $sp,0($t0): $sp=0,$t0=0x3FFFFFC -> $sp=67108816=mem[0x3FFFFFC]
$pc=0x28(~1): nop
$pc=0x2C(~1): nop
$pc=0x30(~1): nop
$pc=0x34(~1): nop
$pc=0x38(~1): nop
$pc=0x3C(~1): nop
$pc=0x40(~1): jal 0x5F[0x17C]: $ra=0x0 -> $ra=0x48,$pc=0x17C
$pc=0x17C(~4): addiu $sp,$sp,-4: $sp=67108816,$sp=67108816 -> $sp=67108812
$pc=0x180(~4): sw $ra,0($sp): $ra=72,$sp=0x3FFFFCC -> mem[0x3FFFFCC]=72=$ra
$pc=0x184(~4): addiu $sp,$sp,-4: $sp=67108812,$sp=67108812 -> $sp=67108808
$pc=0x188(~4): sw $fp,0($sp): $fp=0,$sp=0x3FFFFC8 -> mem[0x3FFFFC8]=0=$fp
$pc=0x18C(~4): addiu $fp,$sp,0: $fp=0,$sp=67108808 -> $fp=67108808
$pc=0x190(~4): addiu $t0,$zero,0: $t0=67108860,$zero=0 -> $t0=0
$pc=0x194(~4): sw $t0,-4($gp): $t0=0,$gp=0x258 -> mem[0x254]=0=$t0
$pc=0x198(~6): lw $t0,-4($gp): $t0=0,$gp=0x258 -> $t0=0=mem[0x254]
$pc=0x19C(~6): addiu $t1,$zero,1: $t1=16384,$zero=0 -> $t1=1
$pc=0x1A0(~6): addu $t0,$t0,$t1: $t0=0,$t0=0,$t1=1 -> $t0=1
$pc=0x1A4(~6): sw $t0,-4($gp): $t0=1,$gp=0x258 -> mem[0x254]=1=$t0
$pc=0x1A8(~8): lw $t0,-4($gp): $t0=1,$gp=0x258 -> $t0=1=mem[0x254]
$pc=0x1AC(~8): addiu $t1,$zero,1: $t1=1,$zero=0 -> $t1=1
$pc=0x1B0(~8): subu $t0,$t0,$t1: $t0=1,$t0=1,$t1=1 -> $t0=0
$pc=0x1B4(~8): beq $zero,$t0,4[0x1C8]: $zero=0,$t0=0 -> $pc=0x1C8
$pc=0x1C8(~8): addiu $t0,$zero,1: $t0=0,$zero=0 -> $t0=1
$pc=0x1CC(~8): beq $zero,$t0,7[0x1EC]: $zero=0,$t0=1 -> $pc=0x1D0
$pc=0x1D0(~8): nop
$pc=0x1D4(~9): lw $t0,-4($gp): $t0=1,$gp=0x258 -> $t0=1=mem[0x254]
$pc=0x1D8(~9): addiu $t1,$zero,1: $t1=1,$zero=0 -> $t1=1
$pc=0x1DC(~9): addu $t0,$t0,$t1: $t0=1,$t0=1,$t1=1 -> $t0=2
$pc=0x1E0(~9): sw $t0,-4($gp): $t0=2,$gp=0x258 -> mem[0x254]=2=$t0
$pc=0x1E4(~11): beq $zero,$zero,5[0x1FC]: $zero=0,$zero=0 -> $pc=0x1FC
$pc=0x1FC(~13): lw $t0,-4($gp): $t0=2,$gp=0x258 -> $t0=2=mem[0x254]
$pc=0x200(~13): addiu $t1,$zero,0: $t1=1,$zero=0 -> $t1=0
$pc=0x204(~13): slt $t0,$t1,$t0: $t1=0,$t0=2 -> $t0=1
$pc=0x208(~13): beq $zero,$t0,7[0x228]: $zero=0,$t0=1 -> $pc=0x20C
$pc=0x20C(~13): nop
$pc=0x210(~14): lw $t0,-4($gp): $t0=1,$gp=0x258 -> $t0=2=mem[0x254]
$pc=0x214(~14): addiu $t1,$zero,1: $t1=0,$zero=0 -> $t1=1
$pc=0x218(~14): subu $t0,$t0,$t1: $t0=2,$t0=2,$t1=1 -> $t0=1
$pc=0x21C(~14): sw $t0,-4($gp): $t0=1,$gp=0x258 -> mem[0x254]=1=$t0
$pc=0x220(~16): beq $zero,$zero,-10[0x1FC]: $zero=0,$zero=0 -> $pc=0x1FC
$pc=0x1FC(~13): lw $t0,-4($gp): $t0=1,$gp=0x258 -> $t0=1=mem[0x254]
$pc=0x200(~13): addiu $t1,$zero,0: $t1=1,$zero=0 -> $t1=0
$pc=0x204(~13): slt $t0,$t1,$t0: $t1=0,$t0=1 -> $t0=1
$pc=0x208(~13): beq $zero,$t0,7[0x228]: $zero=0,$t0=1 -> $pc=0x20C
$pc=0x20C(~13): nop
$pc=0x210(~14): lw $t0,-4($gp): $t0=1,$gp=0x258 -> $t0=1=mem[0x254]
$pc=0x214(~14): addiu $t1,$zero,1: $t1=0,$zero=0 -> $t1=1
$pc=0x218(~14): subu $t0,$t0,$t1: $t0=1,$t0=1,$t1=1 -> $t0=0
$pc=0x21C(~14): sw $t0,-4($gp): $t0=0,$gp=0x258 -> mem[0x254]=0=$t0
$pc=0x220(~16): beq $zero,$zero,-10[0x1FC]: $zero=0,$zero=0 -> $pc=0x1FC
$pc=0x1FC(~13): lw $t0,-4($gp): $t0=0,$gp=0x258 -> $t0=0=mem[0x254]
$pc=0x200(~13): addiu $t1,$zero,0: $t1=1,$zero=0 -> $t1=0
$pc=0x204(~13): slt $t0,$t1,$t0: $t1=0,$t0=0 -> $t0=0
$pc=0x208(~13): beq $zero,$t0,7[0x228]: $zero=0,$t0=0 -> $pc=0x228
$pc=0x228(~16): lw $t0,-4($gp): $t0=0,$gp=0x258 -> $t0=0=mem[0x254]
$pc=0x22C(~16): addu $v0,$zero,$t0: $v0=0,$zero=0,$t0=0 -> $v0=0
$pc=0x230(~16): j 0x8E[0x238]: -> $pc=0x238
$pc=0x238(~17): addiu $sp,$fp,0: $sp=67108808,$fp=67108808 -> $sp=67108808
$pc=0x23C(~17): lw $fp,0($sp): $fp=67108808,$sp=0x3FFFFC8 -> $fp=0=mem[0x3FFFFC8]
$pc=0x240(~17): addiu $sp,$sp,4: $sp=67108808,$sp=67108808 -> $sp=67108812
$pc=0x244(~17): lw $ra,0($sp): $ra=72,$sp=0x3FFFFCC -> $ra=72=mem[0x3FFFFCC]
$pc=0x248(~17): addiu $sp,$sp,4: $sp=67108812,$sp=67108812 -> $sp=67108816
$pc=0x24C(~17): jr $ra: $ra=0x48 -> $pc=0x48
$pc=0x48(~1): addiu $sp,$sp,-4: $sp=67108816,$sp=67108816 -> $sp=67108812
$pc=0x4C(~1): sw $v0,0($sp): $v0=0,$sp=0x3FFFFCC -> mem[0x3FFFFCC]=0=$v0
$pc=0x50(~1): lw $a0,0($sp): $a0=0,$sp=0x3FFFFCC -> $a0=0=mem[0x3FFFFCC]
$pc=0x54(~1): addiu $sp,$sp,4: $sp=67108812,$sp=67108812 -> $sp=67108816
$pc=0x58(~1): addiu $v0,$zero,4001: $v0=0,$zero=0 -> $v0=4001
$pc=0x5C(~1): syscall
exiting with exit code 0
total,max(ratio%)@addr(line#),2max(ratio%)@addr(line#),3max(ratio%)@addr(line#)
calls: 1,1(100.00%)@0x17C(~4),0(0.00%),0(0.00%)
loops: 2,2(100.00%)@0x1FC(~13),0(0.00%),0(0.00%)
loads: 13,3(23.09%)@0x1FC(~13),2(15.38%)@0x210(~14),1(7.69%)@0x24(~1)
stores: 8,2(25.00%)@0x21C(~14),1(12.50%)@0x4C(~1),0(0.00%)