// a0: address
// a1: size, in bytes
.global zero_mem
zero_mem:
    // Check whether we are 8 byte aligned
    addi t0, zero, 8
    remu t1, a0, t0
    beqz t1, after_align_addr

    // Align if we are not
    sub t1, t0, t1
align_addr:
    beqz t1, after_align_addr
    sb zero, 0(a0)
    addi a0, a0, 1
    addi a1, a1, -1
    addi t1, t1, -1
    j align_addr
    

after_align_addr:

    // Now that the address is 8 byte aligned, do the actual zeroing
    // using decreasing granularity: sd(8) -> sw(4) -> sh(2) -> sb(1)
    addi t0, zero, 8

zero_sd_loop:
    beqz a1, zero_done
    blt a1, t0, zero_sw
    sd zero, 0(a0)
    add a0, a0, t0
    sub a1, a1, t0
    j zero_sd_loop

zero_sw:
    addi t0, zero, 4
zero_sw_loop:
    beqz a1, zero_done
    blt a1, t0, zero_sh
    sw zero, 0(a0)
    add a0, a0, t0
    sub a1, a1, t0
    j zero_sw_loop

zero_sh:
    addi t0, zero, 2
zero_sh_loop:
    beqz a1, zero_done
    blt a1, t0, zero_sb
    sh zero, 0(a0)
    add a0, a0, t0
    sub a1, a1, t0
    j zero_sh_loop

zero_sb:
    addi t0, zero, 1
zero_sb_loop:
    blt a1, t0, zero_done
    sb zero, 0(a0)
    add a0, a0, t0
    sub a1, a1, t0
    j zero_sb_loop

zero_done:
    ret


