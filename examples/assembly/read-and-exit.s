# to build executable:
# riscv64-unknown-elf-as read-and-exit.s -o read-and-exit.obj
# riscv64-unknown-elf-ld read-and-exit.obj -o read-and-exit

# declare global _start symbol, so the linker can find the entry point
.global _start

# entry point
_start:
    # perform brk(0) syscall to retrieve current program break
    addi a0, zero, 0
    addi a7, zero, 214
    ecall

    # save returned address
    addi s1, a0, 0

    # perform brk(address + 8) syscall to allocate a double word 
    addi a0, a0, 8
    addi a7, zero, 214
    ecall

    # set double word at address to zero
    sd zero, 0(s1)

    # perform read(0, address, 1) syscall to read one byte from stdin
    addi a0, zero, 0
    addi a1, s1, 0
    addi a2, zero, 1
    addi a7, zero, 63
    ecall

    # perform exit(*address) syscall to use read byte as exit code
    ld a0, 0(s1)
    addi a7, zero, 93
    ecall

# data segment must be present for selfie to load the binary
.data
    # single null byte
    null_byte: .byte 0
