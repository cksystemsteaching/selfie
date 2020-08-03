.text
    .global trap_handler_trampoline

.align 12
trap_handler_trampoline:
    // sscratch stores what should be in satp when we want to use the kernel's vaddr space
    csrrw t0, sscratch, t0
    csrw satp, t0
    csrrw t0, sscratch, t0
    call trap_handler_wrapper
