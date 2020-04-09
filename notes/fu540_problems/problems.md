Zeroing out mallocated memory: fail
Moving heap\_head: FAIL


Observations: Es gibt nicht nur .data und .bss, sondern auch .sdata und .sbss
Linker relaxation: https://www.sifive.com/blog/all-aboard-part-3-linker-relaxation-in-riscv-toolchain


Solution: Eine Kombination aus `-mno-relax` und Moves von .sdata und .sbss in jeweils .data und .bss durch Linker Script (Commits 2c2adf8 und 8047af0)


