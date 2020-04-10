Zeroing out mallocated memory: fail
Moving heap\_head: FAIL


Observations: Es gibt nicht nur .data und .bss, sondern auch .sdata und .sbss
Linker relaxation: https://www.sifive.com/blog/all-aboard-part-3-linker-relaxation-in-riscv-toolchain


Solution: Eine Kombination aus `-mno-relax` und Moves von .sdata und .sbss in jeweils .data und .bss durch Linker Script (Commits 2c2adf8 und 8047af0)

sdata und sbss stehen für small data und small bss. Symbole in diesen Sections werden nicht über auipc/addi Instruktionen adressiert, sondern über einen lwi, relativ zum Global Pointer.

Durch Deaktivieren von Linker Relaxation in Compiler und mergen von sdata und sbss in deren jeweiligen normalen Sections funktionert die Anwendung ohne das Setzen des Global Pointers

Der Global Pointer muss beim Start der Anwendung aufgesetzt werden. Hierbei ist es wichtig, die Assembly-Instructions mit einem .option norelax zu schützen, da dies sonst selbst gp-relativ geladen werden könnte. Der Global Pointer muss auf die Startadresse + 0x800 der .sdata gesetzt werden, sodass der gesamte 2^12 Immedate Range von S-Format abgedeckt wird und die gesamten 4KiB so referenziert werden können. 

# Quelle
- https://content.riscv.org/wp-content/uploads/2019/03/11.15-Shiva-Chen-Compiler-Support-For-Linker-Relaxation-in-RISC-V-2019-03-13.pdf
- https://groups.google.com/a/groups.riscv.org/forum/#!topic/sw-dev/60IdaZj27dY
- https://gnu-mcu-eclipse.github.io/arch/riscv/programmer/#the-gp-global-pointer-register
- https://github.com/riscv/riscv-elf-psabi-doc/blob/master/riscv-elf.md#absolute-addresses
