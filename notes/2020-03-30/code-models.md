# The problem
* linking process led to errors such as  
```test.o: in function `search_for_word_in_memory':
/media/Shared/Martin/Documents/Uni/20SS/PR_Bachelor_Projekt/Software/selfie_bare_metal/wrapper/k210/hello-world.c:89:(.text+0x300): relocation truncated to fit: R_RISCV_HI20 against symbol `foo' defined in COMMON section in test.o```
* it turns out that this is fixed by the compile flag `-mcmodel=medany`

# The code models
* 32-bit signed offsets for symbol references
* determins how code is generated **within** a function
## `medlow` (medium-low code model)
* default code model
* uses `lui`/`ld` pairs to refer to global symbols
    * code is linked around address 0
    * assembler emits `R_RISCV_HI20`/`R_RISCV_LO12_I` sequences
* program and statically defined symbols both mus lie within a single 2GiB address range and must lie between absolute addresses -2GiB and +2GiB
* programs can be statically or dynamically linked


## `medany` (medium-any code model)
* uses `auipc`/`ld` pairs to refer to global symbols
    * code can be linked at any address
    * assembler emits `R_RISCV_PCREL_HI20`/`R_RISCV_PCREL_LO12_I` sequences
* program and statically defined symbols must be within any single 2GiB address range
* programs can be statically or dynamically linked



# Sources
* https://www.sifive.com/blog/all-aboard-part-4-risc-v-code-models
* https://github.com/riscv/riscv-gcc/commit/95d1d5e9aa8fbc019680ba9e5818084c35e5841d
* https://sifive.cdn.prismic.io/sifive%2F15d1d90e-f60e-42a2-b6bf-c805c6c73b0d_riscv-large-code-model-workaround.pdf

**See also:**
* https://github.com/riscv/riscv-elf-psabi-doc/blob/master/riscv-elf.md#relocations
