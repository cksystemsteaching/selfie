OpenSBI expects a flat binary file as input, linked to address 0x8000\_0000.

In its test payload, it uses a _more or less_ linker script `../../wrapper/opensbi/build/platform/kendryte/k210/firmware/payloads/test.elf.ld`. It is dynamically generated using the input file `firmware/payloads/test.elf.ldS` and the **C preprocessor** `riscv64-unknown-elf-cpp`.

Using the C preprocessor as a way to distinguish between RV32 and RV64 seems like a hack. As the preprocessor does only care about hash \# directives, it seems to work out fine.

As we are only supporting RV64, it should work fine without preprocessing and just using RV64



# Memory models
The memory models `medlow` and `medany` are explained in [this `riscv-gcc` commit](https://github.com/riscv/riscv-gcc/commit/95d1d5e9aa8fbc019680ba9e5818084c35e5841d).
