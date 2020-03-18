OpenSBI expects a flat binary file as input, linked to address 0x8000\_0000.

In its test payload, it uses a _more or less_ linker script `../../wrapper/opensbi/build/platform/kendryte/k210/firmware/payloads/test.elf.ld`. It is dynamically generated using the input file `firmware/payloads/test.elf.ldS` and the **C preprocessor** `riscv64-unknown-elf-cpp`.

The preprocessor is used to resolve the payload offset using the \#define `FW_PAYLOAD_OFFSET`.
Usually the board already defines the payload offset in its platform makefile (0x8000\_0000 in QEMU, HiFive Unleashed and MAix BiT). However, a user might overwrite it when invoking `make` or if the board default differs from previous occurrences, thus making it impossible to omit this step and hardcode it directly into the linker script.


# Memory models
The memory models `medlow` and `medany` are explained in [this `riscv-gcc` commit](https://github.com/riscv/riscv-gcc/commit/95d1d5e9aa8fbc019680ba9e5818084c35e5841d).
