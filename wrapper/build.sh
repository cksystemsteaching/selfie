#!/usr/bin/bash

riscv64-unknown-elf-gcc -mabi=lp64 -march=rv64imafdc -ffreestanding -nostdlib -c sbi_wrapper.c -Iopensbi/include -o libsbi_wrapper.o
riscv64-unknown-elf-gcc -mabi=lp64 -march=rv64imafdc -ffreestanding -nostdlib -c hello-world.c -o hello_world.o -D'uint64_t = unsigned long long int'

riscv64-unknown-elf-gcc -mabi=lp64 -march=rv64imafdc -ffreestanding -nostdlib hello_world.o libsbi_wrapper.o -Lopensbi/build/lib -lsbi -o test.elf

riscv64-unknown-elf-objcopy -S -O binary test.elf test.bin
