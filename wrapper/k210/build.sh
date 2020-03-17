#!/usr/bin/bash

#riscv64-unknown-elf-gcc -mabi=lp64 -march=rv64imafdc -ffreestanding -nostdlib -c sbi_wrapper.c -I../opensbi/include -o libsbi_wrapper.o
riscv64-unknown-elf-gcc -mabi=lp64 -march=rv64imafdc -ffreestanding -nostdlib -c hello-world.c -o hello_world.o -D'uint64_t = unsigned long long int'
riscv64-unknown-elf-gcc -mabi=lp64 -march=rv64imafdc -ffreestanding -nostdlib -I../opensbi/include  -c hello-world.S -o hello_world_S.o
riscv64-unknown-elf-gcc -mabi=lp64 -march=rv64imafdc -ffreestanding -nostdlib hello_world.o hello_world_S.o -L../opensbi/build/lib -o own-payload.elf

riscv64-unknown-elf-objcopy -S -O binary own-payload.elf own-payload.bin
