#!/usr/bin/bash

if [ "x$PREFIX" == "x" ]
then
    PREFIX="riscv64-elf-"
fi

if [ "x$CC" == "x" ]
then
    CC=${PREFIX}gcc
fi
if [ "x$LD" == "x" ]
then
    LD=${PREFIX}ld
fi

# COMPILATION
#riscv64-unknown-elf-gcc -mabi=lp64 -march=rv64imafdc -ffreestanding -nostdlib -c sbi_wrapper.c -I../opensbi/include -o libsbi_wrapper.o
${CC} -g3 -mabi=lp64 -march=rv64imafdc -mcmodel=medany -ffreestanding -nostdlib -c ../../selfie.c -o selfie.o -D'uint64_t = unsigned long long int'
${CC} -mabi=lp64 -march=rv64imafdc -mcmodel=medany -ffreestanding -nostdlib -I../opensbi/include  -c hello-world.S -o hello_world_S.o
${CC} -g3 -mabi=lp64 -march=rv64imafdc -mcmodel=medany -ffreestanding -nostdlib -c ../sbi_wrapper.c -o sbi_wrapper.o -I../opensbi/include -L../opensbi/build/lib/ -lsbi

# MERGE OBJECT FILES
${LD} -r -b elf64-littleriscv -m elf64lriscv hello_world_S.o sbi_wrapper.o selfie.o -L../opensbi/build/lib -lsbi -o test.o

# LINKER SCRIPT PREPROCESSING
riscv64-elf-cpp  -DFW_TEXT_START=0x80000000 -DFW_PAYLOAD_OFFSET=0x1A000 -DFW_PAYLOAD_ALIGN=0x1000 -x c test.elf.ldS | grep -v '#' > test.elf.kendryte.ld
riscv64-elf-cpp  -DFW_TEXT_START=0x80000000 -DFW_PAYLOAD_OFFSET=0x200000 -DFW_PAYLOAD_ALIGN=0x1000 -x c test.elf.ldS | grep -v '#' > test.elf.qemu.ld

# LINKING
${CC} -mabi=lp64 -march=rv64imafdc -mcmodel=medany -ffreestanding -nostdlib -Wl,--build-id=none -static-libgcc -lgcc test.o -L../opensbi/build/lib -o own-payload.elf -T ./test.elf.kendryte.ld
${CC} -mabi=lp64 -march=rv64imafdc -mcmodel=medany -ffreestanding -nostdlib -Wl,--build-id=none -static-libgcc -lgcc test.o -L../opensbi/build/lib -o qemu-payload.elf -T ./test.elf.qemu.ld

${PREFIX}objcopy -S -O binary own-payload.elf own-payload.bin
${PREFIX}objcopy -S -O binary qemu-payload.elf qemu-payload.bin
