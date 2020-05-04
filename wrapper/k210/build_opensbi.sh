#!/usr/bin/bash

export CROSS_COMPILE=riscv64-elf-

if [ ! -d "../opensbi" ]; then
    git clone git@github.com:riscv/opensbi.git

    if [ "$?" != "0" ]; then
        printf "ERROR: Could not clone OpenSBI!\n"
        exit
    fi
fi

cd ../opensbi

PLATFORM_RISCV_XLEN=64 make PLATFORM=qemu/virt O=build/ FW_PAYLOAD=y FW_PAYLOAD_PATH=../k210/qemu-payload.bin
PLATFORM_RISCV_XLEN=64 make PLATFORM=kendryte/k210 O=build/ FW_PAYLOAD=y FW_PAYLOAD_PATH=../k210/own-payload.bin FW_PAYLOAD_OFFSET=0x1A000
PLATFORM_RISCV_XLEN=64 make PLATFORM=sifive/fu540 O=build/ FW_PAYLOAD=y FW_PAYLOAD_PATH=../k210/qemu-payload.bin FW_PAYLOAD_OFFSET=0x200000
${CROSS_COMPILE}objcopy -S -O binary --file-alignment 4096 --gap-fill 0xFF build/platform/kendryte/k210/firmware/fw_payload.elf ../k210/test.bin
