#!/usr/bin/bash

export CROSS_COMPILE=riscv64-unknown-elf-

if [ ! -d "../opensbi" ]; then
    git clone git@github.com:riscv/opensbi.git

    if [ "$?" != "0" ]; then
        printf "ERROR: Could not clone OpenSBI!\n"
        exit
    fi
fi

cd ../opensbi

PLATFORM_RISCV_XLEN=64 make PLATFORM=kendryte/k210 O=build/ FW_PAYLOAD=y FW_PAYLOAD_PATH=../k210/own-payload.bin
