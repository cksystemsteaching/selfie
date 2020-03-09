#!/usr/bin/bash

export CROSS_COMPILE=riscv64-unknown-elf-

if [ ! -d "opensbi" ]; then
    git clone git@github.com:riscv/opensbi.git

    if [ "$?" != "0" ]; then
        printf "ERROR: Could not clone OpenSBI!\n"
        exit
    fi
fi

cd opensbi

make PLATFORM=qemu/virt FW_PAYLOAD=y FW_PAYLOAD_PATH=../test.bin
