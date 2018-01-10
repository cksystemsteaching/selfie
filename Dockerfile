FROM ubuntu:16.04

# specify work directory
ENV TOP /opt/selfie
WORKDIR $TOP

# install tools to build RISC-V gnu toolchain, spike and pk
RUN apt-get update \
    && apt-get upgrade -y \
    && apt-get install -y \
    autoconf \
    automake \
    autotools-dev \
    curl \
    device-tree-compiler \
    libmpc-dev \
    libmpfr-dev \
    libgmp-dev \
    libusb-1.0-0-dev \
    gawk \
    build-essential \
    bison \
    flex \
    texinfo \
    gperf \
    libtool \
    patchutils \
    bc \
    zlib1g-dev \
    device-tree-compiler \
    pkg-config \
    git \
    gcc

# get sources from HEAD
RUN git clone https://github.com/riscv/riscv-tools.git \
    && cd riscv-tools \
    && git submodule update --init --recursive

# specify install directory
ENV RISCV $TOP/riscv

# build everything with gcc
RUN mkdir -p $RISCV \
    && cd riscv-tools \
    && CC=gcc CXX=g++ ./build.sh

# add RISC-V tools to path
ENV PATH $PATH:$RISCV/bin

# add selfie to the image
ADD . $TOP/

# fix file time
RUN touch *

# test the RISC-V gnu toolchain
RUN echo '#include <stdio.h>\n int main(void) { printf("Hello world!\\n"); return 0; }' > hello.c \
    && riscv64-unknown-elf-gcc -o hello hello.c \
    && spike pk hello \
    && rm hello.c hello

# remove source files and RISC-V gnu toolchain
RUN rm -rf \
    riscv-tools \
    riscv/bin/riscv64-* \
    riscv/bin/openocd \
    riscv/lib/gcc \
    riscv/libexec \
    riscv/riscv64-unknown-elf \
    riscv/share

# remove apt cache files
RUN apt-get autoremove -y \
    && apt-get clean
