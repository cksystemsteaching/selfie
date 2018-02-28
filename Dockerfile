# builder image
FROM ubuntu:16.04

# specify work directory and RISC-V install directory
ENV TOP /opt
ENV RISCV $TOP/riscv
ENV PATH $PATH:$RISCV/bin

WORKDIR $TOP

# install tools to build RISC-V gnu toolchain, spike and pk
RUN apt-get update && apt-get install -y \
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

# build everything with gcc
RUN mkdir -p $RISCV \
  && cd riscv-tools \
  && CC=gcc CXX=g++ ./build.sh

# test the RISC-V gnu toolchain
RUN echo '#include <stdio.h>\n int main(void) { printf("Hello world!\\n"); return 0; }' > hello.c \
  && riscv64-unknown-elf-gcc -o hello hello.c \
  && spike pk hello

# remove RISC-V gnu toolchain to shrink image size
 RUN rm -rf \
    riscv/bin/riscv64-* \
    riscv/bin/openocd \
    riscv/lib/gcc \
    riscv/libexec \
    riscv/share

# release image
FROM ubuntu:16.04

# specify work directory and RISC-V install directory
ENV TOP /opt
ENV RISCV $TOP/riscv
ENV PATH $PATH:$RISCV/bin

WORKDIR $TOP

# install gcc, git, make and diff
RUN apt-get update && apt-get install -y \
    device-tree-compiler \
    build-essential \
    gcc \
    git \
  && rm -rf /var/lib/apt/lists/*

# copy spike and pk from builder image
COPY --from=0 $RISCV/ $RISCV/

# add selfie to the image
COPY . $TOP/selfie/

# specify user work directory
WORKDIR $TOP/selfie