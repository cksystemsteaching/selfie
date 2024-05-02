#############################
#    Selfie Docker Image    #
# selfie.cs.uni-salzburg.at #
#############################

#####################################
# RISCV gnu toolchain builder image #
#####################################
FROM ubuntu:jammy AS riscvgnutoolchainbuilder

ENV TOP=/opt RISCV=/opt/riscv PATH=$PATH:/opt/riscv/bin

WORKDIR $TOP

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        ca-certificates \
        autoconf automake autotools-dev curl python3 python3-pip libmpc-dev libmpfr-dev \
        libgmp-dev gawk build-essential bison flex texinfo gperf libtool patchutils bc \
        zlib1g-dev libexpat-dev ninja-build git cmake libglib2.0-dev \
    && apt clean

RUN git clone https://github.com/riscv/riscv-gnu-toolchain

ENV MAKEFLAGS=-j4

RUN cd riscv-gnu-toolchain \
    && ./configure --prefix=$RISCV --enable-multilib \
    && make

###################################
# PK (Proxy kernel) builder image #
###################################
FROM ubuntu:jammy AS pkbuilder

ENV TOP=/opt RISCV=/opt/riscv PATH=$PATH:/opt/riscv/bin

WORKDIR $TOP

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        ca-certificates \
        make git \
        gcc-riscv64-linux-gnu libc-dev-riscv64-cross \
    && apt clean

RUN git clone https://github.com/riscv/riscv-pk

# COPY --from=riscvgnutoolchainbuilder $RISCV/ $RISCV/

ENV MAKEFLAGS=-j4

# moving the compiled binaries from riscv64-linux-gnu to riscv64-unknown-elf
# because spike looks for riscv64-unknown-elf by default when running pk
RUN mkdir -p riscv-pk/build \
    && cd riscv-pk/build \
    && ../configure --prefix=$RISCV --host=riscv64-linux-gnu --with-arch=rv64gc --with-abi=lp64d \
    && make \
    && make install \
    && mv $RISCV/riscv64-linux-gnu $RISCV/riscv64-unknown-elf

#######################################
# Spike (ISA simulator) builder image #
#######################################
FROM ubuntu:jammy AS spikebuilder

ENV TOP=/opt RISCV=/opt/riscv PATH=$PATH:/opt/riscv/bin

WORKDIR $TOP

RUN apt-get update \
  && apt-get install -y --no-install-recommends \
       ca-certificates \
       make git \
       g++ device-tree-compiler \
  && apt clean

RUN git clone https://github.com/riscv/riscv-isa-sim

ENV MAKEFLAGS=-j4

RUN mkdir -p riscv-isa-sim/build \
    && cd riscv-isa-sim/build \
    && ../configure --prefix=$RISCV \
    && make \
    && make install

######################
# QEMU builder image #
######################
FROM ubuntu:jammy AS qemubuilder

ENV TOP=/opt RISCV=/opt/riscv PATH=$PATH:/opt/riscv/bin

WORKDIR $TOP

# install statically linked QEMU (so it's easier to move it to another image)
RUN apt-get update \
  && apt-get install -y --no-install-recommends \
       qemu-user-static qemu-system-misc \
  && apt clean

# copy QEMU RISC-V statically linked binary to common output folder
RUN mkdir -p $RISCV/bin \
  && cp /usr/bin/qemu-riscv64-static $RISCV/bin \
  && cp /usr/bin/qemu-system-riscv64 $RISCV/bin \
  && cp /usr/bin/qemu-riscv32-static $RISCV/bin \
  && cp /usr/bin/qemu-system-riscv32 $RISCV/bin

########################################
# Boolector (SMT solver) builder image #
########################################
FROM ubuntu:jammy AS boolectorbuilder

ENV TOP=/opt RISCV=/opt/riscv PATH=$PATH:/opt/riscv/bin

WORKDIR $TOP

# Setting non-interactive mode
RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections

# install tools to build boolector
RUN apt-get update \
  && apt-get install -y --no-install-recommends \
       ca-certificates \
       make git \
       g++ \
       curl cmake \
  && apt clean

RUN git clone https://github.com/Boolector/boolector

ENV MAKEFLAGS=-j4

# build boolector and dependencies
RUN mkdir -p $RISCV \
  && cd boolector \
  && ./contrib/setup-lingeling.sh \
  && ./contrib/setup-btor2tools.sh \
  && ./configure.sh --prefix $RISCV \
  && cd build \
  && make \
  && make install

#########################
# OpenOCD builder image #
#########################
FROM ubuntu:jammy AS openocdbuilder

ENV TOP=/opt RISCV=/opt/riscv PATH=$PATH:/opt/riscv/bin

WORKDIR $TOP

# install tools to build OpenOCD
RUN apt-get update \
  && apt-get install -y --no-install-recommends \
       ca-certificates \
       make git \
       gcc libtool libusb-dev \
       automake pkg-config \
  && apt clean

RUN git clone https://github.com/riscv/riscv-openocd.git

ENV MAKEFLAGS=-j4

RUN mkdir -p $RISCV \
  && cd riscv-openocd \
  && ./bootstrap \
  && ./configure \
       --prefix=$RISCV \
       --program-prefix=riscv64- \
  && make \
  && make install

############################
# Selfie interactive image #
############################
FROM ubuntu:jammy AS selfieall

ENV TOP=/opt RISCV=/opt/riscv PATH=$PATH:/opt/riscv/bin

WORKDIR $TOP

# Setting non-interactive mode
RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections

# install tools for selfie
RUN apt-get update \
  && apt-get install -y --no-install-recommends \
       ca-certificates \
       make git \
       gcc gdb libc6-dev-i386-amd64-cross \
       python3.10 \
       device-tree-compiler gcc-riscv64-linux-gnu \
  && update-alternatives --install /usr/bin/python3 python3 /usr/bin/python3.10 1 \
  && apt-get install -y --no-install-recommends \
       binutils-riscv64-linux-gnu libc-dev-riscv64-cross \
       libusb-dev libhidapi-dev \
       xxd gettext curl \
  && apt clean

# copy spike, pk, qemu and boolector from builder images
COPY --from=pkbuilder $RISCV/ $RISCV/
COPY --from=spikebuilder $RISCV/ $RISCV/
COPY --from=qemubuilder $RISCV/ $RISCV/
COPY --from=boolectorbuilder $RISCV/ $RISCV/
COPY --from=openocdbuilder $RISCV/ $RISCV/

# add selfie sources to the image
COPY . /opt/selfie/

# specify user work directory
WORKDIR /opt/selfie

# test build, then clean selfie
RUN make selfie \
  && make clean

# default command
CMD /bin/bash

#################################
# Selfie interactive full image #
#################################
FROM selfieall AS selfieeverything

# only works on amd64 for now

# install tools for 32-bit selfie
RUN apt-get update \
  && apt-get install -y --no-install-recommends lib32gcc-11-dev \
  && apt clean

# specify user work directory
WORKDIR /opt/selfie

# build baremetal machine files
RUN make --directory machine/

# default command
CMD /bin/bash