#############################
#    Selfie Docker Image    #
# selfie.cs.uni-salzburg.at #
#############################

###################################
# PK (Proxy kernel) builder image #
###################################
FROM ubuntu:latest AS pkbuilder

# specify work directory and RISC-V install directory
ENV TOP=/opt RISCV=/opt/riscv PATH=$PATH:/opt/riscv/bin
WORKDIR $TOP

# install tools to build pk
RUN apt-get update \
  && apt-get install -y --no-install-recommends \
       ca-certificates \
       make git \
       gcc-riscv64-linux-gnu libc-dev-riscv64-cross \
  && rm -rf /var/lib/apt/lists/*

# get sources from HEAD
RUN git clone https://github.com/riscv/riscv-pk

# set build flags compatible with Ubuntu's riscv64-* build flags,
# otherwise compilation fails with linker errors related to stack protection
# also, use multiple cores to speed up compilation
ENV CFLAGS="-fstack-protector -fstack-protector-explicit -U_FORTIFY_SOURCE" \
  CPPFLAGS="-fstack-protector -fstack-protector-explicit -U_FORTIFY_SOURCE" \
  MAKEFLAGS=-j4

# build proxy kernel
# note that at the end, we move the compiled binaries from riscv64-linux-gnu to riscv64-unknown-elf,
# because when running the proxy kernel with 'spike pk', it looks at that path by default
RUN mkdir -p $RISCV \
  && mkdir -p riscv-pk/build \
  && cd riscv-pk/build \
  && ../configure --prefix=$RISCV --host=riscv64-linux-gnu --with-arch=rv64gc --with-abi=lp64d \
  && make \
  && make install \
  && mv $RISCV/riscv64-linux-gnu $RISCV/riscv64-unknown-elf

#######################################
# Spike (ISA simulator) builder image #
#######################################
FROM ubuntu:latest AS spikebuilder

# specify work directory and RISC-V install directory
ENV TOP=/opt RISCV=/opt/riscv PATH=$PATH:/opt/riscv/bin
WORKDIR $TOP

# install tools to build RISC-V spike
RUN apt-get update \
  && apt-get install -y --no-install-recommends \
       ca-certificates \
       make git \
       g++ device-tree-compiler \
  && rm -rf /var/lib/apt/lists/*

# get sources from HEAD
RUN git clone https://github.com/riscv/riscv-isa-sim.git

# use multiple cores to speed up compilation
ENV MAKEFLAGS=-j4

# build spike ISA simulator
RUN mkdir -p $RISCV \
  && mkdir -p riscv-isa-sim/build \
  && cd riscv-isa-sim/build \
  && ../configure --prefix=$RISCV \
  && make \
  && make install

######################
# QEMU builder image #
######################
FROM ubuntu:latest AS qemubuilder

# specify work directory and RISC-V install directory
ENV TOP=/opt RISCV=/opt/riscv PATH=$PATH:/opt/riscv/bin
WORKDIR $TOP

# install statically linked QEMU (so it's easier to move it to another image)
RUN apt-get update \
  && apt-get install -y --no-install-recommends \
       qemu-user-static qemu-system-misc \
  && rm -rf /var/lib/apt/lists/*

# copy QEMU RISC-V statically linked binary to common output folder
RUN mkdir -p $RISCV/bin \
  && cp /usr/bin/qemu-riscv64-static $RISCV/bin \
  && cp /usr/bin/qemu-system-riscv64 $RISCV/bin \
  && cp /usr/bin/qemu-riscv32-static $RISCV/bin \
  && cp /usr/bin/qemu-system-riscv32 $RISCV/bin

########################################
# Boolector (SMT solver) builder image #
########################################
FROM ubuntu:latest AS boolectorbuilder

# specify work directory and RISC-V install directory
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
  && rm -rf /var/lib/apt/lists/*

# get sources from HEAD
RUN git clone https://github.com/Boolector/boolector

# use multiple cores to speed up compilation
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
FROM ubuntu:latest AS openocdbuilder

ENV TOP=/opt RISCV=/opt/riscv PATH=$PATH:/opt/riscv/bin
WORKDIR $TOP

# install tools to build OpenOCD
RUN apt-get update \
  && apt-get install -y --no-install-recommends \
       ca-certificates \
       make git \
       gcc libtool libusb-dev \
       automake pkg-config \
  && rm -rf /var/lib/apt/lists/*

RUN git clone https://github.com/riscv/riscv-openocd.git

# use multiple cores to speed up compilation
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
FROM ubuntu:latest AS selfieall

# specify work directory and RISC-V install directory
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
  && rm -rf /var/lib/apt/lists/*

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
  && rm -rf /var/lib/apt/lists/*

# specify user work directory
WORKDIR /opt/selfie

# build baremetal machine files
RUN make --directory machine/

# default command
CMD /bin/bash