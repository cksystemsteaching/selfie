###################################
# PK (Proxy kernel) builder image #
###################################
FROM ubuntu:18.10 AS pkbuilder

# specify work directory and RISC-V install directory
ENV TOP=/opt RISCV=/opt/riscv PATH=$PATH:/opt/riscv/bin
WORKDIR $TOP

# install tools to build pk
RUN apt-get update \
  && apt-get install --no-install-recommends -y \
       ca-certificates \
       gcc-riscv64-linux-gnu \
       git \
       libc-dev-riscv64-cross \
       make \
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
  && ../configure --prefix=$RISCV --host=riscv64-linux-gnu \
  && make \
  && make install \
  && mv $RISCV/riscv64-linux-gnu $RISCV/riscv64-unknown-elf

#######################################
# Spike (ISA simulator) builder image #
#######################################
FROM ubuntu:16.04 AS spikebuilder

# specify work directory and RISC-V install directory
ENV TOP=/opt RISCV=/opt/riscv PATH=$PATH:/opt/riscv/bin
WORKDIR $TOP

# install tools to build RISC-V spike
RUN apt-get update \
  && apt-get install -y --no-install-recommends \
       ca-certificates \
       device-tree-compiler \
       g++ \
       gcc \
       git \
       libc-dev \
       make \
  && rm -rf /var/lib/apt/lists/*

# get sources from HEAD
RUN git clone https://github.com/riscv/riscv-tools.git \
  && cd riscv-tools \
  && git submodule update --init --recursive riscv-fesvr riscv-isa-sim

# use multiple cores to speed up compilation
ENV MAKEFLAGS=-j4

# build spike ISA simulator
RUN mkdir -p $RISCV \
  && cd riscv-tools \
  && ./build-spike-only.sh

######################
# QEMU builder image #
######################
FROM ubuntu:18.10 AS qemubuilder

# specify work directory and RISC-V install directory
ENV TOP=/opt RISCV=/opt/riscv PATH=$PATH:/opt/riscv/bin
WORKDIR $TOP

# install statically linked QEMU (so it's easier to move it to another image)
RUN apt-get update \
  && apt-get install -y --no-install-recommends \
       qemu-user-static \
  && rm -rf /var/lib/apt/lists/*

# copy QEMU RISC-V statically linked binary to common output folder
RUN mkdir -p $RISCV/bin \
  && cp /usr/bin/qemu-riscv64-static $RISCV/bin

########################################
# Boolector (SMT solver) builder image #
########################################
FROM ubuntu:16.04 AS boolectorbuilder

# specify work directory and RISC-V install directory
ENV TOP=/opt RISCV=/opt/riscv PATH=$PATH:/opt/riscv/bin
WORKDIR $TOP

# install tools to build boolector
RUN apt-get update \
  && apt-get install -y --no-install-recommends \
       ca-certificates \
       cmake \
       g++ \
       gcc \
       git \
       libc-dev \
       make \
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

##################################
# Selfie interactive final image #
##################################
FROM ubuntu:16.04

# specify work directory and RISC-V install directory
ENV TOP=/opt RISCV=/opt/riscv PATH=$PATH:/opt/riscv/bin
WORKDIR $TOP

# install git and basic build tools (gcc, make) for working with selfie,
# and device-tree-compiler which is required for spike
RUN apt-get update \
  && apt-get install -y --no-install-recommends \
       build-essential \
       ca-certificates \
       device-tree-compiler \
       git \
  && rm -rf /var/lib/apt/lists/*

# copy spike, pk, qemu and boolector from builder images
COPY --from=pkbuilder $RISCV/ $RISCV/
COPY --from=spikebuilder $RISCV/ $RISCV/
COPY --from=qemubuilder $RISCV/ $RISCV/
COPY --from=boolectorbuilder $RISCV/ $RISCV/

# add selfie sources to the image
COPY . /opt/selfie/

# specify user work directory
WORKDIR /opt/selfie

# build selfie
RUN make selfie

# default command
CMD /bin/bash