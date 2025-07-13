# Use Debian as the base image

FROM debian:bullseye-slim

# Install necessary packages for building RISC-V GCC toolchain
RUN apt-get update && apt-get install -y \ 
autoconf automake autotools-dev curl python3 python3-pip libmpc-dev libmpfr-dev libgmp-dev gawk build-essential bison flex texinfo gperf libtool patchutils bc zlib1g-dev libexpat-dev ninja-build git cmake libglib2.0-dev libslirp-dev meson z3

# Set working directory
WORKDIR /workspace
COPY . .

#Source venv
RUN ./setup.sh
RUN . venv/bin/activate

#Install Bitwuzla
WORKDIR /opt/bitwuzla
RUN . /workspace/venv/bin/activate && \
    git clone https://github.com/bitwuzla/bitwuzla /opt/bitwuzla && \
    pip install /opt/bitwuzla

# Clone the RISC-V GNU toolchain repository
RUN git clone https://github.com/riscv/riscv-gnu-toolchain /opt/riscv-toolchain
# Set working directory
WORKDIR /opt/riscv-toolchain
# Configure and build the toolchain (this may take a while)
RUN ./configure --prefix=/opt/riscv --enable-multilib --disable-gdb && make -j4

# Add the RISC-V toolchain to the PATH
ENV PATH="/opt/riscv/bin:${PATH}"


# Create a default entry point for the container
ENTRYPOINT ["/bin/bash"]
