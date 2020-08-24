# Build everything
make selfie selfie.h
make wipopt

# Create selfie binary and disassembly
./selfie -c selfie.c -o selfie.rv
./selfie -l selfie.rv -S selfie.s

# Optimize binary and create disassembly of optimized binary
./wipopt selfie.rv selfie.opt.s

# Run unoptimized and optimized version, printing registers before each instruction
./selfie -l selfie.rv -m 2 > usage.txt
./selfie -l selfie.opt -m 2 > usage.opt.txt
