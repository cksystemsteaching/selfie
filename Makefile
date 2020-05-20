# Compiler flags
CFLAGS := -Wall -Wextra -O3 -m64 -D'uint64_t=unsigned long long'

# Bootstrap selfie.c into selfie executable
selfie: selfie.c
	$(CC) $(CFLAGS) $< -o $@

# Compile *.c including selfie.c into RISC-U *.m executable
%.m: %.c selfie
	./selfie -c $< -o $@

# Compile *.c including selfie.c into RISC-U *.s assembly
%.s: %.c selfie
	./selfie -c $< -s $@

# Generate selfie library as selfie.h
selfie.h: selfie.c
	sed 's/main(/selfie_main(/' selfie.c > selfie.h

# Compile *.c with selfie.h as library into *.selfie executable
%.selfie: %.c selfie.h
	$(CC) $(CFLAGS) --include selfie.h $< -o $@

# Translate *.c including selfie.c into SMT-LIB model
%-35.smt: %-35.c selfie
	./selfie -c $< -se 0 35 --merge-enabled
%-10.smt: %-10.c selfie
	./selfie -c $< -se 0 10 --merge-enabled

# Translate *.c including selfie.c into BTOR2 model
%.btor2: %.c tools/modeler.selfie
	./tools/modeler.selfie -c $< - 0 --check-block-access

# Consider these targets as targets, not files
.PHONY : compile quine escape debug replay os vm min mob sat smt btor2 mod x86 all assemble spike qemu boolector btormc grader grade everything clean

# Self-contained fixed-point of self-compilation
compile: selfie
	./selfie -c selfie.c -o selfie1.m -s selfie1.s -m 2 -c selfie.c -o selfie2.m -s selfie2.s
	diff -q selfie1.m selfie2.m
	diff -q selfie1.s selfie2.s

# Compile and run quine and compare its output to itself
quine: selfie
	./selfie -c examples/quine.c selfie.c -m 1 | sed '/selfie/d' | diff --strip-trailing-cr examples/quine.c -

# Demonstrate available escape sequences
escape: selfie
	./selfie -c examples/escape.c -m 1

# Run debugger
debug: selfie
	./selfie -c examples/pointer.c -d 1

# Run replay engine
replay: selfie
	./selfie -c examples/division-by-zero.c -r 1

# Run emulator on emulator
os: selfie.m
	./selfie -l selfie.m -m 2 -l selfie.m -m 1

# Self-compile on two virtual machines
vm: selfie.m selfie.s
	./selfie -l selfie.m -m 3 -l selfie.m -y 3 -l selfie.m -y 2 -c selfie.c -o selfie3.m -s selfie3.s
	diff -q selfie.m selfie3.m
	diff -q selfie.s selfie3.s

# Self-compile on two virtual machines on fully mapped virtual memory
min: selfie.m selfie.s
	./selfie -l selfie.m -min 15 -l selfie.m -y 3 -l selfie.m -y 2 -c selfie.c -o selfie4.m -s selfie4.s
	diff -q selfie.m selfie4.m
	diff -q selfie.s selfie4.s

# Run mobster, the emulator without pager
mob: selfie
	./selfie -c -mob 1

# Run SAT solver natively and as RISC-U executable
sat: tools/babysat.selfie selfie selfie.h
	./tools/babysat.selfie examples/rivest.cnf
	./selfie -c selfie.h tools/babysat.c -m 1 examples/rivest.cnf

# Gather symbolic execution example files as .smt files
smts := $(patsubst %.c,%.smt,$(wildcard symbolic/*.c))

# Run monster, the symbolic execution engine
smt: $(smts)

# Gather symbolic execution example files as .btor2 files
btor2s := $(patsubst %.c,%.btor2,$(wildcard symbolic/*.c))

# Run modeler, the symbolic model generator
btor2: $(btor2s) selfie.btor2

# Run modeler as RISC-U executable
mod: selfie selfie.h
	./selfie -c selfie.h tools/modeler.c -m 1

# Run RISC-V-to-x86 translator natively and as RISC-U executable
# TODO: check self-compilation
x86: tools/riscv-2-x86.selfie selfie.m selfie selfie.h
	./tools/riscv-2-x86.selfie selfie.m
	./selfie -c selfie.h tools/riscv-2-x86.c -m 1 selfie.m

# Run everything that only requires standard tools
all: compile quine debug replay os vm min mob sat btor2 mod x86

# Test autograder
grader: selfie
	cd grader && python3 -m unittest discover -v

# Run autograder
grade:
	grader/self.py self-compile

# Assemble RISC-U with GNU toolchain for RISC-V
assemble: selfie.s
	riscv64-linux-gnu-as selfie.s -o a.out
	rm -f a.out

# Run selfie on spike
spike: selfie.m selfie.s
	spike pk selfie.m -c selfie.c -o selfie5.m -s selfie5.s -m 1
	diff -q selfie.m selfie5.m
	diff -q selfie.s selfie5.s

# Run selfie on qemu usermode emulation
qemu: selfie.m selfie.s
	chmod +x selfie.m
	qemu-riscv64-static selfie.m -c selfie.c -o selfie6.m -s selfie6.s -m 1
	diff -q selfie.m selfie6.m
	diff -q selfie.s selfie6.s

# Test boolector SMT solver
boolector: smt
	$(foreach file, $(wildcard symbolic/*-3-*.smt), [ $$(boolector $(file) -e 0 | grep -c ^sat$$) -eq 3 ];)
	$(foreach file, $(wildcard symbolic/*-2-*.smt), [ $$(boolector $(file) -e 0 | grep -c ^sat$$) -eq 2 ];)
	$(foreach file, $(wildcard symbolic/*-1-*.smt), [ $$(boolector $(file) -e 0 | grep -c ^sat$$) -eq 1 ];)

# Test btormc bounded model checker
btormc: btor2
	$(foreach file, $(btor2s), btormc $(file);)

# Run everything
everything: all assemble spike qemu btormc grader grade

# Clean up
clean:
	rm -f *.m
	rm -f *.s
	rm -f *.smt
	rm -f *.btor2
	rm -f *.selfie
	rm -f *.x86
	rm -f selfie
	rm -f selfie.h
	rm -f selfie.exe
	rm -f examples/*.m
	rm -f examples/*.s
	rm -f symbolic/*.smt
	rm -f symbolic/*.btor2
	rm -f tools/*.selfie