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

# Consider these targets as targets, not files
.PHONY: self self-self quine escape debug replay os vm min mob gib gclib giblib gclibtest sat mon smt mod btor2 selfie-2-x86 all assemble spike qemu x86 boolector btormc validator grader grade extras everything clean

# Self-compile selfie
self: selfie
	./selfie -c selfie.c

# Self-self-compile selfie and check fixed point of self-compilation
self-self: selfie
	./selfie -c selfie.c -o selfie1.m -s selfie1.s -m 2 -c selfie.c -o selfie2.m -s selfie2.s
	diff -q selfie1.m selfie2.m
	diff -q selfie1.s selfie2.s

# Compile and run quine and compare its output to itself
quine: selfie selfie.h
	./selfie -c selfie.h examples/quine.c -m 1 | sed '/selfie/d' | diff --strip-trailing-cr examples/quine.c -

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
	./selfie -l selfie.m -m 3 -l selfie.m -y 3 -l selfie.m -y 2 -c selfie.c -o selfie-vm.m -s selfie-vm.s
	diff -q selfie.m selfie-vm.m
	diff -q selfie.s selfie-vm.s

# Self-compile on two virtual machines on fully mapped virtual memory
min: selfie.m selfie.s
	./selfie -l selfie.m -min 15 -l selfie.m -y 3 -l selfie.m -y 2 -c selfie.c -o selfie-min.m -s selfie-min.s
	diff -q selfie.m selfie-min.m
	diff -q selfie.s selfie-min.s

# Run mobster, the emulator without pager
mob: selfie
	./selfie -c -mob 1

# Self-compile with conservative garbage collector in mipster
gib: selfie selfie.m selfie.s
	./selfie -c selfie.c -gc -m 1 -c selfie.c -o selfie-gib.m -s selfie-gib.s
	diff -q selfie.m selfie-gib.m
	diff -q selfie.s selfie-gib.s

# Self-compile with conservative garbage collector in hypster
hyb: selfie selfie.m selfie.s
	./selfie -l selfie.m -m 3 -l selfie.m -gc -y 1 -c selfie.c -o selfie-hyb.m -s selfie-hyb.s
	diff -q selfie.m selfie-hyb.m
	diff -q selfie.s selfie-hyb.s

# Self-compile with conservative garbage collector as library
gclib: selfie selfie.h selfie.m selfie.s
	./selfie -gc -c selfie.h tools/gc.c -m 3 -c selfie.c -o selfie-gclib.m -s selfie-gclib.s
	diff -q selfie.m selfie-gclib.m
	diff -q selfie.s selfie-gclib.s

# Self-compile with self-collecting garbage collectors
giblib: selfie selfie.h selfie.m selfie.s
	./selfie -gc -c selfie.h tools/gc.c -gc -m 3 -nr -c selfie.c -o selfie-giblib.m -s selfie-giblib.s
	diff -q selfie.m selfie-giblib.m
	diff -q selfie.s selfie-giblib.s

# Test garbage collector as library
gclibtest: selfie selfie.h examples/garbage_collector_test.c
	./selfie -gc -c selfie.h examples/garbage_collector_test.c -m 1

# Compile babysat.c with selfie.h as library into babysat executable
babysat: tools/babysat.c selfie.h
	$(CC) $(CFLAGS) --include selfie.h $< -o $@

# Run babysat, the naive SAT solver, natively and as RISC-U executable
sat: babysat selfie selfie.h
	./babysat examples/rivest.cnf
	./selfie -c selfie.h tools/babysat.c -m 1 examples/rivest.cnf

# Compile monster.c with selfie.h as library into monster executable
monster: tools/monster.c selfie.h
	$(CC) $(CFLAGS) --include selfie.h $< -o $@

# Run monster, the symbolic execution engine, natively and as RISC-U executable
mon: monster selfie.h selfie
	./monster
	./selfie -c selfie.h tools/monster.c -m 1

# Prevent make from deleting intermediate target monster
.SECONDARY: monster

# Translate *.c including selfie.c into SMT-LIB model
%-35.smt: %-35.c monster
	./monster -c $< - 0 35 --merge-enabled
%-10.smt: %-10.c monster
	./monster -c $< - 0 10 --merge-enabled

# Gather symbolic execution example files as .smt files
smts-1 := $(patsubst %.c,%.smt,$(wildcard examples/symbolic/*-1-*.c))
smts-2 := $(patsubst %.c,%.smt,$(wildcard examples/symbolic/*-2-*.c))
smts-3 := $(patsubst %.c,%.smt,$(wildcard examples/symbolic/*-3-*.c))

# Run monster on *.c files in symbolic
smt: $(smts-1) $(smts-2) $(smts-3)

# Compile modeler.c with selfie.h as library into modeler executable
modeler: tools/modeler.c selfie.h
	$(CC) $(CFLAGS) --include selfie.h $< -o $@

# Run modeler, the symbolic model generator, natively and as RISC-U executable
mod: modeler selfie.h selfie
	./modeler
	./selfie -c selfie.h tools/modeler.c -m 1

# Prevent make from deleting intermediate target modeler
.SECONDARY: modeler

# Translate *.c including selfie.c into BTOR2 model
%.btor2: %.c modeler
	./modeler -c $< - 0 --check-block-access

# Gather symbolic execution example files as .btor2 files
btor2s := $(patsubst %.c,%.btor2,$(wildcard examples/symbolic/*.c))

# Run modeler on *.c files in symbolic and even on selfie
btor2: $(btor2s) selfie.btor2

# Compile riscv-2-x86.c with selfie.h as library into riscv-2-x86 executable
riscv-2-x86: tools/riscv-2-x86.c selfie.h
	$(CC) $(CFLAGS) --include selfie.h $< -o $@

# Run RISC-V-to-x86 translator natively and as RISC-U executable
selfie-2-x86: riscv-2-x86 selfie selfie.h selfie.m
	./riscv-2-x86 -c selfie.c
	mv selfie.x86 selfie1.x86
	./selfie -c selfie.h tools/riscv-2-x86.c -m 1 -l selfie.m
	diff -q selfie.x86 selfie1.x86

# Run everything that only requires standard tools
all: self self-self quine debug replay os vm min mob gib gclib giblib gclibtest sat mon smt mod btor2 selfie-2-x86

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
	spike pk selfie.m -c selfie.c -o selfie-spike.m -s selfie-spike.s -m 1
	diff -q selfie.m selfie-spike.m
	diff -q selfie.s selfie-spike.s

# Run selfie on qemu usermode emulation
qemu: selfie.m selfie.s
	chmod +x selfie.m
	qemu-riscv64-static selfie.m -c selfie.c -o selfie-qemu.m -s selfie-qemu.s -m 1
	diff -q selfie.m selfie-qemu.m
	diff -q selfie.s selfie-qemu.s

x86: selfie-2-x86 selfie.m selfie.s selfie.h
	chmod +x selfie.x86
	./selfie.x86 -c selfie.c -o selfie-x86.m -s selfie-x86.s
	diff -q selfie.m selfie-x86.m
	diff -q selfie.s selfie-x86.s
	./selfie.x86 -c selfie.h tools/riscv-2-x86.c -m 1 -l selfie-x86.m
	diff -q selfie.x86 selfie-x86.x86

# Run boolector SMT solver on SMT-LIB files generated by monster
boolector: smt
	$(foreach file, $(smts-1), [ $$(boolector $(file) -e 0 | grep -c ^sat$$) -eq 1 ] &&) true
	$(foreach file, $(smts-2), [ $$(boolector $(file) -e 0 | grep -c ^sat$$) -eq 2 ] &&) true
	$(foreach file, $(smts-3), [ $$(boolector $(file) -e 0 | grep -c ^sat$$) -eq 3 ] &&) true

# Run btormc bounded model checker on BTOR2 files generated by modeler
btormc: btor2
	$(foreach file, $(btor2s), btormc $(file) &&) true

# files where validator fails (e.g. timeout) and succeeds
failingFiles := $(wildcard examples/symbolic/*-fail-*.c)
succeedFiles := $(filter-out $(failingFiles),$(wildcard examples/symbolic/*.c))

# Run validator on *.c files in symbolic
validator: selfie modeler
	$(foreach file, $(succeedFiles), tools/validator.py $(file) &&) true
	$(foreach file, $(failingFiles), ! tools/validator.py $(file) &&) true

# Run everything that requires non-standard tools
extras: assemble spike qemu x86 boolector btormc validator grader grade

# Run everything
everything: all extras

# Clean up
clean:
	rm -f *.m
	rm -f *.s
	rm -f *.smt
	rm -f *.btor2
	rm -f *.x86
	rm -f selfie selfie.h selfie.exe
	rm -f babysat gc monster modeler riscv-2-x86
	rm -f examples/*.m
	rm -f examples/*.s
	rm -f examples/symbolic/*.smt
	rm -f examples/symbolic/*.btor2
