# Copyright (c) the Selfie Project authors. All rights reserved.
# Please see the AUTHORS file for details. Use of this source code is governed
# by a BSD license that can be found in the LICENSE file.

# Selfie is a project of the Computational Systems Group at the Department of
# Computer Sciences of the University of Salzburg in Austria. For further
# information and code please refer to:

# selfie.cs.uni-salzburg.at

# This is the Makefile of the selfie system.

# Compiler flags
CFLAGS := -Wall -Wextra -O3 -D'uint64_t=unsigned long'

# Bootstrap selfie.c into selfie executable
selfie: selfie.c
	$(CC) $(CFLAGS) $< -o $@

# 32-bit compiler flags
32-BIT-CFLAGS := -Wall -Wextra -Wno-builtin-declaration-mismatch -O3 -m32 -D'uint64_t=unsigned long'

# Bootstrap selfie.c into 32-bit selfie executable, requires 32-bit compiler support
selfie-32: selfie.c
	$(CC) $(32-BIT-CFLAGS) $< -o $@

# Compile *.c including selfie.c into RISC-U *.m executable
%.m: %.c selfie
	./selfie -c $< -o $@

# Compile *.c including selfie.c into RISC-U *.s assembly
%.s: %.c selfie
	./selfie -c $< -s $@

# Generate selfie library as selfie.h
selfie.h: selfie.c
	sed 's/main(/selfie_main(/' selfie.c > selfie.h

# Generate selfie library with gc interface as selfie-gc.h
selfie-gc.h: selfie.c
	sed 's/gc_init(uint64_t\* context) {/gc_init_deleted(uint64_t\* context) {/' selfie.c > selfie-gc-intermediate.h
	sed 's/allocate_memory(uint64_t\* context, uint64_t size) {/allocate_memory_deleted(uint64_t\* context, uint64_t size) {/' selfie-gc-intermediate.h > selfie-gc.h
	sed 's/mark_block(uint64_t\* context, uint64_t address) {/mark_block_deleted(uint64_t\* context, uint64_t address) {/' selfie-gc.h > selfie-gc-intermediate.h
	sed 's/sweep(uint64_t\* context) {/sweep_deleted(uint64_t\* context) {/' selfie-gc-intermediate.h > selfie-gc.h
	sed 's/allocate_context() {/allocate_context_deleted() {/' selfie-gc.h > selfie-gc-intermediate.h
	mv selfie-gc-intermediate.h selfie-gc.h

# Generate selfie library with gc interface as selfie-gc-nomain.h
selfie-gc-nomain.h: selfie-gc.h
	sed 's/main(/selfie_main(/' selfie-gc.h > selfie-gc-nomain.h

# Consider these targets as targets, not files
.PHONY: self self-self self-self-check 64-to-32-bit \
		whitespace quine escape debug replay \
		emu emu-emu emu-emu-emu emu-vmm-emu os-emu os-vmm-emu overhead \
		self-emu self-os-emu self-os-vmm-emu min mob \
		gib gclib giblib gclibtest boehmgc cache less

# Run less that only requires standard tools and is not too slow
less: self self-self self-self-check 64-to-32-bit \
		whitespace quine escape debug replay \
		emu emu-emu emu-vmm-emu os-emu os-vmm-emu \
		self-emu self-os-emu self-os-vmm-emu min mob \
		gib gclib giblib gclibtest boehmgc cache

# Self-compile selfie
self: selfie
	./selfie -c selfie.c

# Self-self-compile selfie
self-self: selfie
	./selfie -c selfie.c -m 3 -c selfie.c

# Self-self-compile selfie and check fixed point of self-compilation
self-self-check: selfie
	./selfie -c selfie.c -o selfie0.m -s selfie0.s -m 3 -c selfie.c -o selfie1.m -s selfie1.s
	diff -q selfie0.m selfie1.m
	diff -q selfie0.s selfie1.s

# Self-self-compile selfie from 64-bit system to 32-bit target and check fixed point of self-compilation
64-to-32-bit: selfie
	./selfie -m32 -c selfie.c -o selfie-64-2-32.m -s selfie-64-2-32.s -m 4 -c selfie.c -o selfie-64-2-32-2-32.m -s selfie-64-2-32-2-32.s
	diff -q selfie-64-2-32.m selfie-64-2-32-2-32.m
	diff -q selfie-64-2-32.s selfie-64-2-32-2-32.s

# Compile Hello World! program and identical but minified version
whitespace: selfie
	./selfie -c examples/hello-world.c -o examples/hello-world.m -s examples/hello-world.s \
	         -c examples/hello-world-minified.c -o examples/hello-world-minified.m -s examples/hello-world-minified.s
	diff -q examples/hello-world.m examples/hello-world-minified.m
	diff -q examples/hello-world.s examples/hello-world-minified.s
	./selfie -l examples/hello-world.m -m 1

# Compile and run quine and compare its output to itself
quine: selfie selfie.h
	./selfie -c selfie.h examples/quine.c -m 1 | sed '/selfie/d' | awk '/./' | diff --strip-trailing-cr examples/quine.c -

# Demonstrate available escape sequences
escape: selfie
	./selfie -c examples/escape.c -m 1

# Run debugger
debug: selfie
	./selfie -c examples/pointer.c -d 1

# Run replay engine
replay: selfie
	./selfie -c examples/division-by-zero.c -r 1

# Run selfie on emulator
emu: selfie selfie.m
	./selfie -l selfie.m -m 1

# Run selfie on emulator on emulator
emu-emu: selfie selfie.m
	./selfie -l selfie.m -m 3 -l selfie.m -m 1

# Run selfie on emulator on emulator on emulator, warning: slow!
emu-emu-emu: selfie selfie.m
	./selfie -l selfie.m -m 5 -l selfie.m -m 3 -l selfie.m -m 1

# Run selfie on emulator on hypervisor on emulator
emu-vmm-emu: selfie selfie.m
	./selfie -l selfie.m -m 4 -l selfie.m -y 3 -l selfie.m -m 1

# Run selfie on os on emulator
os-emu: selfie selfie.m
	./selfie -l selfie.m -m 2 -l selfie.m -y 1

# Run selfie on os on hypervisor on emulator
os-vmm-emu: selfie selfie.m
	./selfie -l selfie.m -m 3 -l selfie.m -y 2 -l selfie.m -y 1

# Determine overhead of timer interrupts and context switching
overhead: selfie selfie.m
	./selfie -l selfie.m -m 2 -l selfie.m -c examples/overhead.c -y 1

# Self-compile on emulator
self-emu: selfie selfie.m selfie.s
	./selfie -l selfie.m -m 3 -c selfie.c -o selfie-emu.m -s selfie-emu.s
	diff -q selfie.m selfie-emu.m
	diff -q selfie.s selfie-emu.s

# Self-compile on os on emulator
self-os-emu: selfie selfie.m selfie.s
	./selfie -l selfie.m -m 4 -l selfie.m -y 3 -c selfie.c -o selfie-os.m -s selfie-os.s
	diff -q selfie.m selfie-os.m
	diff -q selfie.s selfie-os.s

# Self-compile on os on hypervisor
self-os-vmm-emu: selfie selfie.m selfie.s
	./selfie -l selfie.m -m 5 -l selfie.m -y 4 -l selfie.m -y 3 -c selfie.c -o selfie-vmm.m -s selfie-vmm.s
	diff -q selfie.m selfie-vmm.m
	diff -q selfie.s selfie-vmm.s

# Self-compile on os on hypervisor on fully mapped virtual memory
min: selfie selfie.m selfie.s
	./selfie -l selfie.m -min 4 -l selfie.m -y 4 -l selfie.m -y 3 -c selfie.c -o selfie-min.m -s selfie-min.s
	diff -q selfie.m selfie-min.m
	diff -q selfie.s selfie-min.s

# Run mobster, the emulator without pager
mob: selfie
	./selfie -c -mob 1

# Self-compile with garbage collector in mipster
gib: selfie selfie.m selfie.s
	./selfie -l selfie.m -gc -m 1 -c selfie.c -o selfie-gib.m -s selfie-gib.s
	diff -q selfie.m selfie-gib.m
	diff -q selfie.s selfie-gib.s

# Self-compile with garbage collector in hypster
hyb: selfie selfie.m selfie.s
	./selfie -l selfie.m -m 3 -l selfie.m -gc -y 1 -c selfie.c -o selfie-hyb.m -s selfie-hyb.s
	diff -q selfie.m selfie-hyb.m
	diff -q selfie.s selfie-hyb.s

# Self-self-compile with garbage collector as library
gclib: selfie selfie.h selfie.m selfie.s tools/gc-lib.c
	./selfie -gc -c selfie.h tools/gc-lib.c -m 3 -c selfie.c -o selfie-gclib.m -s selfie-gclib.s
	diff -q selfie.m selfie-gclib.m
	diff -q selfie.s selfie-gclib.s

# Self-self-compile with self-collecting garbage collectors
giblib: selfie selfie.h selfie.m selfie.s tools/gc-lib.c
	./selfie -gc -c selfie.h tools/gc-lib.c -gc -m 3 -nr -c selfie.c -o selfie-giblib.m -s selfie-giblib.s
	diff -q selfie.m selfie-giblib.m
	diff -q selfie.s selfie-giblib.s

# Test garbage collector as library
gclibtest: selfie selfie.h examples/gc/gc-test.c
	./selfie -gc -c selfie.h examples/gc/gc-test.c -m 1

# Self-self-compile with Boehm garbage collector
boehmgc: selfie selfie-gc.h selfie-gc-nomain.h tools/boehm-gc.c tools/gc-lib.c examples/gc/boehm-gc-test.c
	./selfie -c selfie-gc.h tools/boehm-gc.c -o selfie-boehm-gc.m -gc -m 2 -c selfie-gc.h tools/boehm-gc.c -gc -m 1
	./selfie -l selfie-boehm-gc.m -m 6 -l selfie-boehm-gc.m -gc -y 2 -c selfie-gc.h tools/boehm-gc.c -gc -m 2
	./selfie -gc -c selfie-gc-nomain.h tools/boehm-gc.c tools/gc-lib.c -m 3 -c selfie.c -gc -m 1
	./selfie -gc -c selfie-gc-nomain.h tools/boehm-gc.c tools/gc-lib.c -gc -m 3 -nr -c selfie.c -gc -m 1
	./selfie -gc -c selfie-gc-nomain.h tools/boehm-gc.c examples/gc/boehm-gc-test.c -m 1

# Self-compile with L1 cache and test L1 data cache
cache: selfie selfie.m selfie.s examples/cache/dcache-access-[01].c
	./selfie -l selfie.m -L1 2 -c selfie.c -o selfie-L1.m -s selfie-L1.s
	diff -q selfie.m selfie-L1.m
	diff -q selfie.s selfie-L1.s
	./selfie -c examples/cache/dcache-access-0.c -L1 32
	./selfie -c examples/cache/dcache-access-1.c -L1 32

# Consider these targets as targets, not files
.PHONY: sat brr bzz mon smt beat beator-btor2 rot synthesize rotor-btor2 btor2 more all

# Run more that only requires standard tools and is not too slow
more: sat brr bzz mon smt beat beator-btor2 rot synthesize rotor-btor2 trust reversible

# Run all that only requires standard tools and is not too slow
all: less more

# Compile babysat.c with selfie.h as library into babysat executable
babysat: tools/babysat.c selfie.h
	$(CC) $(CFLAGS) --include selfie.h $< -o $@

# Run babysat, the naive SAT solver, natively and as RISC-U executable
sat: babysat selfie selfie.h
	./babysat examples/sat/rivest.cnf
	./selfie -c selfie.h tools/babysat.c -m 1 examples/sat/rivest.cnf

# Compile buzzr.c with selfie.h as library into buzzr executable
buzzr: tools/buzzr.c selfie.h
	$(CC) $(CFLAGS) --include selfie.h $< -o $@

# Run buzzr, the symbolic execution engine, natively and as RISC-U executable on itself
brr: buzzr selfie.h selfie
	./buzzr -c selfie.h tools/buzzr.c - 1
	./selfie -c selfie.h tools/buzzr.c -m 2 -c selfie.h tools/buzzr.c - 1

# Prevent make from deleting intermediate target buzzr
.SECONDARY: buzzr

# Buzz *-35.c and *-10.c files
%-35.bzz: %-35.c buzzr
	./buzzr -c $< - 10
%-10.bzz: %-10.c buzzr
	./buzzr -c $< - 10

# Gather symbolic execution example files as .bzz files
bzz-1 := $(patsubst %.c,%.bzz,$(wildcard examples/symbolic/*-1-*.c))
bzz-2 := $(patsubst %.c,%.bzz,$(wildcard examples/symbolic/*-2-*.c))
bzz-3 := $(patsubst %.c,%.bzz,$(wildcard examples/symbolic/*-3-*.c))

# Run buzzr on *.c files in symbolic folder
bzz: $(bzz-1) $(bzz-2) $(bzz-3)

# Compile monster.c with selfie.h as library into monster executable
monster: tools/monster.c selfie.h
	$(CC) $(CFLAGS) --include selfie.h $< -o $@

# Run monster, the symbolic execution engine, natively and as RISC-U executable on itself
mon: monster selfie.h selfie
	./monster -c selfie.h tools/monster.c - 0 10
	./selfie -c selfie.h tools/monster.c -m 3 -c selfie.h tools/monster.c - 0 10
# output differs slightly because of different filenames

# Prevent make from deleting intermediate target monster
.SECONDARY: monster

# Translate *-35.c and *-10.c files into SMT-LIB model
%-35.smt: %-35.c monster
	./monster -c $< - 0 35 --merge-enabled
%-10.smt: %-10.c monster
	./monster -c $< - 0 10 --merge-enabled

# Gather symbolic execution example files as .smt files
smts-1 := $(patsubst %.c,%.smt,$(wildcard examples/symbolic/*-1-*.c))
smts-2 := $(patsubst %.c,%.smt,$(wildcard examples/symbolic/*-2-*.c))
smts-3 := $(patsubst %.c,%.smt,$(wildcard examples/symbolic/*-3-*.c))

# Run monster on *.c files in symbolic folder
smt: $(smts-1) $(smts-2) $(smts-3)

# Compile beator.c with selfie.h as library into beator executable
beator: tools/beator.c selfie.h
	$(CC) $(CFLAGS) --include selfie.h $< -o $@

# Run beator, the RISC-U symbolic model generator, natively on itself and as RISC-U executable
beat: beator selfie.h selfie
	./beator -c selfie.h tools/beator.c - 0 --check-block-access
	./selfie -c selfie.h tools/beator.c -m 1
# RISC-U executable also works on itself but output differs slightly
# because of different filenames and values of a6 register

# Prevent make from deleting intermediate target beator
.SECONDARY: beator

# Translate *.c including selfie.c into BTOR2 model using beator
%-beaten.btor2: %.c beator
	./beator -c $< - 0 --check-block-access

# Gather symbolic execution example files as .btor2 files generated by beator
beators := $(patsubst %.c,%-beaten.btor2,$(wildcard examples/symbolic/*.c))

# Run beator on *.c files in symbolic folder and even on selfie
beator-btor2: $(beators) selfie-beaten.btor2

# Compile rotor.c with selfie.h and btor2.h as libraries into rotor executable
rotor: tools/rotor.c tools/btor2.h selfie.h
	$(CC) $(CFLAGS) --include selfie.h --include tools/btor2.h $< -o $@

# Invoke rotor with arguments in arch and rotor variables
arch = -m64
rotor = 0

# Run rotor, the RISC-V symbolic model generator, natively on itself and as RISC-U executable
rot: rotor selfie.h selfie
	./rotor -c selfie.h tools/btor2.h tools/rotor.c - $(rotor)
	./selfie -c selfie.h tools/btor2.h tools/rotor.c -m 1
# RISC-U executable also works on itself but output differs slightly
# because of different filenames and values of a6 register

# Prevent make from deleting intermediate target rotor
.SECONDARY: rotor

# Translate *.c including selfie.c into BTOR2 model using rotor
%-rotorized.btor2: %.c rotor
	./rotor $(arch) -c $< - $(rotor)

# Run rotor to generate 64-bit RISC-V machine model for synthesizing exit system call wrapper
64-bit-riscv-machine-synthesize.btor2: rotor
	./rotor - $(rotor)

# Run rotor to generate 32-bit RISC-V machine model for synthesizing exit system call wrapper
32-bit-riscv-machine-synthesize.btor2: rotor
	./rotor -m32 - $(rotor)

# Run rotor to generate 64-bit and 32-bit RISC-V machine models for synthesizing exit system call wrapper
synthesize: 64-bit-riscv-machine-synthesize.btor2 32-bit-riscv-machine-synthesize.btor2

# Gather symbolic execution example files as .btor2 files generated by rotor
rotors := $(patsubst %.c,%-rotorized.btor2,$(wildcard examples/symbolic/*.c))

# Run rotor on *.c files in symbolic folder and even on selfie as well as to generate RISC-V machine models for code synthesis
rotor-btor2: $(rotors) selfie-rotorized.btor2 synthesize

# Run beator and rotor on *.c files in symbolic folder and even on selfie
btor2: beator-btor2 rotor-btor2

# Generate selfie library for riscr as selfie-riscr.h: riscr wraps the three procedures
# of the scanner and the parser that it extends by compound assignments, see tools/riscr.c
selfie-riscr.h: selfie.c
	sed -e 's/main(/selfie_main(/' \
	    -e 's/^char find_next_character() {/char selfie_find_next_character() {/' \
	    -e 's/^void get_symbol() {/void selfie_get_symbol() {/' \
	    -e 's/^void compile_assignment(char\* variable) {/void selfie_compile_assignment(char* variable) {/' \
	    -e 's/^void compile_statement() {/void selfie_compile_statement() {/' selfie.c > selfie-riscr.h

# Compile riscr.c with selfie-riscr.h as library into riscr executable
riscr: tools/riscr.c selfie-riscr.h
	$(CC) $(CFLAGS) --include selfie-riscr.h $< -o $@

# Generate riscr library as riscr.h
riscr.h: tools/riscr.c
	sed 's/main(/riscr_main(/' tools/riscr.c > riscr.h

# Compile riscr-test.c with selfie-riscr.h and riscr.h as libraries into riscr-test executable
riscr-test: tests/riscr-test.c selfie-riscr.h riscr.h
	$(CC) $(CFLAGS) --include selfie-riscr.h --include riscr.h $< -o $@

# Run riscr-test, hand-written RISC-R code executed forward and backward on riscr, natively and as RISC-U executable,
# and check that mipster refuses RISC-R binaries
rev: riscr-test selfie selfie-riscr.h riscr.h
	echo "RISC-R" | ./riscr-test tests/riscr-test.m
	echo "RISC-R" | ./selfie -c selfie-riscr.h riscr.h tests/riscr-test.c -m 64 tests/riscr-test-emu.m
	! ./selfie -l tests/riscr-test.m -m 1

# Prevent make from deleting intermediate target riscr-test
.SECONDARY: riscr-test

# Run riscr executing RISC-R code forward and backward, natively and as RISC-U executable, exit code is the first input byte plus 14
riscr-rev: riscr selfie selfie-riscr.h rev
	-echo "RISC-R" | ./riscr -l tests/riscr-test.m -rev 1
	-echo "RISC-R" | ./selfie -c selfie-riscr.h tools/riscr.c -m 16 -l tests/riscr-test.m -rev 1

# Garbage-free assignments: riscr compiles x += e, x -= e, and x ^= e without
# history. The test program exits natively, compiled by gcc, as on riscr, forward and backward; it leaves the
# history pointer where the same program without its compound assignments leaves it; the RISC-U binary that
# riscr writes translates to the same RISC-R binary, and so does riscr on mipster; what cannot be uncomputed,
# an expression that reads the variable assigned to or calls a procedure, is a syntax error
garbage-free: riscr selfie selfie-riscr.h
	$(CC) -w -D'uint64_t=unsigned long' tests/riscr-compound-test.c -o riscr-compound-test
	./riscr-compound-test; e=$$?; \
	./riscr -c tests/riscr-compound-test.c -o tests/riscr-compound-test.m -t tests/riscr-compound-test.r -rev 1 | tee riscr-compound-test.txt; \
	grep -q "with exit code $$e$$" riscr-compound-test.txt
	grep -q "initial state restored bit for bit" riscr-compound-test.txt
	grep -v "// garbage-free" tests/riscr-compound-test.c > tests/riscr-compound-base.c
	h=$$(sed -n 's/.*the history pointer of translated code, is \(.*\)/\1/p' riscr-compound-test.txt); \
	b=$$(./riscr -c tests/riscr-compound-base.c -t tests/riscr-compound-base.r -rev 1 | sed -n 's/.*the history pointer of translated code, is \(.*\)/\1/p'); \
	[ -n "$$h" ] && [ "$$h" = "$$b" ] || { echo "history pointer at $$h, without compound assignments at $$b"; exit 1; }; \
	echo "history pointer at $$h with and without compound assignments"
	./riscr -l tests/riscr-compound-test.m -t tests/riscr-compound-file.r > /dev/null
	cmp tests/riscr-compound-test.r tests/riscr-compound-file.r
	./selfie -c selfie-riscr.h tools/riscr.c -m 64 -c tests/riscr-compound-test.c -t tests/riscr-compound-file.r > /dev/null
	cmp tests/riscr-compound-test.r tests/riscr-compound-file.r
	printf 'uint64_t main() { uint64_t x; x = 1; x += x + 1; return x; }\n' > tests/riscr-compound-base.c
	./riscr -c tests/riscr-compound-base.c | grep -q "variable occurs on the right of its own compound assignment"
	printf 'uint64_t f() { return 1; }\nuint64_t main() { uint64_t x; x = 1; x -= f(); return x; }\n' > tests/riscr-compound-base.c
	./riscr -c tests/riscr-compound-base.c | grep -q "procedure call in a compound assignment"
	@echo "$@: compound assignments compute as in C and leave no history"

# Run rotor to generate the 64-bit RISC-R machine model forward and inverse, and
# check on random states that inverse after forward and forward after inverse are the identity
riscr-model: rotor
	./rotor - 0 -riscr
	./rotor - 0 -riscr -inverse
	./rotor - 0 -riscr -roundtrip 100000

# Compile bitr.c with selfie.h and btor2.h as libraries into bitr executable
bitr: tools/bitr.c tools/btor2.h selfie.h
	$(CC) $(CFLAGS) --include selfie.h --include tools/btor2.h $< -o $@

# Check bitr's simulator against mipster and riscr: every symbolic example,
# compiled to RISC-U and translated to RISC-R with a 1MB history stack, reads tests/bitr-input.txt and must
# stop in rotor's model of it with the emulator's exit code after the emulator's number of instructions, or,
# if the emulator throws an exception, with a bad state after that number of instructions
sim: bitr selfie riscr rotor
	for f in $(wildcard examples/symbolic/*.c); do \
	  b=$${f%.c}; \
	  ./selfie -c $$f -o $$b.m > /dev/null && \
	  ./riscr -l $$b.m -history 1 -t $$b.r > /dev/null || exit 1; \
	  for x in m r; do \
	    if [ $$x = m ]; then run="./selfie -l $$b.m -m 1"; model=$$b-rotorized.btor2; \
	    else run="./riscr -l $$b.r -m 1"; model=$$b-rotorized-riscr.btor2; fi; \
	    out=$$($$run < tests/bitr-input.txt 2>&1); \
	    e=$$(echo "$$out" | sed -n 's/.*with exit code \([0-9]*\).*/\1/p'); \
	    n=$$(echo "$$out" | sed -n 's/.*summary: \([0-9]*\) executed instructions.*/\1/p'); \
	    ./rotor -l $$b.$$x - $$e -heapallowance 2097152 -stackallowance 65536 > /dev/null || exit 1; \
	    if [ $$e -lt 11 ]; then expected="bad core-0-bad-exit-code after $$n instructions"; \
	    else expected="after $$((n + 1)) instructions"; fi; \
	    ./bitr $$model -l $$b.$$x -i tests/bitr-input.txt | grep -q "$$expected" || \
	      { echo "$$model: bitr disagrees with emulator, expected $$expected"; exit 1; }; \
	    echo "$$model: exit code $$e after $$n instructions as in emulator"; \
	  done; \
	done

# A loop without history, the bit-length loop: the loop with compound assignments and from, and the loop as
# C* has it, each read a byte with 8 bits and with 1 bit, exit as compiled by gcc, for which from(e) is
# nothing, and run back; the first leaves the history pointer where it is whatever the number of iterations,
# the second does not; riscr on mipster translates the first to the same binary
bit-length: selfie riscr selfie-riscr.h
	printf '\265' > tests/riscr-bitlength-8.txt
	printf '\1' > tests/riscr-bitlength-1.txt
	for t in tests/riscr-bitlength-test tests/riscr-bitlength-history-test; do \
	  $(CC) -w -D'uint64_t=unsigned long' -D'from(e)=' $$t.c -o riscr-bitlength-test || exit 1; \
	  for i in 8 1; do \
	    ./riscr-bitlength-test < tests/riscr-bitlength-$$i.txt; e=$$?; \
	    ./riscr -c $$t.c -history 1 -t $$t.r -rev 1 < tests/riscr-bitlength-$$i.txt > riscr-bitlength-test.txt; \
	    [ $$e = $$i ] && grep -q "with exit code $$e$$" riscr-bitlength-test.txt && \
	    grep -q "initial state restored bit for bit" riscr-bitlength-test.txt || \
	      { echo "$$t: wrong exit code or not reversed for $$i bits"; exit 1; }; \
	    eval h$$i=$$(sed -n 's/.*the history pointer of translated code, is \(.*\)/\1/p' riscr-bitlength-test.txt); \
	  done; \
	  echo "$$t: history pointer at $$h8 after 8 iterations and at $$h1 after 1"; \
	  if [ $$t = tests/riscr-bitlength-test ]; then [ "$$h8" = "$$h1" ] || exit 1; else [ "$$h8" != "$$h1" ] || exit 1; fi; \
	done
	./riscr -c tests/riscr-bitlength-test.c -history 1 -t tests/riscr-bitlength-test.r | grep "loop without history"
	./selfie -c selfie-riscr.h tools/riscr.c -m 64 -c tests/riscr-bitlength-test.c -history 1 -t tests/riscr-bitlength-file.r > /dev/null
	cmp tests/riscr-bitlength-test.r tests/riscr-bitlength-file.r
	echo "$@: the loop leaves no history, whatever the number of iterations"

# Check bitr's bounded model checker: in rotor's model of every symbolic example,
# compiled to RISC-U and translated to RISC-R, bitr finds an input that leads to a non-zero exit code, a division
# by zero, or an invalid memory access, and the emulator, run on that input, does the same after the same number
# of instructions; on one example bitr then enumerates all such inputs and proves that all others halt
bmc: bitr selfie riscr rotor
	for f in $(wildcard examples/symbolic/*.c); do \
	  b=$${f%.c}; \
	  ./selfie -c $$f -o $$b.m > /dev/null && \
	  ./riscr -l $$b.m -history 1 -t $$b.r > /dev/null || exit 1; \
	  for x in m r; do \
	    if [ $$x = m ]; then run="./selfie -l $$b.m -m 1"; model=$$b-rotorized-riscuonly.btor2; isa=-riscuonly; \
	    else run="./riscr -l $$b.r -m 1"; model=$$b-rotorized-riscr.btor2; isa=; fi; \
	    ./rotor -l $$b.$$x - 0 -Pnobadexitcode -Pgoodexitcode -heapallowance 2097152 -stackallowance 65536 $$isa > /dev/null || exit 1; \
	    bad=$$(./bitr $$model -l $$b.$$x -bmc 5000 -w $$b.witness | sed -n 's/.*: bad core-0-\([a-z-]*\) after \([0-9]*\) instructions/\1 \2/p' | head -1); \
	    [ -n "$$bad" ] || { echo "$$model: no bad state found"; exit 1; }; \
	    out=$$($$run < $$b.witness 2>&1); \
	    e=$$(echo "$$out" | sed -n 's/.*with exit code \([0-9]*\).*/\1/p'); \
	    n=$$(echo "$$out" | sed -n 's/.*summary: \([0-9]*\) executed instructions.*/\1/p'); \
	    case "$$bad" in \
	      good-exit-code*) [ $$e -gt 0 ] && [ $$e -lt 11 ] && [ "$${bad#* }" = $$n ] ;; \
	      division-by-zero*) [ $$e = 22 ] && [ "$${bad#* }" = $$n ] ;; \
	      *) [ $$e = 27 ] && [ "$${bad#* }" = $$((n + 1)) ] ;; \
	    esac || { echo "$$model: witness does not replay: bitr found $$bad, emulator exits with $$e after $$n instructions"; exit 1; }; \
	    echo "$$model: $$bad instructions, replayed in emulator with exit code $$e"; \
	  done; \
	done
	./bitr examples/symbolic/division-by-zero-3-35-rotorized-riscuonly.btor2 -l examples/symbolic/division-by-zero-3-35.m -bmc 5000 -all | tee division-by-zero.bmc
	[ $$(grep -c "bad core-0-division-by-zero" division-by-zero.bmc) = 2 ]
	[ $$(grep -c "bad core-0-good-exit-code" division-by-zero.bmc) = 1 ]
	grep -q "halted after 107 instructions on all inputs that reach no bad state" division-by-zero.bmc

# CDCL and babysat agree: on the instances in examples/sat and on every CNF with
# at most 100 variables that bitr generates when model checking the symbolic examples, which is as far as
# babysat's enumeration reaches
cdcl: bitr babysat selfie rotor
	rm -f examples/symbolic/*.cnf
	for f in $(wildcard examples/symbolic/*.c); do \
	  b=$${f%.c}; \
	  out=$$(./selfie -c $$f -o $$b.m 2>&1 && \
	    ./rotor -l $$b.m - 0 -Pnobadexitcode -Pgoodexitcode -riscuonly 2>&1 && \
	    ./bitr $$b-rotorized-riscuonly.btor2 -l $$b.m -bmc 300 -all -dimacs $$b 100 2>&1) || \
	    { echo "$$out" | tail -n 20; echo "$$b: no CNF files"; exit 1; }; \
	done
	n=0; for f in examples/sat/*.cnf examples/symbolic/*.cnf; do \
	  a=$$(./babysat $$f | grep -o "is [un]*satisfiable"); \
	  c=$$(./bitr -sat $$f | grep -o "is [un]*satisfiable"); \
	  [ -n "$$a" ] && [ "$$a" = "$$c" ] || { echo "$$f: babysat says it $$a, CDCL says it $$c"; exit 1; }; \
	  n=$$((n + 1)); \
	done; echo "$@: babysat and CDCL agree on $$n instances"

# Inverse after forward is the identity: proven symbolically by bitr for one step
# of the RISC-R machine model from every state that satisfies the model's constraints, and forward after inverse
# as well; more steps follow by induction, each step of a run that reaches no bad state satisfies the constraints
identity: bitr rotor
	./rotor - 0 -riscr > /dev/null
	./rotor - 0 -riscr -inverse > /dev/null
	./bitr 64-bit-riscr-machine.btor2 -identity 64-bit-riscr-machine-inverse.btor2 | tee riscr-identity.txt
	grep -q "64-bit-riscr-machine-inverse.btor2 after 64-bit-riscr-machine.btor2 is the identity on all 20 states" riscr-identity.txt
	./bitr 64-bit-riscr-machine-inverse.btor2 -identity 64-bit-riscr-machine.btor2 | tee riscr-identity.txt
	grep -q "64-bit-riscr-machine.btor2 after 64-bit-riscr-machine-inverse.btor2 is the identity on all 20 states" riscr-identity.txt
	@echo "$@: the inverse RISC-R machine model undoes the forward model and the forward model the inverse, on all states"

# Prevent make from deleting intermediate target bitr
.SECONDARY: bitr

# Bennett mode: selfie translated to RISC-R compiles selfie on riscr
# to an identical binary and runs back to its initial state; riscr's translator reaches a fixed point
# on itself; takes about 3GB of memory for the history stack and a few minutes
bennett: riscr selfie selfie.h selfie-riscr.h
	./selfie -c selfie.c -o selfie-u.m
	./riscr -l selfie-u.m -t selfie-r.r -rev 4096 -c selfie.c -o selfie-r.m
	cmp selfie-u.m selfie-r.m
	./selfie -c selfie-riscr.h tools/riscr.c -o riscr-u.m
	./riscr -l riscr-u.m -t riscr-r.r
	./riscr -l riscr-r.r -m 3072 -l riscr-u.m -t riscr-r2.r
	cmp riscr-r.r riscr-r2.r
	@echo "$@: self-compilation reproduced in Bennett mode and reversed, translator at its fixed point"

# trusting-trust: Ken Thompson's compiler trojan and Wheeler's diverse
# double-compiling as a self-checking lesson, see examples/trusting-trust/README.md
trust: selfie selfie.h
# an honest identity compiler reproduces its own source byte for byte
	./selfie -c selfie.h examples/trusting-trust/stamp.c -m 16 examples/trusting-trust/stamp.c examples/trusting-trust/honest-stamp.c
	diff -q examples/trusting-trust/stamp.c examples/trusting-trust/honest-stamp.c
# the victim's own source exits 0 under an honest compiler
	./selfie -c selfie.h examples/trusting-trust/stamp.c -m 16 examples/trusting-trust/victim.c examples/trusting-trust/honest-victim.c
	./selfie -c selfie.h examples/trusting-trust/honest-victim.c -m 1 ; test $$? -eq 0
# the trojaned compiler injects exit code 42, found nowhere in victim.c
	./selfie -c selfie.h examples/trusting-trust/stamp-trojan.c -m 16 examples/trusting-trust/victim.c examples/trusting-trust/trojaned-victim.c
	./selfie -c selfie.h examples/trusting-trust/trojaned-victim.c -m 1 ; test $$? -eq 42
# diverse double-compiling: the suspect's output for clean stamp.c differs from the honest compiler's
	./selfie -c selfie.h examples/trusting-trust/stamp-trojan.c -m 16 examples/trusting-trust/stamp.c examples/trusting-trust/suspect-stamp.c
	! diff -q examples/trusting-trust/honest-stamp.c examples/trusting-trust/suspect-stamp.c
	@echo "$@: trojan detected by diverse double-compiling"
	rm -f examples/trusting-trust/honest-stamp.c examples/trusting-trust/honest-victim.c examples/trusting-trust/trojaned-victim.c examples/trusting-trust/suspect-stamp.c

# Entr, see bitr.md: counts over declared bits

bitr.h: tools/bitr.c
	sed 's/main(/bitr_main(/' tools/bitr.c > bitr.h

entr: tools/entr.c bitr.h tools/btor2.h selfie.h
	$(CC) $(CFLAGS) --include selfie.h --include tools/btor2.h --include bitr.h $< -o $@

# what a count is over: one byte of input, for rotor's RISC-U and RISC-R models,
# and the rest of the open states, which are zero, with one byte on the input tape
over-riscu := -over input-buffer 0 8 -zero input-buffer
over-riscr := -over input-tapes 0 8 -zero input-tapes -fix tape-ends 0 1 -zero tape-ends -zero tape-opens -zero input-buffer

model-options := -Pnobadexitcode -Pgoodexitcode -heapallowance 2097152 -stackallowance 65536

# the families of examples/entropy at the sizes that are checked: family, size, count
families := sum-1-1 sum-2-4 password-1-1 password-2-1 loop-1-1 loop-4-1 branch-1-128 branch-2-16384 factor-1-2

# The reference refuses a model with an open state that is not declared, counts
# what bitr enumerates on the symbolic examples, the same as RISC-U and as RISC-R,
# counts what the families of examples/entropy are built to have, also where a
# program reads twice, a byte each, a word of the tape per read, and runs on mipster
count: entr bitr selfie riscr rotor
	b=examples/symbolic/division-by-zero-3-35; \
	./selfie -c $$b.c -o $$b.m > /dev/null && \
	./rotor -l $$b.m - 0 $(model-options) -riscuonly > /dev/null || exit 1; \
	./entr $$b-rotorized-riscuonly.btor2 -l $$b.m -k 5000 | grep "state input-buffer .* is open" || \
	  { echo "$@: an open state that is not declared is not refused"; exit 1; }
	for f in $(wildcard examples/symbolic/*.c); do \
	  b=$${f%.c}; \
	  ./selfie -c $$f -o $$b.m > /dev/null && \
	  ./riscr -l $$b.m -history 1 -t $$b.r > /dev/null && \
	  ./rotor -l $$b.m - 0 $(model-options) -riscuonly > /dev/null && \
	  ./rotor -l $$b.r - 0 $(model-options) > /dev/null || exit 1; \
	  ./entr $$b-rotorized-riscuonly.btor2 -l $$b.m -k 5000 $(over-riscu) -v > $$b.count || exit 1; \
	  u=$$(sed -n 's/.*: count \(.*\) of 256 worlds.*/\1/p' $$b.count); \
	  r=$$(./entr $$b-rotorized-riscr.btor2 -l $$b.r -k 5000 $(over-riscr) | sed -n 's/.*: count \(.*\) of 256 worlds.*/\1/p'); \
	  [ -n "$$u" ] && [ -n "$$r" ] || { echo "$$b: no count"; exit 1; }; \
	  sed -n 's/.*: world [0-9]*: bad \(.*\) after \([0-9]*\) instructions/\1 \2/p' $$b.count | sort -u > $$b.worlds; \
	  case "$$u$$r" in \
	    *to*) \
	      ./bitr $$b-rotorized-riscuonly.btor2 -l $$b.m -bmc 5000 | sed -n 's/.*: bad \(.*\) after \([0-9]*\) instructions/\1 \2/p' | head -1 > $$b.bitr; \
	      grep -qxF "$$(cat $$b.bitr)" $$b.worlds || { echo "$$b: the bad state bitr finds is in no world"; exit 1; }; \
	      echo "$$b: count $$u as RISC-U and $$r as RISC-R of 256 worlds, open at 5000 instructions, with the bad state bitr finds" ;; \
	    *) \
	      [ "$$u" = "$$r" ] || { echo "$$b: count $$u as RISC-U and $$r as RISC-R"; exit 1; }; \
	      ./bitr $$b-rotorized-riscuonly.btor2 -l $$b.m -bmc 5000 -all > $$b.bitr; \
	      sed -n 's/.*: bad \(.*\) after \([0-9]*\) instructions/\1 \2/p' $$b.bitr | sort -u | comm -13 - $$b.worlds | grep -q . && \
	        { echo "$$b: the reference reaches a bad state that bitr does not"; exit 1; }; \
	      if grep -q "witness input-buffer" $$b.bitr; then \
	        sed -n 's/.*: witness input-buffer\[0\] = \([0-9]*\)/\1/p' $$b.bitr | sort -n > $$b.inputs; \
	        sed -n 's/.*: world \([0-9]*\): bad .*/\1/p' $$b.count | sort -n | cmp -s - $$b.inputs || \
	          { echo "$$b: the inputs bitr enumerates are not the bad worlds of the reference"; exit 1; }; \
	      fi; \
	      echo "$$b: count $$u of 256 worlds as RISC-U and as RISC-R, the inputs bitr enumerates" ;; \
	  esac; \
	done
	for x in $(families); do \
	  f=$${x%%-*}; c=$${x##*-}; n=$${x#*-}; n=$${n%-*}; \
	  b=examples/entropy/$$f-$$n; \
	  sed "s/n = 1; \/\/ size/n = $$n; \/\/ size/" examples/entropy/$$f.c > $$b.c; \
	  case $$f in loop) bytes=1 ;; factor) bytes=$$((2 * n)) ;; *) bytes=$$n ;; esac; \
	  over=; i=0; while [ $$i -lt $$bytes ]; do over="$$over -over input-buffer $$i 8"; i=$$((i + 1)); done; \
	  ./selfie -c $$b.c -o $$b.m > /dev/null && \
	  ./rotor -l $$b.m - 0 -Pnobadexitcode -Pgoodexitcode -heapallowance 4096 -stackallowance 4096 -bytestoread $$bytes -riscuonly > /dev/null || exit 1; \
	  ./entr $$b-rotorized-riscuonly.btor2 -l $$b.m -k 20000 $$over -zero input-buffer | grep "count $$c of " || \
	    { echo "$$b: the count as RISC-U is not $$c"; exit 1; }; \
	  if [ $$bytes = 1 ]; then \
	    ./riscr -l $$b.m -history 1 -t $$b.r > /dev/null && \
	    ./rotor -l $$b.r - 0 $(model-options) > /dev/null || exit 1; \
	    ./entr $$b-rotorized-riscr.btor2 -l $$b.r -k 20000 $(over-riscr) | grep "count $$c of " || \
	      { echo "$$b: the count as RISC-R is not $$c"; exit 1; }; \
	  fi; \
	done
	for x in sum-2-0-0-4 factor-1-156-180-1; do \
	  c=$${x##*-}; b=examples/entropy/$${x%%-*}-$$(echo $$x | cut -d- -f2); first=$$(echo $$x | cut -d- -f3); second=$$(echo $$x | cut -d- -f4); \
	  ./riscr -l $$b.m -history 1 -t $$b.r > /dev/null && \
	  ./rotor -l $$b.m - 0 $(model-options) -bytestoread 2 -riscuonly > /dev/null && \
	  ./rotor -l $$b.r - 0 $(model-options) > /dev/null || exit 1; \
	  ./entr $$b-rotorized-riscuonly.btor2 -l $$b.m -k 20000 -zero input-buffer \
	    -fix input-buffer 0 $$first -over input-buffer 0 2 -fix input-buffer 1 $$second -over input-buffer 1 2 | grep "count $$c of 16 " || \
	    { echo "$$b: the count over two bits of two bytes as RISC-U is not $$c"; exit 1; }; \
	  ./entr $$b-rotorized-riscr.btor2 -l $$b.r -k 20000 -zero input-tapes -fix tape-ends 0 9 -zero tape-ends -zero tape-opens -zero input-buffer \
	    -fix input-tapes 0 $$first -over input-tapes 0 2 -fix input-tapes 1 $$second -over input-tapes 1 2 | grep "count $$c of 16 " || \
	    { echo "$$b: the count over two bits of two bytes as RISC-R is not $$c"; exit 1; }; \
	done
	b=examples/symbolic/division-by-zero-3-35; \
	./rotor -l $$b.m - 0 -Pnobadexitcode -Pgoodexitcode -heapallowance 4096 -stackallowance 4096 -riscuonly > /dev/null || exit 1; \
	./selfie -c selfie.h tools/btor2.h bitr.h tools/entr.c -m 512 $$b-rotorized-riscuonly.btor2 -l $$b.m -k 5000 -fix input-buffer 0 48 -over input-buffer 0 2 -zero input-buffer | tee entr-count.txt; \
	grep -q "count 3 of 4 worlds, entropy 1.58 of 2.00 bits" entr-count.txt || { echo "$@: entr on mipster does not count 3 of the inputs 48 to 51"; exit 1; }

entr.h: tools/entr.c
	sed 's/main(/entr_main(/' tools/entr.c > entr.h

entr-trace: tests/entr-trace.c entr.h bitr.h tools/btor2.h selfie.h
	$(CC) $(CFLAGS) --include selfie.h --include tools/btor2.h --include bitr.h --include entr.h $< -o $@

# The loop on the formulas of examples/sat and on the formulas that model
# checking the symbolic examples generates, as make cdcl does. For every setting
# of the switches the ledger accounts for all worlds and the trace replays to the
# count, with every learned clause shown to follow; the counts are the reference's
# where it can enumerate; the answer to whether is bitr's, and babysat's up to 20
# variables, where with all switches off the first world found is babysat's too;
# the loop and the checker of traces run on mipster
ledger: entr entr-trace bitr babysat selfie rotor
	for f in $(wildcard examples/symbolic/*.c); do \
	  b=$${f%.c}; \
	  out=$$(./selfie -c $$f -o $$b.m 2>&1 && \
	    ./rotor -l $$b.m - 0 -Pnobadexitcode -Pgoodexitcode -riscuonly 2>&1 && \
	    ./bitr $$b-rotorized-riscuonly.btor2 -l $$b.m -bmc 300 -all -dimacs $$b 100 2>&1) || \
	    { echo "$$out" | tail -n 20; echo "$$b: no CNF files"; exit 1; }; \
	done
	n=0; for f in examples/sat/*.cnf examples/entropy/*.cnf examples/symbolic/*.cnf; do \
	  v=$$(sed -n 's/^p cnf \([0-9]*\) .*/\1/p' $$f); \
	  c=$$(./entr -cnf $$f -count -trace entr.trace | tee entr-ledger.txt | sed -n 's/.*: count \(.*\) worlds, .*/\1/p'); \
	  [ -n "$$c" ] && grep -q "ledger: .* open: all " entr-ledger.txt || { echo "$$f: no count, or a ledger that does not account for all worlds"; exit 1; }; \
	  ./entr-trace $$f entr.trace | grep -q "replays to count $$c worlds" || { echo "$$f: the trace does not replay to count $$c"; exit 1; }; \
	  if [ $$v -le 20 ]; then \
	    ./entr -cnf $$f -reference | grep -q ": count $$c worlds" || { echo "$$f: the reference does not count $$c"; exit 1; }; \
	    ./entr -cnf $$f -count -O0 -trace entr.trace | tee entr-ledger.txt | grep -q ": count $$c worlds" && grep -q "ledger: .* open: all " entr-ledger.txt || \
	      { echo "$$f: with all switches off the count is not $$c, or the ledger does not account for all worlds"; exit 1; }; \
	    ./entr-trace $$f entr.trace | grep -q "replays to count $$c worlds" || { echo "$$f: the trace with all switches off does not replay to count $$c"; exit 1; }; \
	  fi; \
	  a=$$(./bitr -sat $$f | grep -o "is [un]*satisfiable"); \
	  if [ $$v -le 20 ]; then \
	    d=$$(./babysat $$f | grep -o "is [un]*satisfiable"); \
	    [ -n "$$a" ] && [ "$$a" = "$$d" ] || { echo "$$f: bitr says it $$a, babysat says it $$d"; exit 1; }; \
	  fi; \
	  for o in "-no learn" "-no reduce -no branch -no phase" "-limits 4 8" "-no propagate"; do \
	    if [ $$v -le 20 ] || [ "$$o" != "-no propagate" ]; then \
	      ./entr -cnf $$f -count $$o -trace entr.trace | tee entr-ledger.txt | grep -q ": count $$c worlds" && grep -q "ledger: .* open: all " entr-ledger.txt || \
	        { echo "$$f: with $$o the count is not $$c, or the ledger does not account for all worlds"; exit 1; }; \
	      ./entr-trace $$f entr.trace | grep -q "replays to count $$c worlds" || { echo "$$f: the trace with $$o does not replay to count $$c"; exit 1; }; \
	    fi; \
	  done; \
	  case "$$c" in "0 of"*) [ "$$a" = "is unsatisfiable" ] ;; *) [ "$$a" = "is satisfiable" ] ;; esac || \
	    { echo "$$f: the count is $$c, but bitr says it $$a"; exit 1; }; \
	  for o in "-first" "-first -limits 4 8" "-first -no restart" "-first -no branch" "-first -no phase" "-first -no reduce" "-first -no pure" "-first -no learn" "-first -no propagate" "-first -O0"; do \
	    if [ $$v -gt 20 ]; then case "$$o" in *propagate|*O0) continue ;; esac; fi; \
	    ./entr -cnf $$f $$o -trace entr.trace > entr-ledger.txt; \
	    grep -q "ledger: .* open: all " entr-ledger.txt && [ "$$(grep -o 'is [un]*satisfiable' entr-ledger.txt)" = "$$a" ] || \
	      { echo "$$f: with $$o the answer is not that it $$a, or the ledger does not account for all worlds"; exit 1; }; \
	    ./entr-trace $$f entr.trace | grep -q "replays to count" || { echo "$$f: the trace with $$o does not replay"; exit 1; }; \
	  done; \
	  if [ "$$a" = "is satisfiable" ] && [ $$v -le 20 ]; then \
	    [ "$$(sed -n 's/.* is satisfiable with //p' entr-ledger.txt)" = "$$(./babysat $$f | sed -n 's/.* is satisfiable with //p')" ] || \
	      { echo "$$f: with all switches off the first world found is not babysat's"; exit 1; }; \
	  fi; \
	  n=$$((n + 1)); \
	done; echo "$@: counts, ledgers, traces, and answers agree on $$n formulas"
	./entr -cnf examples/sat/pigeonhole-4-3.cnf -count -O0 | grep "regions undecided"
	./entr -cnf examples/sat/pigeonhole-4-3.cnf -count | grep "regions undecided"
	./entr -cnf examples/entropy/pigeonhole-7-6.cnf -count -no learn | grep "regions undecided"
	./entr -cnf examples/entropy/pigeonhole-7-6.cnf -count -no reduce -no branch -no phase | grep "regions undecided"
	./entr -cnf examples/entropy/pigeonhole-7-6.cnf -count | grep "regions undecided"
	./entr -cnf examples/entropy/pigeonhole-7-6.cnf -first -limits 4 8 -trace entr.trace | grep "[1-9][0-9]* forgotten, [1-9][0-9]* restarts" || { echo "$@: no restart, or no clause forgotten"; exit 1; }
	./entr-trace examples/entropy/pigeonhole-7-6.cnf entr.trace | grep "replays to count 0 of .* after [1-9][0-9]* restarts" || { echo "$@: the trace with restarts does not replay"; exit 1; }
	./entr -cnf examples/sat/rivest.cnf -count -trace entr.trace > /dev/null && { echo "l 1 0"; cat entr.trace; } > entr-wrong.trace; \
	./entr-trace examples/sat/rivest.cnf entr-wrong.trace | grep "learned clause does not follow" || { echo "$@: a clause that does not follow is accepted as learned"; exit 1; }
	./entr -cnf examples/sat/rivest.cnf -count -trace entr.trace > /dev/null && sed 's/^e \([0-9]*\)$$/e 1/' entr.trace > entr-wrong.trace; \
	./entr-trace examples/sat/rivest.cnf entr-wrong.trace | grep "region is not empty by the clause" || { echo "$@: a wrong trace replays"; exit 1; }
	./selfie -c selfie.h tools/btor2.h bitr.h tools/entr.c -m 64 -cnf examples/sat/pigeonhole-4-3.cnf -count -trace entr.trace | tee entr-ledger.txt; \
	grep -q "count 0 of 4096 worlds" entr-ledger.txt && grep -q "ledger: .* open: all 4096 worlds" entr-ledger.txt || { echo "$@: entr on mipster does not count 0 of 4096"; exit 1; }
	./selfie -c selfie.h tools/btor2.h bitr.h entr.h tests/entr-trace.c -m 64 examples/sat/pigeonhole-4-3.cnf entr.trace | tee entr-ledger.txt; \
	grep -q "replays to count 0 of 4096 worlds" entr-ledger.txt || { echo "$@: the checker of traces on mipster does not replay to 0 of 4096"; exit 1; }

# What today's bitr does on the symbolic examples and on the families of
# examples/entropy, next to the reference: the table to measure entr against;
# a program that reads n bytes one at a time reads n words of the input tape
# a part of the table: make baselines baselines-list="branch-8 factor-2" baselines-table=part.txt
baselines-list  := $(wildcard examples/symbolic/*.c) sum-1 sum-2 sum-4 sum-8 sum-16 password-1 password-2 password-4 password-8 password-16 loop-1 loop-16 loop-64 loop-256 branch-1 branch-2 branch-4 branch-8 branch-10 branch-12 factor-1 factor-2 factor-3
baselines-table := baselines.txt

baselines: entr bitr selfie riscr rotor
	echo "benchmark isa | reference: count of worlds, seconds | bitr, first bad state: instructions, seconds, paths forked, SAT calls, conflicts | bitr, all inputs: inputs, seconds" > $(baselines-table)
	ms() { echo $$(( ($$(date +%s%N) - $$1) / 1000000 + 1000 )) | sed 's/\(...\)$$/.\1/' | awk '{ printf "%.3f", $$1 - 1 }'; }; \
	for f in $(baselines-list); do \
	  case $$f in \
	    *.c) b=$${f%.c}; bytes=1 ;; \
	    *) n=$${f#*-}; b=examples/entropy/$$f; \
	       sed "s/n = 1; \/\/ size/n = $$n; \/\/ size/" examples/entropy/$${f%-*}.c > $$b.c; \
	       case $$f in loop-*) bytes=1 ;; factor-*) bytes=$$((2 * n)) ;; *) bytes=$$n ;; esac ;; \
	  esac; \
	  ./selfie -c $$b.c -o $$b.m > /dev/null && \
	  ./riscr -l $$b.m -history 1 -t $$b.r > /dev/null && \
	  ./rotor -l $$b.m - 0 $(model-options) -bytestoread $$bytes -riscuonly > /dev/null && \
	  ./rotor -l $$b.r - 0 $(model-options) -bytestoread $$bytes > /dev/null || exit 1; \
	  for x in m r; do \
	    if [ $$x = m ]; then \
	      model=$$b-rotorized-riscuonly.btor2; isa=RISC-U; \
	      over=; i=0; while [ $$i -lt $$bytes ]; do over="$$over -over input-buffer $$i 8"; i=$$((i + 1)); done; \
	      over="$$over -zero input-buffer"; limit=2; \
	    else \
	      model=$$b-rotorized-riscr.btor2; isa=RISC-R; \
	      over=; i=0; while [ $$i -lt $$bytes ]; do over="$$over -over input-tapes $$i 8"; i=$$((i + 1)); done; \
	      over="$$over -zero input-tapes -fix tape-ends 0 $$((8 * bytes - 7)) -zero tape-ends -zero tape-opens -zero input-buffer"; limit=1; \
	    fi; \
	    if [ $$bytes -le $$limit ]; then \
	      t=$$(date +%s%N); \
	      c=$$(./entr $$model -l $$b.$$x -k 200000 $$over | sed -n 's/.*: count \(.*\) worlds, .*/\1/p'); \
	      reference="$$c, $$(ms $$t)"; \
	    else reference="-"; fi; \
	    t=$$(date +%s%N); \
	    if timeout 60 ./bitr $$model -l $$b.$$x -bmc 200000 > baselines.out; then \
	      first="$$(sed -n 's/.*: bad .* after \([0-9]*\) instructions/\1/p' baselines.out | head -1), $$(ms $$t), $$(sed -n 's/.*: \([0-9]*\) paths forked.*/\1/p' baselines.out), $$(sed -n 's/.*: \([0-9]*\) SAT calls.*/\1/p' baselines.out), $$(sed -n 's/.* and \([0-9]*\) conflicts in total/\1/p' baselines.out)"; \
	    else first="no answer in 60"; fi; \
	    if [ $$x = m ]; then \
	      t=$$(date +%s%N); \
	      if timeout 60 ./bitr $$model -l $$b.$$x -bmc 200000 -all > baselines.out; then \
	        all="$$(grep -c 'witness input-buffer\[0\]' baselines.out), $$(ms $$t)"; \
	      else all="no answer in 60"; fi; \
	    else all="no projection"; fi; \
	    echo "$$(basename $$b) $$isa | $$reference | $$first | $$all" | tee -a $(baselines-table); \
	  done; \
	done

# Consider these targets as targets, not files
.PHONY: rev riscr-rev bennett trust riscr-model sim bmc cdcl identity reversible garbage-free bit-length count baselines ledger

# Run the checks of the RISC-R branch that are not too slow, one after another and after rotor-btor2:
# they share generated files, the binaries, models, and layouts of the symbolic examples and of the
# tests, so make -j must not run two of them, or one of them and rotor-btor2, at the same time
reversible: rotor-btor2 selfie selfie.h selfie-riscr.h riscr riscr.h riscr-test rotor bitr bitr.h entr entr.h entr-trace babysat
	$(MAKE) rev
	$(MAKE) garbage-free
	$(MAKE) riscr-model
	$(MAKE) sim
	$(MAKE) bmc
	$(MAKE) count
	$(MAKE) ledger
	$(MAKE) bit-length
	$(MAKE) cdcl
	$(MAKE) identity

# Consider these targets as targets, not files
.PHONY: spike qemu assemble beator-32 rotor-32 32-bit bitwuzla beator-bitme rotor-bitme bitme extras

# Run everything that requires non-standard tools
extras: spike qemu assemble beator-32 rotor-32 32-bit bitwuzla bitme

# Run selfie on spike
spike: selfie.m selfie.s
	spike pk selfie.m -c selfie.c -o selfie-spike.m -s selfie-spike.s -m 1
	diff -q selfie.m selfie-spike.m
	diff -q selfie.s selfie-spike.s

# Run selfie on qemu usermode emulation
qemu: selfie.m selfie.s
	qemu-riscv64-static selfie.m -c selfie.c -o selfie-qemu.m -s selfie-qemu.s -m 1
	diff -q selfie.m selfie-qemu.m
	diff -q selfie.s selfie-qemu.s

# Assemble RISC-U with GNU toolchain for RISC-V
assemble: selfie.s
	riscv64-linux-gnu-as selfie.s

# Compile beator.c with selfie.h as library into 32-bit beator executable
beator-32: tools/beator.c selfie.h
	$(CC) $(32-BIT-CFLAGS) --include selfie.h $< -o $@

# Compile rotor.c with selfie.h and btor2.h as libraries into 32-bit rotor executable
rotor-32: tools/rotor.c tools/btor2.h selfie.h
	$(CC) $(32-BIT-CFLAGS) --include selfie.h --include tools/btor2.h $< -o $@

# Self-self-compile, self-execute, self-host, self-gc 32-bit selfie
32-bit: selfie-32 selfie.h selfie-gc.h tools/boehm-gc.c beator-32 rotor-32
	./selfie-32 -c selfie.c -o selfie-32.m -s selfie-32.s -m 2 -c selfie.c -o selfie-32-2-32.m -s selfie-32-2-32.s
	diff -q selfie-32.m selfie-32-2-32.m
	diff -q selfie-32.s selfie-32-2-32.s
	./selfie-32 -l selfie-32.m -m 2 -l selfie-32.m -m 1
	./selfie-32 -l selfie-32.m -m 2 -l selfie-32.m -y 1 -l selfie-32.m -y 1
	./selfie-32 -l selfie-32.m -gc -m 1 -c selfie.c
	./selfie-32 -l selfie-32.m -m 3 -l selfie-32.m -gc -y 1 -c selfie.c
	./selfie-32 -gc -c selfie.h tools/gc-lib.c -gc -m 3 -nr -c selfie.c
	./selfie-32 -c selfie-gc.h tools/boehm-gc.c -gc -m 1 -c selfie.c
	qemu-riscv32-static selfie-32.m -c selfie.c -o selfie-qemu-32.m -s selfie-qemu-32.s -m 1
	diff -q selfie-32.m selfie-qemu-32.m
	diff -q selfie-32.s selfie-qemu-32.s
	riscv64-linux-gnu-as selfie-32.s
	./beator-32 -c selfie.h tools/beator.c - 0 --check-block-access
	./rotor-32 -c selfie.h tools/btor2.h tools/rotor.c - $(rotor)

# Run bitwuzla SMT solver on SMT-LIB files generated by monster
bitwuzla: smt
	$(foreach file, $(smts-1), [ $$(bitwuzla $(file) | grep -c ^sat$$) -eq 1 ] &&) true
	$(foreach file, $(smts-2), [ $$(bitwuzla $(file) | grep -c ^sat$$) -eq 2 ] &&) true
	$(foreach file, $(smts-3), [ $$(bitwuzla $(file) | grep -c ^sat$$) -eq 3 ] &&) true

# Run bitme bounded model checker on BTOR2 files generated by beator
beator-bitme: beator-btor2
	$(foreach file, $(beators), tools/bitme.py $(file) &&) true

# Run bitme bounded model checker on BTOR2 files generated by rotor
rotor-bitme: rotor-btor2
	$(foreach file, $(rotors), tools/bitme.py $(file) &&) true
	tools/bitme.py 64-bit-riscv-machine-synthesize.btor2
	tools/bitme.py 32-bit-riscv-machine-synthesize.btor2

# Run bitme bounded model checker on BTOR2 files generated by beator and rotor
bitme: beator-bitme rotor-bitme

# Consider these targets as targets, not files
.PHONY: validator grader grade pythons

# Run everything that requires python
pythons: validator grader grade

# files where validator fails (e.g. timeout) and succeeds
failingFiles := $(wildcard examples/symbolic/*-fail-*.c)
succeedFiles := $(filter-out $(failingFiles),$(wildcard examples/symbolic/*.c))

# Run validator on *.c files in symbolic. The btormc timeout is set to 2m:
# the slowest succeeding file (recursive-ackermann) needs ~70s of btormc
# time, while the slowest failing file that *does* eventually verify
# (three-level-nested-loop-fail) needs ~7m. 2m sits comfortably between
# those bounds, so all succeedFiles verify and all failingFiles either
# fail verification or hit the btormc timeout, as required.
validator: selfie beator
	$(foreach file, $(succeedFiles), tools/validator.py -tb 2m $(file) &&) true
	$(foreach file, $(failingFiles), ! tools/validator.py -tb 2m $(file) &&) true

# Test autograder
grader: selfie
	cd grader && python3 -m unittest discover -v

# Run autograder
grade:
	grader/self.py self-compile

# Consider these targets as targets, not files
.PHONY: everything clean

# Run everything, except anything that requires python
everything: all extras

# Clean up
clean:
	rm -f *.m
	rm -f *.s
	rm -f *.smt
	rm -f *.btor2
	rm -f examples/*.m
	rm -f examples/*.s
	rm -f examples/symbolic/*.smt
	rm -f examples/symbolic/*.btor2
	rm -f examples/symbolic/*.r examples/symbolic/*.witness examples/symbolic/*.cnf examples/symbolic/*.state
	rm -f examples/symbolic/*.rle examples/symbolic/*.cells
	rm -f division-by-zero.bmc riscr-identity.txt
	rm -f tools/*.smt
	rm -f tools/*.btor2
	rm -f tests/*.m tests/riscr-test.txt
	rm -f selfie-riscr.h riscr-compound-test riscr-compound-test.txt tests/riscr-compound-*.r tests/riscr-compound-base.c
	rm -f riscr-bitlength-test riscr-bitlength-test.txt tests/riscr-bitlength-*.r tests/riscr-bitlength-*.txt tests/riscr-bitlength-*.state tests/riscr-bitlength-*.btor2
	rm -f examples/trusting-trust/honest-stamp.c examples/trusting-trust/honest-victim.c examples/trusting-trust/trojaned-victim.c examples/trusting-trust/suspect-stamp.c
	rm -f selfie selfie-32 selfie.h selfie-gc.h selfie-gc-nomain.h selfie.exe
	rm -f babysat buzzr monster beator beator-32 rotor rotor-32 riscr riscr.h riscr-test bitr
	rm -f entr bitr.h entr-count.txt baselines.out entr.h entr-trace entr-ledger.txt entr.trace entr-wrong.trace
	rm -f examples/symbolic/*.count examples/symbolic/*.worlds examples/symbolic/*.bitr examples/symbolic/*.inputs
	rm -f examples/entropy/*-*.c examples/entropy/*.m examples/entropy/*.r examples/entropy/*.btor2
	rm -f selfie-u.m selfie-r.r selfie-r.m riscr-u.m riscr-r.r riscr-r2.r