# Compiler flags
CFLAGS := -Wall -Wextra -O3 -m64 -D'uint64_t=unsigned long long'

# Bootstrap selfie.c into selfie executable
selfie: selfie.c
	$(CC) $(CFLAGS) $< -o $@

# Self-compile selfie.c into RISC-U selfie.m executable and RISC-U selfie.s assembly
selfie.m selfie.s: selfie
	./selfie -c selfie.c -o selfie.m -s selfie.s

# Consider these targets as targets, not files
.PHONY : compile quine escape debug replay os vm min mob smt mc sat all grader grade assemble spike qemu boolector btormc everything clean

# Self-contained fixed-point of self-compilation
compile: selfie
	./selfie -c selfie.c -o selfie1.m -s selfie1.s -m 2 -c selfie.c -o selfie2.m -s selfie2.s
	diff -q selfie1.m selfie2.m
	diff -q selfie1.s selfie2.s

# Compile and run quine and compare its output to itself
quine: selfie
	./selfie -c manuscript/code/quine.c selfie.c -m 1 | sed '/^.\/selfie/d' | diff -q manuscript/code/quine.c -

# Demonstrate available escape sequences
escape: selfie
	./selfie -c manuscript/code/escape.c -m 1

# Run debugger
debug: selfie
	./selfie -c manuscript/code/pointer.c -d 1

# Run replay engine
replay: selfie
	./selfie -c manuscript/code/division-by-zero.c -r 1

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

# Run monster as symbolic execution engine
smt: selfie
	./selfie -c manuscript/code/symbolic/division-by-zero.c -se 0 35 --merge-enabled
	./selfie -c manuscript/code/symbolic/invalid-memory-access.c -se 0 35 --merge-enabled
	./selfie -c manuscript/code/symbolic/memory-access.c -se 0 35 --merge-enabled
	./selfie -c manuscript/code/symbolic/nested-if-else.c -se 0 35 --merge-enabled
	./selfie -c manuscript/code/symbolic/nested-if-else-reverse.c -se 0 35 --merge-enabled
	./selfie -c manuscript/code/symbolic/nested-recursion.c -se 0 35 --merge-enabled
	./selfie -c manuscript/code/symbolic/recursive-ackermann.c -se 0 35 --merge-enabled
	./selfie -c manuscript/code/symbolic/recursive-factorial.c -se 0 35 --merge-enabled
	./selfie -c manuscript/code/symbolic/recursive-fibonacci.c -se 0 10 --merge-enabled
	./selfie -c manuscript/code/symbolic/simple-assignment.c -se 0 35 --merge-enabled
	./selfie -c manuscript/code/symbolic/simple-decreasing-loop.c -se 0 35 --merge-enabled
	./selfie -c manuscript/code/symbolic/simple-if-else.c -se 0 35 --merge-enabled
	./selfie -c manuscript/code/symbolic/simple-if-else-reverse.c -se 0 35 --merge-enabled
	./selfie -c manuscript/code/symbolic/simple-if-without-else.c -se 0 35 --merge-enabled
	./selfie -c manuscript/code/symbolic/simple-increasing-loop.c -se 0 35 --merge-enabled
	./selfie -c manuscript/code/symbolic/three-level-nested-loop.c -se 0 35 --merge-enabled
	./selfie -c manuscript/code/symbolic/two-level-nested-loop.c -se 0 35 --merge-enabled

# Run monster as symbolic model generator
mc: selfie
	./selfie -c manuscript/code/symbolic/simple-assignment.c -mc 0

# Run SAT solver
sat: selfie.m
	./selfie -sat manuscript/cnfs/rivest.cnf
	./selfie -l selfie.m -m 1 -sat manuscript/cnfs/rivest.cnf

# Run everything that does not require non-standard tools
all: compile quine debug replay os vm min mob smt mc sat

# Test autograder
grader:
	cd grader && python3 -m unittest discover -v

# Run autograder
grade:
	./grader/self.py self-compile

# Assemble RISC-U with GNU toolchain for RISC-V
assemble: selfie.m selfie.s
	riscv64-linux-gnu-as selfie.s -o a.out
	rm -rf a.out

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
	boolector manuscript/code/symbolic/division-by-zero.smt -e 0 > division-by-zero.sat
	[ $$(grep ^sat$$ division-by-zero.sat | wc -l) -eq 3 ]
	boolector manuscript/code/symbolic/invalid-memory-access.smt -e 0 > invalid-memory-access.sat
	[ $$(grep ^sat$$ invalid-memory-access.sat | wc -l) -eq 2 ]
	boolector manuscript/code/symbolic/memory-access.smt -e 0 > memory-access.sat
	[ $$(grep ^sat$$ memory-access.sat | wc -l) -eq 1 ]
	boolector manuscript/code/symbolic/nested-if-else.smt -e 0 > nested-if-else.sat
	[ $$(grep ^sat$$ nested-if-else.sat | wc -l) -eq 1 ]
	boolector manuscript/code/symbolic/nested-if-else-reverse.smt -e 0 > nested-if-else-reverse.sat
	[ $$(grep ^sat$$ nested-if-else-reverse.sat | wc -l) -eq 1 ]
	boolector manuscript/code/symbolic/nested-recursion.smt -e 0 > nested-recursion.sat
	[ $$(grep ^sat$$ nested-recursion.sat | wc -l) -eq 1 ]
	boolector manuscript/code/symbolic/recursive-ackermann.smt -e 0 > recursive-ackermann.sat
	[ $$(grep ^sat$$ recursive-ackermann.sat | wc -l) -eq 1 ]
	boolector manuscript/code/symbolic/recursive-factorial.smt -e 0 > recursive-factorial.sat
	[ $$(grep ^sat$$ recursive-factorial.sat | wc -l) -eq 1 ]
	boolector manuscript/code/symbolic/recursive-fibonacci.smt -e 0 > recursive-fibonacci.sat
	[ $$(grep ^sat$$ recursive-fibonacci.sat | wc -l) -eq 1 ]
	boolector manuscript/code/symbolic/simple-assignment.smt -e 0 > simple-assignment.sat
	[ $$(grep ^sat$$ simple-assignment.sat | wc -l) -eq 1 ]
	boolector manuscript/code/symbolic/simple-decreasing-loop.smt -e 0 > simple-decreasing-loop.sat
	[ $$(grep ^sat$$ simple-decreasing-loop.sat | wc -l) -eq 1 ]
	boolector manuscript/code/symbolic/simple-if-else.smt -e 0 > simple-if-else.sat
	[ $$(grep ^sat$$ simple-if-else.sat | wc -l) -eq 1 ]
	boolector manuscript/code/symbolic/simple-if-else-reverse.smt -e 0 > simple-if-else-reverse.sat
	[ $$(grep ^sat$$ simple-if-else-reverse.sat | wc -l) -eq 1 ]
	boolector manuscript/code/symbolic/simple-if-without-else.smt -e 0 > simple-if-without-else.sat
	[ $$(grep ^sat$$ simple-if-without-else.sat | wc -l) -eq 1 ]
	boolector manuscript/code/symbolic/simple-increasing-loop.smt -e 0 > simple-increasing-loop.sat
	[ $$(grep ^sat$$ simple-increasing-loop.sat | wc -l) -eq 1 ]
	boolector manuscript/code/symbolic/three-level-nested-loop.smt -e 0 > three-level-nested-loop.sat
	[ $$(grep ^sat$$ three-level-nested-loop.sat | wc -l) -eq 1 ]
	boolector manuscript/code/symbolic/two-level-nested-loop.smt -e 0 > two-level-nested-loop.sat
	[ $$(grep ^sat$$ two-level-nested-loop.sat | wc -l) -eq 1 ]

# Test btormc bounded model checker
btormc: mc
	btormc manuscript/code/symbolic/simple-assignment.btor2

# Run everything
everything: all grader grade assemble spike qemu boolector btormc

# Clean up
clean:
	rm -rf *.m
	rm -rf *.s
	rm -rf *.smt
	rm -rf *.btor2
	rm -rf *.sat
	rm -rf selfie
	rm -rf selfie.exe
	rm -rf manuscript/code/symbolic/*.smt
	rm -rf manuscript/code/symbolic/*.btor2