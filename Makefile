# Compiler flags
CFLAGS := -Wall -Wextra -O3 -m64 -D'uint64_t=unsigned long long'

# Compile selfie.c into selfie executable
selfie: selfie.c
	$(CC) $(CFLAGS) $< -o $@

# Consider these targets as targets, not files
.PHONY : compile quine escape debug replay os vm min mob smt sat spike qemu boolector all clean

# Self-compile
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
os: selfie
	./selfie -c selfie.c -o selfie.m -m 2 -l selfie.m -m 1

# Self-compile on two virtual machines
vm: selfie
	./selfie -c selfie.c -o selfie3.m -s selfie3.s -m 3 -l selfie3.m -y 3 -l selfie3.m -y 2 -c selfie.c -o selfie4.m -s selfie4.s
	diff -q selfie3.m selfie4.m
	diff -q selfie3.s selfie4.s
	diff -q selfie1.m selfie3.m
	diff -q selfie1.s selfie3.s

# Self-compile on two virtual machines on fully mapped virtual memory
min: selfie
	./selfie -c selfie.c -o selfie5.m -s selfie5.s -min 15 -l selfie5.m -y 3 -l selfie5.m -y 2 -c selfie.c -o selfie6.m -s selfie6.s
	diff -q selfie5.m selfie6.m
	diff -q selfie5.s selfie6.s
	diff -q selfie3.m selfie5.m
	diff -q selfie3.s selfie5.s

# Run mobster
mob: selfie
	./selfie -c -mob 1

# Run monster
smt: selfie
	./selfie -c manuscript/code/symbolic.c -n 0

# Run SAT solver
sat: selfie
	./selfie -sat manuscript/cnfs/rivest.cnf
	./selfie -c selfie.c -m 1 -sat manuscript/cnfs/rivest.cnf

# Run selfie on spike
spike: selfie
	./selfie -c selfie.c -o selfie.m -s selfie.s
	spike pk selfie.m -c selfie.c -o selfie7.m -s selfie7.s -m 1
	diff -q selfie.m selfie7.m
	diff -q selfie.s selfie7.s

# Run selfie on qemu usermode emulation
qemu: selfie
	./selfie -c selfie.c -o selfie.m -s selfie.s
	chmod +x selfie.m
	qemu-riscv64-static selfie.m -c selfie.c -o selfie8.m -s selfie8.s -m 1
	diff -q selfie.m selfie8.m
	diff -q selfie.s selfie8.s

# Test boolector SMT solver
boolector: smt
	boolector manuscript/code/symbolic.t -e 0 > selfie_boolector.sat
	[ $$(grep ^sat$$ selfie_boolector.sat | wc -l) -eq 2 ]
	[ $$(grep ^unsat$$ selfie_boolector.sat | wc -l) -eq 1 ]

# Run everything
all: compile quine debug replay os vm min mob smt sat

# Clean up
clean:
	rm -rf *.m
	rm -rf *.s
	rm -rf *.t
	rm -rf selfie
	rm -rf selfie.exe
	rm -rf manuscript/code/*.t