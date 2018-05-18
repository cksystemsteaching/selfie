# Compiler flags
CFLAGS := -w -O3 -m64 -D'main(a,b)=main(int argc, char** argv)' -Duint64_t='unsigned long long'

# Compile selfie.c into selfie executable
selfie: selfie.c
	$(CC) $(CFLAGS) $< -o $@

# Consider these targets as targets, not files
.PHONY : compile quine debug replay os vm min mob sat all clean

# Self-compile
compile: selfie
	./selfie -c selfie.c -o selfie1.m -s selfie1.s -m 2 -c selfie.c -o selfie2.m -s selfie2.s
	diff -q selfie1.m selfie2.m
	diff -q selfie1.s selfie2.s

# Compile and run quine and compare its output to itself
quine: selfie
	./selfie -c manuscript/code/quine.c selfie.c -m 1 | sed '/^.\/selfie/d' | diff -q manuscript/code/quine.c -

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
	./selfie -c selfie.c -o selfie3.m -s selfie3.s -m 6 -l selfie3.m -y 6 -l selfie3.m -y 4 -c selfie.c -o selfie4.m -s selfie4.s
	diff -q selfie3.m selfie4.m
	diff -q selfie3.s selfie4.s
	diff -q selfie1.m selfie3.m
	diff -q selfie1.s selfie3.s

# Self-compile on two virtual machines on fully mapped virtual memory
min: selfie
	./selfie -c selfie.c -o selfie5.m -s selfie5.s -min 14 -l selfie5.m -y 6 -l selfie5.m -y 4 -c selfie.c -o selfie6.m -s selfie6.s
	diff -q selfie5.m selfie6.m
	diff -q selfie5.s selfie6.s
	diff -q selfie3.m selfie5.m
	diff -q selfie3.s selfie5.s

# Run mobster
mob: selfie
	./selfie -c -mob 1

# Run SAT solver
sat: selfie
	./selfie -sat manuscript/cnfs/rivest.cnf
	./selfie -c selfie.c -m 1 -sat manuscript/cnfs/rivest.cnf

# Run everything
all: compile quine debug replay os vm min mob sat

# Clean up
clean:
	rm -rf *.m
	rm -rf *.s
	rm -rf selfie
	rm -rf selfie.exe