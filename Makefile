# Compiler flags
CFLAGS := -w -m32 -D'main(a,b)=main(a,char**argv)'

# Compile selfie.c into selfie executable
selfie: selfie.c
	$(CC) $(CFLAGS) $< -o $@

# Consider these targets as targets, not files
.PHONY : test clean

# Test self-compilation, self-execution, and self-hosting
test: selfie
	./selfie -c selfie.c -o selfie1.r -s selfie1.s -m 2 -c selfie.c -o selfie2.r -s selfie2.s
	diff -q selfie1.r selfie2.r
	diff -q selfie1.s selfie2.s
<<<<<<< HEAD
	./selfie -c selfie.c -o selfie.r -m 2 -l selfie.r -m 1
	./selfie -c selfie.c -o selfie3.r -s selfie3.s -y 8 -l selfie3.r -y 4 -l selfie3.r -y 2 -c selfie.c -o selfie4.r -s selfie4.s
	diff -q selfie3.r selfie4.r
=======
	./selfie -c selfie.c -o selfie.m -m 1 -l selfie.m -m 1
	./selfie -c selfie.c -o selfie3.m -s selfie3.s -y 2 -l selfie3.m -y 2 -l selfie3.m -y 2 -c selfie.c -o selfie4.m -s selfie4.s
	diff -q selfie3.m selfie4.m
>>>>>>> master
	diff -q selfie3.s selfie4.s
	diff -q selfie1.r selfie3.r
	diff -q selfie1.s selfie3.s
	./selfie -c selfie.c -o selfie5.m -s selfie5.s -min 3 -l selfie5.m -y 2 -l selfie5.m -y 2 -c selfie.c -o selfie6.m -s selfie6.s
	diff -q selfie5.m selfie6.m
	diff -q selfie5.s selfie6.s
	diff -q selfie3.m selfie5.m
	diff -q selfie3.s selfie5.s
	./selfie -c -mob 1

# Clean up
clean:
	rm -rf *.r
	rm -rf *.s
	rm -rf selfie
