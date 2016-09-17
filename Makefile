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
	./selfie -c selfie.c -o selfie.r -m 2 -l selfie.r -m 1
	./selfie -c selfie.c -o selfie3.r -s selfie3.s -y 8 -l selfie3.r -y 4 -l selfie3.r -y 2 -c selfie.c -o selfie4.r -s selfie4.s
	diff -q selfie3.r selfie4.r
	diff -q selfie3.s selfie4.s
	diff -q selfie1.r selfie3.r
	diff -q selfie1.s selfie3.s

# Clean up
clean:
	rm -rf *.r
	rm -rf *.s
	rm -rf selfie
