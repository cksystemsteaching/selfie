# Compiler flags
CFLAGS := -w -m32 -D'main(a,b)=main(a,char**argv)'
OS := $(shell uname)

# Compile selfie.c into selfie executable
selfie: selfie.c
	$(CC) $(CFLAGS) $< -o $@

webassembly: selfie.c
	emcc $(CFLAGS) $< -s ASSERTIONS=2 -s EXTRA_EXPORTED_RUNTIME_METHODS='["FS"]' -o selfie.html --preload-file selfie.c

# Consider these targets as targets, not files
.PHONY : test clean clean-wasm

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
	./selfie -c selfie.c -o selfie5.r -s selfie5.s -min 8 -l selfie5.r -y 4 -l selfie5.r -y 2 -c selfie.c -o selfie6.r -s selfie6.s
	diff -q selfie5.r selfie6.r
	diff -q selfie5.s selfie6.s
	diff -q selfie3.r selfie5.r
	diff -q selfie3.s selfie5.s
	./selfie -c -mob 1

sbrk.dylib: sbrk.c
	$(CC) -m32 -Wall -o sbrk.dylib -dynamiclib sbrk.c

# Clean up webassembly related files
clean-wasm:
	rm -rf selfie.wasm
	rm -rf selfie.js
	rm -rf selfie.html
	rm -rf selfie.data

# Clean up
clean: clean-wasm
	rm -rf *.r
	rm -rf *.s
	rm -rf selfie
