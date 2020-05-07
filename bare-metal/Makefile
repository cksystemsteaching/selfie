PREFIX=riscv64-linux-gnu-
CC=$(PREFIX)gcc
LD=$(PREFIX)ld
OBJCOPY=$(PREFIX)objcopy

# Our ABI, architecture and memory model must match with OpenSBI
CFLAGS=-g3 -mabi=lp64 -march=rv64imafdc -mcmodel=medany -ffreestanding -nostdlib -Iopensbi/include -Wl,--build-id=none
ASFLAGS=$(CFLAGS)
LDFLAGS=-r -b elf64-littleriscv -m elf64lriscv

SELFIE_PATH = ..

OPENSBI_SOURCE_URL=https://github.com/riscv/opensbi/archive/$(OPENSBI_RELEASE).tar.gz
OPENSBI_RELEASE=v0.7
OPENSBI_VERSION_FILE=opensbi/opensbi_version

SBI_WRAPPER_OBJS = sbi_wrapper.o tinycstd.o crt.o selfie.o
SBI_WRAPPER_FILES_PACKAGE = $(SELFIE_PATH)/selfie.c $(SELFIE_PATH)/selfie.m

include defines.mk

all: selfie-qemu selfie-fu540 selfie-k210

.PHONY: selfie-qemu selfie-fu540 selfie-k210
selfie-qemu: selfie-qemu.elf
selfie-fu540: selfie-fu540.elf
selfie-k210: selfie-k210.bin
	$(OBJCOPY) -S -O binary --file-alignment 4096 --gap-fill 0xFF $< tmp.bin
	mv tmp.bin $<


$(eval $(call generate_payload_rules,qemu,0x80000000,0x200000))
$(eval $(call generate_payload_rules,fu540,0x80000000,0x200000))
$(eval $(call generate_payload_rules,k210,0x80000000,0x1A000))

$(eval $(call generate_selfie_sbi_rules,qemu,qemu/virt,0x80000000,0x200000))
$(eval $(call generate_selfie_sbi_rules,fu540,sifive/fu540,0x80000000,0x200000))
$(eval $(call generate_selfie_sbi_rules,k210,kendryte/k210,0x80000000,0x1A000))

sbi_wrapper.o: sbi_files.h
crt.o: opensbi
selfie.o: $(SELFIE_PATH)/selfie.c
	$(CC) $(CFLAGS) -D'uint64_t = unsigned long long int' -c $^ -o $@

selfie_bare_metal.o: $(SBI_WRAPPER_OBJS)
	$(LD) $(LDFLAGS) $^ -o $@

sbi_files.h: $(SBI_WRAPPER_FILES_PACKAGE)
	@echo   "#ifndef SBI_FILES"  		 >$@
	@printf "#define SBI_FILES\n\n"		>>$@

	@for file in $^ ;\
	do \
		xxd -i "$$file" 				>>$@; \
		printf "\n\n"					>>$@; \
	done;

	@echo "#endif /* SBI_FILES */ " 		>>$@

	@# Patch XXD output to remove trailing underscores
	@sed -i -re 's/unsigned char _*/static const char /g' $@
	@# Also, change size variables to compile-time defines
	@sed -i -re 's/unsigned int _*(\w+) = ([0-9]+);/\#define \1 \2/g' $@

$(SELFIE_PATH)/selfie.m: $(SELFIE_PATH)/selfie.c
	$(MAKE) -C$(SELFIE_PATH) selfie.m


# Clean-up
.PHONY: clean
clean:
	rm -rf opensbi
	rm -f *.o


# OpenSBI fetch target
opensbi:
	@curl -L "$(OPENSBI_SOURCE_URL)" -o opensbi.tar.gz
	@tar xf opensbi.tar.gz

	@# Get the directory name from the tar listing and rename it to plain 'opensbi'
	@SBI_DIR=`tar tf opensbi.tar.gz | sed -rn 's/^(opensbi-[^\/]+)\/$$/\1/p'` && mv $$SBI_DIR opensbi
	@rm opensbi.tar.gz

	@printf $(OPENSBI_RELEASE) > $(OPENSBI_VERSION_FILE)
