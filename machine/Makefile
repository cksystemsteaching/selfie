HOSTCC:=$(CC)

PREFIX=riscv64-linux-gnu-
CC=$(PREFIX)gcc
LD=$(PREFIX)ld
AS=$(CC)
OBJCOPY=$(PREFIX)objcopy

# Our ABI, architecture and memory model must match with OpenSBI
CFLAGS=-g3 -mabi=lp64 -march=rv64imafdc -mcmodel=medany -ffreestanding -nostdlib -Iinclude -Iopensbi/include -Wl,--build-id=none -Wall -Wextra -MMD -MP -DKERN_TYPE=$(KERN_TYPE)
ASFLAGS=$(CFLAGS)
LDFLAGS=-r -b elf64-littleriscv -m elf64lriscv

SELFIE_PATH = ..
BUILD_DIR = build

OPENSBI_SOURCE_URL=https://github.com/riscv/opensbi/archive/$(OPENSBI_RELEASE).tar.gz
OPENSBI_RELEASE=v0.7
OPENSBI_VERSION_FILE=opensbi/opensbi_version

SBI_WRAPPER_SRCS_COMMON = bootstrap.c tinycstd.c console.c filesystem.c files_package.c syscalls.c asm/crt.S diag.c sbi_ecall.c
SBI_WRAPPER_SRCS_LIBRARY = bootstrap_library.c selfie.c glue_libraryos.c
SBI_WRAPPER_SRCS_KERNEL =  bootstrap_kernel.c mmu.c context.c trap.c elf.c asm/trap.S

SBI_WRAPPER_FILES_PACKAGE = $(SELFIE_PATH)/selfie.m $(SELFIE_PATH)/selfie.c $(SELFIE_PATH)/examples/hello-world.c $(SELFIE_PATH)/hello-world.m
ASM_STRUCT_HEADERS = include/context.h

include defines.mk

# ==============================================================================

#selfie-k210.bin: selfie-k210.elf
#	$(OBJCOPY) -S -O binary --file-alignment 4096 --gap-fill 0xFF $^ $@


$(eval $(call add-board,qemu,0x80000000,0x200000,qemu/virt))
$(eval $(call add-board,fu540,0x80000000,0x200000,sifive/fu540))
$(eval $(call add-board,k210,0x80000000,0x1A000,kendryte/k210))

$(eval $(call add-build-profile,kernel,$(SBI_WRAPPER_SRCS_COMMON) $(SBI_WRAPPER_SRCS_KERNEL)))
$(eval $(call add-build-profile,library,$(SBI_WRAPPER_SRCS_COMMON) $(SBI_WRAPPER_SRCS_LIBRARY)))

$(eval $(call add-all-targets))

.PHONY: all
all: $(ALL_OPENSBI_ELF_TARGETS)
	echo $(ALL_OPENSBI_ELF_TARGETS)


files_package.c: $(SBI_WRAPPER_FILES_PACKAGE)
	@printf "#include \"filesystem.h\"\n\n" >$@

	@# Package all files as a byte array using xxd
	@for file in $^ ;\
	do \
		BASENAME=`basename $$file` ;\
		VARIABLENAME=`echo $$BASENAME | sed 's/\W/_/g'`; \
		echo "static const char $${VARIABLENAME}[] = {" >> $@; \
		cat "$$file" | xxd -i >>$@; \
		echo "};" >>$@; \
		printf "\n\n"					>>$@; \
	done;

	@# Create a mapping to all packaged files
	@echo "static const KFILE file_defs[] = {" >>$@;
	@for file in $^;\
	do \
		BASENAME=`basename $$file` ;\
		VARIABLENAME=`echo $$BASENAME | sed 's/\W/_/g'`; \
		FILESIZE=`wc -c "$$file" | awk '{print $$1}'`; \
		echo "  {\"$$BASENAME\", $$VARIABLENAME, $$FILESIZE}," >>$@; \
	done;
	@echo "  {\"\", (const char*) NULL, 0}," >>$@;
	@echo "};" >>$@;
	@echo "const KFILE* files = file_defs;" >>$@;

include/asm_offsets.h: $(ASM_STRUCT_HEADERS)
	$(HOSTCC) -I. tools/asm_struct_macro_generator.c -o tools/asm_struct_macro_generator
	tools/asm_struct_macro_generator > "$@"



$(SELFIE_PATH)/selfie.m: $(SELFIE_PATH)/selfie.c
	$(MAKE) -C$(SELFIE_PATH) selfie.m

$(SELFIE_PATH)/hello-world.m: $(SELFIE_PATH)/examples/hello-world.c
	$(MAKE) -C$(SELFIE_PATH)
	$(SELFIE_PATH)/selfie -c $^ -o $@


# Clean-up
.PHONY: clean
clean:
	@case "`realpath $(BUILD_DIR)`" in \
		"`realpath $$PWD`/"*) rm -rf $(BUILD_DIR);;\
		*) echo "WARNING: Build directory '$(BUILD_DIR)' has not been removed as it is not a descending directory";;\
	esac

	rm -f *.elf
	rm -f *.bin
	rm -f files_package.c
	rm -f include/asm_offsets.h
.PHONY: distclean
distclean: clean
	rm -rf opensbi


# OpenSBI fetch target
opensbi:
	@curl -L "$(OPENSBI_SOURCE_URL)" -o opensbi.tar.gz
	@tar xf opensbi.tar.gz

	@# Get the directory name from the tar listing and rename it to plain 'opensbi'
	@SBI_DIR=`tar tf opensbi.tar.gz | sed -rn 's/^(opensbi-[^\/]+)\/$$/\1/p'` && mv $$SBI_DIR opensbi
	@rm opensbi.tar.gz

	@printf $(OPENSBI_RELEASE) > $(OPENSBI_VERSION_FILE)

.PHONY: debug
debug:
	$(eval CFLAGS += -DDEBUG)
	@echo "Enabled debug macro"

.DEFAULT_GOAL := all
