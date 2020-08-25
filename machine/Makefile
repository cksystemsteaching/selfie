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

SBI_WRAPPER_SRCS_COMMON = sbi_wrapper.c tinycstd.c console.c sbi_files.c files_package.c syscalls.c asm/crt.S diag.c
SBI_WRAPPER_SRCS_LIBRARY = bootstrap_library.c selfie.c glue_libraryos.c
SBI_WRAPPER_SRCS_KERNEL =  bootstrap_kernel.c mmu.c context.c trap.c elf.c asm/trap.S

SBI_WRAPPER_SRCS = $(SBI_WRAPPER_SRCS_COMMON)
SBI_WRAPPER_OBJS = $(patsubst %.o,$(BUILD_DIR)/%.o,$(patsubst %.S,%.o,$(SBI_WRAPPER_SRCS:.c=.o)))
SBI_WRAPPER_DEPS = $(SBI_WRAPPER_OBJS:.o=.d)
BUILD_DIR_TREE = $(sort $(BUILD_DIR) $(addprefix $(BUILD_DIR)/,$(filter-out ./,$(dir $(SBI_WRAPPER_SRCS)))))
KERN_TYPE = unknown

SBI_WRAPPER_FILES_PACKAGE = $(SELFIE_PATH)/selfie.m $(SELFIE_PATH)/selfie.c $(SELFIE_PATH)/examples/hello-world.c $(SELFIE_PATH)/hello-world.m
ASM_STRUCT_HEADERS = include/context.h

include defines.mk

ifeq ($(KERN_TYPE), library)
$(eval SBI_WRAPPER_SRCS += $(SBI_WRAPPER_SRCS_LIBRARY))
else ifeq ($(KERN_TYPE), kernel)
$(eval SBI_WRAPPER_SRCS += $(SBI_WRAPPER_SRCS_KERNEL))
else
ifeq ($(MAKECMDGOALS),clean)
else ifeq ($(MAKECMDGOALS),distclean)
else
$(error No build type specified! Please specify either KERN_TYPE=kernel or KERN_TYPE=library when invoking make)
endif
endif

# ==============================================================================

all: selfie-qemu selfie-fu540 selfie-k210

.PHONY: selfie-qemu selfie-fu540 selfie-k210
selfie-qemu: selfie-qemu.elf
selfie-fu540: selfie-fu540.elf
selfie-k210: selfie-k210.bin

selfie-k210.bin: selfie-k210.elf
	$(OBJCOPY) -S -O binary --file-alignment 4096 --gap-fill 0xFF $^ $@


$(eval $(call generate_payload_rules,qemu,0x80000000,0x200000))
$(eval $(call generate_payload_rules,fu540,0x80000000,0x200000))
$(eval $(call generate_payload_rules,k210,0x80000000,0x1A000))

$(eval $(call generate_selfie_sbi_rule,qemu,qemu/virt,0x80000000,0x200000))
$(eval $(call generate_selfie_sbi_rule,fu540,sifive/fu540,0x80000000,0x200000))
$(eval $(call generate_selfie_sbi_rule,k210,kendryte/k210,0x80000000,0x1A000))

$(BUILD_DIR)/%.o: %.c | $(BUILD_DIR_TREE)
	$(CC) -c $(CFLAGS) $< -o $@
$(BUILD_DIR)/%.o: %.S | $(BUILD_DIR_TREE)
	$(AS) -c $(ASFLAGS) $< -o $@

selfie.o: $(SELFIE_PATH)/selfie.c
	$(CC) $(CFLAGS) -Wno-return-type -D'uint64_t = unsigned long long int' -c $^ -o $@

selfie_bare_metal.o: $(SBI_WRAPPER_OBJS)
	$(LD) $(LDFLAGS) $^ -o $@

files_package.c: $(SBI_WRAPPER_FILES_PACKAGE)
	@printf "#include \"sbi_files.h\"\n\n" >$@

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

# Make requires a static pattern rule to add prerequisites
# https://stackoverflow.com/a/46946731
$(SBI_WRAPPER_OBJS): %.o: | include/asm_offsets.h


$(SELFIE_PATH)/selfie.m: $(SELFIE_PATH)/selfie.c
	$(MAKE) -C$(SELFIE_PATH) selfie.m

$(SELFIE_PATH)/hello-world.m: $(SELFIE_PATH)/examples/hello-world.c
	$(MAKE) -C$(SELFIE_PATH)
	$(SELFIE_PATH)/selfie -c $^ -o $@

$(BUILD_DIR_TREE):
	mkdir -p $(BUILD_DIR_TREE)

# Clean-up
.PHONY: clean
clean:
	rm -f *.o asm/*.o
	rm -f *.elf
	rm -f *.bin
	rm -f files_package.c
	rm -f include/asm_offsets.h
	rm -f $(SBI_WRAPPER_DEPS)
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

-include $(SBI_WRAPPER_DEPS)
