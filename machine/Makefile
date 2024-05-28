HOSTCC:=$(CC)

PREFIX=riscv64-linux-gnu-
CC=$(PREFIX)gcc
AS=$(CC)
OBJCOPY=$(PREFIX)objcopy
QEMU=qemu-system-riscv64

# Our ABI, architecture and memory model must match with OpenSBI
CFLAGS=-mabi=lp64d -march=rv64imafdc_zifencei -mcmodel=medany -ffreestanding -Iinclude -Wall -Wextra -MMD -MP -O3
ASFLAGS=$(CFLAGS)
LDFLAGS=-nostdlib -lgcc -Wl,--build-id=none
QEMUFLAGS=-M virt -m 128M -nographic -bios none
# for debugging, add '-gdb tcp::9000 -S' to the QEMUFLAGS

SELFIE_PATH = ..
BUILD_DIR = build

OPENSBI_SOURCE_URL=https://github.com/riscv/opensbi/archive/$(OPENSBI_RELEASE).tar.gz
OPENSBI_RELEASE=v0.7
OPENSBI_VERSION_FILE=opensbi/opensbi_version

SBI_WRAPPER_SRCS_COMMON = bootstrap.c tinycstd.c console.c filesystem.c files_package.c syscalls.c asm/crt.S diag.c sbi_ecall.c
SBI_WRAPPER_SRCS_LIBRARY = bootstrap_library.c selfie.c glue_libraryos.c asm/mem.S
SBI_WRAPPER_SRCS_KERNEL =  bootstrap_kernel.c mmu.c context.c trap.c elf.c asm/trap.S

SBI_WRAPPER_FILES_PACKAGE = $(BUILD_DIR)/selfie.m $(SELFIE_PATH)/selfie.c $(SELFIE_PATH)/examples/hello-world.c $(BUILD_DIR)/hello-world.m
ASM_STRUCT_HEADERS = include/context.h

include defines.mk
include filesystem.mk

# ==============================================================================
# Add rules for packaged RISC-U binaries

$(eval $(call compile_riscu_binary,$(SELFIE_PATH)/selfie.c,$(BUILD_DIR)/selfie.m))
$(eval $(call compile_riscu_binary,$(SELFIE_PATH)/examples/hello-world.c,$(BUILD_DIR)/hello-world.m))

# ==============================================================================

#selfie-k210.bin: selfie-k210.elf
#	$(OBJCOPY) -S -O binary --file-alignment 4096 --gap-fill 0xFF $^ $@


$(eval $(call add-board,qemu,0x80000000,0x200000,qemu/virt))
$(eval $(call add-board,fu540,0x80000000,0x200000,sifive/fu540))
$(eval $(call add-board,k210,0x80000000,0x1A000,kendryte/k210))

$(eval $(call add-build-profile,kernel,$(SBI_WRAPPER_SRCS_COMMON) $(SBI_WRAPPER_SRCS_KERNEL),KERN_TYPE=kernel))
$(eval $(call add-build-profile,library,$(SBI_WRAPPER_SRCS_COMMON) $(SBI_WRAPPER_SRCS_LIBRARY),KERN_TYPE=library))

$(eval $(call add-all-targets))
$(eval $(call add-all-target-aliases))

.PHONY: all
all: all-selfie-elf all-selfie-opensbi-elf

include/asm_offsets.h: $(ASM_STRUCT_HEADERS)
	$(HOSTCC) -Iinclude tools/asm_struct_macro_generator.c -o tools/asm_struct_macro_generator
	tools/asm_struct_macro_generator > "$@"





# Clean-up
.PHONY: clean
clean: clean-fs-package
	@case "`realpath $(BUILD_DIR)`" in \
		"`realpath $$PWD`/"*) rm -rf $(BUILD_DIR); echo "Removed output directory \"$(BUILD_DIR)\"...";;\
		*) echo "WARNING: Build directory '$(BUILD_DIR)' has not been removed as it is not a descending directory";;\
	esac

	rm -f *.elf
	rm -f *.bin
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
	$(eval CFLAGS += -O0 -g3 -DDEBUG)
	@echo "Enabled debug macro"


.PHONY: list-targets
list-targets:
	@echo "List of targets:"
	@echo "===================================================="
	@echo "The build artifacts are placed in directory $(BUILD_DIR)."
	@echo "It contains a subdirectory for each supported board and these"
	@echo "subdirectories themselves contain subdirectories for each profile."
	@echo "There are three main artifacts:"
	@echo " -selfie.elf: The freestanding selfie.elf executable. Requires a bootloader that loads OpenSBI as runtime, e.g. U-Boot"
	@echo " -selfie.bin: Similar to selfie.elf, but not as ELF, but as a flat binary (required by some bootloaders)"
	@echo " -selfie-opensbi.elf: selfie.bin linked with OpenSBI (FW_PAYLOAD). Required if OpenSBI is not loaded by the bootloader"

	@echo "===================================================="
	@echo "all                   : Builds everything"
	@echo "all-selfie-elf        : Builds selfie.elf for each board and each profile"
	@echo "all-selfie-bin        : Builds selfie.bin for each board and each profile"
	@echo "all-selfie-opensbi-elf: Builds selfie-opensbi.elf for each board and each profile"
	@echo "----------------------------------------------------"
	@for board in $(ALL_BOARDS);\
	 do\
		echo "selfie-$$board.elf        : Builds selfie.elf for $$board and each profile";\
		echo "selfie-$$board.bin        : Builds selfie.bin for $$board and each profile";\
		echo "selfie-opensbi-$$board.elf: Builds selfie-opensbi.elf for $$board and each profile";\
		echo "----------------------------------------------------";\
	 done;

	@for board in $(ALL_BOARDS);\
	 do\
		for profile in $(ALL_PROFILES);\
		do\
			echo "selfie-$$board-$$profile.elf        : Builds selfie.elf for $$board and $$profile";\
			echo "selfie-$$board-$$profile.bin        : Builds selfie.bin for $$board and $$profile";\
			echo "selfie-opensbi-$$board-$$profile.elf: Builds selfie-opensbi.elf for $$board and $$profile";\
			echo "....................................................";\
		done;\
		echo "----------------------------------------------------";\
	 done;

.PHONY: test
test: selfie-opensbi-qemu.elf
	@echo "============================================================"
	@echo "       Testing library mode build artifact on QEMU...       "
	@echo "============================================================"
	$(QEMU) $(QEMUFLAGS) -kernel build/qemu/library/selfie-opensbi.elf
	@echo "============================================================"
	@echo "       Testing kernel mode build artifact on QEMU...        "
	@echo "============================================================"
	$(QEMU) $(QEMUFLAGS) -kernel build/qemu/kernel/selfie-opensbi.elf


-include $(ALL_DEPS)
.DEFAULT_GOAL := all
