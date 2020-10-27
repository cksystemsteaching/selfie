ALL_PROFILES=
ALL_BOARDS=
ALL_TARGETS=
ALL_DEPS=

ALL_ELF_TARGETS=
ALL_BIN_TARGETS=
ALL_OPENSBI_ELF_TARGETS=

###############################################################################
# $(eval $(call add-build-profile,profile-name,srcs,defines))
#
# - profile-name  : The name of the build profile, without spaces
# - srcs          : The position where the PC jumps, i.e. where the supervisor binary will be loaded to.
# - defines       : The offset of the payload in the OpenSBI binary
#
define add-build-profile
ALL_PROFILES += $(1)
PROFILE_$(1)_SRCS = $(2)
PROFILE_$(1)_DEFINES = $(foreach def,$(3),-D$(def))
endef

###############################################################################
# $(eval $(call add-board,sbi_start,payload_offset,path))
#
# - sbi_start     : The position where the PC jumps, i.e. where the supervisor binary will be loaded to.
# - payload_offset: The offset of the payload in the OpenSBI binary
# - path          : The path where the linker script shall be emitted
#
define add-board
ALL_BOARDS += $(1)
BOARD_$(1)_PAYLOAD_START = $(2)
BOARD_$(1)_PAYLOAD_OFFSET = $(3)
BOARD_$(1)_SBI_NAME = $(4)
endef


###############################################################################
# $(eval $(call add-target,board,profile))
#
# - board         : The board
# - profile       : The build profile
#
define add-target
$(call generate-target-vars,$(1),$(2))
$(call generate-target-obj-rules,$(1),$(2))
$(call generate-target-combine-rule,$(1),$(2))
$(call generate-target-elf-bin,$(1),$(2))
$(call generate-target-sbi-elf,$(1),$(2))
endef

###############################################################################
# $(eval $(call add-all-targets))
#
define add-all-targets
$(foreach board,$(ALL_BOARDS),$(foreach profile,$(ALL_PROFILES),$(call add-target,$(board),$(profile))))
endef


###############################################################################
# $(eval $(call add-all-targets))
#
define add-all-target-aliases

$(foreach board,$(ALL_BOARDS),
.PHONY: selfie-$(board).elf
selfie-$(board).elf: $(foreach profile,$(ALL_PROFILES),selfie-$(board)-$(profile).elf)

.PHONY: selfie-$(board).bin
selfie-$(board).bin: $(foreach profile,$(ALL_PROFILES),selfie-$(board)-$(profile).bin)

.PHONY: selfie-opensbi-$(board).elf
selfie-opensbi-$(board).elf: $(foreach profile,$(ALL_PROFILES),selfie-opensbi-$(board)-$(profile).elf)
)

.PHONY: all-selfie-elf
all-selfie-elf: $(foreach board,$(ALL_BOARDS),selfie-$(board).elf)

.PHONY: all-selfie-bin
all-selfie-bin: $(foreach board,$(ALL_BOARDS),selfie-$(board).bin)

.PHONY: all-selfie-opensbi-elf
all-selfie-opensbi-elf: $(foreach board,$(ALL_BOARDS),selfie-opensbi-$(board).elf)

endef



###############################################################################
# $(call generate-target-vars,board,profile)
#
# - board         : The board
# - profile       : The build profile
#
define generate-target-vars
TARGET_$(1)_$(2)_DIR  = $(call target-build-dir,$(1),$(2))
TARGET_$(1)_$(2)_OUT_TREE = $$(sort $$(TARGET_$(1)_$(2)_DIR) $$(addprefix $$(TARGET_$(1)_$(2)_DIR)/,$$(filter-out ./,$$(dir $$(PROFILE_$(2)_SRCS)))))
TARGET_$(1)_$(2)_OBJS = $$(patsubst %.o,$$(TARGET_$(1)_$(2)_DIR)/%.o,$$(patsubst %.S,%.o,$$(PROFILE_$(2)_SRCS:.c=.o)))
TARGET_$(1)_$(2)_DEPS = $$(TARGET_$(1)_$(2)_OBJS:.o=.d)

ALL_TARGETS += $(1)_$(2)
ALL_DEPS += $$(TARGET_$(1)_$(2)_DEPS)
endef

###############################################################################
# $(call generate-target-obj-rules,board,profile)
#
# - board         : The board
# - profile       : The build profile
#
define generate-target-obj-rules

$$(TARGET_$(1)_$(2)_OUT_TREE):
	mkdir -p $$@

# Make requires a static pattern rule to add prerequisites
# https://stackoverflow.com/a/46946731
$$(TARGET_$(1)_$(2)_OBJS): %.o: | include/asm_offsets.h

$$(TARGET_$(1)_$(2)_DIR)/%.o: %.c | $$(TARGET_$(1)_$(2)_OUT_TREE)
	$$(CC) -c $$(CFLAGS) $$(PROFILE_$(2)_DEFINES) $$< -o $$@
$$(TARGET_$(1)_$(2)_DIR)/%.o: %.S | $$(TARGET_$(1)_$(2)_OUT_TREE)
	$$(AS) -c $$(ASFLAGS) $$(PROFILE_$(2)_DEFINES) $$< -o $$@

$$(TARGET_$(1)_$(2)_DIR)/selfie.o: $$(SELFIE_PATH)/selfie.c
	$$(CC) $$(CFLAGS) -Wno-return-type -D'uint64_t = unsigned long long int' -c $$^ -o $$@

endef

###############################################################################
# $(call generate-target-combine-rule,board,profile)
#
# - board         : The board
# - profile       : The build profile
#
define generate-target-combine-rule

$$(TARGET_$(1)_$(2)_DIR)/selfie_bare_metal.o: $$(TARGET_$(1)_$(2)_OBJS)
	$$(LD) $$(LDFLAGS) $$^ -o $$@

endef

###############################################################################
# $(call generate-target-elf-bin,board,profile)
#
# - board         : The board
# - profile       : The build profile
#
define generate-target-elf-bin

$$(TARGET_$(1)_$(2)_DIR)/selfie.ld:
	SBI_START=$$(BOARD_$(1)_PAYLOAD_START) PAYLOAD_OFFSET=$$(BOARD_$(1)_PAYLOAD_OFFSET) envsubst '$$$$SBI_START$$$$PAYLOAD_OFFSET' <payload_template.ld >$$@


$$(TARGET_$(1)_$(2)_DIR)/selfie.elf: $$(TARGET_$(1)_$(2)_DIR)/selfie_bare_metal.o | $$(TARGET_$(1)_$(2)_DIR)/selfie.ld
	$$(CC) $$(CFLAGS) -static-libgcc -lgcc $$^ -o $$@ -T $$(TARGET_$(1)_$(2)_DIR)/selfie.ld

$$(TARGET_$(1)_$(2)_DIR)/selfie.bin: $$(TARGET_$(1)_$(2)_DIR)/selfie.elf
	$$(OBJCOPY) -S -O binary $$< $$@

.PHONY: selfie-$(1)-$(2).elf
selfie-$(1)-$(2).elf: $$(TARGET_$(1)_$(2)_DIR)/selfie.elf

.PHONY: selfie-$(1)-$(2).bin
selfie-$(1)-$(2).bin: $$(TARGET_$(1)_$(2)_DIR)/selfie.bin

ALL_ELF_TARGETS += $$(TARGET_$(1)_$(2)_DIR)/selfie.elf
ALL_BIN_TARGETS += $$(TARGET_$(1)_$(2)_DIR)/selfie.bin

endef


###############################################################################
# $(call generate-target-sbi-elf,board,profile)
#
# - board         : The board
# - profile       : The build profile
#
define generate-target-sbi-elf

$$(TARGET_$(1)_$(2)_DIR)/selfie-opensbi.elf: $$(TARGET_$(1)_$(2)_DIR)/selfie.bin | opensbi
	$$(MAKE) -C opensbi CROSS_COMPILE=$$(PREFIX) PLATFORM_RISCV_XLEN=64 PLATFORM=$$(BOARD_$(1)_SBI_NAME) O=build-$(2)/ FW_PAYLOAD=y FW_PAYLOAD_PATH=$$(realpath $$<) FW_TEXT_START=$$(BOARD_$(1)_PAYLOAD_START) FW_PAYLOAD_OFFSET=$$(BOARD_$(1)_PAYLOAD_OFFSET)
	mv opensbi/build-$(2)/platform/$$(BOARD_$(1)_SBI_NAME)/firmware/fw_payload.elf $$@
	rm -r opensbi/build-$(2)/platform/$$(BOARD_$(1)_SBI_NAME)/firmware/*

.PHONY: selfie-opensbi-$(1)-$(2).elf
selfie-opensbi-$(1)-$(2).elf: $$(TARGET_$(1)_$(2)_DIR)/selfie-opensbi.elf

ALL_OPENSBI_ELF_TARGETS += $$(TARGET_$(1)_$(2)_DIR)/selfie-opensbi.elf

endef

###############################################################################
# $(call target-build-dir,board,profile)
#
# - board         : The board
# - profile       : The build profile
#
define target-build-dir
$$(BUILD_DIR)/$(1)/$(2)
endef
