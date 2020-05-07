###############################################################################
# $(call generate_ldscript,path,sbi_start,payload_offset)
#
# Generates a rule for a given target that
# requires the following parameters:
# - path          : The path where the linker script shall be emitted
# - sbi_start     : The position where the PC jumps, i.e. where the supervisor binary will be loaded to.
# - payload_offset: The offset of the payload in the OpenSBI binary
#
define generate_payload_ldscript
	SBI_START=$(2) PAYLOAD_OFFSET=$(3) envsubst '$$SBI_START$$PAYLOAD_OFFSET' <payload_template.ld >$(1)
endef

###############################################################################
# $(eval $(call generate_payload_rules,board,sbi_start,payload_offset))
#
# Generates rules for a board to build both an ELF image as well as a plain binary
# using the board-agnostic selfie_bare_metal.o object file.
#
define generate_payload_rules
payload-$(1).elf: selfie_bare_metal.o
	$$(call generate_payload_ldscript,payload-$(1).ld,$(2),$(3))
	$$(CC) $$(CFLAGS) -static-libgcc -lgcc $$^ -o $$@ -T payload-$(1).ld

payload-$(1).bin: payload-$(1).elf
	$$(OBJCOPY) -S -O binary $$< $$@
endef

# $(eval $(call generate_selfie_sbi_rules,board,sbi_plat,sbi_start,offset)
#
define generate_selfie_sbi_rule
selfie-$(1).elf: payload-$(1).bin
	$$(MAKE) -C opensbi CROSS_COMPILE=$$(PREFIX) PLATFORM_RISCV_XLEN=64 PLATFORM=$(2) O=build/ FW_PAYLOAD=y FW_PAYLOAD_PATH=$$(realpath $$<) FW_TEXT_START=$(3) FW_PAYLOAD_OFFSET=$(4)
	mv opensbi/build/platform/$(2)/firmware/fw_payload.elf $$@
endef
