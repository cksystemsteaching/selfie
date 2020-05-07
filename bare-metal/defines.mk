# $(call generate_ldscript,path,sbi_start,payload_offset)
# Generates a rule for a given target that
# requires the following parameters:
# - path          : The path where the linker script shall be emitted
# - sbi_start     : The position where the PC jumps, i.e. where the supervisor binary will be loaded to.
# - payload_offset: The offset of the payload in the OpenSBI binary
define generate_payload_ldscript
	SBI_START=$(2) PAYLOAD_OFFSET=$(3) envsubst '$$SBI_START$$PAYLOAD_OFFSET' <payload_template.ld >$(1)
endef


