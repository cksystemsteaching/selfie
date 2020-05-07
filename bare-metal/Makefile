OPENSBI_SOURCE_URL=https://github.com/riscv/opensbi/archive/$(OPENSBI_RELEASE).tar.gz
OPENSBI_RELEASE=v0.7


all: selfie-qemu selfie-fu540 selfie-k210

selfie-qemu: opensbi
	echo "Test"

selfie-fu540: opensbi
	echo "Test"

selfie-k210: opensbi
	echo "Test"


# Clean-up
.PHONY: clean
clean:
	rm -rf opensbi


# OpenSBI fetch target
opensbi:
	@curl -L "$(OPENSBI_SOURCE_URL)" -o opensbi.tar.gz
	@tar xf opensbi.tar.gz

	@# Get the directory name from the tar listing and rename it to plain 'opensbi'
	@SBI_DIR=`tar tf opensbi.tar.gz | sed -rn 's/^(opensbi-[^\/]+)\/$$/\1/p'` && mv $$SBI_DIR opensbi
	@rm opensbi.tar.gz
