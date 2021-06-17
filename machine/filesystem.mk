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
	@echo "const KFILE files[] = {" >>$@;
	@for file in $^;\
	do \
		BASENAME=`basename $$file` ;\
		VARIABLENAME=`echo $$BASENAME | sed 's/\W/_/g'`; \
		FILESIZE=`wc -c "$$file" | awk '{print $$1}'`; \
		echo "  {\"$$BASENAME\", $$VARIABLENAME, $$FILESIZE}," >>$@; \
	done;
	@echo "  {\"\", (const char*) NULL, 0}," >>$@;
	@echo "};" >>$@;

.PHONY: clean-fs-package
clean-fs-package:
	rm -f files_package.c
