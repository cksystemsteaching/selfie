# General

# Sections
For whatever reason, the linker adds sections that were not explicitly specified in the linker script.
Unfortunately, this means that some sections that were not explicitly relocated in the linker script may be inserted at seemingly random locations. It turns out that `ld` just places them where they have been before.
It is not possible to discard all unmentioned sections, however, it is possible to discard _explicitly specified_ sections.

This was the reason for the sbss and sdata problems.

## -Wl,--build-id=none
Per default, a hosted compiler adds a build ID to the binary to uniquely identify a build artefact (SHA1 or MD5). The respective section, `.note.gnu.build-id`, is placed at the very beginning of the ELF file and messes up the whole address placement of the .text section so that OpenSBI jumps to the build ID. As we don't need an build ID, discard it using a linker flag

## Static libgcc (--static-libgcc -lgcc)
GCC may emit calls to its support library `libgcc` at its own whim. Unfortunately, `libgcc` itself depends on an implementation of `memset`, `memcpy`, `memcmp` and `memmove`. As we do not have any dynamic linking facilities, we require libgcc to be statically linked. Procedures of a statically linked library that are not used are usually not included into the output (source missing).

# Sources
* https://stackoverflow.com/q/41511317/2909011
* https://sourceware.org/binutils/docs-2.23.1/ld/Options.html#Options
* https://wiki.osdev.org/Libgcc
* https://gcc.gnu.org/onlinedocs/gccint/Libgcc.html
* https://gcc.gnu.org/onlinedocs/gcc-9.2.0/gcc/Standards.html
