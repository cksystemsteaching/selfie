#ifndef KERN_ELF
#define KERN_ELF

#include "context.h"

#define ELF_MAGIC "\177ELF"

#define ELF_CLASS_32 0x01
#define ELF_CLASS_64 0x02

#define ELF_ENDIANESS_LITTLE 0x01
#define ELF_ENDIANESS_BIG 0x02

#define ELF_TYPE_NONE 0x00 // No file type
#define ELF_TYPE_REL  0x01 // Relocatable
#define ELF_TYPE_EXEC 0x02 // Executable
#define ELF_TYPE_DYN  0x03 // Shared objects
#define ELF_TYPE_CORE 0x03 // Core dump

#define ELF_MACHINE_RISCV 243

#define ELF_VERSION_1 0x01

#define ELF_PH_TYPE_NULL 0x00 // Unused
#define ELF_PH_TYPE_LOAD 0x01 // Loadable segment

#define ELF_PH_FLAG_EXECUTABLE 1
#define ELF_PH_FLAG_WRITABLE   2
#define ELF_PH_FLAG_READABLE   4

#define ENOELF          1   // No valid ELF file
#define EOOB            2   // Out of Bounds
#define EINVMACHINE     3   // Executable is not RISC-V
#define EINVCLASS       4   // Executable is not 64 bits
#define EINVTYPE        5   // ELF file is not an executable
#define EUNSUPPORTED    6   // ELF file contains unsupported features
#define EOOM            7   // File couldn't be mapped entirely
#define EINVVADDR       8   // Virtual address is invalid or in upper half

int load_elf(struct context* context, const char* elf, uint64_t len);

const char* elf_strerror(int errno);

#endif /* KERN_ELF */
