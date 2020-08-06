#include "elf.h"
#include "mmu.h"
#include "tinycstd.h"

// https://refspecs.linuxbase.org/elf/elf.pdf
// https://uclibc.org/docs/elf-64-gen.pdf
struct ElfHeader {
    struct {
        char magic[4];
        uint8_t class;
        uint8_t endianness;
        uint8_t version;
        char pad[8];
        uint8_t size;
    } __attribute__((packed)) ident;
    uint16_t type;
    uint16_t machine;
    uint32_t version;

    uint64_t entryPoint;

    uint64_t programHeaderOffset;
    uint64_t sectionHeaderOffset;

    uint32_t flags;

    uint16_t headerSize;
    uint16_t programHeaderEntrySize;
    uint16_t programHeaderEntries;
    uint16_t sectionHeaderEntrySize;
    uint16_t sectionHeaderEntries;
    uint16_t sectionHeaderStringTableIndex;
} __attribute__((packed));

struct ElfProgramHeader {
    uint32_t type;
    uint32_t flags;
    uint64_t offset;
    uint64_t vaddr;
    uint64_t paddr;
    uint64_t fileSize;
    uint64_t memSize;
    uint64_t alignment;
} __attribute__((packed));

int load_elf(struct context* context, const char* elf, uint64_t len) {
    if (len < sizeof(struct ElfHeader))
        return EOOB;

    struct ElfHeader* header = (struct ElfHeader*) elf;

    // Check whether this is a valid ELF file
    if (strncmp(ELF_MAGIC, header->ident.magic, sizeof(ELF_MAGIC) - 1))
        return ENOELF;

    // Check system constraints: RV64 executable (little endian)
    if (header->ident.class != ELF_CLASS_64)
        return EINVCLASS;
    if (header->ident.endianness != ELF_ENDIANESS_LITTLE)
        return EINVMACHINE;
    if (header->type != ELF_TYPE_EXEC)
        return EINVTYPE;
    if (header->machine != ELF_MACHINE_RISCV)
        return EINVMACHINE;

    // Support selfie's binaries for now
    // This means we don't require section header support
    if (header->sectionHeaderOffset != 0x00
            || header->sectionHeaderEntrySize != 0x00
            || header->sectionHeaderEntries != 0x00) {
        return EUNSUPPORTED;
    }

    // Check if program header is in-bounds
    uint64_t phEnd = header->programHeaderOffset + (header->programHeaderEntries * header->programHeaderEntrySize);
    if (phEnd > len)
        return EOOB;


    struct ElfProgramHeader* pheader = (struct ElfProgramHeader*)(elf + header->programHeaderOffset);
    for (uint64_t i = 0; i < header->programHeaderEntries; i++) {
        if (pheader[i].type != ELF_PH_TYPE_LOAD)
            return EUNSUPPORTED;

        uint64_t segmentEnd = pheader[i].offset + pheader[i].fileSize;
        if (segmentEnd > len)
            return EOOB;

        // TODO: Check alignment

        // Copy segment page-wise
        // Add PAGESIZE-1 for rounding up without using floating points.
        // So if fileSize is page-aligned, we do not wastefully map an empty page (integer div)
        // (e.g. fileSize=4096 (1 page) -> 1 but fileSize=4097 (1 page + 1 byte) -> 2 pages)
        uint64_t segmentFilePages = (pheader[i].fileSize + (PAGESIZE - 1)) / PAGESIZE;

        for (uint64_t page = 0; page < segmentFilePages; page++) {
            uint64_t vaddr = pheader[i].vaddr + (PAGESIZE * page);
            uint64_t faddr = pheader[i].offset + (PAGESIZE * page);
            uint64_t ppn = kmap_page(context->pt, vaddr, true);

            kidentity_map_ppn(kernel_pt, ppn, false);
            memcpy((void *)ppn_to_paddr(ppn), (void *)(elf + faddr), PAGESIZE);
        }

        uint64_t segmentMemPages = (pheader[i].memSize + (PAGESIZE - 1)) / PAGESIZE;
        uint64_t pageDelta = segmentMemPages - segmentFilePages;

        for (uint64_t page = 0; page < pageDelta; page++) {
            uint64_t vaddr = pheader[i].vaddr + (page+segmentFilePages)*PAGESIZE;
            uint64_t ppn = kmap_page(context->pt, vaddr, true);
            kidentity_map_ppn(kernel_pt, ppn, false);
        }
    }

    context->saved_regs.pc = header->entryPoint;

    return 0;
}
