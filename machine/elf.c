#include "diag.h"
#include "elf.h"
#include "mmu.h"
#include "numeric-utils.h"
#include "tinycstd.h"

// https://refspecs.linuxbase.org/elf/elf.pdf
// https://uclibc.org/docs/elf-64-gen.pdf
struct elf_header {
  struct {
    char magic[4];
    uint8_t class;
    uint8_t endianness;
    uint8_t version;
    uint8_t os_abi;
    uint8_t abi_version;
    char pad[7];
  } __attribute__((packed)) ident;
  uint16_t type;
  uint16_t machine;
  uint32_t version;

  uint64_t entry_point;

  uint64_t program_header_offset;
  uint64_t section_header_offset;

  uint32_t flags;

  uint16_t header_size;
  uint16_t program_header_entry_size;
  uint16_t program_header_entries;
  uint16_t section_header_entry_size;
  uint16_t section_header_entries;
  uint16_t section_header_string_table_index;
} __attribute__((packed));

struct elf_program_header {
  uint32_t type;
  uint32_t flags;
  uint64_t offset;
  uint64_t vaddr;
  uint64_t paddr;
  uint64_t file_size;
  uint64_t mem_size;
  uint64_t alignment;
} __attribute__((packed));

int load_elf(struct context* context, const char* elf, uint64_t len) {
  uint64_t lowest_lo_page = SV39_MAX_VPN;
  uint64_t highest_lo_page = 0;

  if (len < sizeof(struct elf_header))
    return EOOB;

  struct elf_header* header = (struct elf_header*) elf;

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
  if (header->section_header_offset != 0x00
      || header->section_header_entry_size != 0x00
      || header->section_header_entries != 0x00) {
    return EUNSUPPORTED;
  }

  // Check if program header is in-bounds
  uint64_t ph_end = header->program_header_offset + (header->program_header_entries * header->program_header_entry_size);
  if (ph_end > len)
    return EOOB;


  struct elf_program_header* pheader = (struct elf_program_header*) (elf + header->program_header_offset);
  for (uint64_t i = 0; i < header->program_header_entries; i++) {
    if (pheader[i].type != ELF_PH_TYPE_LOAD)
      return EUNSUPPORTED;

    if (pheader[i].flags != (ELF_PH_FLAG_READABLE | ELF_PH_FLAG_WRITABLE | ELF_PH_FLAG_EXECUTABLE))
      return EUNSUPPORTED;

    uint64_t segment_end = pheader[i].offset + pheader[i].file_size;
    if (segment_end > len)
      return EOOB;

    // Check alignment on page boundaries
    assert(IS_ALIGNED(pheader[i].vaddr, 12));

    // Copy segment page-wise
    // Add PAGESIZE - 1 for rounding up without using floating points.
    // So if file_size is page-aligned, we do not wastefully map an empty page (integer div)
    // (e.g. file_size = 4096 (1 page) -> 1 but file_size = 4097 (1 page + 1 byte) -> 2 pages)
    uint64_t segment_file_pages = (pheader[i].file_size + (PAGESIZE - 1)) / PAGESIZE;

    for (uint64_t page = 0; page < segment_file_pages; page++) {
      uint64_t vaddr = pheader[i].vaddr + (PAGESIZE * page);
      uint64_t faddr = pheader[i].offset + (PAGESIZE * page);

      if (vaddr_to_vpn(vaddr) >= vaddr_to_vpn(SV39_MIN_INVALID_VADDR))
        return EINVVADDR;

      uint64_t ppn = kmap_page(context->pt, vaddr, true);

      if (ppn == 0x00)
        return EOOM;

      lowest_lo_page = MIN(lowest_lo_page, vaddr_to_vpn(vaddr));
      highest_lo_page = MAX(highest_lo_page, vaddr_to_vpn(vaddr));

      memcpy((void *) ppn_to_paddr(ppn), (void *) (elf + faddr), PAGESIZE);
    }

    uint64_t segment_mem_pages = (pheader[i].mem_size + (PAGESIZE - 1)) / PAGESIZE;
    uint64_t page_delta = segment_mem_pages - segment_file_pages;

    for (uint64_t page = 0; page < page_delta; page++) {
      uint64_t vaddr = pheader[i].vaddr + (page + segment_file_pages) * PAGESIZE;

      if (vaddr_to_vpn(vaddr) >= vaddr_to_vpn(SV39_MIN_INVALID_VADDR))
        return EINVVADDR;

      bool map_successful = kmap_page(context->pt, vaddr, true);

      if (!map_successful)
        return EOOM;

      lowest_lo_page = MIN(lowest_lo_page, vaddr_to_vpn(vaddr));
      highest_lo_page = MAX(highest_lo_page, vaddr_to_vpn(vaddr));
    }

    if (context->program_break < pheader[i].vaddr + pheader[i].mem_size)
      context->program_break = pheader[i].vaddr + pheader[i].mem_size;
  }

  context->legal_memory_boundaries.lowest_lo_page = lowest_lo_page;
  context->legal_memory_boundaries.highest_lo_page = highest_lo_page;

  context->saved_regs.pc = header->entry_point;

  return 0;
}

const char* elf_strerror(int errno) {
  switch (errno) {
    case 0x0:
      return "No error";
    case ENOELF:
      return "Not an ELF file";
    case EOOB:
      return "ELF offset out-of-bounds";
    case EINVMACHINE:
      return "Executable is not RISC-V";
    case EINVCLASS:
      return "Executable is not 64 bits";
    case EINVTYPE:
      return "ELF file is not an executable";
    case EUNSUPPORTED:
      return "ELF file contains features unsupported by the loader";
    case EOOM:
      return "ELF file could not be mapped entirely because the kernel is out-of-memory";
    default:
      return "Unknown error";
  }
}
