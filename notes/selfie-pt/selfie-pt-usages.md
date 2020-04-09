# `get_pt`
* `implement_read`
    * `is_virtual_address_mapped`
    * `tlb`
* `implement_write`
    * `is_virtual_address_mapped`
    * `tlb`
* `implement_openat`
    * `down_load_string`
* `do_switch`
    * sets global variable `pt`
* `save_context`
    * `store_virtual_memory` (6 usages)
    * `load_virtual_memory`
* `map_page`
    * maps new page frame to a page
* `restore_context`
    * `store_virtual_memory` (2 usages)
    * `load_virtual_memory` (12 usages)
    * `restore_region`
* `map_and_store`
    * `is_virtual_address_mapped`
    * `store_virtual_memory`
* `map_unmapped_pages`
    * `is_page_mapped`
* `selfie_model_generate`
    * sets global variable `pt`



# `set_pt`
* `init_context`
    * allocates memory and sets pt for new context
* `copy_context`
    * sets pt of context to the global `pt` variable



# global variable `pt`
* `reset_interpreter`
    * variable reset
* `do_switch`
    * gets set to the pt of `to_context`
* `print_ld_before`
    * `is_virtual_address_mapped`
    * `load_virtual_memory` (2 usages)
* `print_ld_after`
    * `is_virtual_address_mapped`
* `record_ld`
    * `is_virtual_address_mapped`
* `do_ld`
    * `is_virtual_address_mapped`
    * `load_virtual_memory`
* `constrain_ld`
    * `load_virtual_memory`
* `print_sd_before`
    * `is_virtual_address_mapped`
    * `load_virtual_memory` (2 usages)
* `print_sd_after`
    * `is_virtual_address_mapped`
* `record_sd`
    * `is_virtual_address_mapped`
    * `load_virtual_memory`
* `do_sd`
    * `is_virtual_address_mapped`
    * `store_virtual_memory`
* `undo_sd`
    * `store_virtual_memory`
* `fetch`
    * `load_virtual_memory` (2 usages)
* `copy_context`
    * `set_pt` (2 contexts use the same page table)
* `selfie_model_generate`
    * `pt` gets set to the pt of `current_context`
    * `load_virtual_memory`



# functions that receive a page table as parameter
## functions
* `void set_pt(uint64_t* context, uint64_t* pt)`
* `uint64_t is_virtual_address_mapped(uint64_t* table, uint64_t vaddr)`
    * `return is_page_mapped(table, get_page_of_virtual_address(vaddr));`
* `uint64_t* tlb(uint64_t* table, uint64_t vaddr)`
    * `frame = get_frame_for_page(table, page);`
* `uint64_t down_load_string(uint64_t* table, uint64_t vaddr, char* s)`
    * `*((uint64_t*) s + i) = load_virtual_memory(table, vaddr);`
    * `*((uint64_t*) s + i) = load_virtual_memory(table, vaddr);`
* `void store_virtual_memory(uint64_t* table, uint64_t vaddr, uint64_t data)`
    * `store_physical_memory(tlb(table, vaddr), data);`
        * `tlb(table, vaddr)`
* `uint64_t load_virtual_memory(uint64_t* table, uint64_t vaddr)`
    * `return load_physical_memory(tlb(table, vaddr));`
        * `tlb(table, vaddr)`
* `void restore_region(uint64_t* context, uint64_t* table, uint64_t* parent_table, uint64_t lo, uint64_t hi)`
    * `if (is_virtual_address_mapped(parent_table, frame_for_page(table, lo)))`
        * `frame_for_page(table, lo)`
    * `frame = load_virtual_memory(parent_table, frame_for_page(table, lo));`
        * `frame_for_page(table, lo)`
    * `get_frame_for_page(parent_table, get_page_of_virtual_address(frame))`
* `uint64_t is_page_mapped(uint64_t* table, uint64_t page)`
    * `if (get_frame_for_page(table, page) != 0)`
* `uint64_t get_frame_for_page(uint64_t* table, uint64_t page)`
    * `return *(table + page);`
* `uint64_t frame_for_page(uint64_t* table, uint64_t page)`
    * `return (uint64_t) (table + page);`

## where changes are needed
* `get_frame_for_page`
    * check if page is in lo or hi page table and return 0 if not

# kernel functions for page frame management
* `pavailable()`
* `pexcess()`
* `pused()`
* `palloc()`
* `pfree()`
