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
