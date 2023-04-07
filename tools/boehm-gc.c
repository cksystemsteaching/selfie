/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

http://selfie.cs.uni-salzburg.at

Boehm GC is a Selfie implementation of a garbage collector originally
developed by Hans Boehm, Alan Demers, and Mark Weiser. It is a
conservative garbage collector that uses the mark sweep algorithm.

Boehm GC runs allocation and collection in constant time. It runs in
parallel to the Selfie GC, since this implementation only contains the
allocation and collection of small objects. Large objects are delegated
to the Selfie GC. Just like the Selfie GC, the Boehm GC is available
in both syscall and library variants.
*/

// --- boehm hook implementations ---

void gc_init_boehm(uint64_t* context);
uint64_t* allocate_memory_boehm(uint64_t* context, uint64_t size);
uint64_t mark_object_boehm(uint64_t* context, uint64_t gc_address);
void sweep_boehm(uint64_t* context);

// --- boehm gc context extension ---

// +----+-------------------------+
// | +0 | chunk heap start        | start of the chunk heap segment
// | +1 | chunk heap bump         | bump pointer of chunk heap segment
// | +2 | chunk used list head    | pointer to head of the chunk used list
// | +3 | chunk free list head    | pointer to head of the chunk free list
// | +4 | small object free lists | pointer to array containing all small object free lists
// +----+-------------------------+

uint64_t* allocate_context() {
  return smalloc(CONTEXTENTRIES * sizeof(uint64_t) + 5 * sizeof(uint64_t*));
}

uint64_t* get_chunk_heap_start(uint64_t* context)           { return (uint64_t*) *(context + CONTEXTENTRIES); }
uint64_t* get_chunk_heap_bump(uint64_t* context)            { return (uint64_t*) *(context + CONTEXTENTRIES + 1); }
uint64_t* get_chunk_used_list_head(uint64_t* context)       { return (uint64_t*) *(context + CONTEXTENTRIES + 2); }
uint64_t* get_chunk_free_list_head(uint64_t* context)       { return (uint64_t*) *(context + CONTEXTENTRIES + 3); }
uint64_t* get_small_object_free_lists(uint64_t* context)    { return (uint64_t*) *(context + CONTEXTENTRIES + 4); }

void set_chunk_heap_start(uint64_t* context, uint64_t* chunk_heap_start)                { *(context + CONTEXTENTRIES)     = (uint64_t) chunk_heap_start; }
void set_chunk_heap_bump(uint64_t* context, uint64_t* chunk_heap_bump)                  { *(context + CONTEXTENTRIES + 1) = (uint64_t) chunk_heap_bump; }
void set_chunk_used_list_head(uint64_t* context, uint64_t* chunk_used_list_head)        { *(context + CONTEXTENTRIES + 2) = (uint64_t) chunk_used_list_head; }
void set_chunk_free_list_head(uint64_t* context, uint64_t* chunk_free_list_head)        { *(context + CONTEXTENTRIES + 3) = (uint64_t) chunk_free_list_head; }
void set_small_object_free_lists(uint64_t* context, uint64_t* small_object_free_lists)  { *(context + CONTEXTENTRIES + 4) = (uint64_t) small_object_free_lists; }

// getters and setters with different access in library/kernel

uint64_t* get_chunk_heap_start_gc(uint64_t* context);
uint64_t* get_chunk_heap_bump_gc(uint64_t* context);
uint64_t* get_chunk_used_list_head_gc(uint64_t* context);
uint64_t* get_chunk_free_list_head_gc(uint64_t* context);
uint64_t* get_small_object_free_lists_gc(uint64_t* context);

void set_chunk_heap_start_gc(uint64_t* context, uint64_t* chunk_heap_start);
void set_chunk_heap_bump_gc(uint64_t* context, uint64_t* chunk_heap_bump);
void set_chunk_used_list_head_gc(uint64_t* context, uint64_t* chunk_used_list_head);
void set_chunk_free_list_head_gc(uint64_t* context, uint64_t* chunk_free_list_head);
void set_small_object_free_lists_gc(uint64_t* context, uint64_t* small_object_free_lists);

// boehm chunks

// chunk header:
// +----+-------------+
// |  0 | list ptr    | pointer to chunk used list
// |  1 | obj size    | size of objects contained in chunk
// | 2..| markbit(s)  | markbit indicating reachability of object (object 0 ... markbit 0)
// | 3..| allocbit(s) | allocbit indicating if object is allocated (object 0 ... allocbit 0)
// +----+-------------+

uint64_t* allocate_chunk(uint64_t* context, uint64_t object_size);
void free_chunk(uint64_t* context, uint64_t* entry);

void align_chunk_allocator(uint64_t* context);
void init_chunk(uint64_t* context, uint64_t* chunk_list_entry);

uint64_t* get_chunk_list_pointer(uint64_t* entry) { return (uint64_t*) *entry; }
uint64_t  get_chunk_object_size(uint64_t* entry)  { return             *(entry + 1); }

uint64_t get_chunk_object_markbit(uint64_t* entry, uint64_t object_index);
uint64_t get_chunk_object_allocbit(uint64_t* entry, uint64_t object_index);

void set_chunk_list_pointer(uint64_t* entry, uint64_t* list_pointer) { *entry       = (uint64_t) list_pointer; }
void set_chunk_object_size(uint64_t* entry, uint64_t object_size)    { *(entry + 1) = object_size; }

void set_chunk_object_markbit(uint64_t* entry, uint64_t object_index, uint64_t markbit);
void set_chunk_object_allocbit(uint64_t* entry, uint64_t object_index, uint64_t allocbit);

void zero_chunk_markbits(uint64_t* entry);
void zero_chunk_allocbits(uint64_t* entry);

void refurbish_chunk(uint64_t* entry);

uint64_t calculate_number_of_words_for_object_bits(uint64_t object_size);

uint64_t calculate_chunk_payload_offset_bytes(uint64_t object_size);
uint64_t calculate_chunk_payload_offset_words(uint64_t object_size);

uint64_t is_address_valid_chunk_object_of_specific_chunk(uint64_t* context, uint64_t address, uint64_t* chunk_list_entry);
uint64_t is_chunk_referenced(uint64_t* entry);

void fill_small_object_free_list(uint64_t* context, uint64_t* entry);

uint64_t* allocate_object(uint64_t* context, uint64_t size);
void free_chunk_object(uint64_t* context, uint64_t* object);

uint64_t calculate_chunk_small_object_index(uint64_t* context, uint64_t* object);

// chunk and small object (coso) list entry:
// +---+--------+
// | 0 | next   | pointer to next entry
// | 1 | memory | pointer to allocated memory (syscall: virtual address)
// +---+--------+

uint64_t* allocate_coso_list_entry(uint64_t* context);

uint64_t* get_coso_list_entry_next(uint64_t* entry)   { return (uint64_t*) *entry; }
uint64_t* get_coso_list_entry_memory(uint64_t* entry) { return (uint64_t*) *(entry + 1); }

void set_coso_list_entry_next(uint64_t* entry, uint64_t* next)     { *entry       = (uint64_t) next; }
void set_coso_list_entry_memory(uint64_t* entry, uint64_t* memory) { *(entry + 1) = (uint64_t) memory; }

uint64_t* get_chunk_list_entry_memory(uint64_t* context, uint64_t* entry);

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t GC_COSO_LIST_ENTRY_SIZE = 16; // 2 * sizeof(uint64_t);
uint64_t GC_STATIC_HEADER_SIZE_IN_WORDS = 2;

uint64_t GC_CHUNK_HEAP_SIZE = 104857600; // fixed chunk heap of 1MB*100 (can hold 256*100 chunks)
uint64_t GC_CHUNK_SIZE = 4096; // same as pagesize
uint64_t GC_CHUNK_SIZE_LOG2 = 12;
uint64_t GC_CHUNK_MIN_HEADER_SIZE = 32; // only one object inside chunk (require single markbit)
uint64_t GC_CHUNK_MAX_SMALL_OBJECT_SIZE = 2032;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t* gc_chunk_heap_start = (uint64_t*) 0;
uint64_t* gc_chunk_heap_bump  = (uint64_t*) 0;

uint64_t* gc_chunk_used_list         = (uint64_t*) 0;
uint64_t* gc_chunk_free_list         = (uint64_t*) 0;
uint64_t* gc_small_object_free_lists = (uint64_t*) 0;

// Definition

uint64_t* get_chunk_heap_start_gc(uint64_t* context) {
  if (is_gc_library(context))
    return gc_chunk_heap_start;
  else
    return get_chunk_heap_start(context);
}

uint64_t* get_chunk_heap_bump_gc(uint64_t* context) {
    if (is_gc_library(context))
    return gc_chunk_heap_bump;
  else
    return get_chunk_heap_bump(context);
}

uint64_t* get_chunk_used_list_head_gc(uint64_t* context) {
    if (is_gc_library(context))
    return gc_chunk_used_list;
  else
    return get_chunk_used_list_head(context);
}

uint64_t* get_chunk_free_list_head_gc(uint64_t* context) {
    if (is_gc_library(context))
    return gc_chunk_free_list;
  else
    return get_chunk_free_list_head(context);
}

uint64_t* get_small_object_free_lists_gc(uint64_t* context) {
    if (is_gc_library(context))
    return gc_small_object_free_lists;
  else
    return get_small_object_free_lists(context);
}

void set_chunk_heap_start_gc(uint64_t* context, uint64_t* chunk_heap_start) {
  if (is_gc_library(context))
    gc_chunk_heap_start = chunk_heap_start;
  else
    set_chunk_heap_start(context, chunk_heap_start);
}

void set_chunk_heap_bump_gc(uint64_t* context, uint64_t* chunk_heap_bump) {
  if (is_gc_library(context))
    gc_chunk_heap_bump = chunk_heap_bump;
  else
    set_chunk_heap_bump(context, chunk_heap_bump);
}

void set_chunk_used_list_head_gc(uint64_t* context, uint64_t* chunk_used_list_head) {
  if (is_gc_library(context))
    gc_chunk_used_list = chunk_used_list_head;
  else
    set_chunk_used_list_head(context, chunk_used_list_head);
}

void set_chunk_free_list_head_gc(uint64_t* context, uint64_t* chunk_free_list_head) {
  if (is_gc_library(context))
    gc_chunk_free_list = chunk_free_list_head;
  else
    set_chunk_free_list_head(context, chunk_free_list_head);
}

void set_small_object_free_lists_gc(uint64_t* context, uint64_t* small_object_free_lists) {
  if (is_gc_library(context))
    gc_small_object_free_lists = small_object_free_lists;
  else
    set_small_object_free_lists(context, small_object_free_lists);
}

uint64_t* allocate_chunk(uint64_t* context, uint64_t object_size) {
  uint64_t* chunk_list_entry;
  uint64_t* ret;

  // 1. Handle chunk allocation/reuse

  // assert: chunk size is always GC_CHUNK_SIZE (since we do not support large objects)

  chunk_list_entry = get_chunk_free_list_head_gc(context);

  if (chunk_list_entry == (uint64_t*) 0) {
    chunk_list_entry = allocate_coso_list_entry(context);

    set_coso_list_entry_memory(chunk_list_entry, get_chunk_heap_bump_gc(context));
    set_chunk_heap_bump_gc(context, get_chunk_heap_bump_gc(context) + GC_CHUNK_SIZE / sizeof(uint64_t));

    if ((uint64_t) get_chunk_heap_bump_gc(context) >= ((uint64_t) get_chunk_heap_start_gc(context) + GC_CHUNK_HEAP_SIZE)) {
      printf("%s: chunk heap size exceeded\n", selfie_name);

      exit(EXITCODE_OUTOFVIRTUALMEMORY);
    }

    init_chunk(context, chunk_list_entry);
  } else
    set_chunk_free_list_head_gc(context, get_coso_list_entry_next(chunk_list_entry));

  set_coso_list_entry_next(chunk_list_entry, get_chunk_used_list_head_gc(context));
  set_chunk_used_list_head_gc(context, chunk_list_entry);

  // 2. Handle chunk header

  ret = get_chunk_list_entry_memory(context, chunk_list_entry);

  // Note: when using the syscall variant, the application basically gets a handle to the emulator's memory (i.e. it's physical memory)
  // Access to this memory may be restricted, but this must be implemented by the emulator. Potential overflow error!
  set_chunk_list_pointer(ret, chunk_list_entry);
  set_chunk_object_size(ret, object_size);
  refurbish_chunk(ret);

  return get_chunk_list_pointer(ret);
}

void free_chunk(uint64_t* context, uint64_t* entry) {
  uint64_t object_size;
  uint64_t* coso_entry;
  uint64_t* small_object_list_head_ptr;
  uint64_t* prev_it;
  uint64_t* it;
  uint64_t* next_it;

  coso_entry = get_chunk_list_pointer(entry);
  object_size = get_chunk_object_size(entry) / sizeof(uint64_t); // in memory words

  zero_chunk_allocbits(entry);

  // 1. remove chunk from used list

  prev_it = (uint64_t*) 0;
  it = get_chunk_used_list_head_gc(context);
  while (it != (uint64_t*) 0) {
    if (it == coso_entry) {
      if (prev_it == (uint64_t*) 0)
        set_chunk_used_list_head_gc(context, get_coso_list_entry_next(it));
      else
        set_coso_list_entry_next(prev_it, get_coso_list_entry_next(it));

      set_coso_list_entry_next(it, get_chunk_free_list_head_gc(context));

      set_chunk_free_list_head_gc(context, it);

      it = (uint64_t*) 0;
    } else {
      prev_it = it;

      it = get_coso_list_entry_next(it);
    }
  }

  // 2. remove all small object list entries

  prev_it = (uint64_t*) 0;
  small_object_list_head_ptr = get_small_object_free_lists_gc(context) + (object_size - 1);
  it = (uint64_t*)*(small_object_list_head_ptr);
  while (it != (uint64_t*) 0) {
    if (is_address_valid_chunk_object_of_specific_chunk(context, (uint64_t) get_coso_list_entry_memory(it), coso_entry)) {
      if (prev_it == (uint64_t*) 0)
        *(small_object_list_head_ptr) = (uint64_t) get_coso_list_entry_next(it);
      else
        set_coso_list_entry_next(prev_it, get_coso_list_entry_next(it));

      next_it = get_coso_list_entry_next(it);

      set_coso_list_entry_next(it, (uint64_t*) 0);
      set_coso_list_entry_memory(it, (uint64_t*) 0);

      it = next_it;
    } else {
      prev_it = it;

      it = get_coso_list_entry_next(it);
    }
  }
}

void align_chunk_allocator(uint64_t* context) {
  uint64_t pb;

  if (is_gc_library(context))
    pb = (uint64_t) smalloc_system(0);
  else
    pb = get_program_break(context);

  pb = pb % GC_CHUNK_SIZE;

  if (pb == 0)
    return;

  pb = GC_CHUNK_SIZE - pb;

  allocate_new_memory(context, pb);
}

void init_chunk(uint64_t* context, uint64_t* chunk_list_entry) {
  uint64_t chunk_vaddr;

  chunk_vaddr = (uint64_t) get_coso_list_entry_memory(chunk_list_entry);

  // mapping the page of a chunk is required before being able to write to it (only required for syscall)
  if (is_gc_library(context) == 0)
    if (is_virtual_address_mapped(get_pt(context), chunk_vaddr) == 0)
      map_page(context, get_page_of_virtual_address(chunk_vaddr), (uint64_t) palloc());
}

uint64_t get_chunk_object_markbit(uint64_t* entry, uint64_t object_index) {
  // assert: object_index is in bounds
  // assert: page containing vaddr is mapped
  return get_bits(*(entry + 2 + (object_index / SIZEOFUINT64INBITS)), (object_index % SIZEOFUINT64INBITS), 1);
}

uint64_t get_chunk_object_allocbit(uint64_t* entry, uint64_t object_index) {
  uint64_t num_words_object_bits;

  num_words_object_bits = calculate_number_of_words_for_object_bits(get_chunk_object_size(entry));

  // assert: object_index is in bounds
  // assert: page containing vaddr is mapped
  return get_bits(*(entry + GC_STATIC_HEADER_SIZE_IN_WORDS + num_words_object_bits + (object_index / SIZEOFUINT64INBITS)), (object_index % SIZEOFUINT64INBITS), 1);
}

uint64_t set_bit(uint64_t val, uint64_t at, uint64_t bit) {
  if (bit > 1)
    bit = 1;

  if (at > (SIZEOFUINT64INBITS - 1))
    return val;

  // assert: at in bounds (0-(SIZEOFUINT64INBITS - 1))

  // special cases:
  //   - at == 0                        -> "left shift calculation" would overflow power two table
  //   - at == (SIZEOFUINT64INBITS - 1) -> "right shift calculation" would overflow power two table

  if (at == 0)
    return bit + left_shift(right_shift(val, 1), 1);
  else {
    if (at == (SIZEOFUINT64INBITS - 1))
      return right_shift(left_shift(val, SIZEOFUINT64INBITS - at), SIZEOFUINT64INBITS - at) + left_shift(bit, at);
    else
      return right_shift(left_shift(val, SIZEOFUINT64INBITS - at), SIZEOFUINT64INBITS - at) + left_shift(bit, at) + left_shift(right_shift(val, at + 1), at + 1);
  }
}

void set_chunk_object_markbit(uint64_t* entry, uint64_t object_index, uint64_t markbit) {
  uint64_t* word_containing_bit;

  word_containing_bit = entry + GC_STATIC_HEADER_SIZE_IN_WORDS + (object_index / SIZEOFUINT64INBITS);

  *(word_containing_bit) = set_bit(*(word_containing_bit), (object_index % SIZEOFUINT64INBITS), markbit);
}

void set_chunk_object_allocbit(uint64_t* entry, uint64_t object_index, uint64_t allocbit) {
  uint64_t* word_containing_bit;
  uint64_t num_words_object_bits;

  // assert: object_index is in bounds
  // assert: page containing vaddr is mapped

  num_words_object_bits = calculate_number_of_words_for_object_bits(get_chunk_object_size(entry));

  // Recall - chunk header:
  // -------------------------------------------------------------
  // | chunk list pointer | object size | mark bits | alloc bits |
  // -------------------------------------------------------------
  word_containing_bit = entry + GC_STATIC_HEADER_SIZE_IN_WORDS + num_words_object_bits + (object_index / SIZEOFUINT64INBITS);

  *(word_containing_bit) = set_bit(*(word_containing_bit), (object_index % SIZEOFUINT64INBITS), allocbit);
}

void zero_chunk_markbits(uint64_t* entry) {
  uint64_t* word_containing_bit;
  uint64_t num_words_object_bits;

  // assert: object_index is in bounds
  // assert: page containing vaddr is mapped

  num_words_object_bits = calculate_number_of_words_for_object_bits(get_chunk_object_size(entry));

  // Recall - chunk header:
  // -------------------------------------------------------------
  // | chunk list pointer | object size | mark bits | alloc bits |
  // -------------------------------------------------------------
  word_containing_bit = entry + GC_STATIC_HEADER_SIZE_IN_WORDS;

  zero_memory(word_containing_bit, num_words_object_bits * sizeof(uint64_t));
}

void zero_chunk_allocbits(uint64_t* entry) {
  uint64_t* word_containing_bit;
  uint64_t num_words_object_bits;

  // assert: object_index is in bounds
  // assert: page containing vaddr is mapped

  num_words_object_bits = calculate_number_of_words_for_object_bits(get_chunk_object_size(entry));

  // Recall - chunk header:
  // -------------------------------------------------------------
  // | chunk list pointer | object size | mark bits | alloc bits |
  // -------------------------------------------------------------
  word_containing_bit = entry + GC_STATIC_HEADER_SIZE_IN_WORDS + num_words_object_bits;

  zero_memory(word_containing_bit, num_words_object_bits * sizeof(uint64_t));
}

void refurbish_chunk(uint64_t* entry) {
  zero_chunk_markbits(entry);
  zero_chunk_allocbits(entry);
}

uint64_t calculate_number_of_words_for_object_bits(uint64_t object_size) {
  uint64_t num_words_object_bits;

  num_words_object_bits = calculate_chunk_payload_offset_words(object_size);
  num_words_object_bits = num_words_object_bits - GC_STATIC_HEADER_SIZE_IN_WORDS; // subtract static part of header (chunk list pointer, object size fields)
  num_words_object_bits = num_words_object_bits / 2;                              // dynamic part of header consists of alloc and mark bits

  return num_words_object_bits;
}

uint64_t calculate_chunk_payload_offset_bytes(uint64_t object_size) {
  uint64_t ret;

  ret = (GC_CHUNK_SIZE - GC_CHUNK_MIN_HEADER_SIZE);              // -> max possible payload size
  ret = ret / object_size;                                       // max payload size -> #objects in payload (= #markbits)
  ret = round_up(ret, SIZEOFUINT64INBITS) / SIZEOFUINT64INBITS;  // #objects -> #words containing markbits
  ret = ret * sizeof(uint64_t);                                  // #words -> #bytes
  ret = ret * 2;                                                 // alloc and mark bits (dynamic part of header)
  ret = ret + sizeof(uint64_t) * GC_STATIC_HEADER_SIZE_IN_WORDS; // add static part of header

  return ret;
}

uint64_t calculate_chunk_payload_offset_words(uint64_t object_size) {
  return calculate_chunk_payload_offset_bytes(object_size) / sizeof(uint64_t);
}

uint64_t is_address_valid_chunk_object_of_specific_chunk(uint64_t* context, uint64_t address, uint64_t* chunk_list_entry) {
  uint64_t object_size;
  uint64_t chunk_payload;
  uint64_t chunk_fragmentation_start;

  object_size = get_chunk_object_size(get_chunk_list_entry_memory(context, chunk_list_entry));                      // object size in bytes
  chunk_payload = calculate_chunk_payload_offset_bytes(object_size);                                                // payload offset in bytes
  chunk_fragmentation_start = (GC_CHUNK_SIZE - chunk_payload);                                                      // payload size
  chunk_fragmentation_start = chunk_fragmentation_start / object_size;                                              // number of objects in chunk
  chunk_fragmentation_start = chunk_fragmentation_start * object_size;                                              // size of all objects in chunk
  chunk_fragmentation_start = chunk_fragmentation_start + chunk_payload;                                            // actual fragmentation offset
  chunk_payload = chunk_payload + (uint64_t) get_coso_list_entry_memory(chunk_list_entry);                          // + vaddr offset of chunk
  chunk_fragmentation_start = chunk_fragmentation_start + (uint64_t) get_coso_list_entry_memory(chunk_list_entry);  // + vaddr offset of chunk

  if ((uint64_t) address >= chunk_fragmentation_start)
    return 0;

  if ((uint64_t) address < chunk_payload)
    return 0;

  return 1;
}

uint64_t is_chunk_referenced(uint64_t* entry) {
  uint64_t markbits_iterator;
  uint64_t markbits_end;

  markbits_end = calculate_chunk_payload_offset_words(get_chunk_object_size(entry));  // end of chunk header (in words)
  markbits_end = markbits_end - GC_STATIC_HEADER_SIZE_IN_WORDS;                       // - static part of header -> only dynamic part remaining (i.e. mark, alloc bits)
  markbits_end = markbits_end / 2;                                                    // ... number of markbits (in words)
  markbits_end = markbits_end + GC_STATIC_HEADER_SIZE_IN_WORDS;                       // end of markbits ... static header + num markbit words

  markbits_iterator = GC_STATIC_HEADER_SIZE_IN_WORDS;

  while (markbits_iterator < markbits_end) {
    if (*(entry + markbits_iterator) != 0)
      return 1;

    markbits_iterator = markbits_iterator + 1;
  }

  return 0;
}

void fill_small_object_free_list(uint64_t* context, uint64_t* chunk_list_entry) {
  uint64_t object_size;
  uint64_t object_count;
  uint64_t i;
  uint64_t payload_offset;
  uint64_t* coso_entry;
  uint64_t* chunk_vaddr;
  uint64_t* small_object_list_ptr;

  chunk_vaddr = get_coso_list_entry_memory(chunk_list_entry);

  object_size = get_chunk_object_size(get_chunk_list_entry_memory(context, chunk_list_entry)); // object size in bytes
  payload_offset = calculate_chunk_payload_offset_bytes(object_size);
  small_object_list_ptr = get_small_object_free_lists_gc(context) + (object_size / sizeof(uint64_t) - 1);
  object_count = (GC_CHUNK_SIZE - payload_offset);
  object_count = object_count / object_size;

  // convert payload offset and object size to words so they can be used in pointer operations
  payload_offset = payload_offset / sizeof(uint64_t);
  object_size = object_size / sizeof(uint64_t);

  i = 0;
  while (i < object_count) {
    coso_entry = allocate_coso_list_entry(context);

    set_coso_list_entry_next(coso_entry, (uint64_t*)(*(small_object_list_ptr)));
    set_coso_list_entry_memory(coso_entry, chunk_vaddr + payload_offset + (i * object_size));

    *(small_object_list_ptr) = (uint64_t) coso_entry;

    i = i + 1;
  }
}

uint64_t* allocate_object(uint64_t* context, uint64_t size) {
  uint64_t* ret;
  uint64_t* chunk;
  uint64_t* small_object_free_list;
  uint64_t object_index;

  small_object_free_list = get_small_object_free_lists_gc(context) + (size / sizeof(uint64_t) - 1);

  // assert: size is a multiple of GC_WORDSIZE and given in bytes

  if (*(small_object_free_list) == 0)
    fill_small_object_free_list(context, allocate_chunk(context, size));

  ret = (uint64_t*)*(small_object_free_list);                           // ret points to head of small object free list

  *(small_object_free_list) = (uint64_t) get_coso_list_entry_next(ret); // set head to next entry
  ret = get_coso_list_entry_memory(ret);                                // ret points to address of object (vaddr)

  // set alloc bit of object
  chunk = (uint64_t*) left_shift(right_shift((uint64_t) ret, GC_CHUNK_SIZE_LOG2), GC_CHUNK_SIZE_LOG2);

  object_index = calculate_chunk_small_object_index(context, ret);

  if (is_gc_library(context) == 0)
    chunk = tlb(get_pt(context), (uint64_t) chunk);

  set_chunk_object_allocbit(chunk, object_index, 1);

  return ret;
}

void free_chunk_object(uint64_t* context, uint64_t* object) {
  uint64_t* chunk;
  uint64_t* small_object_list_entry;
  uint64_t object_index;

  // assert: object as vaddr (syscall)

  chunk = (uint64_t*)(left_shift(right_shift((uint64_t) object, GC_CHUNK_SIZE_LOG2), GC_CHUNK_SIZE_LOG2));

  object_index = calculate_chunk_small_object_index(context, object);

  if (is_gc_library(context) == 0)
    chunk = tlb(get_pt(context), (uint64_t) chunk);

  set_chunk_object_allocbit(chunk, object_index, 0);

  small_object_list_entry = allocate_coso_list_entry(context);
  set_coso_list_entry_next(small_object_list_entry, (uint64_t*)(*(get_small_object_free_lists_gc(context) + (get_chunk_object_size(chunk) / sizeof(uint64_t) - 1))));
  set_coso_list_entry_memory(small_object_list_entry, object);

  *(get_small_object_free_lists_gc(context) + (get_chunk_object_size(chunk) / sizeof(uint64_t) - 1)) = (uint64_t) small_object_list_entry;
}

uint64_t calculate_chunk_small_object_index(uint64_t* context, uint64_t* object) {
  uint64_t* chunk;
  uint64_t object_index;

  // object as vaddr

  chunk = (uint64_t*) left_shift(right_shift((uint64_t) object, GC_CHUNK_SIZE_LOG2), GC_CHUNK_SIZE_LOG2);

  object_index = (uint64_t) object - (uint64_t) chunk; // offset in chunk

  if (is_gc_library(context) == 0)
    chunk = tlb(get_pt(context), (uint64_t) chunk);

  object_index = object_index - calculate_chunk_payload_offset_bytes(get_chunk_object_size(chunk)); // offset in chunk payload
  object_index = object_index / get_chunk_object_size(chunk);

  return object_index;
}

uint64_t* allocate_coso_list_entry(uint64_t* context) {
  if (is_gc_library(context))
    return allocate_new_memory(context, GC_COSO_LIST_ENTRY_SIZE);
  else
    return smalloc_system(GC_COSO_LIST_ENTRY_SIZE);
}

uint64_t* get_chunk_list_entry_memory(uint64_t* context, uint64_t* entry) {
  if (is_gc_library(context))
    return get_coso_list_entry_memory(entry);
  else
    return tlb(get_pt(context), (uint64_t) get_coso_list_entry_memory(entry));
}

// Hook Overrides

void gc_init(uint64_t* context) {
  gc_init_selfie(context);
  gc_init_boehm(context);
}

void gc_init_boehm(uint64_t* context) {
  GC_COSO_LIST_ENTRY_SIZE = sizeof(uint64_t*) * 2;

  GC_CHUNK_MIN_HEADER_SIZE = sizeof(uint64_t*) * 1 + sizeof(uint64_t) * 3; // static header (chunk list ptr + size) + 1 alloc bit word (min) + 1 mark bit word (min)

  GC_CHUNK_MAX_SMALL_OBJECT_SIZE = GC_CHUNK_SIZE - GC_CHUNK_MIN_HEADER_SIZE; // object size in order to fit 2 objects into one chunk
  GC_CHUNK_MAX_SMALL_OBJECT_SIZE = GC_CHUNK_MAX_SMALL_OBJECT_SIZE / 2;

  set_small_object_free_lists_gc(context, smalloc_system(GC_CHUNK_MAX_SMALL_OBJECT_SIZE)); // collector not initialized -> allocate using bump pointer allocator
  zero_memory(get_small_object_free_lists_gc(context), GC_CHUNK_MAX_SMALL_OBJECT_SIZE);

  align_chunk_allocator(context); // note: chunk heap needs to be aligned!

  set_chunk_heap_start_gc(context, allocate_new_memory(context, GC_CHUNK_HEAP_SIZE));
  if (get_chunk_heap_start_gc(context) == (uint64_t*) 0)
    printf("%s: could not initialize gc (chunk heap allocation)\n", (uint64_t) get_chunk_heap_start_gc(context));

  set_chunk_heap_bump_gc(context, get_chunk_heap_start_gc(context));
}

uint64_t* allocate_memory(uint64_t* context, uint64_t size) {
  if (size == 0)
    return allocate_memory_selfie(context, size); // delegate to selfie gc

  if (size > GC_CHUNK_MAX_SMALL_OBJECT_SIZE)
    return allocate_memory_selfie(context, size); // delegate to selfie gc

  return allocate_memory_boehm(context, size);
}

uint64_t* allocate_memory_boehm(uint64_t* context, uint64_t size) {
  uint64_t* object;

  object = allocate_object(context, size);

  if (is_gc_library(context) == 0)
    zero_memory(tlb(get_pt(context), (uint64_t) object), size);
  else
    zero_memory(object, size);

  return object;
}

void mark_object(uint64_t* context, uint64_t address) {
  uint64_t gc_address;

  gc_address = gc_load_memory(context, address);

  if (gc_address >= (uint64_t) get_chunk_heap_start_gc(context)) {
    if (gc_address < (uint64_t) get_chunk_heap_bump_gc(context))
      mark_object_boehm(context, gc_address);
    else
      mark_object_selfie(context, gc_address); // delegate to selfie gc
  } else
    mark_object_selfie(context, gc_address);   // delegate to selfie gc
}

uint64_t mark_object_boehm(uint64_t* context, uint64_t gc_address) {
  uint64_t object_start;
  uint64_t object_end;
  uint64_t chunk;
  uint64_t* chunk_paddr;

  chunk = left_shift(right_shift(gc_address, GC_CHUNK_SIZE_LOG2), GC_CHUNK_SIZE_LOG2);

  if (is_gc_library(context) == 0)
    chunk_paddr = tlb(get_pt(context), chunk);
  else
    chunk_paddr = (uint64_t*) chunk;

  if (is_address_valid_chunk_object_of_specific_chunk(context, gc_address, get_chunk_list_pointer(chunk_paddr))) {
    if (get_chunk_object_markbit(chunk_paddr, calculate_chunk_small_object_index(context, (uint64_t*) gc_address)) == GC_MARKBIT_UNREACHABLE)
      set_chunk_object_markbit(chunk_paddr, calculate_chunk_small_object_index(context, (uint64_t*) gc_address), GC_MARKBIT_REACHABLE);
    else
      return 1;
  } else
    return 1;

  object_start = chunk + calculate_chunk_payload_offset_bytes(get_chunk_object_size(chunk_paddr)) + calculate_chunk_small_object_index(context, (uint64_t*) gc_address) * get_chunk_object_size(chunk_paddr);
  object_end = object_start + get_chunk_object_size(chunk_paddr);

  while (object_start < object_end) {
    mark_object(context, object_start);

    object_start = object_start + GC_WORDSIZE;
  }

  return 1;
}

void sweep(uint64_t* context) {
  // order doesn't matter
  sweep_selfie(context);
  sweep_boehm(context);
}

void sweep_boehm(uint64_t* context) {
  uint64_t* prev_node;
  uint64_t* next_node;
  uint64_t* node;
  uint64_t* chunk;
  uint64_t num_objects;
  uint64_t i;

  prev_node = (uint64_t*) 0;
  node = get_chunk_used_list_head_gc(context);
  while (node != (uint64_t*) 0) {
    chunk = get_chunk_list_entry_memory(context, node);

    i = 0;
    num_objects = (GC_CHUNK_SIZE - calculate_chunk_payload_offset_bytes(get_chunk_object_size(chunk))) / get_chunk_object_size(chunk);
    while (i < num_objects) {
      if (get_chunk_object_allocbit(chunk, i) == 1)
        if (get_chunk_object_markbit(chunk, i) == GC_MARKBIT_UNREACHABLE)
          free_chunk_object(context, get_coso_list_entry_memory(node) + calculate_chunk_payload_offset_words(get_chunk_object_size(chunk)) + i * (get_chunk_object_size(chunk) / sizeof(uint64_t)));

      i = i + 1;
    }

    next_node = get_coso_list_entry_next(node);

    if (is_chunk_referenced(chunk) == 0)
      free_chunk(context, chunk);

    zero_chunk_markbits(chunk);

    node = next_node;
  }
}