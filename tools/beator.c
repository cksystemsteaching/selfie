/*
Copyright (c) the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

selfie.cs.uni-salzburg.at

BEATOR is a binary translator for bounded model checking that
implements a sound and complete translation of RISC-U code to BTOR2
formulae. BEATOR serves as research platform and facilitates teaching
the absolute basics of bit-precise reasoning on real code.

Given a RISC-U binary (or C* source code compiled to RISC-U, including
all of selfie and beator itself), beator generates a BTOR2 file that
models the bit-precise behavior of the binary on a 64-bit machine with
4GB of memory. The translation runs in time and space linear in the
number of instructions in three iterations over all instructions for
encoding the program counter, the data flow, and the control flow.

The first console argument is interpreted as exit code. Value zero
means that any code execution that terminates with a non-zero exit
code is modeled as erroneous whereas a non-zero value means that
any code execution that terminates with a different exit code is
modeled as erroneous. Division by zero as well as memory access to
the code segment and above the 4GB memory of the machine is also
modeled as erroneous.

The optional console argument --check-block-access instructs beator
to generate additional checks for identifying unsafe memory access
outside of malloced memory blocks.

Any remaining console arguments are uninterpreted and passed on as
console arguments to the modeled RISC-U binary.

BEATOR is inspired by Professor Armin Biere from JKU Linz.
*/

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

uint64_t generate_ecall_address_checks(uint64_t cursor_nid, uint64_t current_ecall_nid);
uint64_t generate_ecall_address_and_block_checks(uint64_t cursor_nid, uint64_t current_ecall_nid);

void model_syscalls(uint64_t cursor_nid);

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------    A R C H I T E C T U R E    -----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

uint64_t pc_nid(uint64_t nid, uint64_t pc);
uint64_t is_procedure_call(uint64_t instruction, uint64_t link);
uint64_t validate_procedure_body(uint64_t from_instruction, uint64_t from_link, uint64_t to_address);

void go_to_instruction(uint64_t from_instruction, uint64_t from_link, uint64_t from_address, uint64_t to_address, uint64_t condition_nid);

void model_data_flow_lui();
void model_control_flow_lui_add_sub_mul_divu_remu_sltu_load_store();

void model_data_flow_addi();
void model_control_flow_addi();

void model_data_flow_add();
void model_data_flow_sub();
void model_data_flow_mul();
void model_data_flow_divu();
void model_data_flow_remu();
void model_data_flow_sltu();

void model_data_flow_load();
void model_data_flow_store();

void model_data_flow_beq();
void model_control_flow_beq();
void model_data_flow_jal();
void model_control_flow_jal();
// TODO: model jalr data flow
void model_control_flow_jalr();
void model_data_flow_ecall();
void model_control_flow_ecall();

// ------------------------ GLOBAL CONSTANTS -----------------------

// 4 more digits to accommodate code, data, heap, and stack with
// 1000*4 lines per 32-bit instruction (pc increments by 4) and
// 1000*8(4) lines per 64-bit (32-bit) machine word in memory segments

uint64_t PC_NID_DIGITS = 4;    // 10^4 == 10000
uint64_t PC_NID_FACTOR = 1000; // 1000*8(4) fit into 10000

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void reset_bounds();
void transfer_bounds();

uint64_t record_start_bounds(uint64_t cursor_nid, uint64_t activation_nid, uint64_t reg);
uint64_t record_end_bounds(uint64_t cursor_nid, uint64_t activation_nid, uint64_t reg);

uint64_t model_virtual_address();
uint64_t model_physical_address_in_segment(uint64_t cursor_nid, uint64_t laddr_nid,
  uint64_t start_nid, uint64_t end_nid, uint64_t offset_nid, uint64_t flow_nid);
uint64_t model_physical_address(uint64_t cursor_nid, uint64_t vaddr_nid);
uint64_t model_RAM_access(uint64_t cursor_nid, uint64_t address_nid, uint64_t RAM_address,
  uint64_t RAM_word, uint64_t RAM_word_flow_nid);

uint64_t compute_physical_address(uint64_t vaddr);

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

uint64_t already_seen_instruction(uint64_t address);
uint64_t is_statically_live_instruction(uint64_t address);
void     mark_instruction(uint64_t address, uint64_t mark);

uint64_t get_return_mark(uint64_t address);
void     mark_return(uint64_t address, uint64_t mark);

uint64_t mark_statically_live_code(uint64_t start_address, uint64_t callee_address,
  uint64_t entry_pc, uint64_t mark);

void static_dead_code_elimination(uint64_t start_address, uint64_t entry_pc);

void translate_to_model();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t DEAD = 0;
uint64_t SEEN = 1;
uint64_t LIVE = 2;

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t exit_wrapper_address = 0;

uint64_t* statically_live_code   = (uint64_t*) 0;
uint64_t* statically_live_return = (uint64_t*) 0;

// -----------------------------------------------------------------
// ------------------------ MODEL GENERATOR ------------------------
// -----------------------------------------------------------------

uint64_t control_flow(uint64_t activate_nid, uint64_t control_flow_nid);

uint64_t control_flow_from_beq(uint64_t from_address, uint64_t condition_nid, uint64_t control_flow_nid);
uint64_t control_flow_from_jalr(uint64_t jalr_address, uint64_t condition_nid, uint64_t control_flow_nid);
uint64_t control_flow_from_ecall(uint64_t from_address, uint64_t control_flow_nid);

void check_syscall_id();
void check_exit_code();
void check_division_by_zero(uint64_t division, uint64_t flow_nid);

uint64_t check_addresses();

void generate_address_alignment_check(uint64_t flow_nid);
void generate_segmentation_faults(uint64_t flow_nid);
void generate_block_access_check(uint64_t flow_nid, uint64_t lo_flow_nid, uint64_t up_flow_nid);

uint64_t number_of_bits(uint64_t n);

void beator(uint64_t entry_pc);

uint64_t selfie_model();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t EXITCODE_MODELINGERROR = 1;

uint64_t LO_FLOW = 32; // offset of nids of lower bounds on addresses in registers
uint64_t UP_FLOW = 64; // offset of nids of upper bounds on addresses in registers

// ------------------------ GLOBAL VARIABLES -----------------------

char*    model_name = (char*) 0; // name of model file
uint64_t model_fd   = 0;         // file descriptor of open model file

char* no_syscall_id_check_option        = (char*) 0;
char* no_exit_code_check_option         = (char*) 0;
char* no_division_by_zero_check_option  = (char*) 0;
char* no_address_alignment_check_option = (char*) 0;
char* no_segmentation_faults_option     = (char*) 0;

char* check_block_access_option   = (char*) 0;
char* constant_propagation_option = (char*) 0;
char* linear_address_space_option = (char*) 0;
char* heap_allowance_option       = (char*) 0;
char* stack_allowance_option      = (char*) 0;
char* MMU_option                  = (char*) 0;
char* RAM_option                  = (char*) 0;
char* MMURAM_option               = (char*) 0;

uint64_t syscall_id_check        = 1; // flag for preventing syscall id checks
uint64_t exit_code_check         = 1; // flag for preventing exit code check
uint64_t division_by_zero_check  = 1; // flag for preventing division and remainder by zero checks
uint64_t address_alignment_check = 1; // flag for preventing memory address alignment checks
uint64_t segmentation_faults     = 1; // flag for preventing segmentation fault checks

uint64_t check_block_access   = 0; // flag for generating memory access checks on malloced block level
uint64_t constant_propagation = 0; // flag for constant propagation
uint64_t linear_address_space = 0; // flag for 29-bit (30-bit) linear address space
uint64_t fixed_heap_segment   = 0; // flag for fixing size of heap segment
uint64_t fixed_stack_segment  = 0; // flag for fixing size of stack segment
uint64_t MMU                  = 0; // flag for generating MMU circuit
uint64_t RAM                  = 0; // flag for generating RAM state and circuit
uint64_t MMURAM               = 0; // flag for generating combined MMU and RAM state and circuit

uint64_t heap_allowance  = 0; // additional heap memory in bytes
uint64_t stack_allowance = 0; // additional stack memory in bytes

uint64_t w = 0; // number of written characters

uint64_t current_nid = 0; // nid of current line

uint64_t which_ecall_nid; // nid of $a7 == SYSCALL_EXIT

uint64_t bad_number = 0; // bad number counter

uint64_t bad_exit_code  = 0; // model for this exit code
uint64_t exit_ecall_nid = 0; // nid of exit ecall is active

uint64_t vaddr_sort_nid   = 2;  // nid of virtual or linear address sort
uint64_t vaddr_space_size = 64; // size of virtual address space in bits
uint64_t vaddr_mask_nid   = 27; // nid of bit mask for resetting LSBs in virtual addresses
uint64_t vaddr_alignment  = 3;  // virtual address alignment in bits

uint64_t laddr_space_size = 32; // size of linear address space in bits

uint64_t paddr_sort_nid   = 2;  // nid of physical address sort
uint64_t paddr_space_size = 64; // size of physical address space in bits

uint64_t memory_sort_nid = 3; // nid of physical memory sort

uint64_t heap_start  = 0;
uint64_t heap_size   = 0;
uint64_t stack_start = 0;
uint64_t stack_size  = 0;

uint64_t reg_value_nids = 100; // nids of initial values of registers
uint64_t reg_nids       = 200; // nids of registers
uint64_t reg_init_nids  = 300; // nids of initialization of registers

uint64_t* reg_flow_nids = (uint64_t*) 0; // nids of most recent update of registers

uint64_t bump_pointer_nid = 0; // nid of brk bump pointer

uint64_t reg_a7 = 0; // most recent update of $a7 register in sequential translation flow

uint64_t pcs_nid = 0; // nid of first program counter flag

// per-instruction list of control-flow in-edges
uint64_t* control_in = (uint64_t*) 0;

// per-procedure (target of procedure call jal) address of matching jalr instruction
uint64_t* call_return = (uint64_t*) 0;

uint64_t current_callee = 0; // address of first instruction of current callee

// address of currently farthest forward branch or jump to find matching jalr instruction
uint64_t estimated_return = 0;

uint64_t memory_nid      = 0; // nid of physical memory
uint64_t memory_flow_nid = 0; // nid of most recent update of memory

uint64_t lo_memory_nid      = 0; // nid of lower bounds on addresses in memory
uint64_t lo_memory_flow_nid = 0; // nid of most recent update of lower bounds on addresses in memory

uint64_t up_memory_nid      = 0; // nid of upper bounds on addresses in memory
uint64_t up_memory_flow_nid = 0; // nid of most recent update of upper bounds on addresses in memory

uint64_t* RAM_write_flow_nid = (uint64_t*) 0; // nids of most recent writes of RAM

// for checking division and remainder by zero
// 21 is nid of 1 which is ok as divisor
uint64_t division_flow_nid  = 21;
uint64_t remainder_flow_nid = 21;

// for checking address validity during state transitions with no memory access:
// 30 is nid of start of data segment which must be a valid address (thus also checked)
uint64_t access_flow_start_nid = 30;

// 50 is nid of highest address in 32-bit virtual address space (4GB)
uint64_t lo_flow_start_nid = 30; // nid of most recent update of current lower bound
uint64_t up_flow_start_nid = 50; // nid of most recent update of current upper bound

// for checking address validity for a whole range of addresses
uint64_t access_flow_end_nid = 30;

uint64_t lo_flow_end_nid = 30; // nid of most recent update of current lower bound
uint64_t up_flow_end_nid = 50; // nid of most recent update of current upper bound

// keep track of pc flags of ecalls, 10 is nid of 1-bit 0
uint64_t ecall_flow_nid = 10;

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

uint64_t handle_propr_system_call(uint64_t* context);
uint64_t handle_propr_exception(uint64_t* context);

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t exited_on_timeout = 0;
uint64_t exited_on_read    = 0;

// -----------------------------------------------------------------
// --------------------- CONSTANT PROPAGATION ----------------------
// -----------------------------------------------------------------

uint64_t propr(uint64_t* to_context);

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

uint64_t generate_ecall_address_checks(uint64_t cursor_nid, uint64_t current_ecall_nid) {
  if (check_addresses()) {
    w = w
      // if read, write, or openat ecall is active record $a1 register for checking address validity
      + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; $a1 is start address of buffer for checking address validity\n",
          cursor_nid,             // nid of this line
          current_ecall_nid,      // nid of read, write, or openat ecall is active
          reg_nids + REG_A1,      // nid of current value of $a1 register
          access_flow_start_nid); // nid of address of most recent memory access

    access_flow_start_nid = cursor_nid;

    cursor_nid = cursor_nid + 1;
  }

  return cursor_nid;
}

uint64_t generate_ecall_address_and_block_checks(uint64_t cursor_nid, uint64_t current_ecall_nid) {
  cursor_nid = generate_ecall_address_checks(cursor_nid, current_ecall_nid);

  if (check_block_access) {
    w = w
      // if read or write ecall is active record $a1 + (($a2 - 1) / 8(4)) * 8(4) if $a2 > 0, and
      // $a1 otherwise, as address for checking address validity
      + dprintf(output_fd, "%lu dec 2 %lu ; $a2 - 1\n",
          cursor_nid,        // nid of this line
          reg_nids + REG_A2) // nid of current value of $a2 register
      + dprintf(output_fd, "%lu not 2 %lu ; not %lu\n",
          cursor_nid + 1,                           // nid of this line
          vaddr_mask_nid,                           // nid of bit mask
          two_to_the_power_of(vaddr_alignment) - 1) // virtual address alignment in decimal
      + dprintf(output_fd, "%lu and 2 %lu %lu ; reset %lu LSBs of $a2 - 1\n",
          cursor_nid + 2,  // nid of this line
          cursor_nid,      // nid of $a2 - 1
          cursor_nid + 1,  // nid of preceding line
          vaddr_alignment) // virtual address alignment in bits
      + dprintf(output_fd, "%lu add 2 %lu %lu ; $a1 + (($a2 - 1) / %lu) * %lu\n",
          cursor_nid + 3,    // nid of this line
          reg_nids + REG_A1, // nid of current value of $a1 register
          cursor_nid + 2,    // nid of (($a2 - 1) / 8(4)) * 8(4)
          WORDSIZE,          // word size in bytes
          WORDSIZE)          // word size in bytes
      + dprintf(output_fd, "%lu ugt 1 %lu 20 ; $a2 > 0\n",
          cursor_nid + 4,    // nid of this line
          reg_nids + REG_A2) // nid of current value of $a2 register
      + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; $a1 + (($a2 - 1) / %lu) * %lu if $a2 > 0, and $a1 otherwise\n",
          cursor_nid + 5,    // nid of this line
          cursor_nid + 4,    // nid of $a2 > 0
          cursor_nid + 3,    // nid of $a1 + (($a2 - 1) / 8(4)) * 8(4)
          reg_nids + REG_A1, // nid of current value of $a1 register
          WORDSIZE,          // word size in bytes
          WORDSIZE)          // word size in bytes
      + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; $a1 + (($a2 - 1) / %lu) * %lu is end address of buffer for checking address validity\n",
          cursor_nid + 6,      // nid of this line
          current_ecall_nid,   // nid of read or write ecall is active
          cursor_nid + 5,      // nid of $a1 + (($a2 - 1) / 8(4)) * 8(4) if $a2 > 0, and $a1 otherwise
          access_flow_end_nid, // nid of address of most recent memory access
          WORDSIZE,            // word size in bytes
          WORDSIZE);           // word size in bytes

    access_flow_end_nid = cursor_nid + 6;

    // if read or write ecall is active record $a1 bounds for checking address validity
    cursor_nid = record_end_bounds(record_start_bounds(cursor_nid + 7, current_ecall_nid, REG_A1), current_ecall_nid, REG_A1);
  }

  return cursor_nid;
}

void model_syscalls(uint64_t cursor_nid) {
  uint64_t current_ecall_nid;
  uint64_t kernel_mode_flow_nid;
  uint64_t increment_nid;
  uint64_t input_nid;
  uint64_t paddr_nid;
  uint64_t write_input_nid;
  uint64_t read_ecall_active_nid;
  uint64_t read_ecall_active_increment_nid;
  uint64_t RAM_address;
  uint64_t valid_brk_nid;
  uint64_t invalid_brk_nid;

  current_ecall_nid = cursor_nid;

  w = w
    + dprintf(output_fd, "%lu constd 2 %lu ; SYSCALL_EXIT\n", cursor_nid, SYSCALL_EXIT)
    + dprintf(output_fd, "%lu constd 2 %lu ; SYSCALL_READ\n", cursor_nid + 1, SYSCALL_READ)
    + dprintf(output_fd, "%lu constd 2 %lu ; SYSCALL_WRITE\n", cursor_nid + 2, SYSCALL_WRITE)
    + dprintf(output_fd, "%lu constd 2 %lu ; SYSCALL_OPENAT\n", cursor_nid + 3, SYSCALL_OPENAT)
    + dprintf(output_fd, "%lu constd 2 %lu ; SYSCALL_BRK\n\n", cursor_nid + 4, SYSCALL_BRK);

  which_ecall_nid = cursor_nid + 10;

  w = w
    + dprintf(output_fd, "%lu eq 1 %lu %lu ; $a7 == SYSCALL_EXIT\n",
        which_ecall_nid,   // nid of this line
        reg_nids + REG_A7, // nid of current value of $a7 register
        cursor_nid)        // nid of SYSCALL_EXIT
    + dprintf(output_fd, "%lu eq 1 %lu %lu ; $a7 == SYSCALL_READ\n",
        which_ecall_nid + 1, // nid of this line
        reg_nids + REG_A7,   // nid of current value of $a7 register
        cursor_nid + 1)      // nid of SYSCALL_READ
    + dprintf(output_fd, "%lu eq 1 %lu %lu ; $a7 == SYSCALL_WRITE\n",
        which_ecall_nid + 2, // nid of this line
        reg_nids + REG_A7,   // nid of current value of $a7 register
        cursor_nid + 2)      // nid of SYSCALL_WRITE
    + dprintf(output_fd, "%lu eq 1 %lu %lu ; $a7 == SYSCALL_OPENAT\n",
        which_ecall_nid + 3, // nid of this line
        reg_nids + REG_A7,   // nid of current value of $a7 register
        cursor_nid + 3)      // nid of SYSCALL_OPENAT
    + dprintf(output_fd, "%lu eq 1 %lu %lu ; $a7 == SYSCALL_BRK\n\n",
        which_ecall_nid + 4, // nid of this line
        reg_nids + REG_A7,   // nid of current value of $a7 register
        cursor_nid + 4);     // nid of SYSCALL_BRK


  current_ecall_nid = current_ecall_nid + pcs_nid / 10;

  exit_ecall_nid = current_ecall_nid;

  w = w
    + dprintf(output_fd, "%lu and 1 %lu %lu ; exit ecall is active\n",
      exit_ecall_nid,  // nid of this line
      ecall_flow_nid,  // nid of most recent update of ecall activation
      which_ecall_nid) // nid of $a7 == SYSCALL_EXIT

    // if exit ecall is active stay in kernel mode indefinitely
    + dprintf(output_fd, "%lu ite 1 60 %lu %lu ; stay in kernel mode indefinitely if exit ecall is active\n\n",
        exit_ecall_nid + 1, // nid of this line
        which_ecall_nid,    // nid of $a7 == SYSCALL_EXIT
        exit_ecall_nid);    // nid of exit ecall is active

  kernel_mode_flow_nid = exit_ecall_nid + 1;


  current_ecall_nid = current_ecall_nid + pcs_nid / 10;

  w = w
    // read ecall
    + dprintf(output_fd, "%lu and 1 %lu %lu ; read ecall is active\n",
        current_ecall_nid,    // nid of this line
        ecall_flow_nid,       // nid of most recent update of ecall activation
        which_ecall_nid + 1); // nid of $a7 == SYSCALL_READ

  cursor_nid = generate_ecall_address_and_block_checks(current_ecall_nid + 1, current_ecall_nid);

  // TODO: check file descriptor validity, return error codes

  // if read ecall is active go into kernel mode
  w = w + dprintf(output_fd, "%lu ite 1 %lu 11 %lu ; go into kernel mode if read ecall is active\n",
    cursor_nid,            // nid of this line
    current_ecall_nid,     // nid of read ecall is active
    kernel_mode_flow_nid); // nid of most recent update of kernel-mode flag

  kernel_mode_flow_nid = cursor_nid;

  // if read ecall is active set $a0 (number of read bytes) = 0 bytes
  w = w + dprintf(output_fd, "%lu ite 2 %lu 20 %lu ; set $a0 = 0 bytes if read ecall is active\n",
    cursor_nid + 1,             // nid of this line
    current_ecall_nid,          // nid of read ecall is active
    *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = cursor_nid + 1;

  cursor_nid = cursor_nid + 2;

  w = w
    // determine number of bytes to read in next step
    + dprintf(output_fd, "%lu sub 2 %lu %lu ; $a2 - $a0\n",
        cursor_nid,        // nid of this line
        reg_nids + REG_A2, // nid of current value of $a2 register
        reg_nids + REG_A0) // nid of current value of $a0 register
    + dprintf(output_fd, "%lu ugte 1 %lu %lu ; $a2 - $a0 >= %lu bytes\n",
        cursor_nid + 1, // nid of this line
        cursor_nid,     // nid of $a2 - $a0
        20 + WORDSIZE,  // nid of word size
        WORDSIZE)       // word size
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; read %lu bytes if $a2 - $a0 >= %lu bytes, or else $a2 - $a0 bytes\n",
        cursor_nid + 2, // nid of this line
        cursor_nid + 1, // nid of $a2 - $a0 >= 8 (4) bytes
        20 + WORDSIZE,  // nid of word size
        cursor_nid,     // nid of $a2 - $a0
        WORDSIZE,       // word size
        WORDSIZE);      // word size

  increment_nid = cursor_nid + 2;

  cursor_nid = cursor_nid + 3;

  w = w
    // compute unsigned-extended input
    + dprintf(output_fd, "%lu eq 1 %lu 22 ; increment == 2\n",
        cursor_nid,    // nid of this line
        increment_nid) // nid of increment
    + dprintf(output_fd, "%lu ite 2 %lu 92 91 ; unsigned-extended 2-byte input if increment == 2, or else unsigned-extended 1-byte input\n",
        cursor_nid + 1, // nid of this line
        cursor_nid)     // nid of increment == 2
    + dprintf(output_fd, "%lu eq 1 %lu 23 ; increment == 3\n",
        cursor_nid + 2, // nid of this line
        increment_nid)  // nid of increment
    + dprintf(output_fd, "%lu ite 2 %lu 93 %lu ; unsigned-extended 3-byte input if increment == 3\n",
        cursor_nid + 3, // nid of this line
        cursor_nid + 2, // nid of increment == 3
        cursor_nid + 1) // nid of unsigned-extended 2-byte input
    + dprintf(output_fd, "%lu eq 1 %lu 24 ; increment == 4\n",
        cursor_nid + 4, // nid of this line
        increment_nid); // nid of increment

  if (IS64BITTARGET) {
    w = w
      + dprintf(output_fd, "%lu ite 2 %lu 94 %lu ; unsigned-extended 4-byte input if increment == 4\n",
          cursor_nid + 5, // nid of this line
          cursor_nid + 4, // nid of increment == 4
          cursor_nid + 3) // nid of unsigned-extended 3-byte input
      + dprintf(output_fd, "%lu eq 1 %lu 25 ; increment == 5\n",
          cursor_nid + 6, // nid of this line
          increment_nid)  // nid of increment
      + dprintf(output_fd, "%lu ite 2 %lu 95 %lu ; unsigned-extended 5-byte input if increment == 5\n",
          cursor_nid + 7, // nid of this line
          cursor_nid + 6, // nid of increment == 5
          cursor_nid + 5) // nid of unsigned-extended 4-byte input
      + dprintf(output_fd, "%lu eq 1 %lu 26 ; increment == 6\n",
          cursor_nid + 8, // nid of this line
          increment_nid)  // nid of increment
      + dprintf(output_fd, "%lu ite 2 %lu 96 %lu ; unsigned-extended 6-byte input if increment == 6\n",
          cursor_nid + 9, // nid of this line
          cursor_nid + 8, // nid of increment == 6
          cursor_nid + 7) // nid of unsigned-extended 5-byte input
      + dprintf(output_fd, "%lu eq 1 %lu 27 ; increment == 7\n",
          cursor_nid + 10, // nid of this line
          increment_nid)   // nid of increment
      + dprintf(output_fd, "%lu ite 2 %lu 97 %lu ; unsigned-extended 7-byte input if increment == 7\n",
          cursor_nid + 11, // nid of this line
          cursor_nid + 10, // nid of increment == 7
          cursor_nid + 9)  // nid of unsigned-extended 6-byte input
      + dprintf(output_fd, "%lu eq 1 %lu 28 ; increment == 8\n",
          cursor_nid + 12, // nid of this line
          increment_nid)   // nid of increment
      + dprintf(output_fd, "%lu ite 2 %lu 98 %lu ; 8-byte input if increment == 8\n",
          cursor_nid + 13,  // nid of this line
          cursor_nid + 12,  // nid of increment == 8
          cursor_nid + 11); // nid of unsigned-extended 7-byte input

    input_nid = cursor_nid + 13;

    cursor_nid = cursor_nid + 14;
  } else {
    w = w
      + dprintf(output_fd, "%lu ite 2 %lu 94 %lu ; 4-byte input if increment == 4\n",
          cursor_nid + 5,  // nid of this line
          cursor_nid + 4,  // nid of increment == 4
          cursor_nid + 3); // nid of unsigned-extended 3-byte input

    input_nid = cursor_nid + 5;

    cursor_nid = cursor_nid + 6;
  }

  w = w
    // compute virtual address $a1 + $a0
    + dprintf(output_fd, "%lu add 2 %lu %lu ; $a1 + $a0\n",
        cursor_nid,         // nid of this line
        reg_nids + REG_A1,  // nid of current value of $a1 register
        reg_nids + REG_A0); // nid of current value of $a0 register

  // compute physical address $a1 + $a0
  paddr_nid = model_physical_address(cursor_nid + 1, cursor_nid);

  write_input_nid = paddr_nid + 1;

  if (RAM + MMURAM == 0) {
    w = w
      // write input to memory at physical address $a1 + $a0
      + dprintf(output_fd, "%lu write %lu %lu %lu %lu ; memory[$a1 + $a0] = input\n",
          write_input_nid, // nid of this line
          memory_sort_nid, // nid of physical memory sort
          memory_nid,      // nid of physical memory
          paddr_nid,       // nid of physical address $a1 + $a0
          input_nid);      // nid of input

    cursor_nid = write_input_nid + 1;
  } else
    cursor_nid = write_input_nid;

  w = w
    // read ecall is in kernel mode and not done yet
    + dprintf(output_fd, "%lu ult 1 %lu %lu ; $a0 < $a2\n",
        cursor_nid,        // nid of this line
        reg_nids + REG_A0, // nid of current value of $a0 register
        reg_nids + REG_A2) // nid of current value of $a2 register
    + dprintf(output_fd, "%lu and 1 %lu %lu ; $a7 == SYSCALL_READ and $a0 < $a2\n",
        cursor_nid + 1,      // nid of this line
        which_ecall_nid + 1, // nid of $a7 == SYSCALL_READ
        cursor_nid)          // nid of $a0 < $a2
    + dprintf(output_fd, "%lu and 1 60 %lu ; read ecall is in kernel mode and not done yet\n",
        cursor_nid + 2,  // nid of this line
        cursor_nid + 1); // nid of $a7 == SYSCALL_READ and $a0 < $a2

  read_ecall_active_nid = cursor_nid + 2;

  cursor_nid = cursor_nid + 3;

  w = w
    // if read ecall is in kernel mode and not done yet write input to memory at address $a1 + $a0
    + dprintf(output_fd, "%lu ugt 1 %lu 20 ; increment > 0\n",
        cursor_nid,    // nid of this line
        increment_nid) // nid of increment
    + dprintf(output_fd, "%lu and 1 %lu %lu ; read ecall is in kernel mode and not done yet and increment > 0\n",
        cursor_nid + 1,        // nid of this line
        read_ecall_active_nid, // nid of read ecall is in kernel mode and not done yet
        cursor_nid);           // nid of increment > 0

  read_ecall_active_increment_nid = cursor_nid + 1;

  cursor_nid = cursor_nid + 2;

  if (RAM + MMURAM == 0) {
    w = w
      + dprintf(output_fd, "%lu ite %lu %lu %lu %lu ; read input into memory[$a1 + $a0]\n",
          cursor_nid,                      // nid of this line
          memory_sort_nid,                 // nid of physical memory sort
          read_ecall_active_increment_nid, // nid of read ecall is in kernel mode and not done yet and increment > 0
          write_input_nid,                 // nid of memory[$a1 + $a0] = input
          memory_flow_nid);                // nid of most recent update of memory

    memory_flow_nid = cursor_nid;

    cursor_nid = cursor_nid + 1;
  } else {
    RAM_address = 0;

    while (RAM_address < (data_size + heap_size + stack_size) / WORDSIZE) {
      // if address $a1 + $a0 == RAM address write input at RAM address
      cursor_nid = model_RAM_access(cursor_nid, paddr_nid, RAM_address,
        input_nid, *(RAM_write_flow_nid + RAM_address));

      w = w
        // if this instruction is active set RAM[$a1 + $a0] = input
        + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; read input into RAM[$a1 + $a0]\n",
            cursor_nid + 1,                       // nid of this line
            read_ecall_active_increment_nid,      // read ecall is in kernel mode and not done yet and increment > 0
            cursor_nid,                           // nid of RAM[$a1 + $a0] = input
            *(RAM_write_flow_nid + RAM_address)); // nid of most recent write at RAM address

      *(RAM_write_flow_nid + RAM_address) = cursor_nid + 1;

      cursor_nid  = cursor_nid + 2;
      RAM_address = RAM_address + 1;
    }
  }

  w = w
    // if read ecall is in kernel mode and not done yet increment number of bytes read
    + dprintf(output_fd, "%lu add 2 %lu %lu ; $a0 + increment\n",
        cursor_nid,        // nid of this line
        reg_nids + REG_A0, // nid of current value of $a0 register
        increment_nid)     // nid of increment
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; set $a0 = $a0 + increment if read ecall is in kernel mode and not done yet\n",
        cursor_nid + 1,             // nid of this line
        read_ecall_active_nid,      // nid of read ecall is in kernel mode and not done yet
        cursor_nid,                 // nid of $a0 + increment
        *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = cursor_nid + 1;

  // if read ecall is in kernel mode and not done yet stay in kernel mode
  w = w + dprintf(output_fd, "%lu ite 1 %lu 11 %lu ; stay in kernel mode if read ecall is in kernel mode and not done yet\n\n",
    cursor_nid + 2,        // nid of this line
    read_ecall_active_nid, // nid of read ecall is in kernel mode and not done yet
    kernel_mode_flow_nid); // nid of most recent update of kernel-mode flag

  kernel_mode_flow_nid = cursor_nid + 2;


  current_ecall_nid = current_ecall_nid + pcs_nid / 10;

  w = w
    // write ecall
    + dprintf(output_fd, "%lu and 1 %lu %lu ; write ecall is active\n",
        current_ecall_nid,    // nid of this line
        ecall_flow_nid,       // nid of most recent update of ecall activation
        which_ecall_nid + 2); // nid of $a7 == SYSCALL_WRITE

  cursor_nid = generate_ecall_address_and_block_checks(current_ecall_nid + 1, current_ecall_nid);

  // TODO: check file descriptor validity, return error codes

  // if write ecall is active set $a0 (written number of bytes) = $a2 (size)
  w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; set $a0 = $a2 if write ecall is active\n\n",
    cursor_nid,                 // nid of this line
    current_ecall_nid,          // nid of write ecall is active
    reg_nids + REG_A2,          // nid of current value of $a2 register
    *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = cursor_nid;


  current_ecall_nid = current_ecall_nid + pcs_nid / 10;

  w = w
    // openat ecall
    + dprintf(output_fd, "%lu and 1 %lu %lu ; openat ecall is active\n",
        current_ecall_nid,    // nid of this line
        ecall_flow_nid,       // nid of most recent update of ecall activation
        which_ecall_nid + 3); // nid of $a7 == SYSCALL_OPENAT

  cursor_nid = generate_ecall_address_checks(current_ecall_nid + 1, current_ecall_nid);

  if (check_block_access)
    // if openat ecall is active record $a1 bounds for checking address validity
    cursor_nid = record_start_bounds(cursor_nid, current_ecall_nid, REG_A1);

  // TODO: check address validity of whole filename, flags and mode arguments

  w = w
    + dprintf(output_fd, "%lu state 2 fd-bump-pointer\n", cursor_nid)
    + dprintf(output_fd, "%lu init 2 %lu 21 ; initial fd-bump-pointer is 1 (file descriptor bump pointer)\n",
        cursor_nid + 1, // nid of this line
        cursor_nid)     // nid of fd-bump-pointer

    // if openat ecall is active set $a0 (file descriptor) = fd-bump-pointer + 1 (next file descriptor)
    + dprintf(output_fd, "%lu inc 2 %lu\n",
        cursor_nid + 2, // nid of this line
        cursor_nid)     // nid of fd-bump-pointer
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; fd-bump-pointer + 1 if openat ecall is active\n",
        cursor_nid + 3,    // nid of this line
        current_ecall_nid, // nid of openat ecall is active
        cursor_nid + 2,    // nid of fd-bump-pointer + 1
        cursor_nid)        // nid of fd-bump-pointer
    + dprintf(output_fd, "%lu next 2 %lu %lu ; increment fd-bump-pointer if openat ecall is active\n",
        cursor_nid + 4, // nid of this line
        cursor_nid,     // nid of fd-bump-pointer
        cursor_nid + 3) // nid of fd-bump-pointer + 1
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; set $a0 = fd-bump-pointer + 1 if openat ecall is active\n\n",
        cursor_nid + 5,             // nid of this line
        current_ecall_nid,          // nid of openat ecall is active
        cursor_nid + 2,             // nid of fd-bump-pointer + 1
        *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = cursor_nid + 5;


  current_ecall_nid = current_ecall_nid + pcs_nid / 10;

  // is brk ecall is active?
  w = w + dprintf(output_fd, "%lu and 1 %lu %lu ; brk ecall is active\n",
    current_ecall_nid,    // nid of this line
    ecall_flow_nid,       // nid of most recent update of ecall activation
    which_ecall_nid + 4); // nid of $a7 == SYSCALL_BRK

  cursor_nid = current_ecall_nid + 1;

  bump_pointer_nid = cursor_nid;

  w = w
    + dprintf(output_fd, "%lu state 2 brk-bump-pointer\n", bump_pointer_nid)
    + dprintf(output_fd, "%lu init 2 %lu 33 ; current program break\n",
        cursor_nid + 1,    // nid of this line
        bump_pointer_nid); // nid of brk bump pointer

  cursor_nid = cursor_nid + 2;

  w = w
    // $a0 is valid if brk <= $a0 < $sp and $a0 is word-aligned
    + dprintf(output_fd, "%lu ulte 1 %lu %lu ; brk <= $a0\n",
        cursor_nid,        // nid of this line
        bump_pointer_nid,  // nid of brk bump pointer
        reg_nids + REG_A0) // nid of current value of $a0 register
    + dprintf(output_fd, "%lu ult 1 %lu %lu ; $a0 < $sp\n",
        cursor_nid + 1,    // nid of this line
        reg_nids + REG_A0, // nid of current value of $a0 register
        reg_nids + REG_SP) // nid of current value of $sp register
    + dprintf(output_fd, "%lu and 1 %lu %lu ; brk <= $a0 < $sp\n",
        cursor_nid + 2, // nid of this line
        cursor_nid,     // nid of brk <= $a0
        cursor_nid + 1) // nid of $a0 < $sp
    + dprintf(output_fd, "%lu and 2 %lu %lu ; reset all but %lu LSBs of $a0\n",
        cursor_nid + 3,    // nid of this line
        reg_nids + REG_A0, // nid of current value of $a0 register
        vaddr_mask_nid,    // nid of bit mask
        vaddr_alignment)   // virtual address alignment in bits
    + dprintf(output_fd, "%lu eq 1 %lu 20 ; %lu LSBs of $a0 == 0 ($a0 is word-aligned)\n",
        cursor_nid + 4,  // nid of this line
        cursor_nid + 3,  // nid of 3 (or 2) LSBs of current value of $a0 register
        vaddr_alignment) // virtual address alignment in bits
    + dprintf(output_fd, "%lu and 1 %lu %lu ; brk <= $a0 < $sp and $a0 is word-aligned ($a0 is valid)\n",
        cursor_nid + 5, // nid of this line
        cursor_nid + 2, // nid of brk <= $a0 < $sp
        cursor_nid + 4) // nid of $a0 is word-aligned
    + dprintf(output_fd, "%lu and 1 %lu %lu ; brk ecall is active and $a0 is valid\n",
        cursor_nid + 6,    // nid of this line
        current_ecall_nid, // nid of brk ecall is active
        cursor_nid + 5);   // nid of $a0 is valid

  valid_brk_nid = cursor_nid + 6;

  w = w
    // if brk ecall is active and $a0 is valid set brk = $a0
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; brk = $a0 if brk ecall is active and $a0 is valid\n",
        cursor_nid + 7,    // nid of this line
        valid_brk_nid,     // nid of brk ecall is active and $a0 is valid
        reg_nids + REG_A0, // nid of current value of $a0 register
        bump_pointer_nid)  // nid of brk bump pointer
    + dprintf(output_fd, "%lu next 2 %lu %lu ; set brk = $a0 if brk ecall is active and $a0 is valid\n",
        cursor_nid + 8,   // nid of this line
        bump_pointer_nid, // nid of brk bump pointer
        cursor_nid + 7);  // nid of preceding line

  w = w
    // $a0 is invalid if $a0 is not valid
    + dprintf(output_fd, "%lu not 1 %lu ; $a0 is invalid\n",
        cursor_nid + 9, // nid of this line
        cursor_nid + 5) // nid of $a0 is valid
    + dprintf(output_fd, "%lu and 1 %lu %lu ; brk ecall is active and $a0 is invalid\n",
        cursor_nid + 10,   // nid of this line
        current_ecall_nid, // nid of brk ecall is active
        cursor_nid + 9);   // nid of $a0 is invalid

  invalid_brk_nid = cursor_nid + 10;

  w = w
    // if brk ecall is active and $a0 is invalid set $a0 = brk
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; set $a0 = brk if brk ecall is active and $a0 is invalid\n",
        cursor_nid + 11,            // nid of this line
        invalid_brk_nid,            // nid of brk ecall is active and $a0 is invalid
        bump_pointer_nid,           // nid of brk bump pointer
        *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = cursor_nid + 11;

  cursor_nid = cursor_nid + 12;

  if (check_block_access) {
    w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; lower bound on $t1 = brk if brk ecall is active and $a0 is valid\n",
      cursor_nid,                           // nid of this line
      valid_brk_nid,                        // nid of brk ecall is active and $a0 is valid
      bump_pointer_nid,                     // nid of brk bump pointer
      *(reg_flow_nids + LO_FLOW + REG_T1)); // nid of most recent update of lower bound on $t1 register

    *(reg_flow_nids + LO_FLOW + REG_T1) = cursor_nid;

    w = w
      + dprintf(output_fd, "%lu sub 2 %lu %lu ; $a0 - WORDSIZE\n",
          cursor_nid + 1,    // nid of this line
          reg_nids + REG_A0, // nid of current value of $a0 register
          20 + WORDSIZE)     // nid of word size
      + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; upper bound on $t1 = $a0 - WORDSIZE if brk ecall is active and $a0 is valid\n",
          cursor_nid + 2,                       // nid of this line
          valid_brk_nid,                        // nid of brk ecall is active and $a0 is valid
          cursor_nid + 1,                       // nid of current value of $a0 register - WORDSIZE
          *(reg_flow_nids + UP_FLOW + REG_T1)); // nid of most recent update of upper bound on $t1 register

    *(reg_flow_nids + UP_FLOW + REG_T1) = cursor_nid + 2;

    cursor_nid = cursor_nid + 3;

    w = w + dprintf(output_fd, "%lu ite 2 %lu 30 %lu ; lower bound on $t1 = start of data segment if brk ecall is active and $a0 is invalid\n",
      cursor_nid,                           // nid of this line
      invalid_brk_nid,                      // nid of brk ecall is active and $a0 is invalid
      *(reg_flow_nids + LO_FLOW + REG_T1)); // nid of most recent update of lower bound on $t1 register

    *(reg_flow_nids + LO_FLOW + REG_T1) = cursor_nid;

    w = w + dprintf(output_fd, "%lu ite 2 %lu 50 %lu ; upper bound on $t1 = highest address (4GB) if brk ecall is active and $a0 is invalid\n",
      cursor_nid + 1,                       // nid of this line
      invalid_brk_nid,                      // nid of brk ecall is active and $a0 is invalid
      *(reg_flow_nids + UP_FLOW + REG_T1)); // nid of most recent update of upper bound on $t1 register

    *(reg_flow_nids + UP_FLOW + REG_T1) = cursor_nid + 1;
  }


  w = w + dprintf(output_fd, "\n%lu next 1 60 %lu ; updating kernel-mode flag\n",
    current_ecall_nid + pcs_nid / 10, // nid of this line
    kernel_mode_flow_nid);            // nid of most recent update of kernel-mode flag
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -----------------    A R C H I T E C T U R E    -----------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

uint64_t pc_nid(uint64_t nid, uint64_t pc) {
  return nid + pc * PC_NID_FACTOR;
}

uint64_t is_procedure_call(uint64_t instruction, uint64_t link) {
  if (instruction == JAL)
    if (link != REG_ZR)
      return 1;

  return 0;
}

uint64_t validate_procedure_body(uint64_t from_instruction, uint64_t from_link, uint64_t to_address) {
  if (is_procedure_call(from_instruction, from_link) == 0) {
    // no forward branches and jumps that are not "procedure calls" outside of "procedure body"
    if (to_address > estimated_return)
      // estimating address of jalr at the end of "procedure body"
      estimated_return = to_address;

    if (to_address < current_callee)
      // no backward branches and jumps that are not "procedure calls" outside of "procedure body"
      return 0;
  }

  return 1;
}

void go_to_instruction(uint64_t from_instruction, uint64_t from_link, uint64_t from_address, uint64_t to_address, uint64_t condition_nid) {
  uint64_t* in_edge;

  if (to_address % INSTRUCTIONSIZE == 0) {
    if (to_address < code_start + code_size) {
      if (validate_procedure_body(from_instruction, from_link, to_address)) {
        in_edge = smalloc(sizeof(uint64_t*) + 3 * sizeof(uint64_t));

        *in_edge       = *(control_in + (to_address - code_start) / INSTRUCTIONSIZE);
        *(in_edge + 1) = from_instruction; // from which instruction
        *(in_edge + 2) = from_address;     // at which address
        *(in_edge + 3) = condition_nid;    // under which condition are we coming

        *(control_in + (to_address - code_start) / INSTRUCTIONSIZE) = (uint64_t) in_edge;

        return;
      }
    } else if (from_address == code_start + code_size - INSTRUCTIONSIZE)
      // from_instruction is last instruction in binary
      if (*(control_in + (from_address - code_start) / INSTRUCTIONSIZE) == 0)
        // and unreachable
        return;
  }

  // the instruction at from_address proceeds to an instruction at an invalid to_address

  //report the error on the console
  output_fd = 1;

  printf("%s: invalid instruction address %lu[0x%lX] detected\n", selfie_name, to_address, to_address);

  exit(EXITCODE_MODELINGERROR);
}

void model_data_flow_lui() {
  if (rd != REG_ZR) {
    reset_bounds();

    w = w
      + dprintf(output_fd, "%lu constd 2 %ld ; 0x%lX << 12\n",
        current_nid,                      // nid of this line
        left_shift(imm, 12),              // signed immediate value left-shifted by 12 bits
        sign_shrink(imm, WORDSIZEINBITS)) // immediate value in hexadecimal

      // if this instruction is active set $rd = imm << 12
      + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
          current_nid + 1,        // nid of this line
          pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
          current_nid,            // nid of immediate value left-shifted by 12 bits
          *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    w = w + print_lui() + dprintf(output_fd, "\n");
  }
}

void model_control_flow_lui_add_sub_mul_divu_remu_sltu_load_store() {
  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_data_flow_addi() {
  uint64_t result_nid;

  if (rd != REG_ZR) {
    transfer_bounds();

    if (imm == 0)
      result_nid = reg_nids + rs1;
    else {
      w = w + dprintf(output_fd, "%lu constd 2 %ld ; 0x%lX\n",
        current_nid,                       // nid of this line
        imm,                               // signed immediate value
        sign_shrink(imm, WORDSIZEINBITS)); // immediate value in hexadecimal

      if (rs1 == REG_ZR) {
        result_nid = current_nid;

        current_nid = current_nid + 1;
      } else {
        // compute $rs1 + imm
        w = w + dprintf(output_fd, "%lu add 2 %lu %lu\n",
          current_nid + 1, // nid of this line
          reg_nids + rs1,  // nid of current value of $rs1 register
          current_nid);    // nid of immediate value

        result_nid = current_nid + 1;

        current_nid = current_nid + 2;
      }
    }

    // if this instruction is active set $rd = $rs1 + imm
    w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
      current_nid,            // nid of this line
      pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      result_nid,             // nid of $rs1 + ismm
      *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid;

    w = w + print_addi() + dprintf(output_fd, "\n");
  }
}

void model_control_flow_addi() {
  if (rs1 == REG_ZR)
    if (imm != 0)
      if (rd == REG_A7)
        // assert: next instruction is ecall
        reg_a7 = imm;

  model_control_flow_lui_add_sub_mul_divu_remu_sltu_load_store();
}

void model_data_flow_add() {
  if (rd != REG_ZR) {
    if (check_block_access) {
      w = w
        // lower bound on $rs1 register > lower bound on $rs2 register
        + dprintf(output_fd, "%lu ugt 1 %lu %lu\n",
            current_nid,              // nid of this line
            reg_nids + LO_FLOW + rs1, // nid of lower bound on $rs1 register
            reg_nids + LO_FLOW + rs2) // nid of lower bound on $rs2 register

        // greater lower bound of $rs1 and $rs2 registers
        + dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
            current_nid + 1,          // nid of this line
            current_nid,              // nid of lower bound on $rs1 > lower bound on $rs2
            reg_nids + LO_FLOW + rs1, // nid of lower bound on $rs1 register
            reg_nids + LO_FLOW + rs2) // nid of lower bound on $rs2 register

        // if this instruction is active set lower bound on $rd = greater lower bound of $rs1 and $rs2 registers
        + dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
            current_nid + 2,                  // nid of this line
            pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
            current_nid + 1,                  // nid of greater lower bound of $rs1 and $rs2 registers
            *(reg_flow_nids + LO_FLOW + rd)); // nid of most recent update of lower bound on $rd register

      *(reg_flow_nids + LO_FLOW + rd) = current_nid + 2;

      current_nid = current_nid + 3;

      w = w
        // upper bound on $rs1 register < upper bound on $rs2 register
        + dprintf(output_fd, "%lu ult 1 %lu %lu\n",
            current_nid,              // nid of this line
            reg_nids + UP_FLOW + rs1, // nid of upper bound on $rs1 register
            reg_nids + UP_FLOW + rs2) // nid of upper bound on $rs2 register

        // lesser upper bound of $rs1 and $rs2 registers
        + dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
            current_nid + 1,          // nid of this line
            current_nid,              // nid of upper bound on $rs1 < upper bound on $rs2
            reg_nids + UP_FLOW + rs1, // nid of upper bound on $rs1 register
            reg_nids + UP_FLOW + rs2) // nid of upper bound on $rs2 register

        // if this instruction is active set upper bound on $rd = lesser upper bound of $rs1 and $rs2 registers
        + dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
            current_nid + 2,                  // nid of this line
            pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
            current_nid + 1,                  // nid of lesser upper bound of $rs1 and $rs2 registers
            *(reg_flow_nids + UP_FLOW + rd)); // nid of most recent update of upper bound on $rd register

      *(reg_flow_nids + UP_FLOW + rd) = current_nid + 2;

      current_nid = current_nid + 3;
    }

    w = w
      // compute $rs1 + $rs2
      + dprintf(output_fd, "%lu add 2 %lu %lu\n",
          current_nid,    // nid of this line
          reg_nids + rs1, // nid of current value of $rs1 register
          reg_nids + rs2) // nid of current value of $rs2 register

      // if this instruction is active set $rd = $rs1 + $rs2
      + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
          current_nid + 1,        // nid of this line
          pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
          current_nid,            // nid of $rs1 + $rs2
          *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    w = w + print_add_sub_mul_divu_remu_sltu() + dprintf(output_fd, "\n");
  }
}

void model_data_flow_sub() {
  if (rd != REG_ZR) {
    // TODO: check if bounds on $rs2 are really initial bounds
    transfer_bounds();

    w = w
      // compute $rs1 - $rs2
      + dprintf(output_fd, "%lu sub 2 %lu %lu\n",
          current_nid,    // nid of this line
          reg_nids + rs1, // nid of current value of $rs1 register
          reg_nids + rs2) // nid of current value of $rs2 register

      // if this instruction is active set $rd = $rs1 - $rs2
      + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
          current_nid + 1,        // nid of this line
          pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
          current_nid,            // nid of $rs1 - $rs2
          *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    w = w + print_add_sub_mul_divu_remu_sltu() + dprintf(output_fd, "\n");
  }
}

void model_data_flow_mul() {
  if (rd != REG_ZR) {
    // TODO: check if bounds on $rs1 and $rs2 are really initial bounds
    reset_bounds();

    w = w
      // compute $rs1 * $rs2
      + dprintf(output_fd, "%lu mul 2 %lu %lu\n",
          current_nid,    // nid of this line
          reg_nids + rs1, // nid of current value of $rs1 register
          reg_nids + rs2) // nid of current value of $rs2 register

      // if this instruction is active set $rd = $rs1 * $rs2
      + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
          current_nid + 1,        // nid of this line
          pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
          current_nid,            // nid of $rs1 * $rs2
          *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    w = w + print_add_sub_mul_divu_remu_sltu() + dprintf(output_fd, "\n");
  }
}

void model_data_flow_divu() {
  if (rd != REG_ZR) {
    // TODO: check if bounds on $rs1 and $rs2 are really initial bounds
    reset_bounds();

    // if this instruction is active record $rs2 for checking if $rs2 == 0
    w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; record %s for checking division by zero\n",
      current_nid,             // nid of this line
      pc_nid(pcs_nid, pc),     // nid of pc flag of this instruction
      reg_nids + rs2,          // nid of current value of $rs2 register
      division_flow_nid,       // nid of divisor of most recent division
      get_register_name(rs2)); // register name

    division_flow_nid = current_nid;

    current_nid = current_nid + 1;

    w = w
      // compute $rs1 / $rs2
      + dprintf(output_fd, "%lu udiv 2 %lu %lu\n",
          current_nid,    // nid of this line
          reg_nids + rs1, // nid of current value of $rs1 register
          reg_nids + rs2) // nid of current value of $rs2 register

      // if this instruction is active set $rd = $rs1 / $rs2
      + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
          current_nid + 1,        // nid of this line
          pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
          current_nid,            // nid of $rs1 / $rs2
          *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    w = w + print_add_sub_mul_divu_remu_sltu() + dprintf(output_fd, "\n");
  }
}

void model_data_flow_remu() {
  if (rd != REG_ZR) {
    // TODO: check if bounds on $rs1 and $rs2 are really initial bounds
    reset_bounds();

    // if this instruction is active record $rs2 for checking if $rs2 == 0
    w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; record %s for checking remainder by zero\n",
      current_nid,             // nid of this line
      pc_nid(pcs_nid, pc),     // nid of pc flag of this instruction
      reg_nids + rs2,          // nid of current value of $rs2 register
      remainder_flow_nid,      // nid of divisor of most recent remainder
      get_register_name(rs2)); // register name

    remainder_flow_nid = current_nid;

    current_nid = current_nid + 1;

    w = w
      // compute $rs1 % $rs2
      + dprintf(output_fd, "%lu urem 2 %lu %lu\n",
          current_nid,    // nid of this line
          reg_nids + rs1, // nid of current value of $rs1 register
          reg_nids + rs2) // nid of current value of $rs2 register

      // if this instruction is active set $rd = $rs1 % $rs2
      + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
          current_nid + 1,        // nid of this line
          pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
          current_nid,            // nid of $rs1 % $rs2
          *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    w = w + print_add_sub_mul_divu_remu_sltu() + dprintf(output_fd, "\n");
  }
}

void model_data_flow_sltu() {
  if (rd != REG_ZR) {
    reset_bounds();

    w = w
      // compute $rs1 < $rs2
      + dprintf(output_fd, "%lu ult 1 %lu %lu\n",
          current_nid,    // nid of this line
          reg_nids + rs1, // nid of current value of $rs1 register
          reg_nids + rs2) // nid of current value of $rs2 register

      // cast Boolean to machine word
      + dprintf(output_fd, "%lu ite 2 %lu 21 20\n",
          current_nid + 1, // nid of this line
          current_nid)     // nid of $rs1 < $rs2

      // if this instruction is active set $rd = $rs1 < $rs2
      + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
          current_nid + 2,        // nid of this line
          pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
          current_nid + 1,        // nid of $rs1 < $rs2 cast to machine word
          *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 2;

    w = w + print_add_sub_mul_divu_remu_sltu() + dprintf(output_fd, "\n");
  }
}

void model_data_flow_load() {
  uint64_t vaddr_nid;
  uint64_t paddr_nid;
  uint64_t RAM_address;
  uint64_t RAM_read_flow_nid;

  if (rd != REG_ZR) {
    current_nid = record_start_bounds(current_nid, pc_nid(pcs_nid, pc), rs1);

    vaddr_nid = model_virtual_address();
    paddr_nid = model_physical_address(current_nid, vaddr_nid);

    if (paddr_nid != vaddr_nid)
      // account for mapping code
      current_nid = paddr_nid + 1;

    if (check_addresses()) {
      // if this instruction is active record $rs1 + imm for checking address validity
      w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; for checking address validity\n",
        current_nid,            // nid of this line
        pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
        vaddr_nid,              // nid of virtual address $rs1 + imm
        access_flow_start_nid); // nid of address of most recent memory access

      access_flow_start_nid = current_nid;

      current_nid = current_nid + 1;
    }

    if (check_block_access) {
      w = w
        // read from lower-bounds memory[$rs1 + imm] into lower bound on $rd register
        + dprintf(output_fd, "%lu read 2 %lu %lu\n",
            current_nid,   // nid of this line
            lo_memory_nid, // nid of lower bounds on addresses in memory
            paddr_nid)     // nid of physical address $rs1 + imm

        // if this instruction is active set lower bound on $rd = lower-bounds memory[$rs1 + imm]
        + dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
            current_nid + 1,                  // nid of this line
            pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
            current_nid,                      // nid of lower-bounds memory[$rs1 + imm]
            *(reg_flow_nids + LO_FLOW + rd)); // nid of most recent update of lower bound on $rd register

      *(reg_flow_nids + LO_FLOW + rd) = current_nid + 1;

      current_nid = current_nid + 2;

      w = w
        // read from upper-bounds memory[$rs1 + imm] into upper bound on $rd register
        + dprintf(output_fd, "%lu read 2 %lu %lu\n",
            current_nid,   // nid of this line
            up_memory_nid, // nid of upper bounds on addresses in memory
            paddr_nid)     // nid of physical address $rs1 + imm

        // if this instruction is active set upper bound on $rd = upper-bounds memory[$rs1 + imm]
        + dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
            current_nid + 1,                  // nid of this line
            pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
            current_nid,                      // nid of upper-bounds memory[$rs1 + imm]
            *(reg_flow_nids + UP_FLOW + rd)); // nid of most recent update of upper bound on $rd register

      *(reg_flow_nids + UP_FLOW + rd) = current_nid + 1;

      current_nid = current_nid + 2;
    }

    if (RAM + MMURAM == 0) {
      w = w
        // read from memory[$rs1 + imm] into $rd register
        + dprintf(output_fd, "%lu read 2 %lu %lu\n",
            current_nid, // nid of this line
            memory_nid,  // nid of physical memory
            paddr_nid);  // nid of physical address $rs1 + imm

      RAM_read_flow_nid = current_nid;

      current_nid = current_nid + 1;
    } else {
      RAM_address = 0;

      // read 0 if address $rs1 + imm does not match any RAM address (must not happen)
      RAM_read_flow_nid = 20;

      while (RAM_address < (data_size + heap_size + stack_size) / WORDSIZE) {
        // if address $rs1 + imm == RAM address read RAM[$rs1 + imm] at RAM address
        RAM_read_flow_nid = model_RAM_access(current_nid, paddr_nid, RAM_address,
          pc_nid(memory_nid, RAM_address) + 2, RAM_read_flow_nid);

        current_nid = RAM_read_flow_nid + 1;
        RAM_address = RAM_address + 1;
      }
    }

    w = w
      // if this instruction is active set $rd = memory[$rs1 + imm]
      + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
          current_nid,            // nid of this line
          pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
          RAM_read_flow_nid,      // nid of memory[$rs1 + imm]
          *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid;

    w = w + print_load() + dprintf(output_fd, "\n");
  }
}

void model_data_flow_store() {
  uint64_t vaddr_nid;
  uint64_t paddr_nid;
  uint64_t RAM_address;

  current_nid = record_start_bounds(current_nid, pc_nid(pcs_nid, pc), rs1);

  vaddr_nid = model_virtual_address();
  paddr_nid = model_physical_address(current_nid, vaddr_nid);

  if (paddr_nid != vaddr_nid)
    // account for mapping code
    current_nid = paddr_nid + 1;

  if (check_addresses()) {
    // if this instruction is active record $rs1 + imm for checking address validity
    w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; for checking address validity\n",
      current_nid,            // nid of this line
      pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      vaddr_nid,              // nid of virtual address $rs1 + imm
      access_flow_start_nid); // nid of address of most recent memory access

    access_flow_start_nid = current_nid;

    current_nid = current_nid + 1;
  }

  if (check_block_access) {
    w = w
      // write lower bound on $rs2 register to lower-bounds memory[$rs1 + imm]
      + dprintf(output_fd, "%lu write %lu %lu %lu %lu\n",
          current_nid,              // nid of this line
          memory_sort_nid,          // nid of physical memory sort
          lo_memory_nid,            // nid of lower bounds on addresses in memory
          paddr_nid,                // nid of physical address $rs1 + imm
          reg_nids + LO_FLOW + rs2) // nid of lower bound on $rs2 register

      // if this instruction is active set lower-bounds memory[$rs1 + imm] = lower bound on $rs2
      + dprintf(output_fd, "%lu ite %lu %lu %lu %lu\n",
          current_nid + 1,     // nid of this line
          memory_sort_nid,     // nid of physical memory sort
          pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
          current_nid,         // nid of lower-bounds memory[$rs1 + imm]
          lo_memory_flow_nid); // nid of most recent update of lower-bounds memory

    lo_memory_flow_nid = current_nid + 1;

    current_nid = current_nid + 2;

    w = w
      // write upper bound on $rs2 register to upper-bounds memory[$rs1 + imm]
      + dprintf(output_fd, "%lu write %lu %lu %lu %lu\n",
          current_nid,              // nid of this line
          memory_sort_nid,          // nid of physical memory sort
          up_memory_nid,            // nid of upper bounds on addresses in memory
          paddr_nid,                // nid of physical address $rs1 + imm
          reg_nids + UP_FLOW + rs2) // nid of upper bound on $rs2 register

      // if this instruction is active set upper-bounds memory[$rs1 + imm] = upper bound on $rs2
      + dprintf(output_fd, "%lu ite %lu %lu %lu %lu\n",
          current_nid + 1,     // nid of this line
          memory_sort_nid,     // nid of physical memory sort
          pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
          current_nid,         // nid of upper-bounds memory[$rs1 + imm]
          up_memory_flow_nid); // nid of most recent update of upper-bounds memory

    up_memory_flow_nid = current_nid + 1;

    current_nid = current_nid + 2;
  }

  if (RAM + MMURAM == 0) {
    w = w
      // write $rs2 register to memory[$rs1 + imm]
      + dprintf(output_fd, "%lu write %lu %lu %lu %lu\n",
          current_nid,     // nid of this line
          memory_sort_nid, // nid of physical memory sort
          memory_nid,      // nid of physical memory
          paddr_nid,       // nid of physical address $rs1 + imm
          reg_nids + rs2)  // nid of current value of $rs2 register

      // if this instruction is active set memory[$rs1 + imm] = $rs2
      + dprintf(output_fd, "%lu ite %lu %lu %lu %lu ; ",
          current_nid + 1,     // nid of this line
          memory_sort_nid,     // nid of physical memory sort
          pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
          current_nid,         // nid of memory[$rs1 + imm] = $rs2
          memory_flow_nid);    // nid of most recent update of memory

    memory_flow_nid = current_nid + 1;
  } else {
    RAM_address = 0;

    while (RAM_address < (data_size + heap_size + stack_size) / WORDSIZE) {
      // if address $rs1 + imm == RAM address write current value of $rs2 register at RAM address
      current_nid = model_RAM_access(current_nid, paddr_nid, RAM_address,
        reg_nids + rs2, *(RAM_write_flow_nid + RAM_address));

      w = w
        // if this instruction is active set RAM[$rs1 + imm] = $rs2
        + dprintf(output_fd, "%lu ite 2 %lu %lu %lu",
            current_nid + 1,                      // nid of this line
            pc_nid(pcs_nid, pc),                  // nid of pc flag of this instruction
            current_nid,                          // nid of RAM[$rs1 + imm] = $rs2
            *(RAM_write_flow_nid + RAM_address)); // nid of most recent write at RAM address

      *(RAM_write_flow_nid + RAM_address) = current_nid + 1;

      current_nid = current_nid + 2;
      RAM_address = RAM_address + 1;

      if (RAM_address < (data_size + heap_size + stack_size) / WORDSIZE)
        w = w + dprintf(output_fd, "\n");
      else
        w = w + dprintf(output_fd, " ; ");
    }
  }

  w = w + print_store() + dprintf(output_fd, "\n");
}

void model_data_flow_beq() {
  // compute if beq condition is true
  w = w + dprintf(output_fd, "%lu eq 1 %lu %lu ; ",
    current_nid,     // nid of this line
    reg_nids + rs1,  // nid of current value of $rs1 register
    reg_nids + rs2); // nid of current value of $rs2 register

  w = w + print_beq() + dprintf(output_fd, "\n");

  // compute if beq condition is false
  w = w + dprintf(output_fd, "%lu not 1 %lu\n",
    current_nid + 1, // nid of this line
    current_nid);    // nid of preceding line
}

void model_control_flow_beq() {
  // true branch
  go_to_instruction(is, REG_ZR, pc, pc + imm, current_nid);

  // false branch
  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, current_nid + 1);
}

void model_data_flow_jal() {
  if (rd != REG_ZR) {
    w = w
      // address of next instruction used here and in returning jalr instruction
      + dprintf(output_fd, "%lu constd 2 %lu ; 0x%lX\n",
          current_nid,          // nid of this line
          pc + INSTRUCTIONSIZE, // address of next instruction
          pc + INSTRUCTIONSIZE) // address of next instruction

      // if this instruction is active link $rd register to address of next instruction
      + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
          current_nid + 1,        // nid of this line
          pc_nid(pcs_nid, pc),    // nid of pc flag of this jal instruction
          current_nid,            // nid of address of next instruction
          *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    w = w + print_jal() + dprintf(output_fd, "\n");
  }
}

void model_control_flow_jal() {
  if (rd != REG_ZR) {
    if (is_statically_live_instruction(pc) == 0)
      w = w
        // we still need address of next instruction used in returning jalr instruction
        + dprintf(output_fd, "%lu constd 2 %lu ; 0x%lX\n",
            current_nid,           // nid of this line
            pc + INSTRUCTIONSIZE,  // address of next instruction
            pc + INSTRUCTIONSIZE); // address of next instruction

    // link next instruction to returning jalr instruction via instruction at address pc + imm
    go_to_instruction(JALR, REG_ZR, pc + imm, pc + INSTRUCTIONSIZE, current_nid);
  }

  // jump from this instruction to instruction at address pc + imm
  go_to_instruction(is, rd, pc, pc + imm, 0);
}

void model_control_flow_jalr() {
  if (rd == REG_ZR)
    if (imm == 0)
      if (rs1 == REG_RA)
        if (pc >= estimated_return)
          // no forward branches and jumps outside of "procedure body"
          if (current_callee > code_start) {
            // assert: current_callee points to an instruction to which a jal jumps
            *(call_return + (current_callee - code_start) / INSTRUCTIONSIZE) = pc;

            // assert: next "procedure body" begins right after jalr
            current_callee = pc + INSTRUCTIONSIZE;

            estimated_return = current_callee;

            return;
          }

  //report the error on the console
  output_fd = 1;

  printf("%s: unsupported jalr at address %lu[0x%lX] with estimated address %lu[0x%lX] detected\n", selfie_name, pc, pc, estimated_return, estimated_return);

  exit(EXITCODE_MODELINGERROR);
}

void model_data_flow_ecall() {
  // keep track of whether any ecall is active
  w = w + dprintf(output_fd, "%lu ite 1 %lu 11 %lu ; ",
    current_nid,         // nid of this line
    pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
    ecall_flow_nid);     // nid of most recent update of ecall activation

  ecall_flow_nid = current_nid;

  w = w + print_ecall() + dprintf(output_fd, "\n");
}

void model_control_flow_ecall() {
  if (reg_a7 == SYSCALL_EXIT) {
    // assert: exit ecall is immediately followed by first procedure in code
    current_callee = pc + INSTRUCTIONSIZE;

    estimated_return = current_callee;
  }

  reg_a7 = 0;

  model_control_flow_lui_add_sub_mul_divu_remu_sltu_load_store();
}

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void reset_bounds() {
  if (check_block_access) {
    // if this instruction is active reset lower bound on $rd register to start of data segment
    w = w + dprintf(output_fd, "%lu ite 2 %lu 30 %lu\n",
      current_nid,                      // nid of this line
      pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
      *(reg_flow_nids + LO_FLOW + rd)); // nid of most recent update of lower bound on $rd register

    *(reg_flow_nids + LO_FLOW + rd) = current_nid;

    current_nid = current_nid + 1;

    // if this instruction is active reset upper bound on $rd register to highest address in 32-bit virtual address space (4GB)
    w = w + dprintf(output_fd, "%lu ite 2 %lu 50 %lu\n",
      current_nid,                      // nid of this line
      pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
      *(reg_flow_nids + UP_FLOW + rd)); // nid of most recent update of upper bound on $rd register

    *(reg_flow_nids + UP_FLOW + rd) = current_nid;

    current_nid = current_nid + 1;
  }
}

void transfer_bounds() {
  if (check_block_access) {
    // if this instruction is active set lower bound on $rd = lower bound on $rs1 register
    w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
      current_nid,                      // nid of this line
      pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
      reg_nids + LO_FLOW + rs1,         // nid of lower bound on $rs1 register
      *(reg_flow_nids + LO_FLOW + rd)); // nid of most recent update of lower bound on $rd register

    *(reg_flow_nids + LO_FLOW + rd) = current_nid;

    current_nid = current_nid + 1;

    // if this instruction is active set upper bound on $rd = upper bound on $rs1 register
    w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
      current_nid,                      // nid of this line
      pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
      reg_nids + UP_FLOW + rs1,         // nid of upper bound on $rs1 register
      *(reg_flow_nids + UP_FLOW + rd)); // nid of most recent update of upper bound on $rd register

    *(reg_flow_nids + UP_FLOW + rd) = current_nid;

    current_nid = current_nid + 1;
  }
}

uint64_t record_start_bounds(uint64_t cursor_nid, uint64_t activation_nid, uint64_t reg) {
  if (check_block_access) {
    // if current instruction is active record lower bound on $reg register for checking address validity
    w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
      cursor_nid,               // nid of this line
      activation_nid,           // nid of activation condition of current instruction
      reg_nids + LO_FLOW + reg, // nid of current lower bound on $reg register
      lo_flow_start_nid);       // nid of most recent update of lower bound on memory access

    lo_flow_start_nid = cursor_nid;

    cursor_nid = cursor_nid + 1;

    // if current instruction is active record upper bound on $reg register for checking address validity
    w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
      cursor_nid,               // nid of this line
      activation_nid,           // nid of activation condition of current instruction
      reg_nids + UP_FLOW + reg, // nid of current upper bound on $reg register
      up_flow_start_nid);       // nid of most recent update of upper bound on memory access

    up_flow_start_nid = cursor_nid;

    return cursor_nid + 1;
  } else
    return cursor_nid;
}

uint64_t record_end_bounds(uint64_t cursor_nid, uint64_t activation_nid, uint64_t reg) {
  if (check_block_access) {
    // if current instruction is active record lower bound on $reg register for checking address validity
    w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
      cursor_nid,               // nid of this line
      activation_nid,           // nid of activation condition of current instruction
      reg_nids + LO_FLOW + reg, // nid of current lower bound on $reg register
      lo_flow_end_nid);         // nid of most recent update of lower bound on memory access

    lo_flow_end_nid = cursor_nid;

    cursor_nid = cursor_nid + 1;

    // if current instruction is active record upper bound on $reg register for checking address validity
    w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
      cursor_nid,               // nid of this line
      activation_nid,           // nid of activation condition of current instruction
      reg_nids + UP_FLOW + reg, // nid of current upper bound on $reg register
      up_flow_end_nid);         // nid of most recent update of upper bound on memory access

    up_flow_end_nid = cursor_nid;

    return cursor_nid + 1;
  } else
    return cursor_nid;
}

uint64_t model_virtual_address() {
  if (imm == 0)
    return reg_nids + rs1; // nid of current value of $rs1 register
  else {
    w = w
      + dprintf(output_fd, "%lu constd 2 %ld ; 0x%lX\n",
          current_nid,                      // nid of this line
          imm,                              // signed immediate value
          sign_shrink(imm, WORDSIZEINBITS)) // immediate value in hexadecimal

      // compute $rs1 + imm
      + dprintf(output_fd, "%lu add 2 %lu %lu\n",
          current_nid + 1, // nid of this line
          reg_nids + rs1,  // nid of current value of $rs1 register
          current_nid);    // nid of immediate value

    current_nid = current_nid + 2;

    return current_nid - 1; // nid of $rs1 + imm
  }
}

uint64_t model_physical_address_in_segment(uint64_t cursor_nid, uint64_t laddr_nid,
  uint64_t start_nid, uint64_t end_nid, uint64_t offset_nid, uint64_t flow_nid) {
  uint64_t laddr_alignment;

  w = w + dprintf(output_fd, "%lu ugte 1 %lu %lu ; address >= start of segment\n",
    cursor_nid, // nid of this line
    laddr_nid,  // nid of virtual or linear address
    start_nid); // nid of start of segment

  // in address spaces where the highest address is the largest value
  // wraparound makes this constraint obsolete
  if (end_nid) {
    if (end_nid == 50)
      // 50 is nid of highest address in 32-bit virtual address space (4GB)
      w = w + dprintf(output_fd, "%lu ulte 1 %lu %lu ; address <= end of segment\n",
        cursor_nid + 1, // nid of this line
        laddr_nid,      // nid of virtual address
        end_nid);       // nid of end of segment
    else
      w = w + dprintf(output_fd, "%lu ult 1 %lu %lu ; address < end of segment\n",
        cursor_nid + 1, // nid of this line
        laddr_nid,      // nid of virtual or linear address
        end_nid);       // nid of end of segment

    w = w + dprintf(output_fd, "%lu and 1 %lu %lu\n",
      cursor_nid + 2,  // nid of this line
      cursor_nid,      // nid of >= check
      cursor_nid + 1); // nid of < check

    cursor_nid = cursor_nid + 2;
  }

  if (linear_address_space)
    laddr_alignment = 0;
  else
    laddr_alignment = vaddr_alignment;

  w = w
    // subtract offset of segment in virtual or linear address space
    + dprintf(output_fd, "%lu sub %lu %lu %lu\n",
        cursor_nid + 1, // nid of this line
        vaddr_sort_nid, // nid of virtual or linear address sort
        laddr_nid,      // nid of virtual or linear address
        offset_nid)     // nid of segment offset in virtual or linear address space
    + dprintf(output_fd, "%lu slice 6 %lu %lu %lu\n",
        cursor_nid + 2,                         // nid of this line
        cursor_nid + 1,                         // nid of mapped virtual or linear address
        paddr_space_size - 1 + laddr_alignment, // size of physical address space in bits - 1 + address alignment
        laddr_alignment)                        // 3 (or 2) virtual address alignment, or 0 for linear address
    + dprintf(output_fd, "%lu ite 6 %lu %lu %lu\n",
        cursor_nid + 3, // nid of this line
        cursor_nid,     // nid of segment check
        cursor_nid + 2, // nid of physical address
        flow_nid);      // nid of physical address in other segment

  return cursor_nid + 3; // nid of physical address
}

uint64_t model_physical_address(uint64_t cursor_nid, uint64_t vaddr_nid) {
  uint64_t laddr_nid;

  if (linear_address_space) {
    w = w + dprintf(output_fd, "%lu slice 4 %lu 31 %lu\n",
      cursor_nid,       // nid of this line
      vaddr_nid,        // nid of virtual address
      vaddr_alignment); // 3 (or 2) virtual address alignment

    laddr_nid  = cursor_nid;
    cursor_nid = cursor_nid + 1;
  } else
    laddr_nid = vaddr_nid;

  if (MMU) {
    if (linear_address_space) {
      // use linear segment dimensions
      cursor_nid = model_physical_address_in_segment(cursor_nid, laddr_nid, 40, 41, 40, 8);
      cursor_nid = model_physical_address_in_segment(cursor_nid + 1, laddr_nid, 42, 44, 46, cursor_nid);

      return model_physical_address_in_segment(cursor_nid + 1, laddr_nid, 45, 0, 47, cursor_nid);
    } else {
      // use virtual segment dimensions
      cursor_nid = model_physical_address_in_segment(cursor_nid, laddr_nid, 30, 31, 30, 8);
      cursor_nid = model_physical_address_in_segment(cursor_nid + 1, laddr_nid, 32, 34, 36, cursor_nid);

      return model_physical_address_in_segment(cursor_nid + 1, laddr_nid, 35, 50, 37, cursor_nid);
    }
  } else
    return laddr_nid;
}

uint64_t model_RAM_access(uint64_t cursor_nid, uint64_t address_nid, uint64_t RAM_address,
  uint64_t RAM_word, uint64_t RAM_word_flow_nid) {
  w = w
    // address == RAM address
    + dprintf(output_fd, "%lu eq 1 %lu %lu\n",
        cursor_nid,                      // nid of this line
        address_nid,                     // nid of virtual, linear, or physical address
        pc_nid(memory_nid, RAM_address)) // nid of virtual, linear, or physical RAM address
    // if paddr == RAM address access RAM word
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
        cursor_nid + 1,     // nid of this line
        cursor_nid,         // address == RAM address
        RAM_word,           // nid of RAM word
        RAM_word_flow_nid); // nid of most recent access of RAM word at RAM address

  return cursor_nid + 1;
}

uint64_t compute_linear_address(uint64_t vaddr) {
  if (linear_address_space)
    return vaddr / WORDSIZE;
  else
    return vaddr;
}

uint64_t compute_physical_address(uint64_t vaddr) {
  if (MMU + RAM + MMURAM > 0) {
    if (vaddr >= data_start)
      if (vaddr < data_start + data_size)
        // vaddr in data segment
        vaddr = vaddr - data_start;
      else if (vaddr >= heap_start)
        if (vaddr < heap_start + heap_size)
          // vaddr in heap segment
          vaddr = vaddr - heap_start + data_size;
        else if (vaddr >= stack_start)
          if (vaddr <= stack_start + stack_size - WORDSIZE)
            // vaddr in stack segment
            vaddr = vaddr - stack_start + data_size + heap_size;
          else
            exit(EXITCODE_MODELINGERROR);
        else
          exit(EXITCODE_MODELINGERROR);
      else
        exit(EXITCODE_MODELINGERROR);
    else
      exit(EXITCODE_MODELINGERROR);

    // bypass linear address space
    return vaddr / WORDSIZE;
  }

  return compute_linear_address(vaddr);
}

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

uint64_t already_seen_instruction(uint64_t address) {
  if (statically_live_code != (uint64_t*) 0)
    return *(statically_live_code + (address - code_start) / INSTRUCTIONSIZE) == SEEN;
  else
    return 1;
}

uint64_t is_statically_live_instruction(uint64_t address) {
  if (statically_live_code != (uint64_t*) 0)
    return *(statically_live_code + (address - code_start) / INSTRUCTIONSIZE) == LIVE;
  else
    return 1;
}

void mark_instruction(uint64_t address, uint64_t mark) {
  *(statically_live_code + (address - code_start) / INSTRUCTIONSIZE) = mark;
}

uint64_t get_return_mark(uint64_t address) {
  return *(statically_live_return + (address - code_start) / INSTRUCTIONSIZE);
}

void mark_return(uint64_t address, uint64_t mark) {
  *(statically_live_return + (address - code_start) / INSTRUCTIONSIZE) = mark;
}

uint64_t mark_statically_live_code(uint64_t start_address, uint64_t callee_address,
  uint64_t entry_pc, uint64_t mark) {
  uint64_t next_pc;

  pc = start_address;

  while (1) {
    if (pc < code_start)
      // segfaulting pc
      exit(EXITCODE_MODELINGERROR);
    else if (pc >= code_start + code_size)
      // segfaulting pc
      exit(EXITCODE_MODELINGERROR);

    if (pc == entry_pc)
      // from here on mark as live
      mark = LIVE;

    if (mark == SEEN)
      if (already_seen_instruction(pc))
        return mark;

    if (mark == LIVE)
      if (is_statically_live_instruction(pc))
        return mark;

    mark_instruction(pc, mark);

    fetch();
    decode();

    next_pc = pc + INSTRUCTIONSIZE;

    if (is == ADDI) {
      if (rd == REG_A7)
        if (rs1 == REG_ZR)
          if (imm != 0)
            // assert: next instruction is ecall
            reg_a7 = imm;
    } else if (is == BEQ)
      // assert: only branching forward but not beyond jalr

      // mark true branch first, fast forwarding to jalr
      mark_statically_live_code(pc + imm, callee_address, entry_pc, mark);
    else if (is == JAL) {
      if (rd == REG_RA) {
        // assert: procedure call
        if (pc + imm == exit_wrapper_address)
          // exit wrapper does not return
          mark = DEAD;
        else
          mark = mark_statically_live_code(pc + imm, pc + imm, entry_pc, mark);

        if (mark == DEAD) {
          // procedure does not return
          if (callee_address == 0)
            // not in procedure or no path yet to jalr
            return DEAD;
          else
            return get_return_mark(callee_address);
        }
      } else
        next_pc = pc + imm;
    } else if (is == JALR) {
      // assert: jalr returning from procedure call
      mark_return(callee_address, mark);

      return mark;
    } else if (is == ECALL) {
      if (reg_a7 == SYSCALL_EXIT) {
        reg_a7 = 0;

        // assert: there is only one exit wrapper

        if (callee_address != 0)
          // actual exit wrapper call
          exit_wrapper_address = callee_address;

        return DEAD;
      }
    }

    pc = next_pc;
  }
}

void static_dead_code_elimination(uint64_t start_address, uint64_t entry_pc) {
  uint64_t saved_pc;

  statically_live_code   = zmalloc(code_size / INSTRUCTIONSIZE * sizeof(uint64_t));
  statically_live_return = zmalloc(code_size / INSTRUCTIONSIZE * sizeof(uint64_t));

  saved_pc = pc;

  mark_statically_live_code(start_address, 0, entry_pc, SEEN);

  pc = saved_pc;
}

void translate_to_model() {
  // assert: 1 <= is <= number of RISC-U instructions

  if (is_statically_live_instruction(pc)) {
    if (is == ADDI)
      model_data_flow_addi();
    else if (is == LOAD)
      model_data_flow_load();
    else if (is == STORE)
      model_data_flow_store();
    else if (is == ADD)
      model_data_flow_add();
    else if (is == SUB)
      model_data_flow_sub();
    else if (is == MUL)
      model_data_flow_mul();
    else if (is == DIVU)
      model_data_flow_divu();
    else if (is == REMU)
      model_data_flow_remu();
    else if (is == SLTU)
      model_data_flow_sltu();
    else if (is == BEQ)
      model_data_flow_beq();
    else if (is == JAL)
      model_data_flow_jal();
    // TODO: model jalr data flow
    else if (is == LUI)
      model_data_flow_lui();
    else if (is == ECALL)
      model_data_flow_ecall();
  }

  if (is == ADDI)
    model_control_flow_addi();
  else if (is == LOAD)
    model_control_flow_lui_add_sub_mul_divu_remu_sltu_load_store();
  else if (is == STORE)
    model_control_flow_lui_add_sub_mul_divu_remu_sltu_load_store();
  else if (is == ADD)
    model_control_flow_lui_add_sub_mul_divu_remu_sltu_load_store();
  else if (is == SUB)
    model_control_flow_lui_add_sub_mul_divu_remu_sltu_load_store();
  else if (is == MUL)
    model_control_flow_lui_add_sub_mul_divu_remu_sltu_load_store();
  else if (is == DIVU)
    model_control_flow_lui_add_sub_mul_divu_remu_sltu_load_store();
  else if (is == REMU)
    model_control_flow_lui_add_sub_mul_divu_remu_sltu_load_store();
  else if (is == SLTU)
    model_control_flow_lui_add_sub_mul_divu_remu_sltu_load_store();
  else if (is == BEQ)
    model_control_flow_beq();
  else if (is == JAL)
    model_control_flow_jal();
  else if (is == JALR)
    model_control_flow_jalr();
  else if (is == LUI)
    model_control_flow_lui_add_sub_mul_divu_remu_sltu_load_store();
  else if (is == ECALL)
    model_control_flow_ecall();
}

// -----------------------------------------------------------------
// ------------------------ MODEL GENERATOR ------------------------
// -----------------------------------------------------------------

uint64_t control_flow(uint64_t activate_nid, uint64_t control_flow_nid) {
  if (control_flow_nid == 10)
    // instruction proceeding here is first instruction to do so
    return activate_nid;
  else {
    // activate current instruction if instruction proceeding here is active
    w = w + dprintf(output_fd, "%lu ite 1 %lu 11 %lu\n",
      current_nid,       // nid of this line
      activate_nid,      // nid of pc flag of instruction proceeding here
      control_flow_nid); // nid of previously processed in-edge

    current_nid = current_nid + 1;

    return current_nid - 1;
  }
}

uint64_t control_flow_from_beq(uint64_t from_address, uint64_t condition_nid, uint64_t control_flow_nid) {
  w = w
    // is beq active and its condition true or false?
    + dprintf(output_fd, "%lu and 1 %lu %lu ; beq %lu[0x%lX]",
        current_nid,                   // nid of this line
        pc_nid(pcs_nid, from_address), // nid of pc flag of instruction proceeding here
        condition_nid,                 // nid of true or false beq condition
        from_address, from_address)    // address of instruction proceeding here
    + print_code_line_number_for_instruction(from_address, code_start)
    + dprintf(output_fd, "\n");

  current_nid = current_nid + 1;

  // activate this instruction if beq is active and its condition is true (false)
  control_flow_nid = control_flow(current_nid - 1, control_flow_nid);

  return control_flow_nid;
}

uint64_t control_flow_from_jalr(uint64_t jalr_address, uint64_t condition_nid, uint64_t control_flow_nid) {
  w = w
    // is value of $ra register with LSB reset equal to address of this instruction?
    + dprintf(output_fd, "%lu not 2 21 ; jalr %lu[0x%lX]",
        current_nid,                // nid of this line
        jalr_address, jalr_address) // address of instruction proceeding here
    + print_code_line_number_for_instruction(jalr_address, code_start)
    + dprintf(output_fd, "\n")
    + dprintf(output_fd, "%lu and 2 %lu %lu\n",
        current_nid + 1,   // nid of this line
        reg_nids + REG_RA, // nid of current value of $ra register
        current_nid)       // nid of not 1
    + dprintf(output_fd, "%lu eq 1 %lu %lu\n",
        current_nid + 2, // nid of this line
        current_nid + 1, // nid of current value of $ra register with LSB reset
        condition_nid)   // nid of address of this instruction (generated by jal)

    // is jalr active and the previous condition true or false?
    + dprintf(output_fd, "%lu and 1 %lu %lu\n",
        current_nid + 3,               // nid of this line
        pc_nid(pcs_nid, jalr_address), // nid of pc flag of instruction proceeding here
        current_nid + 2);              // nid of return address condition

  current_nid = current_nid + 4;

  // activate this instruction if jalr is active and its condition is true (false)
  control_flow_nid = control_flow(current_nid - 1, control_flow_nid);

  return control_flow_nid;
}

uint64_t control_flow_from_ecall(uint64_t from_address, uint64_t control_flow_nid) {
  w = w
    + dprintf(output_fd, "%lu state 1 kernel-mode-pc-flag-%lu[0x%lX]",
        current_nid,                // nid of this line
        from_address, from_address) // address of instruction proceeding here
    + print_code_line_number_for_instruction(from_address, code_start)
    + dprintf(output_fd, "\n")

    + dprintf(output_fd, "%lu init 1 %lu 10 ; ecall is initially inactive\n",
        current_nid + 1, // nid of this line
        current_nid)     // nid of kernel-mode pc flag of ecall

    + dprintf(output_fd, "%lu ite 1 %lu 60 %lu ; activate ecall and keep active while in kernel mode\n",
        current_nid + 2,               // nid of this line
        current_nid,                   // nid of kernel-mode pc flag of ecall
        pc_nid(pcs_nid, from_address)) // nid of pc flag of instruction proceeding here

    + dprintf(output_fd, "%lu next 1 %lu %lu ; keep ecall active while in kernel mode\n",
        current_nid + 3, // nid of this line
        current_nid,     // nid of kernel-mode pc flag of ecall
        current_nid + 2) // nid of previous line

    + dprintf(output_fd, "%lu and 1 %lu 62 ; ecall is active but not in kernel mode anymore\n",
        current_nid + 4, // nid of this line
        current_nid);    // nid of kernel-mode pc flag of ecall

  current_nid = current_nid + 5;

  // activate this instruction if ecall is active but not in kernel mode anymore
  control_flow_nid = control_flow(current_nid - 1, control_flow_nid);

  return control_flow_nid;
}

void check_syscall_id() {
  w = w
    + dprintf(output_fd, "%lu not 1 %lu ; $a7 != SYSCALL_EXIT\n",
        current_nid,     // nid of this line
        which_ecall_nid) // nid of $a7 == SYSCALL_EXIT
    + dprintf(output_fd, "%lu not 1 %lu ; $a7 != SYSCALL_READ\n",
        current_nid + 1,     // nid of this line
        which_ecall_nid + 1) // nid of $a7 == SYSCALL_READ
    + dprintf(output_fd, "%lu not 1 %lu ; $a7 != SYSCALL_WRITE\n",
        current_nid + 2,     // nid of this line
        which_ecall_nid + 2) // nid of $a7 == SYSCALL_WRITE
    + dprintf(output_fd, "%lu not 1 %lu ; $a7 != SYSCALL_OPENAT\n",
        current_nid + 3,     // nid of this line
        which_ecall_nid + 3) // nid of $a7 == SYSCALL_OPENAT
    + dprintf(output_fd, "%lu not 1 %lu ; $a7 != SYSCALL_BRK\n",
        current_nid + 4,     // nid of this line
        which_ecall_nid + 4) // nid of $a7 == SYSCALL_BRK
    + dprintf(output_fd, "%lu and 1 %lu %lu ; ... and $a7 != SYSCALL_READ\n",
        current_nid + 5, // nid of this line
        current_nid,     // nid of $a7 != SYSCALL_EXIT
        current_nid + 1) // nid of $a7 != SYSCALL_READ
    + dprintf(output_fd, "%lu and 1 %lu %lu ; ... and $a7 != SYSCALL_WRITE\n",
        current_nid + 6, // nid of this line
        current_nid + 5, // nid of preceding line
        current_nid + 2) // nid of $a7 != SYSCALL_WRITE
    + dprintf(output_fd, "%lu and 1 %lu %lu ; ... and $a7 != SYSCALL_OPENAT\n",
        current_nid + 7, // nid of this line
        current_nid + 6, // nid of preceding line
        current_nid + 3) // nid of $a7 != SYSCALL_OPENAT
    + dprintf(output_fd, "%lu and 1 %lu %lu ; ... and $a7 != SYSCALL_BRK\n\n",
        current_nid + 8, // nid of this line
        current_nid + 7, // nid of preceding line
        current_nid + 4) // nid of $a7 != SYSCALL_BRK

    // if any ecall is active check if $a7 register contains invalid syscall id
    + dprintf(output_fd, "%lu and 1 %lu %lu ; ecall is active for invalid syscall id\n",
        current_nid + 9, // nid of this line
        ecall_flow_nid,  // nid of most recent update of ecall activation
        current_nid + 8) // nid of invalid syscall id check
    + dprintf(output_fd, "%lu bad %lu b%lu ; invalid syscall id\n\n",
        current_nid + 10, // nid of this line
        current_nid + 9,  // nid of preceding line
        bad_number);      // bad number

  current_nid = current_nid + 11;

  bad_number = bad_number + 1;
}

void check_exit_code() {
  uint64_t exit_code_check_nid;

  if (bad_exit_code == 0) {
    w = w + dprintf(output_fd, "%lu neq 1 %lu 20 ; $a0 != zero exit code\n",
      current_nid,        // nid of this line
      reg_nids + REG_A0); // nid of current value of $a0 register

    exit_code_check_nid = current_nid;

    current_nid = current_nid + 1;
  } else {
    w = w
      + dprintf(output_fd, "%lu constd 2 %ld ; non-zero exit code\n",
          current_nid,   // nid of this line
          bad_exit_code) // value of non-zero exit code
      + dprintf(output_fd, "%lu eq 1 %lu %lu ; $a0 == non-zero exit code\n",
          current_nid + 1,   // nid of this line
          reg_nids + REG_A0, // nid of current value of $a0 register
          current_nid);      // nid of value of non-zero exit code

    exit_code_check_nid = current_nid + 1;

    current_nid = current_nid + 2;
  }

  w = w
    + dprintf(output_fd, "%lu and 1 %lu %lu ; exit ecall is active with non-zero exit code\n",
        current_nid,         // nid of this line
        exit_ecall_nid,      // nid of exit ecall is active
        exit_code_check_nid) // nid of exit code check
    + dprintf(output_fd, "%lu bad %lu b%lu ; non-zero exit code\n\n",
        current_nid + 1, // nid of this line
        current_nid,     // nid of preceding line
        bad_number);     // bad number

  current_nid = current_nid + 2;

  bad_number = bad_number + 1;
}

void check_division_by_zero(uint64_t division, uint64_t flow_nid) {
  w = w
    // check if divisor == 0
    + dprintf(output_fd, "%lu eq 1 %lu 20\n",
        current_nid, // nid of this line
        flow_nid)    // nid of divisor of most recent division or remainder
    + dprintf(output_fd, "%lu bad %lu b%lu ; ",
        current_nid + 1, // nid of this line
        current_nid,     // nid of divisor == 0
        bad_number);     // bad number
  if (division)
    w = w + dprintf(output_fd, "division by zero\n\n");
  else
    w = w + dprintf(output_fd, "remainder by zero\n\n");

  current_nid = current_nid + 2;

  bad_number = bad_number + 1;
}

uint64_t check_addresses() {
  if (address_alignment_check)
    return 1;
  else if (segmentation_faults)
    return 1;
  else if (check_block_access)
    return 1;
  else
    return 0;
}

void generate_address_alignment_check(uint64_t flow_nid) {
  w = w
    // check if address of most recent memory access is word-aligned
    + dprintf(output_fd, "%lu and 2 %lu %lu ; reset all but %lu LSBs of address\n",
        current_nid,     // nid of this line
        flow_nid,        // nid of address of most recent memory access
        vaddr_mask_nid,  // nid of bit mask
        vaddr_alignment) // virtual address alignment in bits
    + dprintf(output_fd, "%lu neq 1 %lu 20 ; %lu LSBs of address != 0 (address is not word-aligned)\n",
        current_nid + 1, // nid of this line
        current_nid,     // nid of 3 (or 2) LSBs of address of most recent memory access
        vaddr_alignment) // virtual address alignment in bits
    + dprintf(output_fd, "%lu bad %lu b%lu ; word-unaligned memory access\n\n",
        current_nid + 2, // nid of this line
        current_nid + 1, // nid of previous check
        bad_number);     // bad number

  current_nid = current_nid + 3;

  bad_number = bad_number + 1;
}

void generate_segmentation_faults(uint64_t flow_nid) {
  w = w
    + dprintf(output_fd, "%lu ult 1 %lu 30 ; address < start of data segment\n",
        current_nid, // nid of this line
        flow_nid)    // nid of address of most recent memory access
    + dprintf(output_fd, "%lu bad %lu b%lu ; memory access below data segment\n",
        current_nid + 1, // nid of this line
        current_nid,     // nid of previous check
        bad_number);     // bad number

  current_nid = current_nid + 2;

  bad_number = bad_number + 1;

  w = w
    + dprintf(output_fd, "%lu ugte 1 %lu 31 ; address >= end of data segment\n",
        current_nid, // nid of this line
        flow_nid)    // nid of address of most recent memory access
    + dprintf(output_fd, "%lu ult 1 %lu 32 ; address < start of heap segment\n",
        current_nid + 1, // nid of this line
        flow_nid)        // nid of address of most recent memory access
    + dprintf(output_fd, "%lu and 1 %lu %lu\n",
        current_nid + 2, // nid of this line
        current_nid,     // nid of >= check
        current_nid + 1) // nid of < check
    + dprintf(output_fd, "%lu bad %lu b%lu ; memory access in between data and heap segments\n",
        current_nid + 3, // nid of this line
        current_nid + 2, // nid of previous check
        bad_number);     // bad number

  current_nid = current_nid + 4;

  bad_number = bad_number + 1;

  w = w
    + dprintf(output_fd, "%lu ugte 1 %lu %lu ; address >= current end of heap segment\n",
        current_nid,      // nid of this line
        flow_nid,         // nid of address of most recent memory access
        bump_pointer_nid) // nid of brk bump pointer
    + dprintf(output_fd, "%lu ult 1 %lu %lu ; address < current start of stack segment\n",
        current_nid + 1,   // nid of this line
        flow_nid,          // nid of address of most recent memory access
        reg_nids + REG_SP) // nid of current value of $sp register
    + dprintf(output_fd, "%lu and 1 %lu %lu\n",
        current_nid + 2, // nid of this line
        current_nid,     // nid of >= check
        current_nid + 1) // nid of < check
    + dprintf(output_fd, "%lu bad %lu b%lu ; memory access in between current heap and stack segments\n",
        current_nid + 3, // nid of this line
        current_nid + 2, // nid of previous check
        bad_number);     // bad number

  current_nid = current_nid + 4;

  bad_number = bad_number + 1;

  if (fixed_heap_segment) {
    w = w
      + dprintf(output_fd, "%lu ugte 1 %lu 34 ; address >= allowed end of heap segment\n",
          current_nid, // nid of this line
          flow_nid)    // nid of address of most recent memory access
      + dprintf(output_fd, "%lu ult 1 %lu %lu ; address < current end of heap segment\n",
          current_nid + 1,  // nid of this line
          flow_nid,         // nid of address of most recent memory access
          bump_pointer_nid) // nid of brk bump pointer
      + dprintf(output_fd, "%lu and 1 %lu %lu\n",
          current_nid + 2, // nid of this line
          current_nid,     // nid of >= check
          current_nid + 1) // nid of < check
      + dprintf(output_fd, "%lu bad %lu b%lu ; memory access in between allowed and current end of heap segment\n",
          current_nid + 3, // nid of this line
          current_nid + 2, // nid of previous check
          bad_number);     // bad number

    current_nid = current_nid + 4;

    bad_number = bad_number + 1;
  }

  if (fixed_stack_segment) {
    w = w
      + dprintf(output_fd, "%lu ugte 1 %lu %lu ; address >= current start of stack segment\n",
        current_nid,       // nid of this line
        flow_nid,          // nid of address of most recent memory access
        reg_nids + REG_SP) // nid of current value of $sp register
      + dprintf(output_fd, "%lu ult 1 %lu 35 ; address < allowed start of stack segment\n",
          current_nid + 1, // nid of this line
          flow_nid)        // nid of address of most recent memory access
      + dprintf(output_fd, "%lu and 1 %lu %lu\n",
          current_nid + 2, // nid of this line
          current_nid,     // nid of >= check
          current_nid + 1) // nid of < check
      + dprintf(output_fd, "%lu bad %lu b%lu ; memory access in between current and allowed start of stack segment\n",
          current_nid + 3, // nid of this line
          current_nid + 2, // nid of previous check
          bad_number);     // bad number

    current_nid = current_nid + 4;

    bad_number = bad_number + 1;
  }

  w = w
    + dprintf(output_fd, "%lu ugt 1 %lu 50 ; address > highest address in 32-bit virtual address space (4GB)\n",
        current_nid, // nid of this line
        flow_nid)    // nid of address of most recent memory access
    + dprintf(output_fd, "%lu bad %lu b%lu ; memory access above stack segment\n\n",
        current_nid + 1, // nid of this line
        current_nid,     // nid of previous check
        bad_number);     // bad number

  current_nid = current_nid + 2;

  bad_number = bad_number + 1;
}

void generate_block_access_check(uint64_t flow_nid, uint64_t lo_flow_nid, uint64_t up_flow_nid) {
  w = w
    // check if address of most recent memory access < current lower bound
    + dprintf(output_fd, "%lu ult 1 %lu %lu\n",
        current_nid, // nid of this line
        flow_nid,    // nid of address of most recent memory access
        lo_flow_nid) // nid of current lower bound on memory addresses
    + dprintf(output_fd, "%lu bad %lu b%lu ; memory access below lower bound\n",
        current_nid + 1, // nid of this line
        current_nid,     // nid of previous check
        bad_number);     // bad number

  current_nid = current_nid + 2;

  bad_number = bad_number + 1;

  w = w
    // check if address of most recent memory access > current upper bound
    + dprintf(output_fd, "%lu ugt 1 %lu %lu\n",
        current_nid, // nid of this line
        flow_nid,    // nid of address of most recent memory access
        up_flow_nid) // nid of current upper bound on memory addresses
    + dprintf(output_fd, "%lu bad %lu b%lu ; memory access above upper bound\n\n",
        current_nid + 1, // nid of this line
        current_nid,     // nid of previous check
        bad_number);     // bad number

  current_nid = current_nid + 2;

  bad_number = bad_number + 1;
}

uint64_t number_of_bits(uint64_t n) {
  if (n > 1)
    return log_two(n * 2 - 1);
  else if (n > 0)
    return 1;
  else
    return 0;
}

void beator(uint64_t entry_pc) {
  uint64_t i;

  uint64_t memory_word;

  uint64_t code_nid;
  uint64_t control_nid;
  uint64_t condition_nid;

  uint64_t data_flow_nid;
  uint64_t control_flow_nid;

  uint64_t* in_edge;

  uint64_t from_instruction;
  uint64_t from_address;
  uint64_t jalr_address;

  w = w
    + dprintf(output_fd, "; %s\n\n", SELFIE_URL)
    + dprintf(output_fd, "; BTOR2 %s generated by %s\n", model_name, selfie_name);
  if (syscall_id_check == 0)
    w = w + dprintf(output_fd, "; with %s\n", no_syscall_id_check_option);
  if (exit_code_check == 0)
    w = w + dprintf(output_fd, "; with %s\n", no_exit_code_check_option);
  if (division_by_zero_check == 0)
    w = w + dprintf(output_fd, "; with %s\n", no_division_by_zero_check_option);
  if (address_alignment_check == 0)
    w = w + dprintf(output_fd, "; with %s\n", no_address_alignment_check_option);
  if (segmentation_faults == 0)
    w = w + dprintf(output_fd, "; with %s\n", no_segmentation_faults_option);
  if (linear_address_space)
    w = w + dprintf(output_fd, "; with %s\n", linear_address_space_option);
  if (fixed_heap_segment)
    w = w + dprintf(output_fd, "; with %s %lu\n", heap_allowance_option, heap_allowance);
  if (fixed_stack_segment)
    w = w + dprintf(output_fd, "; with %s %lu\n", stack_allowance_option, stack_allowance);
  if (MMU)
    w = w + dprintf(output_fd, "; with %s\n", MMU_option);
  if (RAM)
    w = w + dprintf(output_fd, "; with %s\n", RAM_option);
  if (MMURAM)
    w = w + dprintf(output_fd, "; with %s\n", MMURAM_option);
  if (check_block_access)
    w = w + dprintf(output_fd, "; with %s\n", check_block_access_option);
  w = w + dprintf(output_fd, "\n; RISC-V code obtained from %s and invoked as:", binary_name);
  i = 0;
  while (i < number_of_remaining_arguments()) {
    w = w + dprintf(output_fd, " %s", (char*) *(remaining_arguments() + i));
    i = i + 1;
  }
  if (constant_propagation)
    w = w + dprintf(output_fd, "\n; with %s", constant_propagation_option);
  w = w + dprintf(output_fd, "\n\n");

  w = w
    + dprintf(output_fd, "1 sort bitvec 1 ; Boolean\n")
    + dprintf(output_fd, "2 sort bitvec %lu ; %lu-bit machine word\n", WORDSIZEINBITS, WORDSIZEINBITS);

  if (linear_address_space + MMU + RAM + MMURAM == 0)
    w = w + dprintf(output_fd, "3 sort array 2 2 ; %lu-bit physical memory\n", paddr_space_size);
  else if (linear_address_space) {
    laddr_space_size = laddr_space_size - vaddr_alignment;

    w = w + dprintf(output_fd, "\n4 sort bitvec %lu ; %lu-bit linear address\n", laddr_space_size, laddr_space_size);

    vaddr_sort_nid = 4;

    if (MMU + RAM + MMURAM == 0) {
      paddr_space_size = laddr_space_size;

      w = w + dprintf(output_fd, "5 sort array 4 2 ; %lu-bit physical memory\n", paddr_space_size);

      paddr_sort_nid  = 4;
      memory_sort_nid = 5;
    }
  }

  // assert: value of stack pointer is word-aligned

  heap_start  = get_heap_seg_start(current_context);
  heap_size   = get_program_break(current_context) - heap_start + heap_allowance;
  stack_start = *(registers + REG_SP) - stack_allowance;
  stack_size  = VIRTUALMEMORYSIZE * GIGABYTE - stack_start;

  if (MMU + RAM + MMURAM > 0) {
    paddr_space_size = number_of_bits((data_size + heap_size + stack_size) / WORDSIZE);

    w = w
      + dprintf(output_fd, "\n6 sort bitvec %lu ; %lu-bit physical address\n",
        paddr_space_size,
        paddr_space_size);

    paddr_sort_nid = 6;

    if (RAM + MMURAM == 0) {
      w = w
        + dprintf(output_fd, "7 sort array 6 2 ; %lu-bit physical memory (%luB)\n",
          paddr_space_size,
          data_size + heap_size + stack_size);

      memory_sort_nid = 7;
    } else
      memory_sort_nid = 0; // unused

    if (MMURAM == 0)
      // nid used if MMU cannot match address
      w = w + dprintf(output_fd, "8 zero 6\n");
  }

  w = w
    + dprintf(output_fd, "\n; %luB total memory, %luB data, %luB heap (%luB,%luB), %luB stack (%luB,%luB)\n\n",
        data_size + heap_size + stack_size,
        data_size,
        heap_size,
        heap_size - heap_allowance,
        heap_allowance,
        stack_size,
        stack_size - stack_allowance,
        stack_allowance)

    + dprintf(output_fd, "10 zero 1\n11 one 1\n\n")
    + dprintf(output_fd, "20 zero 2\n21 one 2\n22 constd 2 2\n23 constd 2 3\n24 constd 2 4\n");

  if (IS64BITTARGET)
    w = w + dprintf(output_fd, "25 constd 2 5\n26 constd 2 6\n27 constd 2 7\n28 constd 2 8\n");

  w = w
    + dprintf(output_fd, "\n; start of data segment in %lu-bit virtual memory\n", vaddr_space_size)
    + dprintf(output_fd, "30 constd 2 %lu ; 0x%lX\n", data_start, data_start)
    + dprintf(output_fd, "; end of data segment in %lu-bit virtual memory\n", vaddr_space_size)
    + dprintf(output_fd, "31 constd 2 %lu ; 0x%lX\n\n", data_start + data_size, data_start + data_size)

    + dprintf(output_fd, "; start of heap segment in %lu-bit virtual memory (initial program break)\n", vaddr_space_size)
    + dprintf(output_fd, "32 constd 2 %lu ; 0x%lX\n", heap_start, heap_start)
    + dprintf(output_fd, "; current end of heap segment in %lu-bit virtual memory (current program break)\n", vaddr_space_size)
    + dprintf(output_fd, "33 constd 2 %lu ; 0x%lX\n\n", get_program_break(current_context), get_program_break(current_context));

  if (fixed_heap_segment)
    w = w
      + dprintf(output_fd, "; allowed end of heap segment in %lu-bit virtual memory (with %luB allowance)\n", vaddr_space_size, heap_allowance)
      + dprintf(output_fd, "34 constd 2 %lu ; 0x%lX\n", heap_start + heap_size, heap_start + heap_size)
      + dprintf(output_fd, "; allowed start of stack segment in %lu-bit virtual memory (with %luB allowance)\n", vaddr_space_size, stack_allowance)
      + dprintf(output_fd, "35 constd 2 %lu ; 0x%lX\n\n", stack_start, stack_start);

  if (MMU)
    w = w
      + dprintf(output_fd, "; offset of heap segment in %lu-bit virtual memory\n", vaddr_space_size)
      + dprintf(output_fd, "36 constd 2 %lu ; 0x%lX\n", heap_start - data_size, heap_start - data_size)
      + dprintf(output_fd, "; offset of stack segment in %lu-bit virtual memory\n", vaddr_space_size)
      + dprintf(output_fd, "37 constd 2 %lu ; 0x%lX\n\n", stack_start - data_size - heap_size, stack_start - data_size - heap_size);

  if (linear_address_space) {
    w = w
      + dprintf(output_fd, "; start of data segment in %lu-bit linear memory\n", laddr_space_size)
      + dprintf(output_fd, "40 constd 4 %lu ; 0x%lX\n", data_start / WORDSIZE, data_start / WORDSIZE)
      + dprintf(output_fd, "; end of data segment in %lu-bit linear memory\n", laddr_space_size)
      + dprintf(output_fd, "41 constd 4 %lu ; 0x%lX\n\n", (data_start + data_size) / WORDSIZE, (data_start + data_size) / WORDSIZE)

      + dprintf(output_fd, "; start of heap segment in %lu-bit linear memory (initial program break)\n", laddr_space_size)
      + dprintf(output_fd, "42 constd 4 %lu ; 0x%lX\n", heap_start / WORDSIZE, heap_start / WORDSIZE)
      + dprintf(output_fd, "; current end of heap segment in %lu-bit linear memory (current program break)\n", laddr_space_size)
      + dprintf(output_fd, "43 constd 4 %lu ; 0x%lX\n\n", get_program_break(current_context) / WORDSIZE, get_program_break(current_context) / WORDSIZE);

    if (fixed_heap_segment)
      w = w
        + dprintf(output_fd, "; allowed end of heap segment in %lu-bit linear memory (with %luB allowance)\n", laddr_space_size, heap_allowance)
        + dprintf(output_fd, "44 constd 4 %lu ; 0x%lX\n", (heap_start + heap_size) / WORDSIZE, (heap_start + heap_size) / WORDSIZE)
        + dprintf(output_fd, "; allowed start of stack segment in %lu-bit linear memory (with %luB allowance)\n", laddr_space_size, stack_allowance)
        + dprintf(output_fd, "45 constd 4 %lu ; 0x%lX\n\n", stack_start / WORDSIZE, stack_start / WORDSIZE);

    if (MMU)
      w = w
        + dprintf(output_fd, "; offset of heap segment in %lu-bit linear memory\n", laddr_space_size)
        + dprintf(output_fd, "46 constd 4 %lu ; 0x%lX\n", (heap_start - data_size) / WORDSIZE, (heap_start - data_size) / WORDSIZE)
        + dprintf(output_fd, "; offset of stack segment in %lu-bit linear memory\n", laddr_space_size)
        + dprintf(output_fd, "47 constd 4 %lu ; 0x%lX\n\n", (stack_start - data_size - heap_size) / WORDSIZE, (stack_start - data_size - heap_size) / WORDSIZE);
  }

  w = w
    // avoiding 2^32 for 32-bit version
    + dprintf(output_fd, "; highest address in 32-bit virtual address space (4GB)\n\n")
    + dprintf(output_fd, "50 constd 2 %lu ; 0x%lX\n\n",
      HIGHESTVIRTUALADDRESS, HIGHESTVIRTUALADDRESS)

    + dprintf(output_fd, "; kernel-mode flag\n\n")

    + dprintf(output_fd, "60 state 1 kernel-mode\n")
    + dprintf(output_fd, "61 init 1 60 10 kernel-mode ; initial value is false\n")
    + dprintf(output_fd, "62 not 1 60\n\n")

    + dprintf(output_fd, "; unsigned-extended inputs for byte-wise reading\n\n");

  w = w
    + dprintf(output_fd, "71 sort bitvec 8 ; 1 byte\n")
    + dprintf(output_fd, "72 sort bitvec 16 ; 2 bytes\n")
    + dprintf(output_fd, "73 sort bitvec 24 ; 3 bytes\n");

  if (IS64BITTARGET)
    w = w
      + dprintf(output_fd, "74 sort bitvec 32 ; 4 bytes\n")
      + dprintf(output_fd, "75 sort bitvec 40 ; 5 bytes\n")
      + dprintf(output_fd, "76 sort bitvec 48 ; 6 bytes\n")
      + dprintf(output_fd, "77 sort bitvec 56 ; 7 bytes\n");

  w = w
    + dprintf(output_fd, "\n81 input 71 1-byte-input\n")
    + dprintf(output_fd, "82 input 72 2-byte-input\n")
    + dprintf(output_fd, "83 input 73 3-byte-input\n");

  if (IS64BITTARGET)
    w = w
      + dprintf(output_fd, "84 input 74 4-byte-input\n")
      + dprintf(output_fd, "85 input 75 5-byte-input\n")
      + dprintf(output_fd, "86 input 76 6-byte-input\n")
      + dprintf(output_fd, "87 input 77 7-byte-input\n\n")

      + dprintf(output_fd, "91 uext 2 81 56 ; uext-1-byte-input\n")
      + dprintf(output_fd, "92 uext 2 82 48 ; uext-2-byte-input\n")
      + dprintf(output_fd, "93 uext 2 83 40 ; uext-3-byte-input\n")
      + dprintf(output_fd, "94 uext 2 84 32 ; uext-4-byte-input\n")
      + dprintf(output_fd, "95 uext 2 85 24 ; uext-5-byte-input\n")
      + dprintf(output_fd, "96 uext 2 86 16 ; uext-6-byte-input\n")
      + dprintf(output_fd, "97 uext 2 87 8 ; uext-7-byte-input\n")
      + dprintf(output_fd, "98 input 2 8-byte-input\n\n");
  else
    w = w
      + dprintf(output_fd, "\n91 uext 2 81 24 ; uext-1-byte-input\n")
      + dprintf(output_fd, "92 uext 2 82 16 ; uext-2-byte-input\n")
      + dprintf(output_fd, "93 uext 2 83 8 ; uext-3-byte-input\n")
      + dprintf(output_fd, "94 input 2 4-byte-input\n\n");

  w = w
    + dprintf(output_fd, "; 32 %lu-bit general-purpose registers\n\n", WORDSIZEINBITS)
    + dprintf(output_fd, "; non-zero initial register values\n");

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    if (i == 0)
      w = w + dprintf(output_fd, "\n");
    else if (*(registers + i) != 0)
      w = w + dprintf(output_fd, "%lu constd 2 %lu ; 0x%lX for %s\n",
        reg_value_nids + i,                            // nid of this line
        sign_shrink(*(registers + i), WORDSIZEINBITS), // unsigned initial value
        *(registers + i),                              // initial value in hexadecimal as comment
        get_register_name(i));                         // register name as comment

    i = i + 1;
  }

  w = w + dprintf(output_fd, "\n; registers\n");

  reg_flow_nids = smalloc(3 * NUMBEROFREGISTERS * sizeof(uint64_t*));

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    *(reg_flow_nids + i) = reg_nids + i;

    if (i == 0)
      w = w + dprintf(output_fd, "\n%lu zero 2 %s ; register $0 is always 0\n",
        *(reg_flow_nids + i),  // nid of this line
        get_register_name(i)); // register name
    else
      w = w + dprintf(output_fd, "%lu state 2 %s ; register $%lu\n",
        *(reg_flow_nids + i), // nid of this line
        get_register_name(i), // register name
        i);                   // register index as comment

    i = i + 1;
  }

  if (check_block_access)
    while (i < 3 * NUMBEROFREGISTERS) {
      *(reg_flow_nids + i) = reg_nids + i;

      if (i == LO_FLOW)
        w = w + dprintf(output_fd, "\n%lu constd 2 %lu ; 0x%lX start of data segment\n",
          *(reg_flow_nids + i), // nid of this line
          data_start,           // start of data segment
          data_start);          // start of data segment in hexadecimal
      else if (i == UP_FLOW)
        w = w + dprintf(output_fd, "\n%lu constd 2 %lu ; 0x%lX highest address in 32-bit virtual address space (4GB)\n",
          *(reg_flow_nids + i),   // nid of this line
          HIGHESTVIRTUALADDRESS,  // highest address in 32-bit virtual address space (4GB)
          HIGHESTVIRTUALADDRESS); // highest address in 32-bit virtual address space (4GB) in hexadecimal
      else {
        w = w + dprintf(output_fd, "%lu state 2 ", *(reg_flow_nids + i));

        if (i < LO_FLOW + NUMBEROFREGISTERS)
          w = w + dprintf(output_fd, "lo-%s ; lower bound on $%lu\n",
            get_register_name(i % NUMBEROFREGISTERS), // register name
            i % NUMBEROFREGISTERS);                   // register index as comment
        else if (i < UP_FLOW + NUMBEROFREGISTERS)
          w = w + dprintf(output_fd, "up-%s ; upper bound on $%lu\n",
            get_register_name(i % NUMBEROFREGISTERS), // register name
            i % NUMBEROFREGISTERS);                   // register index as comment
      }

      i = i + 1;
    }

  w = w + dprintf(output_fd, "\n; initializing registers\n");

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    if (i == 0)
      w = w + dprintf(output_fd, "\n");
    else if (*(registers + i) == 0)
      w = w + dprintf(output_fd, "%lu init 2 %lu 20 %s ; initial value is 0\n",
        reg_init_nids + i,     // nid of this line
        reg_nids + i,          // nid of to-be-initialized register
        get_register_name(i)); // register name as comment
    else
      w = w + dprintf(output_fd, "%lu init 2 %lu %lu %s ; initial value is %lu\n",
        reg_init_nids + i,                              // nid of this line
        reg_nids + i,                                   // nid of to-be-initialized register
        reg_value_nids + i,                             // nid of unsigned initial value
        get_register_name(i),                           // register name as comment
        sign_shrink(*(registers + i), WORDSIZEINBITS)); // unsigned initial value

    i = i + 1;
  }

  if (check_block_access)
    while (i < 3 * NUMBEROFREGISTERS) {
      if (i % NUMBEROFREGISTERS == 0)
        w = w + dprintf(output_fd, "\n");
      else if (i < LO_FLOW + NUMBEROFREGISTERS)
        w = w + dprintf(output_fd, "%lu init 2 %lu 30 %s ; initial value is start of data segment\n",
          reg_init_nids + i,                         // nid of this line
          reg_nids + i,                              // nid of to-be-initialized register
          get_register_name(i % NUMBEROFREGISTERS)); // register name as comment
      else if (i < UP_FLOW + NUMBEROFREGISTERS)
        w = w + dprintf(output_fd, "%lu init 2 %lu 50 %s ; initial value is highest address in 32-bit virtual address space (4GB)\n",
          reg_init_nids + i,                         // nid of this line
          reg_nids + i,                              // nid of to-be-initialized register
          get_register_name(i % NUMBEROFREGISTERS)); // register name as comment

      i = i + 1;
    }

  w = w + dprintf(output_fd, "\n; %lu-bit program counter encoded in Boolean flags\n\n", WORDSIZEINBITS);

  pcs_nid = ten_to_the_power_of(log_ten(heap_start + heap_size + stack_size) + PC_NID_DIGITS);

  pc = code_start;

  while (pc < code_start + code_size) {
    current_nid = pc_nid(pcs_nid, pc);

    if (is_statically_live_instruction(pc)) {
      // pc flag of current instruction
      w = w + dprintf(output_fd, "%lu state 1 pc=0x%lX\n", current_nid, pc);

      if (pc == entry_pc)
        // set pc here by initializing pc flag of instruction to true
        w = w + dprintf(output_fd, "%lu init 1 %lu 11 ; initial program counter\n",
          current_nid + 1, // nid of this line
          current_nid);    // nid of pc flag of current instruction
      else
        // initialize all other pc flags to false
        w = w + dprintf(output_fd, "%lu init 1 %lu 10\n",
          current_nid + 1, // nid of this line
          current_nid);    // nid of pc flag of current instruction
    } else
      w = w + dprintf(output_fd, "; %lu unreachable state at %lX\n", current_nid, pc);

    pc = pc + INSTRUCTIONSIZE;
  }

  pc = data_start;

  if (RAM + MMURAM == 0) {
    current_nid = pc_nid(pcs_nid, pc);
    memory_nid  = current_nid;

    w = w + dprintf(output_fd, "\n%lu state %lu memory-dump\n\n", current_nid, memory_sort_nid);

    data_flow_nid = current_nid;
  } else {
    memory_nid  = pcs_nid * 2;
    current_nid = memory_nid;

    w = w + dprintf(output_fd, "\n; %lu-bit physical memory\n\n", paddr_space_size);

    data_flow_nid = 0;

    RAM_write_flow_nid = smalloc((data_size + heap_size + stack_size) / WORDSIZE * sizeof(uint64_t));
  }

  w = w + dprintf(output_fd, "; data segment\n\n");

  // assert: data segment is not empty

  while (pc <= VIRTUALMEMORYSIZE * GIGABYTE - WORDSIZE) {
    if (pc == data_start + data_size) {
      pc = heap_start;

      if (heap_size > 0)
        w = w + dprintf(output_fd, "\n; heap segment\n\n");
    }

    if (pc == heap_start + heap_size) {
      // assert: stack pointer <= HIGHESTVIRTUALADDRESS
      pc = stack_start;

      w = w + dprintf(output_fd, "\n; stack segment\n\n");
      // assert: stack segment is not empty
    }

    if (RAM + MMURAM > 0)
      current_nid = pc_nid(memory_nid, compute_physical_address(pc));
    else if (current_nid == memory_nid)
      // account for nid offset by 1 of memory-dump state
      current_nid = current_nid + 1;
    else if (pc < stack_start)
      current_nid = pc_nid(pcs_nid, pc);
    else
      current_nid = pc_nid(pcs_nid, pc - stack_start + heap_start + heap_size);

    // address in data, heap, or stack segment
    if (MMURAM == 0)
      w = w + dprintf(output_fd, "%lu constd %lu %lu ; 0x%lX paddr, 0x%lX vaddr\n",
        current_nid,                  // nid of this line
        paddr_sort_nid,               // nid of physical address sort
        compute_physical_address(pc), // physical address of current machine word
        compute_physical_address(pc), // physical address of current machine word in hexadecimal as comment
        pc);                          // virtual address of current machine word in hexadecimal as comment
    else
      w = w + dprintf(output_fd, "%lu constd %lu %lu ; 0x%lX laddr, 0x%lX vaddr\n",
        current_nid,                // nid of this line
        vaddr_sort_nid,             // nid of virtual or linear address sort
        compute_linear_address(pc), // virtual or linear address of current machine word
        compute_linear_address(pc), // virtual or linear address of current machine word in hexadecimal as comment
        pc);                        // virtual address of current machine word in hexadecimal as comment

    if (is_virtual_address_mapped(get_pt(current_context), pc))
      memory_word = load_virtual_memory(get_pt(current_context), pc);
    else
      // memory allocated but not yet mapped is zeroed
      memory_word = 0;

    if (memory_word == 0) {
      // load memory word == 0
      if (RAM + MMURAM > 0) {
        // implementing memory word as state variable, after constd for paddr
        w = w
          // wasting one nid so that state variables have the same offset
          + dprintf(output_fd, "%lu state 2 RAM-word-%lu\n",
              current_nid + 2,              // nid of this line
              compute_physical_address(pc)) // physical address of current machine word
          // initialize memory word in RAM with zero
          + dprintf(output_fd, "%lu init 2 %lu 20\n",
              current_nid + 3,  // nid of this line
              current_nid + 2); // nid of memory word in RAM

        *(RAM_write_flow_nid + compute_physical_address(pc)) = current_nid + 2;

        // account for last declared and initialized memory word, see below
        data_flow_nid = current_nid + 4;
      } else {
        w = w + dprintf(output_fd, "%lu write %lu %lu %lu 20\n",
          current_nid + 1, // nid of this line
          memory_sort_nid, // nid of physical memory sort
          data_flow_nid,   // nid of most recent update of memory
          current_nid);    // nid of address of current memory word

        data_flow_nid = current_nid + 1;
      }
    } else {
      // load non-zero memory word, use sign
      if (RAM + MMURAM > 0) {
        w = w
          + dprintf(output_fd, "%lu constd 2 %lu ; 0x%lX word\n",
              current_nid + 1,          // nid of this line
              memory_word, memory_word) // value of memory word at current address
          // implementing memory word as state variable, after constd for paddr
          + dprintf(output_fd, "%lu state 2 RAM-word-%lu\n",
              current_nid + 2,              // nid of this line
              compute_physical_address(pc)) // physical address of current machine word
          // initialize memory word in RAM with non-zero value
          + dprintf(output_fd, "%lu init 2 %lu %lu\n",
              current_nid + 3,  // nid of this line
              current_nid + 2,  // nid of memory word in RAM
              current_nid + 1); // nid of value of memory word at current address

        *(RAM_write_flow_nid + compute_physical_address(pc)) = current_nid + 2;

        // account for last declared and initialized memory word, see below
        data_flow_nid = current_nid + 4;
      } else {
        w = w
          + dprintf(output_fd, "%lu constd 2 %lu ; 0x%lX word\n",
              current_nid + 1,          // nid of this line
              memory_word, memory_word) // value of memory word at current address
          + dprintf(output_fd, "%lu write %lu %lu %lu %lu\n",
              current_nid + 2,  // nid of this line
              memory_sort_nid,  // nid of physical memory sort
              data_flow_nid,    // nid of most recent update of memory
              current_nid,      // nid of address of current memory word
              current_nid + 1); // nid of value of memory word at current address

        data_flow_nid = current_nid + 2;
      }
    }

    if (pc + WORDSIZE == 0)
      // check 32-bit overflow to terminate loop
      pc = HIGHESTVIRTUALADDRESS;
    else
      pc = pc + WORDSIZE;
  }

  if (RAM + MMURAM == 0) {
    w = w + dprintf(output_fd, "\n; %lu-bit physical memory\n\n", paddr_space_size);

    memory_nid = pcs_nid * 2;

    current_nid = memory_nid;

    w = w
      + dprintf(output_fd, "%lu state %lu physical-memory ; data, heap, stack segments\n",
          current_nid,     // nid of this line
          memory_sort_nid) // nid of physical memory sort
      + dprintf(output_fd, "%lu init %lu %lu %lu ; loading data, heap, stack segments into memory\n",
          current_nid + 1, // nid of this line
          memory_sort_nid, // nid of physical memory sort
          current_nid,     // nid of physical memory
          data_flow_nid);  // nid of most recent update of memory

    memory_flow_nid = current_nid;

    current_nid = current_nid + 2;
  } else
    // account for last declared and initialized memory word
    current_nid = data_flow_nid;

  if (check_block_access) {
    lo_memory_nid = current_nid;

    w = w
      + dprintf(output_fd, "\n%lu state %lu lower-bounds ; for checking address validity\n",
          current_nid,     // nid of this line
          memory_sort_nid) // nid of physical memory sort
      + dprintf(output_fd, "%lu init %lu %lu 30 ; initializing lower bounds to start of data segment\n",
          current_nid + 1, // nid of this line
          memory_sort_nid, // nid of physical memory sort
          current_nid);    // nid of lower bounds on addresses in memory

    lo_memory_flow_nid = current_nid;

    current_nid = current_nid + 2;

    up_memory_nid = current_nid;

    w = w
      + dprintf(output_fd, "%lu state %lu upper-bounds ; for checking address validity\n",
          current_nid,     // nid of this line
          memory_sort_nid) // nid of physical memory sort
      + dprintf(output_fd, "%lu init %lu %lu 50 ; initializing upper bounds to highest address in 32-bit virtual address space (4GB)\n",
          current_nid + 1, // nid of this line
          memory_sort_nid, // nid of physical memory sort
          current_nid);    // nid of upper bounds on addresses in memory

    up_memory_flow_nid = current_nid;
  }

  w = w + dprintf(output_fd, "\n; data flow\n\n");

  code_nid = pcs_nid * 3;

  control_in  = zmalloc(code_size / INSTRUCTIONSIZE * sizeof(uint64_t));
  call_return = zmalloc(code_size / INSTRUCTIONSIZE * sizeof(uint64_t));

  current_callee   = code_start;
  estimated_return = code_start;

  pc = code_start;

  while (pc < code_start + code_size) {
    fetch();
    decode();

    current_nid = pc_nid(code_nid, pc);

    translate_to_model();

    pc = pc + INSTRUCTIONSIZE;
  }

  w = w + dprintf(output_fd, "\n; syscalls\n\n");

  current_nid = pcs_nid * 4;

  model_syscalls(current_nid);

  w = w + dprintf(output_fd, "\n; control flow\n\n");

  control_nid = pcs_nid * 5;

  pc = code_start;

  while (pc < code_start + code_size) {
    current_nid = pc_nid(control_nid, pc);

    in_edge = (uint64_t*) *(control_in + (pc - code_start) / INSTRUCTIONSIZE);

    // nid of 1-bit 0
    control_flow_nid = 10;

    while (in_edge != (uint64_t*) 0) {
      from_instruction = *(in_edge + 1);
      from_address     = *(in_edge + 2);
      condition_nid    = *(in_edge + 3);

      if (from_instruction == BEQ) {
        if (is_statically_live_instruction(from_address))
          control_flow_nid = control_flow_from_beq(from_address, condition_nid, control_flow_nid);
      } else if (from_instruction == JALR) {
        jalr_address = *(call_return + (from_address - code_start) / INSTRUCTIONSIZE);

        if (jalr_address != 0) {
          if (is_statically_live_instruction(jalr_address))
            control_flow_nid = control_flow_from_jalr(jalr_address, condition_nid, control_flow_nid);
        } else {
          // no jalr returning from jal found
          w = w
            + dprintf(output_fd, "; exit ecall wrapper call or runaway jal %lu[0x%lX]", from_address, from_address)
            + print_code_line_number_for_instruction(from_address, code_start)
            + dprintf(output_fd, "\n");

          // this instruction may stay deactivated if there is no more in-edges
        }
      } else if (from_instruction == ECALL) {
        if (is_statically_live_instruction(from_address))
          control_flow_nid = control_flow_from_ecall(from_address, control_flow_nid);
      } else {
        if (is_statically_live_instruction(from_address)) {
          if (from_instruction == JAL) w = w + dprintf(output_fd, "; jal "); else w = w + dprintf(output_fd, "; ");
          w = w
            + dprintf(output_fd, "%lu[0x%lX]", from_address, from_address)
            + print_code_line_number_for_instruction(from_address, code_start)
            + dprintf(output_fd, "\n");

          // activate this instruction if instruction proceeding here is active
          control_flow_nid = control_flow(pc_nid(pcs_nid, from_address), control_flow_nid);
        }
      }

      in_edge = (uint64_t*) *in_edge;
    }

    if (is_statically_live_instruction(pc)) {
      if (control_flow_nid == 10)
        if (pc != entry_pc) {
          output_fd = 1;

          printf("%s: no in-edges at reachable instruction address %lu[0x%lX] detected\n", selfie_name, pc, pc);

          exit(EXITCODE_MODELINGERROR);
        }

      w = w
        // update pc flag of current instruction
        + dprintf(output_fd, "%lu next 1 %lu %lu ; ->%lu[0x%lX]",
            current_nid,         // nid of this line
            pc_nid(pcs_nid, pc), // nid of pc flag of current instruction
            control_flow_nid,    // nid of most recently processed in-edge
            pc, pc)              // address of current instruction
        + print_code_line_number_for_instruction(pc, code_start)
        + dprintf(output_fd, "\n");
    }

    if (current_nid >= pc_nid(control_nid, pc) + PC_NID_FACTOR * 4) {
      // the instruction at pc is reachable by too many other instructions

      // report the error on the console
      output_fd = 1;

      printf("%s: cannot handle %lu in-edges at instruction address %lu[0x%lX]\n", selfie_name,
        current_nid - pc_nid(control_nid, pc), pc, pc);

      exit(EXITCODE_MODELINGERROR);
    }

    pc = pc + INSTRUCTIONSIZE;
  }

  w = w + dprintf(output_fd, "\n; updating registers\n");

  current_nid = pcs_nid * 6;

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    if (i == 0)
      w = w + dprintf(output_fd, "\n");
    else
      w = w + dprintf(output_fd, "%lu next 2 %lu %lu %s ; register $%lu\n",
        current_nid + i,      // nid of this line
        reg_nids + i,         // nid of register
        *(reg_flow_nids + i), // nid of most recent update to register
        get_register_name(i), // register name
        i);                   // register index as comment

    i = i + 1;
  }

  if (check_block_access)
    while (i < 3 * NUMBEROFREGISTERS) {
      if (i % NUMBEROFREGISTERS == 0)
        w = w + dprintf(output_fd, "\n");
      else {
        w = w + dprintf(output_fd, "%lu next 2 %lu %lu ",
          current_nid + i,       // nid of this line
          reg_nids + i,          // nid of register
          *(reg_flow_nids + i)); // nid of most recent update to register

        if (i < LO_FLOW + NUMBEROFREGISTERS)
          w = w + dprintf(output_fd, "lo-%s ; lower bound on $%lu\n",
            get_register_name(i % NUMBEROFREGISTERS), // register name
            i % NUMBEROFREGISTERS);                   // register index as comment
        else if (i < UP_FLOW + NUMBEROFREGISTERS)
          w = w + dprintf(output_fd, "up-%s ; upper bound on $%lu\n",
            get_register_name(i % NUMBEROFREGISTERS), // register name
            i % NUMBEROFREGISTERS);                   // register index as comment
      }

      i = i + 1;
    }

  w = w + dprintf(output_fd, "\n; updating %lu-bit physical memory\n\n", paddr_space_size);

  current_nid = pcs_nid * 7;

  if (RAM + MMURAM == 0) {
    w = w + dprintf(output_fd, "%lu next %lu %lu %lu physical-memory\n",
      current_nid,      // nid of this line
      memory_sort_nid,  // nid of physical memory sort
      memory_nid,       // nid of physical memory
      memory_flow_nid); // nid of most recent write to memory

    current_nid = current_nid + 1;
  } else {
    i = 0;

    while (i < (data_size + heap_size + stack_size) / WORDSIZE) {
      w = w + dprintf(output_fd, "%lu next 2 %lu %lu RAM-word-%lu\n",
        current_nid,               // nid of this line
        pc_nid(memory_nid, i) + 2, // nid of RAM
        *(RAM_write_flow_nid + i), // nid of most recent write to RAM
        i);                        // physical address of machine word

      current_nid = current_nid + 1;

      i = i + 1;
    }
  }

  w = w + dprintf(output_fd, "\n");

  if (check_block_access)
    w = w
      + dprintf(output_fd, "%lu next %lu %lu %lu lower-bounds\n",
        current_nid,        // nid of this line
        memory_sort_nid,    // nid of physical memory sort
        lo_memory_nid,      // nid of lower bounds on addresses in memory
        lo_memory_flow_nid) // nid of most recent write to lower bounds on addresses in memory
      + dprintf(output_fd, "%lu next %lu %lu %lu upper-bounds\n\n",
        current_nid + 1,     // nid of this line
        memory_sort_nid,     // nid of physical memory sort
        up_memory_nid,       // nid of upper bounds on addresses in memory
        up_memory_flow_nid); // nid of most recent write to upper bounds on addresses in memory

  current_nid = pcs_nid * 8;

  bad_number = 0;

  if (syscall_id_check) {
    w = w + dprintf(output_fd, "; checking syscall id\n\n");

    check_syscall_id();
  }

  if (exit_code_check) {
    w = w + dprintf(output_fd, "; checking exit code\n\n");

    check_exit_code();
  }

  if (division_by_zero_check) {
    w = w + dprintf(output_fd, "; checking division and remainder by zero\n\n");

    check_division_by_zero(1, division_flow_nid);
    check_division_by_zero(0, remainder_flow_nid);
  }

  if (address_alignment_check) {
    w = w
      + dprintf(output_fd, "; checking address validity\n\n")
      + dprintf(output_fd, "; is start address of memory access word-aligned?\n\n");

    generate_address_alignment_check(access_flow_start_nid);

    if (check_block_access) {
      w = w + dprintf(output_fd, "; is end address of memory access word-aligned?\n\n");

      generate_address_alignment_check(access_flow_end_nid);
    }
  }

  if (segmentation_faults) {
    w = w
      + dprintf(output_fd, "; checking segmentation faults\n\n")
      + dprintf(output_fd, "; is start address of memory access in a valid segment?\n\n");

    generate_segmentation_faults(access_flow_start_nid);

    if (check_block_access) {
      w = w + dprintf(output_fd, "; is end address of memory access in a valid segment?\n\n");

      generate_segmentation_faults(access_flow_end_nid);
    }
  }

  if (check_block_access) {
    w = w + dprintf(output_fd, "; is start address of memory access in memory block?\n\n");

    generate_block_access_check(access_flow_start_nid, lo_flow_start_nid, up_flow_start_nid);

    w = w + dprintf(output_fd, "; is end address of memory access in memory block?\n\n");

    generate_block_access_check(access_flow_end_nid, lo_flow_end_nid, up_flow_end_nid);
  }

  // TODO: check validity of return addresses in jalr

  w = w + dprintf(output_fd, "; end of BTOR2 %s\n", model_name);
}

uint64_t selfie_model() {
  uint64_t entry_pc;
  uint64_t model_arguments;

  no_syscall_id_check_option        = "--no-syscall-id-check";
  no_exit_code_check_option         = "--no-exit-code-check";
  no_division_by_zero_check_option  = "--no-division-by-zero-check";
  no_address_alignment_check_option = "--no-address-alignment-check";
  no_segmentation_faults_option     = "--no-segmentation-faults";

  check_block_access_option   = "--check-block-access";
  constant_propagation_option = "--constant-propagation";
  linear_address_space_option = "--linear-address-space";
  heap_allowance_option       = "--heap-allowance";
  stack_allowance_option      = "--stack-allowance";
  MMU_option                  = "--MMU";
  RAM_option                  = "--RAM";
  MMURAM_option               = "--MMURAM";

  if (IS64BITTARGET == 0) {
    // assert: 32-bit system
    vaddr_mask_nid  = 23;
    vaddr_alignment = 2;

    vaddr_space_size = WORDSIZEINBITS;
    paddr_space_size = vaddr_space_size;
  }

  if (string_compare(argument, "-")) {
    if (number_of_remaining_arguments() > 0) {
      bad_exit_code = atoi(peek_argument(0));

      model_arguments = 0;

      while (model_arguments == 0) {
        if (number_of_remaining_arguments() > 1) {
          if (string_compare(peek_argument(1), no_syscall_id_check_option)) {
            syscall_id_check = 0;

            get_argument();
          } else if (string_compare(peek_argument(1), no_exit_code_check_option)) {
            exit_code_check = 0;

            get_argument();
          } else if (string_compare(peek_argument(1), no_division_by_zero_check_option)) {
            division_by_zero_check = 0;

            get_argument();
          } else if (string_compare(peek_argument(1), no_address_alignment_check_option)) {
            address_alignment_check = 0;

            get_argument();
          } else if (string_compare(peek_argument(1), no_segmentation_faults_option)) {
            segmentation_faults = 0;

            get_argument();
          } else if (string_compare(peek_argument(1), check_block_access_option)) {
            check_block_access = 1;

            get_argument();
          } else if (string_compare(peek_argument(1), constant_propagation_option)) {
            constant_propagation = 1;

            get_argument();
          } else if (string_compare(peek_argument(1), linear_address_space_option)) {
            linear_address_space = 1;

            get_argument();
          } else if (string_compare(peek_argument(1), heap_allowance_option)) {
            fixed_heap_segment = 1;

            get_argument();

            if (number_of_remaining_arguments() > 1) {
              heap_allowance = round_up(atoi(peek_argument(1)), WORDSIZE);

              get_argument();
            } else
              exit(EXITCODE_BADARGUMENTS);
          } else if (string_compare(peek_argument(1), stack_allowance_option)) {
            fixed_stack_segment = 1;

            get_argument();

            if (number_of_remaining_arguments() > 1) {
              stack_allowance = round_up(atoi(peek_argument(1)), WORDSIZE);

              get_argument();
            } else
              exit(EXITCODE_BADARGUMENTS);
          } else if (string_compare(peek_argument(1), MMU_option)) {
            MMU = 1;

            fixed_heap_segment  = 1;
            fixed_stack_segment = 1;

            get_argument();
          } else if (string_compare(peek_argument(1), RAM_option)) {
            RAM = 1;
            MMU = 1;

            fixed_heap_segment  = 1;
            fixed_stack_segment = 1;

            get_argument();
          } else if (string_compare(peek_argument(1), MMURAM_option)) {
            MMURAM = 1;

            fixed_heap_segment  = 1;
            fixed_stack_segment = 1;

            get_argument();
          } else
            model_arguments = 1;
        } else
          model_arguments = 1;
      }

      if (MMURAM) {
        MMU = 0;
        RAM = 0;
      }

      if (segmentation_faults == 0) {
        if (MMU)
          printf("%s: warning: %s with %s\n", selfie_name, MMU_option, no_segmentation_faults_option);
        if (RAM)
          printf("%s: warning: %s with %s\n", selfie_name, RAM_option, no_segmentation_faults_option);
        if (MMURAM)
          printf("%s: warning: %s with %s\n", selfie_name, MMURAM_option, no_segmentation_faults_option);
      }

      if (code_size == 0) {
        printf("%s: nothing to model\n", selfie_name);

        return EXITCODE_BADARGUMENTS;
      }

      // use extension ".btor2" in name of SMT-LIB file
      model_name = replace_extension(binary_name, "-beaten", "btor2");

      // assert: model_name is mapped and not longer than MAX_FILENAME_LENGTH

      model_fd = open_write_only(model_name, S_IRUSR_IWUSR_IRGRP_IROTH);

      if (signed_less_than(model_fd, 0)) {
        printf("%s: could not create model file %s\n", selfie_name, model_name);

        exit(EXITCODE_IOERROR);
      }

      reset_library();

      reset_interpreter();
      reset_profiler();
      reset_microkernel();

      init_memory(1);

      current_context = create_context(MY_CONTEXT, 0);

      // assert: number_of_remaining_arguments() > 0

      boot_loader(current_context);

      entry_pc = get_pc(current_context);

      if (constant_propagation) {
        printf("%s: --------------------------------------------------------------------------------\n", selfie_name);
        printf("%s: constant propagation with ", selfie_name);

        exited_on_timeout = 0;
        exited_on_read    = 0;

        TIMESLICE = 10000000;

        run = 1;

        propr(current_context);

        run = 0;

        if (exited_on_timeout)
          printf("%s: constant propagation could not find read call\n", selfie_name);
        else if (exited_on_read == 0) {
          printf("%s: constant propagation yields empty model\n", selfie_name);

          exit(EXITCODE_MODELINGERROR);
        }
      }

      restore_context(current_context);

      do_switch(current_context, TIMEROFF);

      static_dead_code_elimination(entry_pc, get_pc(current_context));

      output_name = model_name;
      output_fd   = model_fd;

      run = 0;

      model = 1;

      beator(get_pc(current_context));

      model = 0;

      output_name = (char*) 0;
      output_fd   = 1;

      printf("%s: %lu characters of model formulae written into %s\n", selfie_name, w, model_name);

      printf("%s: ################################################################################\n", selfie_name);

      return EXITCODE_NOERROR;
    } else
      return EXITCODE_BADARGUMENTS;
  } else
    return EXITCODE_BADARGUMENTS;
}

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// ----------------------    R U N T I M E    ----------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ---------------------------- KERNEL -----------------------------
// -----------------------------------------------------------------

uint64_t handle_propr_system_call(uint64_t* context) {
  uint64_t a7;

  set_exception(context, EXCEPTION_NOEXCEPTION);

  set_ec_syscall(context, get_ec_syscall(context) + 1);

  a7 = *(get_regs(context) + REG_A7);

  if (a7 == SYSCALL_BRK) {
    if (is_gc_enabled(context))
      implement_gc_brk(context);
    else
      implement_brk(context);
  } else if (a7 == SYSCALL_READ) {
    exited_on_read = 1;

    set_exit_code(context, sign_shrink(EXITCODE_NOERROR, SYSCALL_BITWIDTH));

    return EXIT;
  } else if (a7 == SYSCALL_WRITE)
    implement_write(context);
  else if (a7 == SYSCALL_OPENAT)
    implement_openat(context);
  else if (a7 == SYSCALL_EXIT) {
    implement_exit(context);

    // TODO: exit only if all contexts have exited
    return EXIT;
  } else {
    printf("%s: unknown system call %lu\n", selfie_name, a7);

    set_exit_code(context, EXITCODE_UNKNOWNSYSCALL);

    return EXIT;
  }

  return DONOTEXIT;
}

uint64_t handle_propr_timer(uint64_t* context) {
  set_exception(context, EXCEPTION_NOEXCEPTION);

  set_ec_timer(context, get_ec_timer(context) + 1);

  exited_on_timeout = 1;

  return EXIT;
}

uint64_t handle_propr_exception(uint64_t* context) {
  uint64_t exception;

  exception = get_exception(context);

  if (exception == EXCEPTION_SYSCALL)
    return handle_propr_system_call(context);
  else if (exception == EXCEPTION_PAGEFAULT)
    return handle_page_fault(context);
  else if (exception == EXCEPTION_DIVISIONBYZERO)
    return handle_division_by_zero(context);
  else if (exception == EXCEPTION_TIMER)
    return handle_propr_timer(context);
  else {
    printf("%s: context %s threw uncaught exception: ", selfie_name, get_name(context));
    print_exception(exception, get_fault(context));
    println();

    set_exit_code(context, EXITCODE_UNCAUGHTEXCEPTION);

    return EXIT;
  }
}

// -----------------------------------------------------------------
// --------------------- CONSTANT PROPAGATION ----------------------
// -----------------------------------------------------------------

uint64_t propr(uint64_t* to_context) {
  uint64_t timeout;
  uint64_t* from_context;

  printf("propr\n");
  printf("%s: --------------------------------------------------------------------------------\n", selfie_name);

  timeout = TIMESLICE;

  while (1) {
    from_context = mipster_switch(to_context, timeout);

    if (get_parent(from_context) != MY_CONTEXT) {
      // switch to parent which is in charge of handling exceptions
      to_context = get_parent(from_context);

      timeout = TIMEROFF;
    } else if (handle_propr_exception(from_context) == EXIT)
      return get_exit_code(from_context);
    else {
      // TODO: scheduler should go here
      to_context = from_context;

      timeout = TIMESLICE;
    }
  }
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

int main(int argc, char** argv) {
  uint64_t exit_code;

  init_selfie((uint64_t) argc, (uint64_t*) argv);

  init_library();
  init_system();
  init_target();
  init_kernel();

  exit_code = selfie(1);

  if (exit_code == EXITCODE_MOREARGUMENTS)
    exit_code = selfie_model();

  return exit_selfie(exit_code, " - exit-code [ --check-block-access ] ...");
}