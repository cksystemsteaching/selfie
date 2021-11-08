/*
Copyright (c) 2015-2021, the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

http://selfie.cs.uni-salzburg.at

Modeler is a binary translator for bounded model checking that
implements a sound and complete translation of RISC-U code to BTOR2
formulae. Modeler serves as research platform and facilitates teaching
the absolute basics of bit-precise reasoning on real code.

Given a RISC-U binary (or C* source code compiled to RISC-U, including
all of selfie and modeler itself), modeler generates a BTOR2 file that
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

The optional console argument --check-block-access instructs modeler
to generate additional checks for identifying unsafe memory access
outside of malloced memory blocks.

Any remaining console arguments are uninterpreted and passed on as
console arguments to the modeled RISC-U binary.

Modeler is inspired by Professor Armin Biere from JKU Linz.
*/

// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~
// -----------------------------------------------------------------
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void model_syscalls();

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

// -----------------------------------------------------------------
// ---------------------------- MEMORY -----------------------------
// -----------------------------------------------------------------

void reset_bounds();
void transfer_bounds();

uint64_t record_start_bounds(uint64_t cursor_nid, uint64_t activation_nid, uint64_t reg);
uint64_t record_end_bounds(uint64_t cursor_nid, uint64_t activation_nid, uint64_t reg);

uint64_t model_virtual_address();
uint64_t model_physical_address_in_segment(uint64_t cursor_nid, uint64_t laddr_nid,
  uint64_t start_nid, uint64_t end_nid, uint64_t offset_nid, uint64_t word_alignment,
  uint64_t flow_nid);
uint64_t model_physical_address(uint64_t cursor_nid, uint64_t vaddr_nid);

uint64_t compute_physical_address(uint64_t vaddr);

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

uint64_t is_statically_live_instruction(uint64_t address);
void     mark_statically_live_instruction(uint64_t address, uint64_t mark);

uint64_t mark_statically_live_code(uint64_t callee_pc, uint64_t exit_pc, uint64_t mark);
void     static_dead_code_elimination(uint64_t entry_pc, uint64_t exit_pc);

void translate_to_model();

// ------------------------ GLOBAL VARIABLES -----------------------

uint64_t exit_procedure_entry = 0;

uint64_t* statically_live_code = (uint64_t*) 0;

// -----------------------------------------------------------------
// ------------------------ MODEL GENERATOR ------------------------
// -----------------------------------------------------------------

uint64_t control_flow(uint64_t activate_nid, uint64_t control_flow_nid);

uint64_t control_flow_from_beq(uint64_t from_address, uint64_t condition_nid, uint64_t control_flow_nid);
uint64_t control_flow_from_jalr(uint64_t jalr_address, uint64_t condition_nid, uint64_t control_flow_nid);
uint64_t control_flow_from_ecall(uint64_t from_address, uint64_t control_flow_nid);

void check_division_by_zero(uint64_t division, uint64_t flow_nid);

void generate_address_alignment_check(uint64_t flow_nid);
void generate_segmentation_faults(uint64_t flow_nid);
void generate_block_access_check(uint64_t flow_nid, uint64_t lo_flow_nid, uint64_t up_flow_nid);

void modeler();

uint64_t selfie_model();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t EXITCODE_MODELINGERROR = 1;

uint64_t LO_FLOW = 32; // offset of nids of lower bounds on addresses in registers
uint64_t UP_FLOW = 64; // offset of nids of upper bounds on addresses in registers

// ------------------------ GLOBAL VARIABLES -----------------------

char*    model_name = (char*) 0; // name of model file
uint64_t model_fd   = 0;         // file descriptor of open model file

char* no_syscall_id_check_option       = (char*) 0;
char* no_division_by_zero_check_option = (char*) 0;
char* no_address_validity_check_option = (char*) 0;
char* no_segmentation_faults_option    = (char*) 0;

char* check_block_access_option   = (char*) 0;
char* constant_propagation_option = (char*) 0;
char* linear_address_space_option = (char*) 0;
char* heap_allowance_option       = (char*) 0;
char* stack_allowance_option      = (char*) 0;
char* segment_memory_option       = (char*) 0;

uint64_t syscall_id_check       = 1; // flag for preventing syscall id checks
uint64_t division_by_zero_check = 1; // flag for preventing division and remainder by zero checks
uint64_t address_validity_check = 1; // flag for preventing memory access validity checks
uint64_t segmentation_faults    = 1; // flag for preventing segmentation fault checks

uint64_t check_block_access   = 0; // flag for generating memory access validity checks on malloced block level
uint64_t constant_propagation = 0; // flag for constant propagation
uint64_t linear_address_space = 0; // flag for 29-bit linear address space
uint64_t fixed_heap_segment   = 0; // flag for fixing size of heap segment
uint64_t fixed_stack_segment  = 0; // flag for fixing size of stack segment
uint64_t segment_memory       = 0; // flag for segmenting memory

uint64_t virtual_address_sort_nid  = 0; // nid of virtual address sort
uint64_t physical_address_sort_nid = 0; // nid of physical address sort
uint64_t memory_sort_nid           = 0; // nid of physical memory sort

uint64_t heap_allowance  = 0; // additional heap memory in bytes
uint64_t stack_allowance = 0; // additional stack memory in bytes

uint64_t bad_exit_code = 0; // model for this exit code

uint64_t physical_address_space_size = 64; // size of physical address space in bits

uint64_t heap_start  = 0;
uint64_t heap_size   = 0;
uint64_t stack_start = 0;
uint64_t stack_size  = 0;

uint64_t w = 0; // number of written characters

uint64_t current_nid = 0; // nid of current line

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

// for checking division and remainder by zero
// 21 is nid of 1 which is ok as divisor
uint64_t division_flow_nid  = 21;
uint64_t remainder_flow_nid = 21;

// for checking address validity during state transitions with no memory access:
// 30 is nid of start of data segment which must be a valid address (thus also checked)
uint64_t access_flow_start_nid = 30;

// 50 is nid of 4GB of memory addresses
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
// -------------------     I N T E R F A C E     -------------------
// -----------------------------------------------------------------
// *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~ *~*~

// -----------------------------------------------------------------
// ----------------------- MIPSTER SYSCALLS ------------------------
// -----------------------------------------------------------------

void model_syscalls() {
  uint64_t current_ecall_nid;
  uint64_t increment_nid;
  uint64_t input_nid;
  uint64_t paddr_nid;
  uint64_t write_input_nid;
  uint64_t read_loop_nid;
  uint64_t kernel_mode_flow_nid;

  w = w
    + dprintf(output_fd, "%lu constd 2 %lu ; SYSCALL_EXIT\n", current_nid, SYSCALL_EXIT)
    + dprintf(output_fd, "%lu constd 2 %lu ; SYSCALL_READ\n", current_nid + 1, SYSCALL_READ)
    + dprintf(output_fd, "%lu constd 2 %lu ; SYSCALL_WRITE\n", current_nid + 2, SYSCALL_WRITE)
    + dprintf(output_fd, "%lu constd 2 %lu ; SYSCALL_OPENAT\n", current_nid + 3, SYSCALL_OPENAT)
    + dprintf(output_fd, "%lu constd 2 %lu ; SYSCALL_BRK\n\n", current_nid + 4, SYSCALL_BRK)

    + dprintf(output_fd, "%lu eq 1 %lu %lu ; $a7 == SYSCALL_EXIT\n",
        current_nid + 10,  // nid of this line
        reg_nids + REG_A7, // nid of current value of $a7 register
        current_nid)        // nid of SYSCALL_EXIT
    + dprintf(output_fd, "%lu eq 1 %lu %lu ; $a7 == SYSCALL_READ\n",
        current_nid + 11,  // nid of this line
        reg_nids + REG_A7, // nid of current value of $a7 register
        current_nid + 1)   // nid of SYSCALL_READ
    + dprintf(output_fd, "%lu eq 1 %lu %lu ; $a7 == SYSCALL_WRITE\n",
        current_nid + 12,  // nid of this line
        reg_nids + REG_A7, // nid of current value of $a7 register
        current_nid + 2)   // nid of SYSCALL_WRITE
    + dprintf(output_fd, "%lu eq 1 %lu %lu ; $a7 == SYSCALL_OPENAT\n",
        current_nid + 13,  // nid of this line
        reg_nids + REG_A7, // nid of current value of $a7 register
        current_nid + 3)   // nid of SYSCALL_OPENAT
    + dprintf(output_fd, "%lu eq 1 %lu %lu ; $a7 == SYSCALL_BRK\n\n",
        current_nid + 14,  // nid of this line
        reg_nids + REG_A7, // nid of current value of $a7 register
        current_nid + 4)   // nid of SYSCALL_BRK

    + dprintf(output_fd, "%lu not 1 %lu ; $a7 != SYSCALL_EXIT\n",
        current_nid + 20, // nid of this line
        current_nid + 10) // nid of $a7 == SYSCALL_EXIT
    + dprintf(output_fd, "%lu ite 1 %lu 10 %lu ; ... and $a7 != SYSCALL_READ\n",
        current_nid + 21, // nid of this line
        current_nid + 11, // nid of $a7 == SYSCALL_READ
        current_nid + 20) // nid of preceding line
    + dprintf(output_fd, "%lu ite 1 %lu 10 %lu ; ... and $a7 != SYSCALL_WRITE\n",
        current_nid + 22, // nid of this line
        current_nid + 12, // nid of $a7 == SYSCALL_WRITE
        current_nid + 21) // nid of preceding line
    + dprintf(output_fd, "%lu ite 1 %lu 10 %lu ; ... and $a7 != SYSCALL_OPENAT\n",
        current_nid + 23, // nid of this line
        current_nid + 13, // nid of $a7 == SYSCALL_OPENAT
        current_nid + 22) // nid of preceding line
    + dprintf(output_fd, "%lu ite 1 %lu 10 %lu ; ... and $a7 != SYSCALL_BRK (invalid syscall id in $a7 detected)\n\n",
        current_nid + 24,  // nid of this line
        current_nid + 14,  // nid of $a7 == SYSCALL_BRK
        current_nid + 23); // nid of preceding line

  if (syscall_id_check)
    w = w
      // if any ecall is active check if $a7 register contains invalid syscall id
      + dprintf(output_fd, "%lu and 1 %lu %lu ; ecall is active for invalid syscall id\n",
          current_nid + 30, // nid of this line
          ecall_flow_nid,   // nid of most recent update of ecall activation
          current_nid + 24) // nid of invalid syscall id check
      + dprintf(output_fd, "%lu bad %lu ; ecall invalid syscall id\n\n",
          current_nid + 31,  // nid of this line
          current_nid + 30); // nid of preceding line


  current_ecall_nid = current_nid + pcs_nid / 10;

  // if exit ecall is active check if exit code in $a0 register is not 0
  w = w + dprintf(output_fd, "%lu and 1 %lu %lu ; exit ecall is active\n",
    current_ecall_nid, // nid of this line
    ecall_flow_nid,    // nid of most recent update of ecall activation
    current_nid + 10); // nid of $a7 == SYSCALL_EXIT
  if (bad_exit_code == 0)
    w = w + dprintf(output_fd, "%lu neq 1 %lu 20 ; $a0 != zero exit code\n",
      current_ecall_nid + 2, // nid of this line
      reg_nids + REG_A0);    // nid of current value of $a0 register
  else
    w = w
      + dprintf(output_fd, "%lu constd 2 %ld ; bad exit code\n",
          current_ecall_nid + 1, // nid of this line
          bad_exit_code)         // value of bad exit code
      + dprintf(output_fd, "%lu eq 1 %lu %lu ; $a0 == bad non-zero exit code\n",
          current_ecall_nid + 2,  // nid of this line
          reg_nids + REG_A0,      // nid of current value of $a0 register
          current_ecall_nid + 1); // nid of value of bad non-zero exit code
  w = w
    + dprintf(output_fd, "%lu and 1 %lu %lu ; exit ecall is active with non-zero exit code\n",
        current_ecall_nid + 3, // nid of this line
        current_ecall_nid,     // nid of exit ecall is active
        current_ecall_nid + 2) // nid of non-zero exit code
    + dprintf(output_fd, "%lu bad %lu ; non-zero exit code\n",
        current_ecall_nid + 4, // nid of this line
        current_ecall_nid + 3) // nid of preceding line

    // if exit ecall is active stay in kernel mode indefinitely
    + dprintf(output_fd, "%lu ite 1 60 %lu %lu ; stay in kernel mode indefinitely if exit ecall is active\n\n",
        current_ecall_nid + 50, // nid of this line
        current_nid + 10,       // nid of $a7 == SYSCALL_EXIT
        current_ecall_nid);     // nid of exit ecall is active

  kernel_mode_flow_nid = current_ecall_nid + 50;


  current_ecall_nid = current_nid + pcs_nid / 10 + pcs_nid / 100;

  w = w
    // read ecall
    + dprintf(output_fd, "%lu and 1 %lu %lu ; read ecall is active\n",
        current_ecall_nid, // nid of this line
        ecall_flow_nid,    // nid of most recent update of ecall activation
        current_nid + 11)  // nid of $a7 == SYSCALL_READ

    // if read ecall is active record $a1 register for checking address validity
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; $a1 is start address of write buffer for checking address validity\n",
        current_ecall_nid + 1,  // nid of this line
        current_ecall_nid,      // nid of read ecall is active
        reg_nids + REG_A1,      // nid of current value of $a1 register
        access_flow_start_nid); // nid of address of most recent memory access

  access_flow_start_nid = current_ecall_nid + 1;

  w = w
    // if read ecall is active record $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and
    // $a1 otherwise, as address for checking address validity
    + dprintf(output_fd, "%lu dec 2 %lu ; $a2 - 1\n",
        current_ecall_nid + 2, // nid of this line
        reg_nids + REG_A2)     // nid of current value of $a2 register
    + dprintf(output_fd, "%lu not 2 27 ; not 7\n",
        current_ecall_nid + 3) // nid of this line
    + dprintf(output_fd, "%lu and 2 %lu %lu ; reset 3 LSBs of $a2 - 1\n",
        current_ecall_nid + 4, // nid of this line
        current_ecall_nid + 2, // nid of $a2 - 1
        current_ecall_nid + 3) // nid of not 7
    + dprintf(output_fd, "%lu add 2 %lu %lu ; $a1 + (($a2 - 1) / 8) * 8\n",
        current_ecall_nid + 5, // nid of this line
        reg_nids + REG_A1,     // nid of current value of $a1 register
        current_ecall_nid + 4) // nid of (($a2 - 1) / 8) * 8
    + dprintf(output_fd, "%lu ugt 1 %lu 20 ; $a2 > 0\n",
        current_ecall_nid + 6, // nid of this line
        reg_nids + REG_A2)     // nid of current value of $a2 register
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and $a1 otherwise\n",
        current_ecall_nid + 7, // nid of this line
        current_ecall_nid + 6, // nid of $a2 > 0
        current_ecall_nid + 5, // nid of $a1 + (($a2 - 1) / 8) * 8
        reg_nids + REG_A1)  // nid of current value of $a1 register
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; $a1 + (($a2 - 1) / 8) * 8 is end address of write buffer for checking address validity\n",
        current_ecall_nid + 8, // nid of this line
        current_ecall_nid ,    // nid of read ecall is active
        current_ecall_nid + 7, // nid of $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and $a1 otherwise
        access_flow_end_nid);  // nid of address of most recent memory access

  access_flow_end_nid = current_ecall_nid + 8;

  // if read ecall is active record $a1 bounds for checking address validity
  record_end_bounds(record_start_bounds(current_ecall_nid + 9, current_ecall_nid, REG_A1), current_ecall_nid, REG_A1);

  // TODO: check file descriptor validity, return error codes

  // if read ecall is active go into kernel mode
  w = w + dprintf(output_fd, "%lu ite 1 %lu 11 %lu ; go into kernel mode if read ecall is active\n",
    current_ecall_nid + 50, // nid of this line
    current_ecall_nid,      // nid of read ecall is active
    kernel_mode_flow_nid);  // nid of most recent update of kernel-mode flag

  kernel_mode_flow_nid = current_ecall_nid + 50;

  // if read ecall is active set $a0 (number of read bytes) = 0 bytes
  w = w + dprintf(output_fd, "%lu ite 2 %lu 20 %lu ; set $a0 = 0 bytes if read ecall is active\n",
    current_ecall_nid + 51,     // nid of this line
    current_ecall_nid,          // nid of read ecall is active
    *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_ecall_nid + 51;

  w = w
    // determine number of bytes to read in next step
    + dprintf(output_fd, "%lu sub 2 %lu %lu ; $a2 - $a0\n",
        current_ecall_nid + 60, // nid of this line
        reg_nids + REG_A2,      // nid of current value of $a2 register
        reg_nids + REG_A0)      // nid of current value of $a0 register
    + dprintf(output_fd, "%lu ugte 1 %lu 28 ; $a2 - $a0 >= 8 bytes\n",
        current_ecall_nid + 61, // nid of this line
        current_ecall_nid + 60) // nid of $a2 - $a0
    + dprintf(output_fd, "%lu ite 2 %lu 28 %lu ; read 8 bytes if $a2 - $a0 >= 8 bytes, or else $a2 - $a0 bytes\n",
        current_ecall_nid + 62,  // nid of this line
        current_ecall_nid + 61,  // nid of $a2 - $a0 >= 8 bytes
        current_ecall_nid + 60); // nid of $a2 - $a0

  increment_nid = current_ecall_nid + 62;

  w = w
    // compute unsigned-extended input
    + dprintf(output_fd, "%lu eq 1 %lu 22 ; increment == 2\n",
        current_ecall_nid + 70, // nid of this line
        increment_nid)          // nid of increment
    + dprintf(output_fd, "%lu ite 2 %lu 92 91 ; unsigned-extended 2-byte input if increment == 2, or else unsigned-extended 1-byte input\n",
        current_ecall_nid + 71, // nid of this line
        current_ecall_nid + 70) // nid of increment == 2
    + dprintf(output_fd, "%lu eq 1 %lu 23 ; increment == 3\n",
        current_ecall_nid + 72, // nid of this line
        increment_nid)          // nid of increment
    + dprintf(output_fd, "%lu ite 2 %lu 93 %lu ; unsigned-extended 3-byte input if increment == 3\n",
        current_ecall_nid + 73, // nid of this line
        current_ecall_nid + 72, // nid of increment == 3
        current_ecall_nid + 71) // nid of unsigned-extended 2-byte input
    + dprintf(output_fd, "%lu eq 1 %lu 24 ; increment == 4\n",
        current_ecall_nid + 74, // nid of this line
        increment_nid)          // nid of increment
    + dprintf(output_fd, "%lu ite 2 %lu 94 %lu ; unsigned-extended 4-byte input if increment == 4\n",
        current_ecall_nid + 75, // nid of this line
        current_ecall_nid + 74, // nid of increment == 4
        current_ecall_nid + 73) // nid of unsigned-extended 3-byte input
    + dprintf(output_fd, "%lu eq 1 %lu 25 ; increment == 5\n",
        current_ecall_nid + 76, // nid of this line
        increment_nid)          // nid of increment
    + dprintf(output_fd, "%lu ite 2 %lu 95 %lu ; unsigned-extended 5-byte input if increment == 5\n",
        current_ecall_nid + 77, // nid of this line
        current_ecall_nid + 76, // nid of increment == 5
        current_ecall_nid + 75) // nid of unsigned-extended 4-byte input
    + dprintf(output_fd, "%lu eq 1 %lu 26 ; increment == 6\n",
        current_ecall_nid + 78, // nid of this line
        increment_nid)          // nid of increment
    + dprintf(output_fd, "%lu ite 2 %lu 96 %lu ; unsigned-extended 6-byte input if increment == 6\n",
        current_ecall_nid + 79, // nid of this line
        current_ecall_nid + 78, // nid of increment == 6
        current_ecall_nid + 77) // nid of unsigned-extended 5-byte input
    + dprintf(output_fd, "%lu eq 1 %lu 27 ; increment == 7\n",
        current_ecall_nid + 80, // nid of this line
        increment_nid)          // nid of increment
    + dprintf(output_fd, "%lu ite 2 %lu 97 %lu ; unsigned-extended 7-byte input if increment == 7\n",
        current_ecall_nid + 81, // nid of this line
        current_ecall_nid + 80, // nid of increment == 7
        current_ecall_nid + 79) // nid of unsigned-extended 6-byte input
    + dprintf(output_fd, "%lu eq 1 %lu 28 ; increment == 8\n",
        current_ecall_nid + 82, // nid of this line
        increment_nid)          // nid of increment
    + dprintf(output_fd, "%lu ite 2 %lu 98 %lu ; 8-byte input if increment == 8\n",
        current_ecall_nid + 83,  // nid of this line
        current_ecall_nid + 82,  // nid of increment == 8
        current_ecall_nid + 81); // nid of unsigned-extended 7-byte input

  input_nid = current_ecall_nid + 83;

  w = w
    // compute virtual address $a1 + $a0
    + dprintf(output_fd, "%lu add 2 %lu %lu ; $a1 + $a0\n",
        current_ecall_nid + 84, // nid of this line
        reg_nids + REG_A1,      // nid of current value of $a1 register
        reg_nids + REG_A0);     // nid of current value of $a0 register

  // compute physical address $a1 + $a0
  paddr_nid = model_physical_address(current_ecall_nid + 85, current_ecall_nid + 84);

  write_input_nid = paddr_nid + 1;

  w = w
    // write input to memory at physical address $a1 + $a0
    + dprintf(output_fd, "%lu write %lu %lu %lu %lu ; memory[$a1 + $a0] = input\n",
        write_input_nid, // nid of this line
        memory_sort_nid, // nid of physical memory sort
        memory_nid,      // nid of physical memory
        paddr_nid,       // nid of physical address $a1 + $a0
        input_nid);      // nid of input

  read_loop_nid = write_input_nid + 1;

  w = w
    // read ecall is in kernel mode and not done yet
    + dprintf(output_fd, "%lu ult 1 %lu %lu ; $a0 < $a2\n",
        read_loop_nid,     // nid of this line
        reg_nids + REG_A0, // nid of current value of $a0 register
        reg_nids + REG_A2) // nid of current value of $a2 register
    + dprintf(output_fd, "%lu and 1 %lu %lu ; $a7 == SYSCALL_READ and $a0 < $a2\n",
        read_loop_nid + 1, // nid of this line
        current_nid + 11,  // nid of $a7 == SYSCALL_READ
        read_loop_nid)     // nid of $a0 < $a2
    + dprintf(output_fd, "%lu and 1 60 %lu ; read ecall is in kernel mode and not done yet\n",
        read_loop_nid + 2, // nid of this line
        read_loop_nid + 1) // nid of $a7 == SYSCALL_READ and $a0 < $a2

    // if read ecall is in kernel mode and not done yet write input to memory at address $a1 + $a0
    + dprintf(output_fd, "%lu ugt 1 %lu 20 ; increment > 0\n",
        read_loop_nid + 3, // nid of this line
        increment_nid)     // nid of increment
    + dprintf(output_fd, "%lu and 1 %lu %lu ; read ecall is in kernel mode and not done yet and increment > 0\n",
        read_loop_nid + 4, // nid of this line
        read_loop_nid + 2, // nid of read ecall is in kernel mode and not done yet
        read_loop_nid + 3) // nid of increment > 0
    + dprintf(output_fd, "%lu ite %lu %lu %lu %lu ; set memory[$a1 + $a0] = input if read ecall is in kernel mode and not done yet and increment > 0\n",
        read_loop_nid + 5, // nid of this line
        memory_sort_nid,   // nid of physical memory sort
        read_loop_nid + 4, // nid of read ecall is in kernel mode and not done yet and increment > 0
        write_input_nid,   // nid of memory[$a1 + $a0] = input
        memory_flow_nid);  // nid of most recent update of memory

  memory_flow_nid = read_loop_nid + 5;

  w = w
    // if read ecall is in kernel mode and not done yet increment number of bytes read
    + dprintf(output_fd, "%lu add 2 %lu %lu ; $a0 + increment\n",
        read_loop_nid + 6, // nid of this line
        reg_nids + REG_A0, // nid of current value of $a0 register
        increment_nid)     // nid of increment
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; set $a0 = $a0 + increment if read ecall is in kernel mode and not done yet\n",
        read_loop_nid + 7, // nid of this line
        read_loop_nid + 2, // nid of read ecall is in kernel mode and not done yet
        read_loop_nid + 6, // nid of $a0 + increment
        *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = read_loop_nid + 7;

  // if read ecall is in kernel mode and not done yet stay in kernel mode
  w = w + dprintf(output_fd, "%lu ite 1 %lu 11 %lu ; stay in kernel mode if read ecall is in kernel mode and not done yet\n\n",
    read_loop_nid + 8,     // nid of this line
    read_loop_nid + 2,     // nid of read ecall is in kernel mode and not done yet
    kernel_mode_flow_nid); // nid of most recent update of kernel-mode flag

  kernel_mode_flow_nid = read_loop_nid + 8;


  current_ecall_nid = current_nid + pcs_nid / 10 + pcs_nid / 100 * 2;

  w = w
    // write ecall
    + dprintf(output_fd, "%lu and 1 %lu %lu ; write ecall is active\n",
        current_ecall_nid, // nid of this line
        ecall_flow_nid,    // nid of most recent update of ecall activation
        current_nid + 12)  // nid of $a7 == SYSCALL_WRITE

    // if write ecall is active record $a1 register for checking address validity
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; $a1 is start address of read buffer for checking address validity\n",
        current_ecall_nid + 1,  // nid of this line
        current_ecall_nid,      // nid of write ecall is active
        reg_nids + REG_A1,      // nid of current value of $a1 register
        access_flow_start_nid); // nid of address of most recent memory access

  access_flow_start_nid = current_ecall_nid + 1;

  w = w
    // if write ecall is active record $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and
    // $a1 otherwise, as address for checking address validity
    + dprintf(output_fd, "%lu dec 2 %lu ; $a2 - 1\n",
        current_ecall_nid + 2, // nid of this line
        reg_nids + REG_A2)     // nid of current value of $a2 register
    + dprintf(output_fd, "%lu not 2 27 ; not 7\n",
        current_ecall_nid + 3) // nid of this line
    + dprintf(output_fd, "%lu and 2 %lu %lu ; reset 3 LSBs of $a2 - 1\n",
        current_ecall_nid + 4, // nid of this line
        current_ecall_nid + 2, // nid of $a2 - 1
        current_ecall_nid + 3) // nid of not 7
    + dprintf(output_fd, "%lu add 2 %lu %lu ; $a1 + (($a2 - 1) / 8) * 8\n",
        current_ecall_nid + 5, // nid of this line
        reg_nids + REG_A1,     // nid of current value of $a1 register
        current_ecall_nid + 4) // nid of (($a2 - 1) / 8) * 8
    + dprintf(output_fd, "%lu ugt 1 %lu 20 ; $a2 > 0\n",
        current_ecall_nid + 6, // nid of this line
        reg_nids + REG_A2)     // nid of current value of $a2 register
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and $a1 otherwise\n",
        current_ecall_nid + 7, // nid of this line
        current_ecall_nid + 6, // nid of $a2 > 0
        current_ecall_nid + 5, // nid of $a1 + (($a2 - 1) / 8) * 8
        reg_nids + REG_A1)  // nid of current value of $a1 register
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; $a1 + (($a2 - 1) / 8) * 8 is end address of read buffer for checking address validity\n",
        current_ecall_nid + 8, // nid of this line
        current_ecall_nid ,    // nid of write ecall is active
        current_ecall_nid + 7, // nid of $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and $a1 otherwise
        access_flow_end_nid);  // nid of address of most recent memory access

  access_flow_end_nid = current_ecall_nid + 8;

  // if write ecall is active record $a1 bounds for checking address validity
  record_end_bounds(record_start_bounds(current_ecall_nid + 9, current_ecall_nid, REG_A1), current_ecall_nid, REG_A1);

  // TODO: check file descriptor validity, return error codes

  // if write ecall is active set $a0 (written number of bytes) = $a2 (size)
  w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; set $a0 = $a2 if write ecall is active\n\n",
    current_ecall_nid + 50,     // nid of this line
    current_ecall_nid,          // nid of write ecall is active
    reg_nids + REG_A2,          // nid of current value of $a2 register
    *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_ecall_nid + 50;


  current_ecall_nid = current_nid + pcs_nid / 10 + pcs_nid / 100 * 3;

  w = w
    // openat ecall
    + dprintf(output_fd, "%lu and 1 %lu %lu ; openat ecall is active\n",
        current_ecall_nid, // nid of this line
        ecall_flow_nid,    // nid of most recent update of ecall activation
        current_nid + 13)  // nid of $a7 == SYSCALL_OPENAT

    // if openat ecall is active record $a1 register for checking address validity
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; $a1 is start address of filename for checking address validity\n",
        current_ecall_nid + 1,  // nid of this line
        current_ecall_nid,      // nid of openat ecall is active
        reg_nids + REG_A1,      // nid of current value of $a1 register
        access_flow_start_nid); // nid of address of most recent memory access

  access_flow_start_nid = current_ecall_nid + 1;

  // if openat ecall is active record $a1 bounds for checking address validity
  record_start_bounds(current_ecall_nid + 2, current_ecall_nid, REG_A1);

  // TODO: check address validity of whole filename, flags and mode arguments

  w = w
    + dprintf(output_fd, "%lu state 2 fd-bump\n", current_ecall_nid + 50)
    + dprintf(output_fd, "%lu init 2 %lu 21 ; initial fd-bump is 1 (file descriptor bump pointer)\n",
        current_ecall_nid + 51, // nid of this line
        current_ecall_nid + 50) // nid of fd-bump

    // if openat ecall is active set $a0 (file descriptor) = fd-bump + 1 (next file descriptor)
    + dprintf(output_fd, "%lu inc 2 %lu\n",
        current_ecall_nid + 52, // nid of this line
        current_ecall_nid + 50) // nid of fd-bump
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; fd-bump + 1 if openat ecall is active\n",
        current_ecall_nid + 53, // nid of this line
        current_ecall_nid,      // nid of openat ecall is active
        current_ecall_nid + 52, // nid of fd-bump + 1
        current_ecall_nid + 50) // nid of fd-bump
    + dprintf(output_fd, "%lu next 2 %lu %lu ; increment fd-bump if openat ecall is active\n",
        current_ecall_nid + 54, // nid of this line
        current_ecall_nid + 50, // nid of fd-bump
        current_ecall_nid + 53) // nid of fd-bump + 1
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; set $a0 = fd-bump + 1 if openat ecall is active\n\n",
        current_ecall_nid + 55,     // nid of this line
        current_ecall_nid,          // nid of openat ecall is active
        current_ecall_nid + 52,     // nid of fd-bump + 1
        *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_ecall_nid + 55;


  current_ecall_nid = current_nid + pcs_nid / 10 + pcs_nid / 100 * 4;

  // is brk ecall is active?
  w = w + dprintf(output_fd, "%lu and 1 %lu %lu ; brk ecall is active\n",
    current_ecall_nid, // nid of this line
    ecall_flow_nid,    // nid of most recent update of ecall activation
    current_nid + 14); // nid of $a7 == SYSCALL_BRK

  bump_pointer_nid = current_ecall_nid + 50;

  w = w
    + dprintf(output_fd, "%lu state 2 brk ; brk bump pointer\n", bump_pointer_nid)
    + dprintf(output_fd, "%lu init 2 %lu 33 ; current program break\n",
        current_ecall_nid + 51, // nid of this line
        bump_pointer_nid)       // nid of brk bump pointer

    // if brk ecall is active and $a0 is valid set brk = $a0
    // $a0 is valid if brk <= $a0 < $sp and $a0 is word-aligned
    + dprintf(output_fd, "%lu ulte 1 %lu %lu ; brk <= $a0\n",
        current_ecall_nid + 52, // nid of this line
        bump_pointer_nid,       // nid of brk bump pointer
        reg_nids + REG_A0)      // nid of current value of $a0 register
    + dprintf(output_fd, "%lu ult 1 %lu %lu ; $a0 < $sp\n",
        current_ecall_nid + 53, // nid of this line
        reg_nids + REG_A0,      // nid of current value of $a0 register
        reg_nids + REG_SP)      // nid of current value of $sp register
    + dprintf(output_fd, "%lu and 1 %lu %lu ; brk <= $a0 < $sp\n",
        current_ecall_nid + 54, // nid of this line
        current_ecall_nid + 52, // nid of brk <= $a0
        current_ecall_nid + 53) // nid of $a0 < $sp
    + dprintf(output_fd, "%lu and 2 %lu 27 ; reset all but 3 LSBs of $a0\n",
        current_ecall_nid + 55, // nid of this line
        reg_nids + REG_A0)      // nid of current value of $a0 register
    + dprintf(output_fd, "%lu eq 1 %lu 20 ; 3 LSBs of $a0 == 0 ($a0 is word-aligned)\n",
        current_ecall_nid + 56, // nid of this line
        current_ecall_nid + 55) // nid of 3 LSBs of current value of $a0 register
    + dprintf(output_fd, "%lu and 1 %lu %lu ; brk <= $a0 < $sp and $a0 is word-aligned ($a0 is valid)\n",
        current_ecall_nid + 57, // nid of this line
        current_ecall_nid + 54, // nid of brk <= $a0 < $sp
        current_ecall_nid + 56) // nid of $a0 is word-aligned
    + dprintf(output_fd, "%lu and 1 %lu %lu ; brk ecall is active and $a0 is valid\n",
        current_ecall_nid + 58, // nid of this line
        current_ecall_nid + 00, // nid of brk ecall is active
        current_ecall_nid + 57) // nid of $a0 is valid
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; brk = $a0 if brk ecall is active and $a0 is valid\n",
        current_ecall_nid + 59, // nid of this line
        current_ecall_nid + 58, // nid of brk ecall is active and $a0 is valid
        reg_nids + REG_A0,      // nid of current value of $a0 register
        bump_pointer_nid)       // nid of brk bump pointer
    + dprintf(output_fd, "%lu next 2 %lu %lu ; set brk = $a0 if brk ecall is active and $a0 is valid\n",
        current_ecall_nid + 60, // nid of this line
        bump_pointer_nid,       // nid of brk bump pointer
        current_ecall_nid + 59) // nid of preceding line

    // if brk ecall is active and $a0 is invalid set $a0 = brk
    + dprintf(output_fd, "%lu not 1 %lu ; $a0 is invalid\n",
        current_ecall_nid + 61, // nid of this line
        current_ecall_nid + 57) // nid of $a0 is valid
    + dprintf(output_fd, "%lu and 1 %lu %lu ; brk ecall is active and $a0 is invalid\n",
        current_ecall_nid + 62, // nid of this line
        current_ecall_nid + 00, // nid of brk ecall is active
        current_ecall_nid + 61) // nid of $a0 is invalid
    + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; set $a0 = brk if brk ecall is active and $a0 is invalid\n",
        current_ecall_nid + 63,     // nid of this line
        current_ecall_nid + 62,     // nid of brk ecall is active and $a0 is invalid
        bump_pointer_nid,           // nid of brk bump pointer
        *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_ecall_nid + 63;

  if (check_block_access) {
    w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; lower bound on $t1 = brk if brk ecall is active and $a0 is valid\n",
      current_ecall_nid + 64,               // nid of this line
      current_ecall_nid + 58,               // nid of brk ecall is active and $a0 is valid
      bump_pointer_nid,                     // nid of brk bump pointer
      *(reg_flow_nids + LO_FLOW + REG_T1)); // nid of most recent update of lower bound on $t1 register

    *(reg_flow_nids + LO_FLOW + REG_T1) = current_ecall_nid + 64;

    w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; upper bound on $t1 = $a0 if brk ecall is active and $a0 is valid\n",
      current_ecall_nid + 65,               // nid of this line
      current_ecall_nid + 58,               // nid of brk ecall is active and $a0 is valid
      reg_nids + REG_A0,                    // nid of current value of $a0 register
      *(reg_flow_nids + UP_FLOW + REG_T1)); // nid of most recent update of upper bound on $t1 register

    *(reg_flow_nids + UP_FLOW + REG_T1) = current_ecall_nid + 65;

    w = w + dprintf(output_fd, "%lu ite 2 %lu 30 %lu ; lower bound on $t1 = start of data segment if brk ecall is active and $a0 is invalid\n",
      current_ecall_nid + 66,               // nid of this line
      current_ecall_nid + 62,               // nid of brk ecall is active and $a0 is invalid
      *(reg_flow_nids + LO_FLOW + REG_T1)); // nid of most recent update of lower bound on $t1 register

    *(reg_flow_nids + LO_FLOW + REG_T1) = current_ecall_nid + 66;

    w = w + dprintf(output_fd, "%lu ite 2 %lu 50 %lu ; upper bound on $t1 = 4GB of memory addresses if brk ecall is active and $a0 is invalid\n",
      current_ecall_nid + 67,               // nid of this line
      current_ecall_nid + 62,               // nid of brk ecall is active and $a0 is invalid
      *(reg_flow_nids + UP_FLOW + REG_T1)); // nid of most recent update of upper bound on $t1 register

    *(reg_flow_nids + UP_FLOW + REG_T1) = current_ecall_nid + 67;
  }

  w = w + dprintf(output_fd, "\n%lu next 1 60 %lu ; update kernel-mode flag\n",
    current_nid + pcs_nid / 10 + pcs_nid / 100 * 5, // nid of this line
    kernel_mode_flow_nid);                          // nid of most recent update of kernel-mode flag
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
  return nid + pc * 100;
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
        in_edge = smalloc(SIZEOFUINT64STAR + 3 * SIZEOFUINT64);

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
      + dprintf(output_fd, "%lu constd 2 %ld ; 0x%lX << 12\n", current_nid, left_shift(imm, 12), imm)

      // if this instruction is active set $rd = imm << 12
      + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
          current_nid + 1,        // nid of this line
          pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
          current_nid,            // nid of immediate argument left-shifted by 12 bits
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
      w = w + dprintf(output_fd, "%lu constd 2 %ld ; 0x%lX\n", current_nid, imm, imm);

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
  if (rd != REG_ZR)
    if (imm != 0)
      if (rs1 == REG_ZR)
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

      // unsigned-extend $rs1 < $rs2 by 63 bits to 64 bits
      + dprintf(output_fd, "%lu uext 2 %lu 63\n",
          current_nid + 1, // nid of this line
          current_nid)     // nid of $rs1 < $rs2

      // if this instruction is active set $rd = $rs1 < $rs2
      + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
          current_nid + 2,        // nid of this line
          pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
          current_nid + 1,        // nid of unsigned-64-bit-extended $rs1 < $rs2
          *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 2;

    w = w + print_add_sub_mul_divu_remu_sltu() + dprintf(output_fd, "\n");
  }
}

void model_data_flow_load() {
  uint64_t vaddr_nid;
  uint64_t paddr_nid;

  if (rd != REG_ZR) {
    current_nid = record_start_bounds(current_nid, pc_nid(pcs_nid, pc), rs1);

    vaddr_nid = model_virtual_address();
    paddr_nid = model_physical_address(current_nid, vaddr_nid);

    if (paddr_nid != vaddr_nid)
      current_nid = paddr_nid + 1;

    // if this instruction is active record $rs1 + imm for checking address validity
    w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
      current_nid,            // nid of this line
      pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      vaddr_nid,              // nid of virtual address $rs1 + imm
      access_flow_start_nid); // nid of address of most recent memory access

    access_flow_start_nid = current_nid;

    current_nid = current_nid + 1;

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

    w = w
      // read from memory[$rs1 + imm] into $rd register
      + dprintf(output_fd, "%lu read 2 %lu %lu\n",
          current_nid, // nid of this line
          memory_nid,  // nid of physical memory
          paddr_nid)   // nid of physical address $rs1 + imm

      // if this instruction is active set $rd = memory[$rs1 + imm]
      + dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
          current_nid + 1,        // nid of this line
          pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
          current_nid,            // nid of memory[$rs1 + imm]
          *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    w = w + print_load() + dprintf(output_fd, "\n");
  }
}

void model_data_flow_store() {
  uint64_t vaddr_nid;
  uint64_t paddr_nid;

  current_nid = record_start_bounds(current_nid, pc_nid(pcs_nid, pc), rs1);

  vaddr_nid = model_virtual_address();
  paddr_nid = model_physical_address(current_nid, vaddr_nid);

  if (paddr_nid != vaddr_nid)
    current_nid = paddr_nid + 1;

  // if this instruction is active record $rs1 + imm for checking address validity
  w = w + dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
    current_nid,            // nid of this line
    pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
    vaddr_nid,              // nid of virtual address $rs1 + imm
    access_flow_start_nid); // nid of address of most recent memory access

  access_flow_start_nid = current_nid;

  current_nid = current_nid + 1;

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

    // if this instruction is active reset upper bound on $rd register to 4GB of memory addresses
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
      + dprintf(output_fd, "%lu constd 2 %ld ; 0x%lX\n", current_nid, imm, imm)

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
  uint64_t start_nid, uint64_t end_nid, uint64_t offset_nid, uint64_t word_alignment,
  uint64_t flow_nid) {
  w = w
    + dprintf(output_fd, "%lu ugte 1 %lu %lu ; address >= start of segment\n",
      cursor_nid, // nid of this line
      laddr_nid,  // nid of virtual or linear address
      start_nid)  // nid of start of segment
    + dprintf(output_fd, "%lu ult 1 %lu %lu ; address < end of segment\n",
      cursor_nid + 1, // nid of this line
      laddr_nid,      // nid of virtual or linear address
      end_nid)        // nid of end of segment
    + dprintf(output_fd, "%lu and 1 %lu %lu\n",
      cursor_nid + 2, // nid of this line
      cursor_nid,     // nid of >= check
      cursor_nid + 1) // nid of < check
    + dprintf(output_fd, "%lu sub %lu %lu %lu\n",
      cursor_nid + 3,           // nid of this line
      virtual_address_sort_nid, // nid of address sort
      laddr_nid,                // nid of virtual or linear address
      offset_nid)               // nid of segment offset in virtual or linear address space
    + dprintf(output_fd, "%lu slice 6 %lu %lu %lu\n",
      cursor_nid + 4,                                   // nid of this line
      cursor_nid + 3,                                   // nid of mapped virtual or linear address
      physical_address_space_size - 1 + word_alignment, // size of physical address space in bits - 1 + word alignment
      word_alignment)                                   // 3 for virtual address, 0 for linear address
    + dprintf(output_fd, "%lu ite 6 %lu %lu %lu\n",
      cursor_nid + 5, // nid of this line
      cursor_nid + 2, // nid of segment check
      cursor_nid + 4, // nid of physical address
      flow_nid);      // nid of physical address in other segment

  return cursor_nid + 5; // nid of physical address
}

uint64_t model_physical_address(uint64_t cursor_nid, uint64_t vaddr_nid) {
  uint64_t laddr_nid;

  if (linear_address_space) {
    w = w + dprintf(output_fd, "%lu slice 4 %lu 31 3\n",
      cursor_nid, // nid of this line
      vaddr_nid); // nid of virtual address

    laddr_nid  = cursor_nid;
    cursor_nid = cursor_nid + 1;
  } else
    laddr_nid = vaddr_nid;

  if (segment_memory) {
    if (linear_address_space) {
      cursor_nid = model_physical_address_in_segment(cursor_nid, laddr_nid, 40, 41, 40, 0, 8);
      cursor_nid = model_physical_address_in_segment(cursor_nid + 1, laddr_nid, 42, 44, 46, 0, cursor_nid);

      return model_physical_address_in_segment(cursor_nid + 1, laddr_nid, 45, 51, 47, 0, cursor_nid);
    } else {
      cursor_nid = model_physical_address_in_segment(cursor_nid, laddr_nid, 30, 31, 30, 3, 8);
      cursor_nid = model_physical_address_in_segment(cursor_nid + 1, laddr_nid, 32, 34, 36, 3, cursor_nid);

      return model_physical_address_in_segment(cursor_nid + 1, laddr_nid, 35, 50, 37, 3, cursor_nid);
    }
  } else
    return laddr_nid;
}

uint64_t compute_physical_address(uint64_t vaddr) {
  if (segment_memory) {
    if (vaddr >= data_start)
      if (vaddr < data_start + data_size)
        // vaddr in data segment
        vaddr = vaddr - data_start;
      else if (vaddr >= heap_start)
        if (vaddr < heap_start + heap_size)
          // vaddr in heap segment
          vaddr = vaddr - heap_start + data_size;
        else if (vaddr >= stack_start)
          if (vaddr < stack_start + stack_size)
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

    return vaddr / WORDSIZE;
  }

  if (linear_address_space)
    return vaddr / WORDSIZE;
  else
    return vaddr;
}

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

uint64_t is_statically_live_instruction(uint64_t address) {
  if (statically_live_code != (uint64_t*) 0)
    return *(statically_live_code + (address - code_start) / INSTRUCTIONSIZE);
  else
    return 1;
}

void mark_statically_live_instruction(uint64_t address, uint64_t mark) {
  *(statically_live_code + (address - code_start) / INSTRUCTIONSIZE) = mark;
}

uint64_t mark_statically_live_code(uint64_t callee_pc, uint64_t exit_pc, uint64_t mark) {
  uint64_t next_pc;

  pc = callee_pc;

  while (1) {
    if (pc < code_start)
      exit(1);
    else if (pc >= code_start + code_size)
      exit(1);
    else if (pc == exit_pc) {
      // procedure containing exit pc does not return to jal
      exit_procedure_entry = callee_pc;

      return 1;
    }

    if (is_statically_live_instruction(pc) != mark)
      mark_statically_live_instruction(pc, mark);
    else
      // already marked
      return 0;

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
      // assert: only branching forward

      // mark true branch first
      mark_statically_live_code(pc + imm, exit_pc, mark);
    else if (is == JAL) {
      if (rd == REG_RA) {
        // assert: procedure call
        if (pc + imm == exit_procedure_entry)
          // "returning" from exit
          return 1;
        else if (mark_statically_live_code(pc + imm, exit_pc, mark))
          // "returning" from exit
          return 1;
      } else
        // assert: forward jump
        next_pc = pc + imm;
    } else if (is == JALR)
      // assert: return from procedure call
      return 0;
    else if (is == ECALL) {
      if (reg_a7 == SYSCALL_EXIT) {
        reg_a7 = 0;

        // exit wrapper does not return to jal
        exit_procedure_entry = callee_pc;

        return 1;
      }
    }

    pc = next_pc;
  }
}

void static_dead_code_elimination(uint64_t entry_pc, uint64_t exit_pc) {
  uint64_t saved_pc;

  exit_procedure_entry = 0;

  saved_pc = pc;

  if (exit_pc == 0)
    mark_statically_live_code(entry_pc, 0, 1);
  else
    mark_statically_live_code(entry_pc, exit_pc, 0);

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
    + dprintf(output_fd, "%lu state 1 ; kernel-mode pc flag of ecall %lu[0x%lX]",
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

void check_division_by_zero(uint64_t division, uint64_t flow_nid) {
  w = w
    // check if divisor == 0
    + dprintf(output_fd, "%lu eq 1 %lu 20\n",
        current_nid, // nid of this line
        flow_nid)    // nid of divisor of most recent division or remainder
    + dprintf(output_fd, "%lu bad %lu ; ",
        current_nid + 1, // nid of this line
        current_nid);    // nid of divisor == 0
  if (division)
    w = w + dprintf(output_fd, "division by zero\n\n");
  else
    w = w + dprintf(output_fd, "remainder by zero\n\n");

  current_nid = current_nid + 2;
}

void generate_address_alignment_check(uint64_t flow_nid) {
  w = w
    // check if address of most recent memory access is word-aligned
    + dprintf(output_fd, "%lu and 2 %lu 27\n",
        current_nid, // nid of this line
        flow_nid)    // nid of address of most recent memory access
    + dprintf(output_fd, "%lu neq 1 %lu 20\n",
        current_nid + 1, // nid of this line
        current_nid)     // nid of 3 LSBs of address of most recent memory access
    + dprintf(output_fd, "%lu bad %lu ; word-unaligned memory access\n\n",
        current_nid + 2,  // nid of this line
        current_nid + 1); // nid of previous check

  current_nid = current_nid + 3;
}

void generate_segmentation_faults(uint64_t flow_nid) {
  w = w
    + dprintf(output_fd, "%lu ult 1 %lu 30 ; address < start of data segment\n",
        current_nid, // nid of this line
        flow_nid)    // nid of address of most recent memory access
    + dprintf(output_fd, "%lu bad %lu ; memory access below data segment\n",
        current_nid + 1, // nid of this line
        current_nid);    // nid of previous check

  current_nid = current_nid + 2;

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
    + dprintf(output_fd, "%lu bad %lu ; memory access in between data and heap segments\n",
        current_nid + 3,  // nid of this line
        current_nid + 2); // nid of previous check

  current_nid = current_nid + 4;

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
    + dprintf(output_fd, "%lu bad %lu ; memory access in between current heap and stack segments\n",
        current_nid + 3,  // nid of this line
        current_nid + 2); // nid of previous check

  current_nid = current_nid + 4;

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
      + dprintf(output_fd, "%lu bad %lu ; memory access in between allowed and current end of heap segment\n",
          current_nid + 3,  // nid of this line
          current_nid + 2); // nid of previous check

    current_nid = current_nid + 4;
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
      + dprintf(output_fd, "%lu bad %lu ; memory access in between current and allowed start of stack segment\n",
          current_nid + 3,  // nid of this line
          current_nid + 2); // nid of previous check

    current_nid = current_nid + 4;
  }

  w = w
    + dprintf(output_fd, "%lu ugte 1 %lu 50 ; address >= 4GB of memory addresses\n",
        current_nid, // nid of this line
        flow_nid)    // nid of address of most recent memory access
    + dprintf(output_fd, "%lu bad %lu ; memory access above stack segment\n\n",
        current_nid + 1, // nid of this line
        current_nid);    // nid of previous check

  current_nid = current_nid + 2;
}

void generate_block_access_check(uint64_t flow_nid, uint64_t lo_flow_nid, uint64_t up_flow_nid) {
  w = w
    // check if address of most recent memory access < current lower bound
    + dprintf(output_fd, "%lu ult 1 %lu %lu\n",
        current_nid, // nid of this line
        flow_nid,    // nid of address of most recent memory access
        lo_flow_nid) // nid of current lower bound on memory addresses
    + dprintf(output_fd, "%lu bad %lu ; memory access below lower bound\n",
        current_nid + 1, // nid of this line
        current_nid);    // nid of previous check

  current_nid = current_nid + 2;

  w = w
    // check if address of most recent memory access >= current upper bound
    + dprintf(output_fd, "%lu ugte 1 %lu %lu\n",
        current_nid, // nid of this line
        flow_nid,    // nid of address of most recent memory access
        up_flow_nid) // nid of current upper bound on memory addresses
    + dprintf(output_fd, "%lu bad %lu ; memory access at or above upper bound\n\n",
        current_nid + 1, // nid of this line
        current_nid);    // nid of previous check

  current_nid = current_nid + 2;
}

uint64_t number_of_bits(uint64_t n) {
  if (n > 1)
    return log_two(n * 2 - 1);
  else if (n > 0)
    return 1;
  else
    return 0;
}

void modeler(uint64_t entry_pc) {
  uint64_t i;

  uint64_t machine_word;

  uint64_t memory_dump_nid;
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
  if (division_by_zero_check == 0)
    w = w + dprintf(output_fd, "; with %s\n", no_division_by_zero_check_option);
  if (address_validity_check == 0)
    w = w + dprintf(output_fd, "; with %s\n", no_address_validity_check_option);
  if (segmentation_faults == 0)
    w = w + dprintf(output_fd, "; with %s\n", no_segmentation_faults_option);
  if (linear_address_space)
    w = w + dprintf(output_fd, "; with %s\n", linear_address_space_option);
  if (fixed_heap_segment)
    w = w + dprintf(output_fd, "; with %s %lu\n", heap_allowance_option, heap_allowance);
  if (fixed_stack_segment)
    w = w + dprintf(output_fd, "; with %s %lu\n", stack_allowance_option, stack_allowance);
  if (segment_memory)
    w = w + dprintf(output_fd, "; with %s\n", segment_memory_option);
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
    + dprintf(output_fd, "2 sort bitvec 64 ; 64-bit machine word\n");

  if (linear_address_space == 0) {
    w = w + dprintf(output_fd, "3 sort array 2 2 ; 64-bit physical memory\n\n");

    virtual_address_sort_nid  = 2;
    physical_address_sort_nid = 2;
    memory_sort_nid           = 3;
  } else {
    w = w
      + dprintf(output_fd, "4 sort bitvec 29 ; 29-bit linear address\n")
      + dprintf(output_fd, "5 sort array 4 2 ; 29-bit physical memory\n\n");

    virtual_address_sort_nid  = 4;
    physical_address_sort_nid = 4;
    memory_sort_nid           = 5;

    physical_address_space_size = 29;
  }

  // assert: value of stack pointer is 64-bit-word-aligned

  heap_start  = get_heap_seg_start(current_context);
  heap_size   = get_program_break(current_context) - heap_start + heap_allowance;
  stack_start = *(registers + REG_SP) - stack_allowance;
  stack_size  = VIRTUALMEMORYSIZE * GIGABYTE - stack_start;

  if (segment_memory) {
    physical_address_space_size = number_of_bits((data_size + heap_size + stack_size) / WORDSIZE);

    w = w
      + dprintf(output_fd, "6 sort bitvec %lu ; %lu-bit physical address\n",
        physical_address_space_size,
        physical_address_space_size)
      + dprintf(output_fd, "7 sort array 6 2 ; %lu-bit physical memory (%luB)\n",
        physical_address_space_size,
        data_size + heap_size + stack_size)
      + dprintf(output_fd, "8 zero 6\n\n");

    physical_address_sort_nid = 6;
    memory_sort_nid           = 7;
  }

  w = w
    + dprintf(output_fd, "; %luB total memory, %luB data, %luB heap (%luB,%luB), %luB stack (%luB,%luB)\n\n",
        data_size + heap_size + stack_size,
        data_size,
        heap_size,
        heap_size - heap_allowance,
        heap_allowance,
        stack_size,
        stack_size - stack_allowance,
        stack_allowance)

    + dprintf(output_fd, "10 zero 1\n11 one 1\n\n")
    + dprintf(output_fd, "20 zero 2\n21 one 2\n22 constd 2 2\n23 constd 2 3\n24 constd 2 4\n25 constd 2 5\n26 constd 2 6\n27 constd 2 7\n28 constd 2 8\n\n")

    + dprintf(output_fd, "; start of data segment in 64-bit virtual memory\n")
    + dprintf(output_fd, "30 constd 2 %lu ; 0x%lX\n", data_start, data_start)
    + dprintf(output_fd, "; end of data segment in 64-bit virtual memory\n")
    + dprintf(output_fd, "31 constd 2 %lu ; 0x%lX\n\n", data_start + data_size, data_start + data_size)

    + dprintf(output_fd, "; start of heap segment in 64-bit virtual memory (initial program break)\n")
    + dprintf(output_fd, "32 constd 2 %lu ; 0x%lX\n", heap_start, heap_start)
    + dprintf(output_fd, "; current end of heap segment in 64-bit virtual memory (current program break)\n")
    + dprintf(output_fd, "33 constd 2 %lu ; 0x%lX\n\n", get_program_break(current_context), get_program_break(current_context));

  if (fixed_heap_segment)
    w = w
      + dprintf(output_fd, "; allowed end of heap segment in 64-bit virtual memory (with %luB allowance)\n", heap_allowance)
      + dprintf(output_fd, "34 constd 2 %lu ; 0x%lX\n", heap_start + heap_size, heap_start + heap_size)
      + dprintf(output_fd, "; allowed start of stack segment in 64-bit virtual memory (with %luB allowance)\n", stack_allowance)
      + dprintf(output_fd, "35 constd 2 %lu ; 0x%lX\n\n", stack_start, stack_start);

  if (segment_memory)
    w = w
      + dprintf(output_fd, "; offset of heap segment in 64-bit virtual memory\n")
      + dprintf(output_fd, "36 constd 2 %lu ; 0x%lX\n", heap_start - data_size, heap_start - data_size)
      + dprintf(output_fd, "; offset of stack segment in 64-bit virtual memory\n")
      + dprintf(output_fd, "37 constd 2 %lu ; 0x%lX\n\n", stack_start - data_size - heap_size, stack_start - data_size - heap_size);

  if (linear_address_space) {
    w = w
      + dprintf(output_fd, "; start of data segment in 29-bit linear memory\n")
      + dprintf(output_fd, "40 constd 4 %lu ; 0x%lX\n", data_start / WORDSIZE, data_start / WORDSIZE)
      + dprintf(output_fd, "; end of data segment in 29-bit linear memory\n")
      + dprintf(output_fd, "41 constd 4 %lu ; 0x%lX\n\n", (data_start + data_size) / WORDSIZE, (data_start + data_size) / WORDSIZE)

      + dprintf(output_fd, "; start of heap segment in 29-bit linear memory (initial program break)\n")
      + dprintf(output_fd, "42 constd 4 %lu ; 0x%lX\n", heap_start / WORDSIZE, heap_start / WORDSIZE)
      + dprintf(output_fd, "; current end of heap segment in 29-bit linear memory (current program break)\n")
      + dprintf(output_fd, "43 constd 4 %lu ; 0x%lX\n\n", get_program_break(current_context) / WORDSIZE, get_program_break(current_context) / WORDSIZE);

    if (fixed_heap_segment)
      w = w
        + dprintf(output_fd, "; allowed end of heap segment in 29-bit linear memory (with %luB allowance)\n", heap_allowance)
        + dprintf(output_fd, "44 constd 4 %lu ; 0x%lX\n", (heap_start + heap_size) / WORDSIZE, (heap_start + heap_size) / WORDSIZE)
        + dprintf(output_fd, "; allowed start of stack segment in 29-bit linear memory (with %luB allowance)\n", stack_allowance)
        + dprintf(output_fd, "45 constd 4 %lu ; 0x%lX\n\n", stack_start / WORDSIZE, stack_start / WORDSIZE);

    if (segment_memory)
      w = w
        + dprintf(output_fd, "; offset of heap segment in 29-bit linear memory\n")
        + dprintf(output_fd, "46 constd 4 %lu ; 0x%lX\n", (heap_start - data_size) / WORDSIZE, (heap_start - data_size) / WORDSIZE)
        + dprintf(output_fd, "; offset of stack segment in 29-bit linear memory\n")
        + dprintf(output_fd, "47 constd 4 %lu ; 0x%lX\n\n", (stack_start - data_size - heap_size) / WORDSIZE, (stack_start - data_size - heap_size) / WORDSIZE);
  }

  w = w
    + dprintf(output_fd, "; 4GB of virtual memory\n\n")
    + dprintf(output_fd, "50 constd 2 %lu ; 0x%lX end of 32-bit virtual address space\n",
      VIRTUALMEMORYSIZE * GIGABYTE, VIRTUALMEMORYSIZE * GIGABYTE);

  if (linear_address_space)
    w = w
      + dprintf(output_fd, "51 zero 4 ; end of 29-bit linear address space (2^29 in 29-bit arithmetic)\n");

  w = w
    + dprintf(output_fd, "\n; kernel-mode flag\n\n")

    + dprintf(output_fd, "60 state 1 kernel-mode\n")
    + dprintf(output_fd, "61 init 1 60 10 kernel-mode ; initial value is false\n")
    + dprintf(output_fd, "62 not 1 60\n\n")

    + dprintf(output_fd, "; unsigned-extended inputs for byte-wise reading\n\n")

    + dprintf(output_fd, "71 sort bitvec 8 ; 1 byte\n")
    + dprintf(output_fd, "72 sort bitvec 16 ; 2 bytes\n")
    + dprintf(output_fd, "73 sort bitvec 24 ; 3 bytes\n")
    + dprintf(output_fd, "74 sort bitvec 32 ; 4 bytes\n")
    + dprintf(output_fd, "75 sort bitvec 40 ; 5 bytes\n")
    + dprintf(output_fd, "76 sort bitvec 48 ; 6 bytes\n")
    + dprintf(output_fd, "77 sort bitvec 56 ; 7 bytes\n\n")

    + dprintf(output_fd, "81 input 71 ; 1 byte\n")
    + dprintf(output_fd, "82 input 72 ; 2 bytes\n")
    + dprintf(output_fd, "83 input 73 ; 3 bytes\n")
    + dprintf(output_fd, "84 input 74 ; 4 bytes\n")
    + dprintf(output_fd, "85 input 75 ; 5 bytes\n")
    + dprintf(output_fd, "86 input 76 ; 6 bytes\n")
    + dprintf(output_fd, "87 input 77 ; 7 bytes\n\n")

    + dprintf(output_fd, "91 uext 2 81 56 ; 1 byte\n")
    + dprintf(output_fd, "92 uext 2 82 48 ; 2 bytes\n")
    + dprintf(output_fd, "93 uext 2 83 40 ; 3 bytes\n")
    + dprintf(output_fd, "94 uext 2 84 32 ; 4 bytes\n")
    + dprintf(output_fd, "95 uext 2 85 24 ; 5 bytes\n")
    + dprintf(output_fd, "96 uext 2 86 16 ; 6 bytes\n")
    + dprintf(output_fd, "97 uext 2 87 8 ; 7 bytes\n")
    + dprintf(output_fd, "98 input 2 ; 8 bytes\n\n")

    + dprintf(output_fd, "; 32 64-bit general-purpose registers\n");

  w = w + dprintf(output_fd, "\n; non-zero initial register values\n");

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    if (i == 0)
      w = w + dprintf(output_fd, "\n");
    else if (*(registers + i) != 0)
      w = w + dprintf(output_fd, "%lu constd 2 %ld ; 0x%lX for %s\n",
        reg_value_nids + i,    // nid of this line
        *(registers + i),      // initial value with sign
        *(registers + i),      // initial value in hexadecimal as comment
        get_register_name(i)); // register name as comment

    i = i + 1;
  }

  w = w + dprintf(output_fd, "\n; registers\n");

  reg_flow_nids = smalloc(3 * NUMBEROFREGISTERS * SIZEOFUINT64STAR);

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
        w = w + dprintf(output_fd, "\n%lu constd 2 %lu ; 0x%lX 4GB of memory addresses\n",
          *(reg_flow_nids + i),          // nid of this line
          VIRTUALMEMORYSIZE * GIGABYTE,  // 4GB of memory addresses
          VIRTUALMEMORYSIZE * GIGABYTE); // 4GB of memory addresses in hexadecimal
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
      w = w + dprintf(output_fd, "%lu init 2 %lu %lu %s ; initial value is %ld\n",
        reg_init_nids + i,    // nid of this line
        reg_nids + i,         // nid of to-be-initialized register
        reg_value_nids + i,   // nid of initial value
        get_register_name(i), // register name as comment
        *(registers + i));    // initial value with sign

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
        w = w + dprintf(output_fd, "%lu init 2 %lu 50 %s ; initial value is 4GB of memory addresses\n",
          reg_init_nids + i,                         // nid of this line
          reg_nids + i,                              // nid of to-be-initialized register
          get_register_name(i % NUMBEROFREGISTERS)); // register name as comment

      i = i + 1;
    }

  w = w + dprintf(output_fd, "\n; 64-bit program counter encoded in Boolean flags\n\n");

  // 3 more digits to accommodate code, data, heap, and stack with
  // 100*4 lines per 32-bit instruction (pc increments by 4) and
  // 100*8 lines per 64-bit machine word in memory segments
  pcs_nid = ten_to_the_power_of(log_ten(heap_start + heap_size + stack_size) + 3);

  pc = code_start;

  while (pc < code_start + code_size) {
    current_nid = pc_nid(pcs_nid, pc);

    if (is_statically_live_instruction(pc)) {
      // pc flag of current instruction
      w = w + dprintf(output_fd, "%lu state 1 ; 0x%lX\n", current_nid, pc);

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

  current_nid = pc_nid(pcs_nid, pc);

  w = w + dprintf(output_fd, "\n%lu state %lu memory-dump\n", current_nid, memory_sort_nid);

  memory_dump_nid = current_nid;
  data_flow_nid   = current_nid;

  w = w + dprintf(output_fd, "\n; data segment\n\n");

  // assert: data segment is not empty

  while (pc < VIRTUALMEMORYSIZE * GIGABYTE) {
    if (pc == data_start + data_size) {
      pc = get_heap_seg_start(current_context);

      if (pc != get_program_break(current_context))
        w = w + dprintf(output_fd, "\n; heap segment\n\n");
    }

    if (pc == get_program_break(current_context)) {
      // assert: stack pointer < VIRTUALMEMORYSIZE * GIGABYTE
      pc = *(registers + REG_SP);

      w = w + dprintf(output_fd, "\n; stack segment\n\n");
      // assert: stack segment is not empty
    }

    if (current_nid == memory_dump_nid)
      // account for nid offset by 1 of memory-dump state
      current_nid = current_nid + 1;
    else if (pc < *(registers + REG_SP))
      current_nid = pc_nid(pcs_nid, pc);
    else
      current_nid = pc_nid(pcs_nid, get_program_break(current_context) + (pc - *(registers + REG_SP)));

    // address in data, heap, or stack segment
    w = w + dprintf(output_fd, "%lu constd %lu %lu ; 0x%lX paddr, 0x%lX vaddr\n",
      current_nid,                  // nid of this line
      physical_address_sort_nid,    // nid of physical address sort
      compute_physical_address(pc), // physical address of current machine word
      compute_physical_address(pc), // physical address of current machine word in hexadecimal as comment
      pc);                          // virtual address of current machine word in hexadecimal as comment

    if (is_virtual_address_mapped(get_pt(current_context), pc))
      machine_word = load_virtual_memory(get_pt(current_context), pc);
    else
      // memory allocated but not yet mapped
      machine_word = 0;

    if (machine_word == 0) {
      // load machine word == 0
      w = w + dprintf(output_fd, "%lu write %lu %lu %lu 20\n",
        current_nid + 1, // nid of this line
        memory_sort_nid, // nid of physical memory sort
        data_flow_nid,   // nid of most recent update of memory
        current_nid);    // nid of address of current machine word

      data_flow_nid = current_nid + 1;
    } else {
      w = w
        // load non-zero machine word, use sign
        + dprintf(output_fd, "%lu constd 2 %ld ; 0x%lX\n",
            current_nid + 1,            // nid of this line
            machine_word, machine_word) // value of machine word at current address
        + dprintf(output_fd, "%lu write %lu %lu %lu %lu\n",
            current_nid + 2,  // nid of this line
            memory_sort_nid,  // nid of physical memory sort
            data_flow_nid,    // nid of most recent update of memory
            current_nid,      // nid of address of current machine word
            current_nid + 1); // nid of value of machine word at current address

      data_flow_nid = current_nid + 2;
    }

    pc = pc + WORDSIZE;
  }

  w = w + dprintf(output_fd, "\n; %lu-bit physical memory\n\n", physical_address_space_size);

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

  if (check_block_access) {
    current_nid = current_nid + 2;

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
      + dprintf(output_fd, "\n%lu state %lu upper-bounds ; for checking address validity\n",
          current_nid,     // nid of this line
          memory_sort_nid) // nid of physical memory sort
      + dprintf(output_fd, "%lu init %lu %lu 50 ; initializing upper bounds to 4GB of memory addresses\n",
          current_nid + 1, // nid of this line
          memory_sort_nid, // nid of physical memory sort
          current_nid);    // nid of upper bounds on addresses in memory

    up_memory_flow_nid = current_nid;
  }

  w = w + dprintf(output_fd, "\n; data flow\n\n");

  code_nid = pcs_nid * 3;

  control_in  = zmalloc(code_size / INSTRUCTIONSIZE * SIZEOFUINT64);
  call_return = zmalloc(code_size / INSTRUCTIONSIZE * SIZEOFUINT64);

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

  model_syscalls();

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

    if (current_nid >= pc_nid(control_nid, pc) + 400) {
      // the instruction at pc is reachable by too many other instructions

      // report the error on the console
      output_fd = 1;

      printf("%s: too many in-edges at instruction address %lu[0x%lX] detected\n", selfie_name, pc, pc);

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

  w = w + dprintf(output_fd, "\n; updating %lu-bit physical memory\n\n", physical_address_space_size);

  current_nid = pcs_nid * 7;

  w = w + dprintf(output_fd, "%lu next %lu %lu %lu physical-memory\n",
    current_nid,      // nid of this line
    memory_sort_nid,  // nid of physical memory sort
    memory_nid,       // nid of physical memory
    memory_flow_nid); // nid of most recent write to memory

  if (check_block_access)
    w = w
      + dprintf(output_fd, "%lu next %lu %lu %lu lower-bounds\n",
        current_nid + 1,    // nid of this line
        memory_sort_nid,    // nid of physical memory sort
        lo_memory_nid,      // nid of lower bounds on addresses in memory
        lo_memory_flow_nid) // nid of most recent write to lower bounds on addresses in memory
      + dprintf(output_fd, "%lu next %lu %lu %lu upper-bounds\n",
        current_nid + 2,     // nid of this line
        memory_sort_nid,     // nid of physical memory sort
        up_memory_nid,       // nid of upper bounds on addresses in memory
        up_memory_flow_nid); // nid of most recent write to upper bounds on addresses in memory

  w = w + dprintf(output_fd, "\n");

  current_nid = pcs_nid * 8;

  if (division_by_zero_check) {
    w = w + dprintf(output_fd, "; checking division and remainder by zero\n\n");

    check_division_by_zero(1, division_flow_nid);
    check_division_by_zero(0, remainder_flow_nid);
  }

  current_nid = pcs_nid * 9;

  if (address_validity_check) {
    w = w
      + dprintf(output_fd, "; checking address validity\n\n")
      + dprintf(output_fd, "; is start address of memory access word-aligned?\n\n");

    generate_address_alignment_check(access_flow_start_nid);

    w = w + dprintf(output_fd, "; is end address of memory access word-aligned?\n\n");

    generate_address_alignment_check(access_flow_end_nid);
  }

  if (segmentation_faults) {
    w = w
      + dprintf(output_fd, "; checking segmentation faults\n\n")
      + dprintf(output_fd, "; is start address of memory access in a valid segment?\n\n");

    generate_segmentation_faults(access_flow_start_nid);

    w = w + dprintf(output_fd, "; is end address of memory access in a valid segment?\n\n");

    generate_segmentation_faults(access_flow_end_nid);
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

  no_syscall_id_check_option       = "--no-syscall-id-check";
  no_division_by_zero_check_option = "--no-division-by-zero-check";
  no_address_validity_check_option = "--no-address-validity-check";
  no_segmentation_faults_option    = "--no-segmentation-faults";

  check_block_access_option   = "--check-block-access";
  constant_propagation_option = "--constant-propagation";
  linear_address_space_option = "--linear-address-space";
  heap_allowance_option       = "--heap-allowance";
  stack_allowance_option      = "--stack-allowance";
  segment_memory_option       = "--segment-memory";

  check_block_access   = 0;
  constant_propagation = 0;
  linear_address_space = 0;
  fixed_heap_segment   = 0;
  fixed_stack_segment  = 0;
  segment_memory       = 0;

  heap_allowance  = 0;
  stack_allowance = 0;

  if (string_compare(argument, "-")) {
    if (number_of_remaining_arguments() > 0) {
      bad_exit_code = atoi(peek_argument(0));

      model_arguments = 0;

      while (model_arguments == 0) {
        if (number_of_remaining_arguments() > 1) {
          if (string_compare(peek_argument(1), no_syscall_id_check_option)) {
            syscall_id_check = 0;

            get_argument();
          } else if (string_compare(peek_argument(1), no_division_by_zero_check_option)) {
            division_by_zero_check = 0;

            get_argument();
          } else if (string_compare(peek_argument(1), no_address_validity_check_option)) {
            address_validity_check = 0;

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
          } else if (string_compare(peek_argument(1), segment_memory_option)) {
            segment_memory = 1;

            fixed_heap_segment  = 1;
            fixed_stack_segment = 1;

            get_argument();
          } else
            model_arguments = 1;
        } else
          model_arguments = 1;
      }

      if (code_size == 0) {
        printf("%s: nothing to model\n", selfie_name);

        return EXITCODE_BADARGUMENTS;
      }

      // use extension ".btor2" in name of SMT-LIB file
      model_name = replace_extension(binary_name, "btor2");

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

      do_switch(current_context, current_context, TIMEROFF);

      entry_pc = get_pc(current_context);

      statically_live_code = zmalloc(code_size / INSTRUCTIONSIZE * SIZEOFUINT64);

      static_dead_code_elimination(entry_pc, 0);

      if (constant_propagation) {
        printf("%s: >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>\n", selfie_name);
        printf("%s: constant propagation with ", selfie_name);

        exit_on_read = 1;

        run = 1;

        mipster(current_context);

        run = 0;

        exit_on_read = 0;

        static_dead_code_elimination(entry_pc, get_pc(current_context));
      } else
        run = 0;

      output_name = model_name;
      output_fd   = model_fd;

      model = 1;

      modeler(get_pc(current_context));

      model = 0;

      output_name = (char*) 0;
      output_fd   = 1;

      printf("%s: %lu characters of model formulae written into %s\n", selfie_name, w, model_name);

      return EXITCODE_NOERROR;
    } else
      return EXITCODE_BADARGUMENTS;
  } else
    return EXITCODE_BADARGUMENTS;
}

// -----------------------------------------------------------------
// ----------------------------- MAIN ------------------------------
// -----------------------------------------------------------------

int main(int argc, char** argv) {
  uint64_t exit_code;

  init_selfie((uint64_t) argc, (uint64_t*) argv);

  init_library();

  init_system();

  exit_code = selfie(1);

  if (exit_code == EXITCODE_MOREARGUMENTS)
    exit_code = selfie_model();

  return exit_selfie(exit_code, " - exit-code [ --check-block-access ] ...");
}