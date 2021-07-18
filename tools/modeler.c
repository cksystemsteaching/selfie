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

void reset_bounds();

void model_lui();

void transfer_bounds();

void model_addi();
void model_add();
void model_sub();
void model_mul();
void model_divu();
void model_remu();
void model_sltu();

uint64_t record_start_bounds(uint64_t offset, uint64_t activation_nid, uint64_t reg);
uint64_t record_end_bounds(uint64_t offset, uint64_t activation_nid, uint64_t reg);
uint64_t compute_address();

void model_load();
void model_store();

void model_beq();
void model_jal();
void model_jalr();
void model_ecall();

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void translate_to_model();

// -----------------------------------------------------------------
// ------------------------ MODEL GENERATOR ------------------------
// -----------------------------------------------------------------

uint64_t control_flow(uint64_t activate_nid, uint64_t control_flow_nid);

void check_division_by_zero(uint64_t division, uint64_t flow_nid);

void check_address_validity(uint64_t start, uint64_t flow_nid, uint64_t lo_flow_nid, uint64_t up_flow_nid);

void modeler();

uint64_t selfie_model();

// ------------------------ GLOBAL CONSTANTS -----------------------

uint64_t EXITCODE_MODELINGERROR = 1;

uint64_t LO_FLOW = 32; // offset of nids of lower bounds on addresses in registers
uint64_t UP_FLOW = 64; // offset of nids of upper bounds on addresses in registers

// ------------------------ GLOBAL VARIABLES -----------------------

char*    model_name = (char*) 0; // name of model file
uint64_t model_fd   = 0;         // file descriptor of open model file

uint64_t check_block_access = 0; // flag for checking memory access validity on malloced block level

uint64_t bad_exit_code = 0; // model for this exit code

uint64_t current_nid = 0; // nid of current line

uint64_t  reg_nids      = 0;             // nids of registers
uint64_t* reg_flow_nids = (uint64_t*) 0; // nids of most recent update of registers

uint64_t reg_a7 = 0; // most recent update of $a7 register in sequential translation flow

uint64_t pcs_nid = 0; // nid of first program counter flag

// per-instruction list of control-flow in-edges
uint64_t* control_in = (uint64_t*) 0;

// per-procedure (target of procedure call jal) address of matching jalr instruction
uint64_t* call_return = (uint64_t*) 0;

uint64_t current_callee = 0; // address of first instruction of current callee

// address of currently farthest forward branch or jump to find matching jalr instruction
uint64_t estimated_return = 0;

uint64_t memory_nid      = 0; // nid of memory
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
  uint64_t kernel_mode_flow_nid;

  dprintf(output_fd, "%lu constd 2 %lu ; SYSCALL_EXIT\n", current_nid, SYSCALL_EXIT);
  dprintf(output_fd, "%lu constd 2 %lu ; SYSCALL_READ\n", (current_nid + 1), SYSCALL_READ);
  dprintf(output_fd, "%lu constd 2 %lu ; SYSCALL_WRITE\n", (current_nid + 2), SYSCALL_WRITE);
  dprintf(output_fd, "%lu constd 2 %lu ; SYSCALL_OPENAT\n", (current_nid + 3), SYSCALL_OPENAT);
  dprintf(output_fd, "%lu constd 2 %lu ; SYSCALL_BRK\n\n", (current_nid + 4), SYSCALL_BRK);

  dprintf(output_fd, "%lu eq 1 %lu %lu ; $a7 == SYSCALL_EXIT\n",
    (current_nid + 10),  // nid of this line
    (reg_nids + REG_A7), // nid of current value of $a7 register
    current_nid);        // nid of SYSCALL_EXIT
  dprintf(output_fd, "%lu eq 1 %lu %lu ; $a7 == SYSCALL_READ\n",
    (current_nid + 11),  // nid of this line
    (reg_nids + REG_A7), // nid of current value of $a7 register
    (current_nid + 1));  // nid of SYSCALL_READ
  dprintf(output_fd, "%lu eq 1 %lu %lu ; $a7 == SYSCALL_WRITE\n",
    (current_nid + 12),  // nid of this line
    (reg_nids + REG_A7), // nid of current value of $a7 register
    (current_nid + 2));  // nid of SYSCALL_WRITE
  dprintf(output_fd, "%lu eq 1 %lu %lu ; $a7 == SYSCALL_OPENAT\n",
    (current_nid + 13),  // nid of this line
    (reg_nids + REG_A7), // nid of current value of $a7 register
    (current_nid + 3));  // nid of SYSCALL_OPENAT
  dprintf(output_fd, "%lu eq 1 %lu %lu ; $a7 == SYSCALL_BRK\n\n",
    (current_nid + 14),  // nid of this line
    (reg_nids + REG_A7), // nid of current value of $a7 register
    (current_nid + 4));  // nid of SYSCALL_BRK

  dprintf(output_fd, "%lu not 1 %lu ; $a7 != SYSCALL_EXIT\n",
    (current_nid + 20),  // nid of this line
    (current_nid + 10)); // nid of $a7 == SYSCALL_EXIT
  dprintf(output_fd, "%lu ite 1 %lu 10 %lu ; ... and $a7 != SYSCALL_READ\n",
    (current_nid + 21),  // nid of this line
    (current_nid + 11),  // nid of $a7 == SYSCALL_READ
    (current_nid + 20)); // nid of preceding line
  dprintf(output_fd, "%lu ite 1 %lu 10 %lu ; ... and $a7 != SYSCALL_WRITE\n",
    (current_nid + 22),  // nid of this line
    (current_nid + 12),  // nid of $a7 == SYSCALL_WRITE
    (current_nid + 21)); // nid of preceding line
  dprintf(output_fd, "%lu ite 1 %lu 10 %lu ; ... and $a7 != SYSCALL_OPENAT\n",
    (current_nid + 23),  // nid of this line
    (current_nid + 13),  // nid of $a7 == SYSCALL_OPENAT
    (current_nid + 22)); // nid of preceding line
  dprintf(output_fd, "%lu ite 1 %lu 10 %lu ; ... and $a7 != SYSCALL_BRK (invalid syscall id in $a7 detected)\n\n",
    (current_nid + 24),  // nid of this line
    (current_nid + 14),  // nid of $a7 == SYSCALL_BRK
    (current_nid + 23)); // nid of preceding line

  // if any ecall is active check if $a7 register contains invalid syscall id
  dprintf(output_fd, "%lu and 1 %lu %lu ; ecall is active for invalid syscall id\n",
    (current_nid + 30),  // nid of this line
    ecall_flow_nid,      // nid of most recent update of ecall activation
    (current_nid + 24)); // nid of invalid syscall id check
  dprintf(output_fd, "%lu bad %lu ; ecall invalid syscall id\n\n",
    (current_nid + 31),  // nid of this line
    (current_nid + 30)); // nid of preceding line


  // if exit ecall is active check if exit code in $a0 register is not 0
  dprintf(output_fd, "%lu and 1 %lu %lu ; exit ecall is active\n",
    (current_nid + 1000), // nid of this line
    ecall_flow_nid,       // nid of most recent update of ecall activation
    (current_nid + 10));  // nid of $a7 == SYSCALL_EXIT
  if (bad_exit_code == 0)
    dprintf(output_fd, "%lu neq 1 %lu 20 ; $a0 != zero exit code\n",
      (current_nid + 1002), // nid of this line
      (reg_nids + REG_A0)); // nid of current value of $a0 register
  else {
    dprintf(output_fd, "%lu constd 2 %ld ; bad exit code\n",
      (current_nid + 1001), // nid of this line
      bad_exit_code);       // value of bad exit code
    dprintf(output_fd, "%lu eq 1 %lu %lu ; $a0 == bad non-zero exit code\n",
      (current_nid + 1002),  // nid of this line
      (reg_nids + REG_A0),   // nid of current value of $a0 register
      (current_nid + 1001)); // nid of value of bad non-zero exit code
  }
  dprintf(output_fd, "%lu and 1 %lu %lu ; exit ecall is active with non-zero exit code\n",
    (current_nid + 1003),  // nid of this line
    (current_nid + 1000),  // nid of exit ecall is active
    (current_nid + 1002)); // nid of non-zero exit code
  dprintf(output_fd, "%lu bad %lu ; non-zero exit code\n",
    (current_nid + 1004),  // nid of this line
    (current_nid + 1003)); // nid of preceding line

  // if exit ecall is active stay in kernel mode indefinitely
  dprintf(output_fd, "%lu ite 1 60 %lu %lu ; stay in kernel mode indefinitely if exit ecall is active\n\n",
    (current_nid + 1050),  // nid of this line
    (current_nid + 10),    // nid of $a7 == SYSCALL_EXIT
    (current_nid + 1000)); // nid of exit ecall is active

  kernel_mode_flow_nid = current_nid + 1050;


  // read ecall
  dprintf(output_fd, "%lu and 1 %lu %lu ; read ecall is active\n",
    (current_nid + 1100), // nid of this line
    ecall_flow_nid,       // nid of most recent update of ecall activation
    (current_nid + 11));  // nid of $a7 == SYSCALL_READ

  // if read ecall is active record $a1 register for checking address validity
  dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; $a1 is start address of write buffer for checking address validity\n",
    (current_nid + 1101),   // nid of this line
    (current_nid + 1100),   // nid of read ecall is active
    (reg_nids + REG_A1),    // nid of current value of $a1 register
    access_flow_start_nid); // nid of address of most recent memory access

  access_flow_start_nid = current_nid + 1101;

  // if read ecall is active record $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and
  // $a1 otherwise, as address for checking address validity
  dprintf(output_fd, "%lu dec 2 %lu ; $a2 - 1\n",
    (current_nid + 1102), // nid of this line
    (reg_nids + REG_A2)); // nid of current value of $a2 register
  dprintf(output_fd, "%lu not 2 27 ; not 7\n",
    (current_nid + 1103)); // nid of this line
  dprintf(output_fd, "%lu and 2 %lu %lu ; reset 3 LSBs of $a2 - 1\n",
    (current_nid + 1104),  // nid of this line
    (current_nid + 1102),  // nid of $a2 - 1
    (current_nid + 1103)); // nid of not 7
  dprintf(output_fd, "%lu add 2 %lu %lu ; $a1 + (($a2 - 1) / 8) * 8\n",
    (current_nid + 1105),  // nid of this line
    (reg_nids + REG_A1),   // nid of current value of $a1 register
    (current_nid + 1104)); // nid of (($a2 - 1) / 8) * 8
  dprintf(output_fd, "%lu ugt 1 %lu 20 ; $a2 > 0\n",
    (current_nid + 1106), // nid of this line
    (reg_nids + REG_A2)); // nid of current value of $a2 register
  dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and $a1 otherwise\n",
    (current_nid + 1107), // nid of this line
    (current_nid + 1106), // nid of $a2 > 0
    (current_nid + 1105), // nid of $a1 + (($a2 - 1) / 8) * 8
    (reg_nids + REG_A1)); // nid of current value of $a1 register
  dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; $a1 + (($a2 - 1) / 8) * 8 is end address of write buffer for checking address validity\n",
    (current_nid + 1108), // nid of this line
    (current_nid + 1100), // nid of read ecall is active
    (current_nid + 1107), // nid of $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and $a1 otherwise
    access_flow_end_nid); // nid of address of most recent memory access

  access_flow_end_nid = current_nid + 1108;

  // if read ecall is active record $a1 bounds for checking address validity
  record_end_bounds(record_start_bounds(1109, current_nid + 1100, REG_A1), current_nid + 1100, REG_A1);

  // TODO: check file descriptor validity, return error codes

  // if read ecall is active go into kernel mode
  dprintf(output_fd, "%lu ite 1 %lu 11 %lu ; go into kernel mode if read ecall is active\n",
    (current_nid + 1150),  // nid of this line
    (current_nid + 1100),  // nid of read ecall is active
    kernel_mode_flow_nid); // nid of most recent update of kernel-mode flag

  kernel_mode_flow_nid = current_nid + 1150;

  // if read ecall is active set $a0 (number of read bytes) = 0 bytes
  dprintf(output_fd, "%lu ite 2 %lu 20 %lu ; set $a0 = 0 bytes if read ecall is active\n",
    (current_nid + 1151),       // nid of this line
    (current_nid + 1100),       // nid of read ecall is active
    *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_nid + 1151;

  // determine number of bytes to read in next step
  dprintf(output_fd, "%lu sub 2 %lu %lu ; $a2 - $a0\n",
    (current_nid + 1160), // nid of this line
    (reg_nids + REG_A2),  // nid of current value of $a2 register
    (reg_nids + REG_A0)); // nid of current value of $a0 register
  dprintf(output_fd, "%lu ugte 1 %lu 28 ; $a2 - $a0 >= 8 bytes\n",
    (current_nid + 1161),  // nid of this line
    (current_nid + 1160)); // nid of $a2 - $a0
  dprintf(output_fd, "%lu ite 2 %lu 28 %lu ; read 8 bytes if $a2 - $a0 >= 8 bytes, or else $a2 - $a0 bytes\n",
    (current_nid + 1162),  // nid of this line
    (current_nid + 1161),  // nid of $a2 - $a0 >= 8 bytes
    (current_nid + 1160)); // nid of $a2 - $a0

  // compute unsigned-extended input
  dprintf(output_fd, "%lu eq 1 %lu 22 ; increment == 2\n",
    (current_nid + 1170),  // nid of this line
    (current_nid + 1162)); // nid of increment
  dprintf(output_fd, "%lu ite 2 %lu 92 91 ; unsigned-extended 2-byte input if increment == 2, or else unsigned-extended 1-byte input\n",
    (current_nid + 1171),  // nid of this line
    (current_nid + 1170)); // nid of increment == 2
  dprintf(output_fd, "%lu eq 1 %lu 23 ; increment == 3\n",
    (current_nid + 1172),  // nid of this line
    (current_nid + 1162)); // nid of increment
  dprintf(output_fd, "%lu ite 2 %lu 93 %lu ; unsigned-extended 3-byte input if increment == 3\n",
    (current_nid + 1173),  // nid of this line
    (current_nid + 1172),  // nid of increment == 3
    (current_nid + 1171)); // nid of unsigned-extended 2-byte input
  dprintf(output_fd, "%lu eq 1 %lu 24 ; increment == 4\n",
    (current_nid + 1174),  // nid of this line
    (current_nid + 1162)); // nid of increment
  dprintf(output_fd, "%lu ite 2 %lu 94 %lu ; unsigned-extended 4-byte input if increment == 4\n",
    (current_nid + 1175),  // nid of this line
    (current_nid + 1174),  // nid of increment == 4
    (current_nid + 1173)); // nid of unsigned-extended 3-byte input
  dprintf(output_fd, "%lu eq 1 %lu 25 ; increment == 5\n",
    (current_nid + 1176),  // nid of this line
    (current_nid + 1162)); // nid of increment
  dprintf(output_fd, "%lu ite 2 %lu 95 %lu ; unsigned-extended 5-byte input if increment == 5\n",
    (current_nid + 1177),  // nid of this line
    (current_nid + 1176),  // nid of increment == 5
    (current_nid + 1175)); // nid of unsigned-extended 4-byte input
  dprintf(output_fd, "%lu eq 1 %lu 26 ; increment == 6\n",
    (current_nid + 1178),  // nid of this line
    (current_nid + 1162)); // nid of increment
  dprintf(output_fd, "%lu ite 2 %lu 96 %lu ; unsigned-extended 6-byte input if increment == 6\n",
    (current_nid + 1179),  // nid of this line
    (current_nid + 1178),  // nid of increment == 6
    (current_nid + 1177)); // nid of unsigned-extended 5-byte input
  dprintf(output_fd, "%lu eq 1 %lu 27 ; increment == 7\n",
    (current_nid + 1180),  // nid of this line
    (current_nid + 1162)); // nid of increment
  dprintf(output_fd, "%lu ite 2 %lu 97 %lu ; unsigned-extended 7-byte input if increment == 7\n",
    (current_nid + 1181),  // nid of this line
    (current_nid + 1180),  // nid of increment == 7
    (current_nid + 1179)); // nid of unsigned-extended 6-byte input
  dprintf(output_fd, "%lu eq 1 %lu 28 ; increment == 8\n",
    (current_nid + 1182),  // nid of this line
    (current_nid + 1162)); // nid of increment
  dprintf(output_fd, "%lu ite 2 %lu 98 %lu ; 8-byte input if increment == 8\n",
    (current_nid + 1183),  // nid of this line
    (current_nid + 1182),  // nid of increment == 8
    (current_nid + 1181)); // nid of unsigned-extended 7-byte input

  // write input to memory at address $a1 + $a0
  dprintf(output_fd, "%lu add 2 %lu %lu ; $a1 + $a0\n",
    (current_nid + 1184), // nid of this line
    (reg_nids + REG_A1),  // nid of current value of $a1 register
    (reg_nids + REG_A0)); // nid of current value of $a0 register
  dprintf(output_fd, "%lu write 3 %lu %lu %lu ; memory[$a1 + $a0] = input\n",
    (current_nid + 1185),  // nid of this line
    memory_nid,            // nid of memory
    (current_nid + 1184),  // nid of $a1 + $a0
    (current_nid + 1183)); // nid of input

  // read ecall is in kernel mode and not done yet
  dprintf(output_fd, "%lu ult 1 %lu %lu ; $a0 < $a2\n",
    (current_nid + 1190), // nid of this line
    (reg_nids + REG_A0),  // nid of current value of $a0 register
    (reg_nids + REG_A2)); // nid of current value of $a2 register
  dprintf(output_fd, "%lu and 1 %lu %lu ; $a7 == SYSCALL_READ and $a0 < $a2\n",
    (current_nid + 1191),  // nid of this line
    (current_nid + 11),    // nid of $a7 == SYSCALL_READ
    (current_nid + 1190)); // nid of $a0 < $a2
  dprintf(output_fd, "%lu and 1 60 %lu ; read ecall is in kernel mode and not done yet\n",
    (current_nid + 1192),  // nid of this line
    (current_nid + 1191)); // nid of $a7 == SYSCALL_READ and $a0 < $a2

  // if read ecall is in kernel mode and not done yet write input to memory at address $a1 + $a0
  dprintf(output_fd, "%lu ugt 1 %lu 20 ; increment > 0\n",
    (current_nid + 1193),  // nid of this line
    (current_nid + 1162)); // nid of increment
  dprintf(output_fd, "%lu and 1 %lu %lu ; read ecall is in kernel mode and not done yet and increment > 0\n",
    (current_nid + 1194),  // nid of this line
    (current_nid + 1192),  // nid of read ecall is in kernel mode and not done yet
    (current_nid + 1193)); // nid of increment > 0
  dprintf(output_fd, "%lu ite 3 %lu %lu %lu ; set memory[$a1 + $a0] = input if read ecall is in kernel mode and not done yet and increment > 0\n",
    (current_nid + 1195), // nid of this line
    (current_nid + 1194), // nid of read ecall is in kernel mode and not done yet and increment > 0
    (current_nid + 1185), // nid of memory[$a1 + $a0] = input
    memory_flow_nid);     // nid of most recent update of memory

  memory_flow_nid = current_nid + 1195;

  // if read ecall is in kernel mode and not done yet increment number of bytes read
  dprintf(output_fd, "%lu add 2 %lu %lu ; $a0 + increment\n",
    (current_nid + 1196),  // nid of this line
    (reg_nids + REG_A0),   // nid of current value of $a0 register
    (current_nid + 1162)); // nid of increment
  dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; set $a0 = $a0 + increment if read ecall is in kernel mode and not done yet\n",
    (current_nid + 1197),       // nid of this line
    (current_nid + 1192),       // nid of read ecall is in kernel mode and not done yet
    (current_nid + 1196),       // nid of $a0 + increment
    *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_nid + 1197;

  // if read ecall is in kernel mode and not done yet stay in kernel mode
  dprintf(output_fd, "%lu ite 1 %lu 11 %lu ; stay in kernel mode if read ecall is in kernel mode and not done yet\n\n",
    (current_nid + 1198),  // nid of this line
    (current_nid + 1192),  // nid of read ecall is in kernel mode and not done yet
    kernel_mode_flow_nid); // nid of most recent update of kernel-mode flag

  kernel_mode_flow_nid = current_nid + 1198;


  // write ecall
  dprintf(output_fd, "%lu and 1 %lu %lu ; write ecall is active\n",
    (current_nid + 1200), // nid of this line
    ecall_flow_nid,       // nid of most recent update of ecall activation
    (current_nid + 12));  // nid of $a7 == SYSCALL_WRITE

  // if write ecall is active record $a1 register for checking address validity
  dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; $a1 is start address of read buffer for checking address validity\n",
    (current_nid + 1201),   // nid of this line
    (current_nid + 1200),   // nid of write ecall is active
    (reg_nids + REG_A1),    // nid of current value of $a1 register
    access_flow_start_nid); // nid of address of most recent memory access

  access_flow_start_nid = current_nid + 1201;

  // if write ecall is active record $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and
  // $a1 otherwise, as address for checking address validity
  dprintf(output_fd, "%lu dec 2 %lu ; $a2 - 1\n",
    (current_nid + 1202), // nid of this line
    (reg_nids + REG_A2)); // nid of current value of $a2 register
  dprintf(output_fd, "%lu not 2 27 ; not 7\n",
    (current_nid + 1203)); // nid of this line
  dprintf(output_fd, "%lu and 2 %lu %lu ; reset 3 LSBs of $a2 - 1\n",
    (current_nid + 1204),  // nid of this line
    (current_nid + 1202),  // nid of $a2 - 1
    (current_nid + 1203)); // nid of not 7
  dprintf(output_fd, "%lu add 2 %lu %lu ; $a1 + (($a2 - 1) / 8) * 8\n",
    (current_nid + 1205),  // nid of this line
    (reg_nids + REG_A1),   // nid of current value of $a1 register
    (current_nid + 1204)); // nid of (($a2 - 1) / 8) * 8
  dprintf(output_fd, "%lu ugt 1 %lu 20 ; $a2 > 0\n",
    (current_nid + 1206), // nid of this line
    (reg_nids + REG_A2)); // nid of current value of $a2 register
  dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and $a1 otherwise\n",
    (current_nid + 1207), // nid of this line
    (current_nid + 1206), // nid of $a2 > 0
    (current_nid + 1205), // nid of $a1 + (($a2 - 1) / 8) * 8
    (reg_nids + REG_A1)); // nid of current value of $a1 register
  dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; $a1 + (($a2 - 1) / 8) * 8 is end address of read buffer for checking address validity\n",
    (current_nid + 1208), // nid of this line
    (current_nid + 1200), // nid of write ecall is active
    (current_nid + 1207), // nid of $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and $a1 otherwise
    access_flow_end_nid); // nid of address of most recent memory access

  access_flow_end_nid = current_nid + 1208;

  // if write ecall is active record $a1 bounds for checking address validity
  record_end_bounds(record_start_bounds(1209, current_nid + 1200, REG_A1), current_nid + 1200, REG_A1);

  // TODO: check file descriptor validity, return error codes

  // if write ecall is active set $a0 (written number of bytes) = $a2 (size)
  dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; set $a0 = $a2 if write ecall is active\n\n",
    (current_nid + 1250),       // nid of this line
    (current_nid + 1200),       // nid of write ecall is active
    (reg_nids + REG_A2),        // nid of current value of $a2 register
    *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_nid + 1250;


  // openat ecall
  dprintf(output_fd, "%lu and 1 %lu %lu ; openat ecall is active\n",
    (current_nid + 1300), // nid of this line
    ecall_flow_nid,       // nid of most recent update of ecall activation
    (current_nid + 13));  // nid of $a7 == SYSCALL_OPENAT

  // if openat ecall is active record $a1 register for checking address validity
  dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; $a1 is start address of filename for checking address validity\n",
    (current_nid + 1301),   // nid of this line
    (current_nid + 1300),   // nid of openat ecall is active
    (reg_nids + REG_A1),    // nid of current value of $a1 register
    access_flow_start_nid); // nid of address of most recent memory access

  access_flow_start_nid = current_nid + 1301;

  // if openat ecall is active record $a1 bounds for checking address validity
  record_start_bounds(1302, current_nid + 1300, REG_A1);

  // TODO: check address validity of whole filename, flags and mode arguments

  dprintf(output_fd, "%lu state 2 fd-bump\n", (current_nid + 1350));
  dprintf(output_fd, "%lu init 2 %lu 21 ; initial fd-bump is 1 (file descriptor bump pointer)\n",
    (current_nid + 1351),  // nid of this line
    (current_nid + 1350)); // nid of fd-bump

  // if openat ecall is active set $a0 (file descriptor) = fd-bump + 1 (next file descriptor)
  dprintf(output_fd, "%lu inc 2 %lu\n",
    (current_nid + 1352),  // nid of this line
    (current_nid + 1350)); // nid of fd-bump
  dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; fd-bump + 1 if openat ecall is active\n",
    (current_nid + 1353),  // nid of this line
    (current_nid + 1300),  // nid of openat ecall is active
    (current_nid + 1352),  // nid of fd-bump + 1
    (current_nid + 1350)); // nid of fd-bump
  dprintf(output_fd, "%lu next 2 %lu %lu ; increment fd-bump if openat ecall is active\n",
    (current_nid + 1354),  // nid of this line
    (current_nid + 1350),  // nid of fd-bump
    (current_nid + 1353)); // nid of fd-bump + 1
  dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; set $a0 = fd-bump + 1 if openat ecall is active\n\n",
    (current_nid + 1355),       // nid of this line
    (current_nid + 1300),       // nid of openat ecall is active
    (current_nid + 1352),       // nid of fd-bump + 1
    *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_nid + 1355;


  // is brk ecall is active?
  dprintf(output_fd, "%lu and 1 %lu %lu ; brk ecall is active\n",
    (current_nid + 1400), // nid of this line
    ecall_flow_nid,       // nid of most recent update of ecall activation
    (current_nid + 14));  // nid of $a7 == SYSCALL_BRK

  dprintf(output_fd, "%lu state 2 brk\n", (current_nid + 1450));
  dprintf(output_fd, "%lu init 2 %lu 31 ; initial program break\n",
    (current_nid + 1451),  // nid of this line
    (current_nid + 1450)); // nid of brk

  // if brk ecall is active and $a0 is valid set brk = $a0
  // $a0 is valid if brk <= $a0 < $sp and $a0 is word-aligned
  dprintf(output_fd, "%lu ulte 1 %lu %lu ; brk <= $a0\n",
    (current_nid + 1452), // nid of this line
    (current_nid + 1450), // nid of brk
    (reg_nids + REG_A0)); // nid of current value of $a0 register
  dprintf(output_fd, "%lu ult 1 %lu %lu ; $a0 < $sp\n",
    (current_nid + 1453), // nid of this line
    (reg_nids + REG_A0),  // nid of current value of $a0 register
    (reg_nids + REG_SP)); // nid of current value of $sp register
  dprintf(output_fd, "%lu and 1 %lu %lu ; brk <= $a0 < $sp\n",
    (current_nid + 1454),  // nid of this line
    (current_nid + 1452),  // nid of brk <= $a0
    (current_nid + 1453)); // nid of $a0 < $sp
  dprintf(output_fd, "%lu and 2 %lu 27 ; reset all but 3 LSBs of $a0\n",
    (current_nid + 1455), // nid of this line
    (reg_nids + REG_A0)); // nid of current value of $a0 register
  dprintf(output_fd, "%lu eq 1 %lu 20 ; 3 LSBs of $a0 == 0 ($a0 is word-aligned)\n",
    (current_nid + 1456),  // nid of this line
    (current_nid + 1455)); // nid of 3 LSBs of current value of $a0 register
  dprintf(output_fd, "%lu and 1 %lu %lu ; brk <= $a0 < $sp and $a0 is word-aligned ($a0 is valid)\n",
    (current_nid + 1457),  // nid of this line
    (current_nid + 1454),  // nid of brk <= $a0 < $sp
    (current_nid + 1456)); // nid of $a0 is word-aligned
  dprintf(output_fd, "%lu and 1 %lu %lu ; brk ecall is active and $a0 is valid\n",
    (current_nid + 1458),  // nid of this line
    (current_nid + 1400),  // nid of brk ecall is active
    (current_nid + 1457)); // nid of $a0 is valid
  dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; brk = $a0 if brk ecall is active and $a0 is valid\n",
    (current_nid + 1459),  // nid of this line
    (current_nid + 1458),  // nid of brk ecall is active and $a0 is valid
    (reg_nids + REG_A0),   // nid of current value of $a0 register
    (current_nid + 1450)); // nid of brk
  dprintf(output_fd, "%lu next 2 %lu %lu ; set brk = $a0 if brk ecall is active and $a0 is valid\n",
    (current_nid + 1460),  // nid of this line
    (current_nid + 1450),  // nid of brk
    (current_nid + 1459)); // nid of preceding line

  // if brk ecall is active and $a0 is invalid set $a0 = brk
  dprintf(output_fd, "%lu not 1 %lu ; $a0 is invalid\n",
    (current_nid + 1461),  // nid of this line
    (current_nid + 1457)); // nid of $a0 is valid
  dprintf(output_fd, "%lu and 1 %lu %lu ; brk ecall is active and $a0 is invalid\n",
    (current_nid + 1462),  // nid of this line
    (current_nid + 1400),  // nid of brk ecall is active
    (current_nid + 1461)); // nid of $a0 is invalid
  dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; set $a0 = brk if brk ecall is active and $a0 is invalid\n",
    (current_nid + 1463),       // nid of this line
    (current_nid + 1462),       // nid of brk ecall is active and $a0 is invalid
    (current_nid + 1450),       // nid of brk
    *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_nid + 1463;

  if (check_block_access) {
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; lower bound on $t1 = brk if brk ecall is active and $a0 is valid\n",
      (current_nid + 1464),                 // nid of this line
      (current_nid + 1458),                 // nid of brk ecall is active and $a0 is valid
      (current_nid + 1450),                 // nid of brk
      *(reg_flow_nids + LO_FLOW + REG_T1)); // nid of most recent update of lower bound on $t1 register

    *(reg_flow_nids + LO_FLOW + REG_T1) = current_nid + 1464;

    dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; upper bound on $t1 = $a0 if brk ecall is active and $a0 is valid\n",
      (current_nid + 1465),                 // nid of this line
      (current_nid + 1458),                 // nid of brk ecall is active and $a0 is valid
      (reg_nids + REG_A0),                  // nid of current value of $a0 register
      *(reg_flow_nids + UP_FLOW + REG_T1)); // nid of most recent update of upper bound on $t1 register

    *(reg_flow_nids + UP_FLOW + REG_T1) = current_nid + 1465;

    dprintf(output_fd, "%lu ite 2 %lu 30 %lu ; lower bound on $t1 = start of data segment if brk ecall is active and $a0 is invalid\n",
      (current_nid + 1466),                 // nid of this line
      (current_nid + 1462),                 // nid of brk ecall is active and $a0 is invalid
      *(reg_flow_nids + LO_FLOW + REG_T1)); // nid of most recent update of lower bound on $t1 register

    *(reg_flow_nids + LO_FLOW + REG_T1) = current_nid + 1466;

    dprintf(output_fd, "%lu ite 2 %lu 50 %lu ; upper bound on $t1 = 4GB of memory addresses if brk ecall is active and $a0 is invalid\n",
      (current_nid + 1467),                 // nid of this line
      (current_nid + 1462),                 // nid of brk ecall is active and $a0 is invalid
      *(reg_flow_nids + UP_FLOW + REG_T1)); // nid of most recent update of upper bound on $t1 register

    *(reg_flow_nids + UP_FLOW + REG_T1) = current_nid + 1467;
  }

  dprintf(output_fd, "\n%lu next 1 60 %lu ; update kernel-mode flag\n",
    (current_nid + 1500),  // nid of this line
    kernel_mode_flow_nid); // nid of most recent update of kernel-mode flag
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

  printf("%s: invalid instruction address 0x%lX detected\n", selfie_name, to_address);

  exit(EXITCODE_MODELINGERROR);
}

void reset_bounds() {
  if (check_block_access) {
    // if this instruction is active reset lower bound on $rd register to start of data segment
    dprintf(output_fd, "%lu ite 2 %lu 30 %lu\n",
      current_nid,                      // nid of this line
      pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
      *(reg_flow_nids + LO_FLOW + rd)); // nid of most recent update of lower bound on $rd register

    *(reg_flow_nids + LO_FLOW + rd) = current_nid;

    current_nid = current_nid + 1;

    // if this instruction is active reset upper bound on $rd register to 4GB of memory addresses
    dprintf(output_fd, "%lu ite 2 %lu 50 %lu\n",
      current_nid,                      // nid of this line
      pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
      *(reg_flow_nids + UP_FLOW + rd)); // nid of most recent update of upper bound on $rd register

    *(reg_flow_nids + UP_FLOW + rd) = current_nid;

    current_nid = current_nid + 1;
  }
}

void model_lui() {
  if (rd != REG_ZR) {
    reset_bounds();

    dprintf(output_fd, "%lu constd 2 %ld ; 0x%lX << 12\n", current_nid, left_shift(imm, 12), imm);

    // if this instruction is active set $rd = imm << 12
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
      current_nid + 1,      // nid of this line
      pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      current_nid,            // nid of immediate argument left-shifted by 12 bits
      *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_lui();println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void transfer_bounds() {
  if (check_block_access) {
    // if this instruction is active set lower bound on $rd = lower bound on $rs1 register
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
      current_nid,                      // nid of this line
      pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
      reg_nids + LO_FLOW + rs1,       // nid of lower bound on $rs1 register
      *(reg_flow_nids + LO_FLOW + rd)); // nid of most recent update of lower bound on $rd register

    *(reg_flow_nids + LO_FLOW + rd) = current_nid;

    current_nid = current_nid + 1;

    // if this instruction is active set upper bound on $rd = upper bound on $rs1 register
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
      current_nid,                      // nid of this line
      pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
      reg_nids + UP_FLOW + rs1,       // nid of upper bound on $rs1 register
      *(reg_flow_nids + UP_FLOW + rd)); // nid of most recent update of upper bound on $rd register

    *(reg_flow_nids + UP_FLOW + rd) = current_nid;

    current_nid = current_nid + 1;
  }
}

void model_addi() {
  uint64_t result_nid;

  if (rd != REG_ZR) {
    transfer_bounds();

    if (imm == 0)
      result_nid = reg_nids + rs1;
    else {
      dprintf(output_fd, "%lu constd 2 %ld ; 0x%lX\n", current_nid, imm, imm);

      if (rs1 == REG_ZR) {
        result_nid = current_nid;

        current_nid = current_nid + 1;

        if (rd == REG_A7)
          // assert: next instruction is ecall
          reg_a7 = imm;
      } else {
        // compute $rs1 + imm
        dprintf(output_fd, "%lu add 2 %lu %lu\n",
          current_nid + 1, // nid of this line
          reg_nids + rs1,  // nid of current value of $rs1 register
          current_nid);      // nid of immediate value

        result_nid = current_nid + 1;

        current_nid = current_nid + 2;
      }
    }

    // if this instruction is active set $rd = $rs1 + imm
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
      current_nid,            // nid of this line
      pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      result_nid,             // nid of $rs1 + ismm
      *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid;

    print_addi();println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_add() {
  if (rd != REG_ZR) {
    if (check_block_access) {
      // lower bound on $rs1 register > lower bound on $rs2 register
      dprintf(output_fd, "%lu ugt 1 %lu %lu\n",
        current_nid,                 // nid of this line
        reg_nids + LO_FLOW + rs1,  // nid of lower bound on $rs1 register
        reg_nids + LO_FLOW + rs2); // nid of lower bound on $rs2 register

      // greater lower bound of $rs1 and $rs2 registers
      dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
        current_nid + 1,           // nid of this line
        current_nid,                 // nid of lower bound on $rs1 > lower bound on $rs2
        reg_nids + LO_FLOW + rs1,  // nid of lower bound on $rs1 register
        reg_nids + LO_FLOW + rs2); // nid of lower bound on $rs2 register

      // if this instruction is active set lower bound on $rd = greater lower bound of $rs1 and $rs2 registers
      dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
        (current_nid + 2),                // nid of this line
        pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
        (current_nid + 1),                // nid of greater lower bound of $rs1 and $rs2 registers
        *(reg_flow_nids + LO_FLOW + rd)); // nid of most recent update of lower bound on $rd register

      *(reg_flow_nids + LO_FLOW + rd) = current_nid + 2;

      current_nid = current_nid + 3;

      // upper bound on $rs1 register < upper bound on $rs2 register
      dprintf(output_fd, "%lu ult 1 %lu %lu\n",
        current_nid,                 // nid of this line
        (reg_nids + UP_FLOW + rs1),  // nid of upper bound on $rs1 register
        (reg_nids + UP_FLOW + rs2)); // nid of upper bound on $rs2 register

      // lesser upper bound of $rs1 and $rs2 registers
      dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
        (current_nid + 1),           // nid of this line
        current_nid,                 // nid of upper bound on $rs1 < upper bound on $rs2
        (reg_nids + UP_FLOW + rs1),  // nid of upper bound on $rs1 register
        (reg_nids + UP_FLOW + rs2)); // nid of upper bound on $rs2 register

      // if this instruction is active set upper bound on $rd = lesser upper bound of $rs1 and $rs2 registers
      dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
        (current_nid + 2),                // nid of this line
        pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
        (current_nid + 1),                // nid of lesser upper bound of $rs1 and $rs2 registers
        *(reg_flow_nids + UP_FLOW + rd)); // nid of most recent update of upper bound on $rd register

      *(reg_flow_nids + UP_FLOW + rd) = current_nid + 2;

      current_nid = current_nid + 3;
    }

    // compute $rs1 + $rs2
    dprintf(output_fd, "%lu add 2 %lu %lu\n",
      current_nid,       // nid of this line
      (reg_nids + rs1),  // nid of current value of $rs1 register
      (reg_nids + rs2)); // nid of current value of $rs2 register

    // if this instruction is active set $rd = $rs1 + $rs2
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
      (current_nid + 1),      // nid of this line
      pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      current_nid,            // nid of $rs1 + $rs2
      *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_add_sub_mul_divu_remu_sltu();println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_sub() {
  if (rd != REG_ZR) {
    // TODO: check if bounds on $rs2 are really initial bounds
    transfer_bounds();

    // compute $rs1 - $rs2
    dprintf(output_fd, "%lu sub 2 %lu %lu\n",
      current_nid,       // nid of this line
      (reg_nids + rs1),  // nid of current value of $rs1 register
      (reg_nids + rs2)); // nid of current value of $rs2 register

    // if this instruction is active set $rd = $rs1 - $rs2
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
      (current_nid + 1),      // nid of this line
      pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      current_nid,            // nid of $rs1 - $rs2
      *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_add_sub_mul_divu_remu_sltu();println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_mul() {
  if (rd != REG_ZR) {
    // TODO: check if bounds on $rs1 and $rs2 are really initial bounds
    reset_bounds();

    // compute $rs1 * $rs2
    dprintf(output_fd, "%lu mul 2 %lu %lu\n",
      current_nid,       // nid of this line
      (reg_nids + rs1),  // nid of current value of $rs1 register
      (reg_nids + rs2)); // nid of current value of $rs2 register

    // if this instruction is active set $rd = $rs1 * $rs2
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
      (current_nid + 1),      // nid of this line
      pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      current_nid,            // nid of $rs1 * $rs2
      *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_add_sub_mul_divu_remu_sltu();println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_divu() {
  if (rd != REG_ZR) {
    // TODO: check if bounds on $rs1 and $rs2 are really initial bounds
    reset_bounds();

    // if this instruction is active record $rs2 for checking if $rs2 == 0
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; record %s for checking division by zero\n",
      current_nid,         // nid of this line
      pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
      (reg_nids + rs2),    // nid of current value of $rs2 register
      division_flow_nid,   // nid of divisor of most recent division
      get_register_name(rs2));     // register name

    division_flow_nid = current_nid;

    current_nid = current_nid + 1;

    // compute $rs1 / $rs2
    dprintf(output_fd, "%lu udiv 2 %lu %lu\n",
      current_nid,       // nid of this line
      (reg_nids + rs1),  // nid of current value of $rs1 register
      (reg_nids + rs2)); // nid of current value of $rs2 register

    // if this instruction is active set $rd = $rs1 / $rs2
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
      (current_nid + 1),      // nid of this line
      pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      current_nid,            // nid of $rs1 / $rs2
      *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_add_sub_mul_divu_remu_sltu();println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_remu() {
  if (rd != REG_ZR) {
    // TODO: check if bounds on $rs1 and $rs2 are really initial bounds
    reset_bounds();

    // if this instruction is active record $rs2 for checking if $rs2 == 0
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; record %s for checking remainder by zero\n",
      current_nid,         // nid of this line
      pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
      (reg_nids + rs2),    // nid of current value of $rs2 register
      remainder_flow_nid,  // nid of divisor of most recent remainder
      get_register_name(rs2));     // register name

    remainder_flow_nid = current_nid;

    current_nid = current_nid + 1;

    // compute $rs1 % $rs2
    dprintf(output_fd, "%lu urem 2 %lu %lu\n",
      current_nid,       // nid of this line
      (reg_nids + rs1),  // nid of current value of $rs1 register
      (reg_nids + rs2)); // nid of current value of $rs2 register

    // if this instruction is active set $rd = $rs1 % $rs2
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
      (current_nid + 1),      // nid of this line
      pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      current_nid,            // nid of $rs1 % $rs2
      *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_add_sub_mul_divu_remu_sltu();println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_sltu() {
  if (rd != REG_ZR) {
    reset_bounds();

    // compute $rs1 < $rs2
    dprintf(output_fd, "%lu ult 1 %lu %lu\n",
      current_nid,       // nid of this line
      reg_nids + rs1,  // nid of current value of $rs1 register
      reg_nids + rs2); // nid of current value of $rs2 register

    // unsigned-extend $rs1 < $rs2 by 63 bits to 64 bits
    dprintf(output_fd, "%lu uext 2 %lu 63\n",
      current_nid + 1, // nid of this line
      current_nid);      // nid of $rs1 < $rs2

    // if this instruction is active set $rd = $rs1 < $rs2
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
      current_nid + 2,      // nid of this line
      pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      current_nid + 1,      // nid of unsigned-64-bit-extended $rs1 < $rs2
      *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 2;

    print_add_sub_mul_divu_remu_sltu();println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

uint64_t record_start_bounds(uint64_t offset, uint64_t activation_nid, uint64_t reg) {
  if (check_block_access) {
    // if current instruction is active record lower bound on $reg register for checking address validity
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
      current_nid + offset,     // nid of this line
      activation_nid,             // nid of activation condition of current instruction
      reg_nids + LO_FLOW + reg, // nid of current lower bound on $reg register
      lo_flow_start_nid);         // nid of most recent update of lower bound on memory access

    lo_flow_start_nid = current_nid + offset;

    offset = offset + 1;

    // if current instruction is active record upper bound on $reg register for checking address validity
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
      current_nid + offset,     // nid of this line
      activation_nid,             // nid of activation condition of current instruction
      reg_nids + UP_FLOW + reg, // nid of current upper bound on $reg register
      up_flow_start_nid);         // nid of most recent update of upper bound on memory access

    up_flow_start_nid = current_nid + offset;

    return offset + 1;
  } else
    return offset;
}

uint64_t record_end_bounds(uint64_t offset, uint64_t activation_nid, uint64_t reg) {
  if (check_block_access) {
    // if current instruction is active record lower bound on $reg register for checking address validity
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
      current_nid + offset,     // nid of this line
      activation_nid,             // nid of activation condition of current instruction
      reg_nids + LO_FLOW + reg, // nid of current lower bound on $reg register
      lo_flow_end_nid);           // nid of most recent update of lower bound on memory access

    lo_flow_end_nid = current_nid + offset;

    offset = offset + 1;

    // if current instruction is active record upper bound on $reg register for checking address validity
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
      current_nid + offset,     // nid of this line
      activation_nid,             // nid of activation condition of current instruction
      reg_nids + UP_FLOW + reg, // nid of current upper bound on $reg register
      up_flow_end_nid);           // nid of most recent update of upper bound on memory access

    up_flow_end_nid = current_nid + offset;

    return offset + 1;
  } else
    return offset;
}

uint64_t compute_address() {
  if (imm == 0)
    return reg_nids + rs1; // nid of current value of $rs1 register
  else {
    dprintf(output_fd, "%lu constd 2 %ld ; 0x%lX\n", current_nid, imm, imm);

    // compute $rs1 + imm
    dprintf(output_fd, "%lu add 2 %lu %lu\n",
      (current_nid + 1), // nid of this line
      (reg_nids + rs1),  // nid of current value of $rs1 register
      current_nid);      // nid of immediate value

    current_nid = current_nid + 2;

    return current_nid - 1; // nid of $rs1 + imm
  }
}

void model_load() {
  uint64_t address_nid;

  if (rd != REG_ZR) {
    current_nid = current_nid + record_start_bounds(0, pc_nid(pcs_nid, pc), rs1);

    address_nid = compute_address();

    // if this instruction is active record $rs1 + imm for checking address validity
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
      current_nid,            // nid of this line
      pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      address_nid,            // nid of $rs1 + imm
      access_flow_start_nid); // nid of address of most recent memory access

    access_flow_start_nid = current_nid;

    current_nid = current_nid + 1;

    if (check_block_access) {
      // read from lower-bounds memory[$rs1 + imm] into lower bound on $rd register
      dprintf(output_fd, "%lu read 2 %lu %lu\n",
        current_nid,   // nid of this line
        lo_memory_nid, // nid of lower bounds on addresses in memory
        address_nid);  // nid of $rs1 + imm

      // if this instruction is active set lower bound on $rd = lower-bounds memory[$rs1 + imm]
      dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
        current_nid + 1,                // nid of this line
        pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
        current_nid,                      // nid of lower-bounds memory[$rs1 + imm]
        *(reg_flow_nids + LO_FLOW + rd)); // nid of most recent update of lower bound on $rd register

      *(reg_flow_nids + LO_FLOW + rd) = current_nid + 1;

      current_nid = current_nid + 2;

      // read from upper-bounds memory[$rs1 + imm] into upper bound on $rd register
      dprintf(output_fd, "%lu read 2 %lu %lu\n",
        current_nid,   // nid of this line
        up_memory_nid, // nid of upper bounds on addresses in memory
        address_nid);  // nid of $rs1 + imm

      // if this instruction is active set upper bound on $rd = upper-bounds memory[$rs1 + imm]
      dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
        current_nid + 1,                // nid of this line
        pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
        current_nid,                      // nid of upper-bounds memory[$rs1 + imm]
        *(reg_flow_nids + UP_FLOW + rd)); // nid of most recent update of upper bound on $rd register

      *(reg_flow_nids + UP_FLOW + rd) = current_nid + 1;

      current_nid = current_nid + 2;
    }

    // read from memory[$rs1 + imm] into $rd register
    dprintf(output_fd, "%lu read 2 %lu %lu\n",
      current_nid,  // nid of this line
      memory_nid,   // nid of memory
      address_nid); // nid of $rs1 + imm

    // if this instruction is active set $rd = memory[$rs1 + imm]
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
      (current_nid + 1),      // nid of this line
      pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      current_nid,            // nid of memory[$rs1 + imm]
      *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_load();println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_store() {
  uint64_t address_nid;

  current_nid = current_nid + record_start_bounds(0, pc_nid(pcs_nid, pc), rs1);

  address_nid = compute_address();

  // if this instruction is active record $rs1 + imm for checking address validity
  dprintf(output_fd, "%lu ite 2 %lu %lu %lu\n",
    current_nid,            // nid of this line
    pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
    address_nid,            // nid of $rs1 + imm
    access_flow_start_nid); // nid of address of most recent memory access

  access_flow_start_nid = current_nid;

  current_nid = current_nid + 1;

  if (check_block_access) {
    // write lower bound on $rs2 register to lower-bounds memory[$rs1 + imm]
    dprintf(output_fd, "%lu write 3 %lu %lu %lu\n",
      current_nid,                 // nid of this line
      lo_memory_nid,               // nid of lower bounds on addresses in memory
      address_nid,                 // nid of $rs1 + imm
      reg_nids + LO_FLOW + rs2); // nid of lower bound on $rs2 register

    // if this instruction is active set lower-bounds memory[$rs1 + imm] = lower bound on $rs2
    dprintf(output_fd, "%lu ite 3 %lu %lu %lu\n",
      current_nid + 1,   // nid of this line
      pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
      current_nid,         // nid of lower-bounds memory[$rs1 + imm]
      lo_memory_flow_nid); // nid of most recent update of lower-bounds memory

    lo_memory_flow_nid = current_nid + 1;

    current_nid = current_nid + 2;

    // write upper bound on $rs2 register to upper-bounds memory[$rs1 + imm]
    dprintf(output_fd, "%lu write 3 %lu %lu %lu\n",
      current_nid,                 // nid of this line
      up_memory_nid,               // nid of upper bounds on addresses in memory
      address_nid,                 // nid of $rs1 + imm
      (reg_nids + UP_FLOW + rs2)); // nid of upper bound on $rs2 register

    // if this instruction is active set upper-bounds memory[$rs1 + imm] = upper bound on $rs2
    dprintf(output_fd, "%lu ite 3 %lu %lu %lu\n",
      current_nid + 1,   // nid of this line
      pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
      current_nid,         // nid of upper-bounds memory[$rs1 + imm]
      up_memory_flow_nid); // nid of most recent update of upper-bounds memory

    up_memory_flow_nid = current_nid + 1;

    current_nid = current_nid + 2;
  }

  // write $rs2 register to memory[$rs1 + imm]
  dprintf(output_fd, "%lu write 3 %lu %lu %lu\n",
    current_nid,       // nid of this line
    memory_nid,        // nid of memory
    address_nid,       // nid of $rs1 + imm
    (reg_nids + rs2)); // nid of current value of $rs2 register

  // if this instruction is active set memory[$rs1 + imm] = $rs2
  dprintf(output_fd, "%lu ite 3 %lu %lu %lu ; ",
    current_nid + 1,   // nid of this line
    pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
    current_nid,         // nid of memory[$rs1 + imm] = $rs2
    memory_flow_nid);    // nid of most recent update of memory

  memory_flow_nid = current_nid + 1;

  print_store();println();

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_beq() {
  // compute if beq condition is true
  dprintf(output_fd, "%lu eq 1 %lu %lu ; ",
    current_nid,       // nid of this line
    reg_nids + rs1,  // nid of current value of $rs1 register
    reg_nids + rs2); // nid of current value of $rs2 register

  print_beq();println();

  // true branch
  go_to_instruction(is, REG_ZR, pc, pc + imm, current_nid);

  // compute if beq condition is false
  dprintf(output_fd, "%lu not 1 %lu\n",
    current_nid + 1, // nid of this line
    current_nid);    // nid of preceding line

  // false branch
  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, current_nid + 1);
}

void model_jal() {
  if (rd != REG_ZR) {
    // address of next instruction used here and in returning jalr instruction
    dprintf(output_fd, "%lu constd 2 %lu ; 0x%lX\n",
      current_nid,             // nid of this line
      pc + INSTRUCTIONSIZE,  // address of next instruction
      pc + INSTRUCTIONSIZE); // address of next instruction

    // if this instruction is active link $rd register to address of next instruction
    dprintf(output_fd, "%lu ite 2 %lu %lu %lu ; ",
      current_nid + 1,      // nid of this line
      pc_nid(pcs_nid, pc),    // nid of pc flag of this jal instruction
      current_nid,            // nid of address of next instruction
      *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_jal();println();

    // link next instruction to returning jalr instruction via instruction at address pc + imm
    go_to_instruction(JALR, REG_ZR, pc + imm, pc + INSTRUCTIONSIZE, current_nid);
  }

  // jump from this instruction to instruction at address pc + imm
  go_to_instruction(is, rd, pc, pc + imm, 0);
}

void model_jalr() {
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

  printf("%s: unsupported jalr at address 0x%lX with estimated address 0x%lX detected\n", selfie_name, pc, estimated_return);

  exit(EXITCODE_MODELINGERROR);
}

void model_ecall() {
  if (reg_a7 == SYSCALL_EXIT) {
    // assert: exit ecall is immediately followed by first procedure in code
    current_callee = pc + INSTRUCTIONSIZE;

    estimated_return = current_callee;
  }

  reg_a7 = 0;

  // keep track of whether any ecall is active
  dprintf(output_fd, "%lu ite 1 %lu 11 %lu ; ",
    current_nid,         // nid of this line
    pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
    ecall_flow_nid);     // nid of most recent update of ecall activation

  ecall_flow_nid = current_nid;

  print_ecall();println();

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

// -----------------------------------------------------------------
// -------------------------- INTERPRETER --------------------------
// -----------------------------------------------------------------

void translate_to_model() {
  // assert: 1 <= is <= number of RISC-U instructions
  if (is == ADDI)
    model_addi();
  else if (is == LOAD)
    model_load();
  else if (is == STORE)
    model_store();
  else if (is == ADD)
    model_add();
  else if (is == SUB)
    model_sub();
  else if (is == MUL)
    model_mul();
  else if (is == DIVU)
    model_divu();
  else if (is == REMU)
    model_remu();
  else if (is == SLTU)
    model_sltu();
  else if (is == BEQ)
    model_beq();
  else if (is == JAL)
    model_jal();
  else if (is == JALR)
    model_jalr();
  else if (is == LUI)
    model_lui();
  else if (is == ECALL)
    model_ecall();
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
    dprintf(output_fd, "%lu ite 1 %lu 11 %lu\n",
      current_nid,       // nid of this line
      activate_nid,      // nid of pc flag of instruction proceeding here
      control_flow_nid); // nid of previously processed in-edge

    current_nid = current_nid + 1;

    return current_nid - 1;
  }
}

void check_division_by_zero(uint64_t division, uint64_t flow_nid) {
  // check if divisor == 0
  dprintf(output_fd, "%lu eq 1 %lu 20\n",
    current_nid, // nid of this line
    flow_nid);   // nid of divisor of most recent division or remainder
  dprintf(output_fd, "%lu bad %lu ; ",
    current_nid + 1, // nid of this line
    current_nid);      // nid of divisor == 0
  if (division)
    dprintf(output_fd, "division by zero\n\n");
  else
    dprintf(output_fd, "remainder by zero\n\n");

  current_nid = current_nid + 2;
}

void check_address_validity(uint64_t start, uint64_t flow_nid, uint64_t lo_flow_nid, uint64_t up_flow_nid) {
  if (start)
    dprintf(output_fd, "; at start of memory block\n\n");
  else
    dprintf(output_fd, "; at end of memory block\n\n");

  // check if address of most recent memory access < current lower bound
  dprintf(output_fd, "%lu ult 1 %lu %lu\n",
    current_nid,  // nid of this line
    flow_nid,     // nid of address of most recent memory access
    lo_flow_nid); // nid of current lower bound on memory addresses
  dprintf(output_fd, "%lu bad %lu ; memory access below lower bound\n",
    current_nid + 1, // nid of this line
    current_nid);      // nid of previous check

  current_nid = current_nid + 2;

  // check if address of most recent memory access >= current upper bound
  dprintf(output_fd, "%lu ugte 1 %lu %lu\n",
    current_nid,  // nid of this line
    flow_nid,     // nid of address of most recent memory access
    up_flow_nid); // nid of current upper bound on memory addresses
  dprintf(output_fd, "%lu bad %lu ; memory access at or above upper bound\n",
    current_nid + 1, // nid of this line
    current_nid);      // nid of previous check

  current_nid = current_nid + 2;

  // check if address of most recent memory access is word-aligned
  dprintf(output_fd, "%lu and 2 %lu 27\n",
    current_nid, // nid of this line
    flow_nid);   // nid of address of most recent memory access
  dprintf(output_fd, "%lu neq 1 %lu 20\n",
    current_nid + 1, // nid of this line
    current_nid);      // nid of 3 LSBs of address of most recent memory access
  dprintf(output_fd, "%lu bad %lu ; word-unaligned memory access\n\n",
    current_nid + 2,  // nid of this line
    current_nid + 1); // nid of previous check

  current_nid = current_nid + 3;
}

void modeler() {
  uint64_t i;

  uint64_t machine_word;

  uint64_t loader_nid;
  uint64_t code_nid;
  uint64_t control_nid;
  uint64_t condition_nid;

  uint64_t data_flow_nid;
  uint64_t control_flow_nid;

  uint64_t* in_edge;

  uint64_t from_instruction;
  uint64_t from_address;
  uint64_t jalr_address;

  dprintf(output_fd, "; %s\n\n", SELFIE_URL);

  dprintf(output_fd, "; BTOR2 %s generated by %s for\n", model_name, selfie_name);
  dprintf(output_fd, "; RISC-V code obtained from %s and\n; invoked as", binary_name);

  i = 0;

  while (i < number_of_remaining_arguments()) {
    dprintf(output_fd, " %s", (char*) *(remaining_arguments() + i));

    i = i + 1;
  }

  dprintf(output_fd, "\n\n1 sort bitvec 1 ; Boolean\n");
  dprintf(output_fd, "2 sort bitvec 64 ; 64-bit machine word\n");
  dprintf(output_fd, "3 sort array 2 2 ; 64-bit memory\n\n");

  dprintf(output_fd, "10 zero 1\n11 one 1\n\n");

  dprintf(output_fd, "20 zero 2\n21 one 2\n22 constd 2 2\n23 constd 2 3\n24 constd 2 4\n25 constd 2 5\n26 constd 2 6\n27 constd 2 7\n28 constd 2 8\n\n");

  dprintf(output_fd, "; word-aligned end of code segment in memory\n\n");

  // start of data segment for checking address validity
  dprintf(output_fd, "30 constd 2 %lu ; 0x%lX\n\n", data_start, data_start);

  dprintf(output_fd, "; word-aligned end of data segment in memory (initial program break)\n\n");

  // initial program break
  dprintf(output_fd, "31 constd 2 %lu ; 0x%lX\n\n", get_program_break(current_context), get_program_break(current_context));

  dprintf(output_fd, "; word-aligned initial $sp (stack pointer) value from boot loader\n\n");

  // value in register $sp from boot loader
  dprintf(output_fd, "40 constd 2 %lu ; 0x%lX\n\n", *(registers + REG_SP), *(registers + REG_SP));

  dprintf(output_fd, "; 4GB of memory\n\n");

  dprintf(output_fd, "50 constd 2 %lu ; 0x%lX\n\n", (VIRTUALMEMORYSIZE * GIGABYTE), (VIRTUALMEMORYSIZE * GIGABYTE));

  dprintf(output_fd, "; kernel-mode flag\n\n");

  dprintf(output_fd, "60 state 1 kernel-mode\n");
  dprintf(output_fd, "61 init 1 60 10 kernel-mode ; initial value is false\n");
  dprintf(output_fd, "62 not 1 60\n\n");

  dprintf(output_fd, "; unsigned-extended inputs for byte-wise reading\n\n");

  dprintf(output_fd, "71 sort bitvec 8 ; 1 byte\n");
  dprintf(output_fd, "72 sort bitvec 16 ; 2 bytes\n");
  dprintf(output_fd, "73 sort bitvec 24 ; 3 bytes\n");
  dprintf(output_fd, "74 sort bitvec 32 ; 4 bytes\n");
  dprintf(output_fd, "75 sort bitvec 40 ; 5 bytes\n");
  dprintf(output_fd, "76 sort bitvec 48 ; 6 bytes\n");
  dprintf(output_fd, "77 sort bitvec 56 ; 7 bytes\n\n");

  dprintf(output_fd, "81 input 71 ; 1 byte\n");
  dprintf(output_fd, "82 input 72 ; 2 bytes\n");
  dprintf(output_fd, "83 input 73 ; 3 bytes\n");
  dprintf(output_fd, "84 input 74 ; 4 bytes\n");
  dprintf(output_fd, "85 input 75 ; 5 bytes\n");
  dprintf(output_fd, "86 input 76 ; 6 bytes\n");
  dprintf(output_fd, "87 input 77 ; 7 bytes\n\n");

  dprintf(output_fd, "91 uext 2 81 56 ; 1 byte\n");
  dprintf(output_fd, "92 uext 2 82 48 ; 2 bytes\n");
  dprintf(output_fd, "93 uext 2 83 40 ; 3 bytes\n");
  dprintf(output_fd, "94 uext 2 84 32 ; 4 bytes\n");
  dprintf(output_fd, "95 uext 2 85 24 ; 5 bytes\n");
  dprintf(output_fd, "96 uext 2 86 16 ; 6 bytes\n");
  dprintf(output_fd, "97 uext 2 87 8 ; 7 bytes\n");
  dprintf(output_fd, "98 input 2 ; 8 bytes\n\n");

  dprintf(output_fd, "; 32 64-bit general-purpose registers\n");

  reg_nids = 100;

  reg_flow_nids = smalloc(3 * NUMBEROFREGISTERS * SIZEOFUINT64STAR);

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    *(reg_flow_nids + i) = reg_nids + i;

    if (i == 0)
      dprintf(output_fd, "\n%lu zero 2 %s ; register $0 is always 0\n",
        *(reg_flow_nids + i), // nid of this line
        get_register_name(i));        // register name
    else
      dprintf(output_fd, "%lu state 2 %s ; register $%lu\n",
        *(reg_flow_nids + i), // nid of this line
        get_register_name(i),         // register name
        i);                   // register index as comment

    i = i + 1;
  }

  if (check_block_access)
    while (i < 3 * NUMBEROFREGISTERS) {
      *(reg_flow_nids + i) = reg_nids + i;

      if (i == LO_FLOW)
        dprintf(output_fd, "\n%lu constd 2 %lu ; 0x%lX\n",
          *(reg_flow_nids + i),      // nid of this line
          code_start + code_size,  // end of code segment
          code_start + code_size); // end of code segment
      else if (i == UP_FLOW)
        dprintf(output_fd, "\n%lu constd 2 %lu ; 0x%lX\n",
          *(reg_flow_nids + i), // nid of this line
          VIRTUALMEMORYSIZE * GIGABYTE,  // 4GB of memory addresses
          VIRTUALMEMORYSIZE * GIGABYTE); // 4GB of memory addresses
      else {
        dprintf(output_fd, "%lu state 2 ", *(reg_flow_nids + i));

        if (i < LO_FLOW + NUMBEROFREGISTERS)
          dprintf(output_fd, "lo-%s ; lower bound on $%lu\n",
            get_register_name(i % NUMBEROFREGISTERS), // register name
            i % NUMBEROFREGISTERS);         // register index as comment
        else if (i < UP_FLOW + NUMBEROFREGISTERS)
          dprintf(output_fd, "up-%s ; upper bound on $%lu\n",
            get_register_name(i % NUMBEROFREGISTERS), // register name
            i % NUMBEROFREGISTERS);         // register index as comment
      }

      i = i + 1;
    }

  dprintf(output_fd, "\n; initializing registers\n");

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    if (i == 0)
      println();
    else if (i == REG_SP)
      dprintf(output_fd, "%lu init 2 %lu 40 %s ; initial value from boot loader\n",
        (reg_nids * 2 + i), // nid of this line
        (reg_nids + i),     // nid of $sp register
        get_register_name(i));      // register name as comment
    else
      // ignoring non-zero value in register $a6 from initial context switch
      dprintf(output_fd, "%lu init 2 %lu 20 %s ; initial value is 0\n",
        (reg_nids * 2 + i), // nid of this line
        (reg_nids + i),     // nid of to-be-initialized register
        get_register_name(i));      // register name as comment

    i = i + 1;
  }

  if (check_block_access)
    while (i < 3 * NUMBEROFREGISTERS) {
      if (i % NUMBEROFREGISTERS == 0)
        println();
      else if (i < LO_FLOW + NUMBEROFREGISTERS)
        dprintf(output_fd, "%lu init 2 %lu 30 %s ; initial value is start of data segment\n",
          reg_nids * 2 + i,                // nid of this line
          reg_nids + i,                    // nid of to-be-initialized register
          get_register_name(i % NUMBEROFREGISTERS)); // register name as comment
      else if (i < UP_FLOW + NUMBEROFREGISTERS)
        dprintf(output_fd, "%lu init 2 %lu 50 %s ; initial value is 4GB of memory addresses\n",
          reg_nids * 2 + i,                // nid of this line
          reg_nids + i,                    // nid of to-be-initialized register
          get_register_name(i % NUMBEROFREGISTERS)); // register name as comment

      i = i + 1;
    }

  dprintf(output_fd, "\n; 64-bit program counter encoded in Boolean flags\n\n");

  // 3 more digits to accommodate code, data, and stack with
  // 100*4 lines per 32-bit instruction (pc increments by 4) and
  // 100*8 lines per 64-bit machine word in data segment
  pcs_nid = ten_to_the_power_of(
    log_ten(data_start + data_size +
      (VIRTUALMEMORYSIZE * GIGABYTE - *(registers + REG_SP))) + 3);

  while (pc < code_start + code_size) {
    current_nid = pc_nid(pcs_nid, pc);

    // pc flag of current instruction
    dprintf(output_fd, "%lu state 1\n", current_nid);

    if (pc == e_entry)
      // set pc here by initializing pc flag of instruction at address 0 to true
      dprintf(output_fd, "%lu init 1 %lu 11 ; initial program counter\n",
        current_nid + 1, // nid of this line
        current_nid);    // nid of pc flag of current instruction
    else
      // initialize all other pc flags to false
      dprintf(output_fd, "%lu init 1 %lu 10\n",
        current_nid + 1, // nid of this line
        current_nid);    // nid of pc flag of current instruction

    pc = pc + INSTRUCTIONSIZE;
  }

  current_nid = pc_nid(pcs_nid, pc);

  dprintf(output_fd, "\n%lu state 3 boot-loader\n", current_nid);

  loader_nid    = current_nid;
  data_flow_nid = current_nid;
  current_nid   = current_nid + 1;

  dprintf(output_fd, "\n; data segment\n\n");

  // assert: pc == code_start + code_size

  while (pc < VIRTUALMEMORYSIZE * GIGABYTE) {
    if (pc == data_start + data_size) {
      // assert: stack pointer < VIRTUALMEMORYSIZE * GIGABYTE
      pc = *(registers + REG_SP);

      dprintf(output_fd, "\n; stack\n\n");
    }

    // address in data segment or stack
    dprintf(output_fd, "%lu constd 2 %lu ; 0x%lX\n",
      current_nid,     // nid of this line
      pc, pc); // address of current machine word

    machine_word = load_virtual_memory(pt, pc);

    if (machine_word == 0) {
      // load machine word == 0
      dprintf(output_fd, "%lu write 3 %lu %lu 20\n",
        (current_nid + 1), // nid of this line
        data_flow_nid,     // nid of most recent update to data segment
        current_nid);      // nid of address of current machine word

      data_flow_nid = current_nid + 1;
    } else {
      // load non-zero machine word, use sign
      dprintf(output_fd, "%lu constd 2 %ld ; 0x%lX\n",
        current_nid + 1,                   // nid of this line
        machine_word, machine_word); // value of machine word at current address
      dprintf(output_fd, "%lu write 3 %lu %lu %lu\n",
        current_nid + 2,  // nid of this line
        data_flow_nid,      // nid of most recent update to data segment
        current_nid,        // nid of address of current machine word
        current_nid + 1); // nid of value of machine word at current address

      data_flow_nid = current_nid + 2;
    }

    pc = pc + WORDSIZE;

    if (current_nid == loader_nid + 1)
      current_nid = loader_nid + WORDSIZE;
    else
      current_nid = current_nid + WORDSIZE;
  }

  dprintf(output_fd, "\n; 64-bit memory\n\n");

  memory_nid = pcs_nid * 2;

  current_nid = memory_nid;

  dprintf(output_fd, "%lu state 3 memory ; data segment, heap, stack\n", current_nid);
  dprintf(output_fd, "%lu init 3 %lu %lu ; loading data segment and stack into memory\n",
    current_nid + 1, // nid of this line
    current_nid,       // nid of memory
    data_flow_nid);    // nid of most recent update to data segment

  memory_flow_nid = current_nid;

  if (check_block_access) {
    current_nid = current_nid + 2;

    lo_memory_nid = current_nid;

    dprintf(output_fd, "\n%lu state 3 lower-bounds ; for checking address validity\n", current_nid);
    dprintf(output_fd, "%lu init 3 %lu 30 ; initializing lower bounds to start of data segment\n",
      current_nid + 1, // nid of this line
      current_nid);      // nid of lower bounds on addresses in memory

    lo_memory_flow_nid = current_nid;

    current_nid = current_nid + 2;

    up_memory_nid = current_nid;

    dprintf(output_fd, "\n%lu state 3 upper-bounds ; for checking address validity\n", current_nid);
    dprintf(output_fd, "%lu init 3 %lu 50 ; initializing upper bounds to 4GB of memory addresses\n",
      current_nid + 1, // nid of this line
      current_nid);      // nid of upper bounds on addresses in memory

    up_memory_flow_nid = current_nid;
  }

  dprintf(output_fd, "\n; data flow\n\n");

  code_nid = pcs_nid * 3;

  control_in  = zmalloc(code_size / INSTRUCTIONSIZE * SIZEOFUINT64);
  call_return = zmalloc(code_size / INSTRUCTIONSIZE * SIZEOFUINT64);

  current_callee   = code_start;
  estimated_return = code_start;

  pc = get_pc(current_context);

  while (pc < code_start + code_size) {
    current_nid = pc_nid(code_nid, pc);

    fetch();
    decode();

    translate_to_model();

    pc = pc + INSTRUCTIONSIZE;
  }

  dprintf(output_fd, "\n; syscalls\n\n");

  current_nid = pcs_nid * 4;

  model_syscalls();

  dprintf(output_fd, "\n; control flow\n\n");

  control_nid = pcs_nid * 5;

  pc = get_pc(current_context);

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
        // is beq active and its condition true or false?
        dprintf(output_fd, "%lu and 1 %lu %lu ; beq %lu[0x%lX]",
          current_nid,                         // nid of this line
          pc_nid(pcs_nid, from_address),       // nid of pc flag of instruction proceeding here
          condition_nid,                       // nid of true or false beq condition
          from_address, from_address); // address of instruction proceeding here
        print_code_line_number_for_instruction(from_address, code_start);println();

        current_nid = current_nid + 1;

        // activate this instruction if beq is active and its condition is true (false)
        control_flow_nid = control_flow(current_nid - 1, control_flow_nid);
      } else if (from_instruction == JALR) {
        jalr_address = *(call_return + (from_address - code_start) / INSTRUCTIONSIZE);

        if (jalr_address != 0) {
          // is value of $ra register with LSB reset equal to address of this instruction?
          dprintf(output_fd, "%lu not 2 21 ; jalr %lu[0x%lX]",
            current_nid,                         // nid of this line
            jalr_address, jalr_address); // address of instruction proceeding here
          print_code_line_number_for_instruction(jalr_address, code_start);println();
          dprintf(output_fd, "%lu and 2 %lu %lu\n",
            current_nid + 1,   // nid of this line
            reg_nids + REG_RA, // nid of current value of $ra register
            current_nid);        // nid of not 1
          dprintf(output_fd, "%lu eq 1 %lu %lu\n",
            current_nid + 2, // nid of this line
            current_nid + 1, // nid of current value of $ra register with LSB reset
            condition_nid);    // nid of address of this instruction (generated by jal)

          // is jalr active and the previous condition true or false?
          dprintf(output_fd, "%lu and 1 %lu %lu\n",
            current_nid + 3,             // nid of this line
            pc_nid(pcs_nid, jalr_address), // nid of pc flag of instruction proceeding here
            current_nid + 2);            // nid of return address condition

          current_nid = current_nid + 4;

          // activate this instruction if jalr is active and its condition is true (false)
          control_flow_nid = control_flow(current_nid - 1, control_flow_nid);
        } else {
          // no jalr returning from jal found

          dprintf(output_fd, "; exit ecall wrapper call or runaway jal %lu[0x%lX]", from_address, from_address);
          print_code_line_number_for_instruction(from_address, code_start);println();

          // this instruction may stay deactivated if there is no more in-edges
        }
      } else if (from_instruction == ECALL) {
        dprintf(output_fd, "%lu state 1 ; kernel-mode pc flag of ecall %lu[0x%lX]",
          current_nid,                         // nid of this line
          from_address, from_address); // address of instruction proceeding here
        print_code_line_number_for_instruction(from_address, code_start);println();

        dprintf(output_fd, "%lu init 1 %lu 10 ; ecall is initially inactive\n",
          current_nid + 1, // nid of this line
          current_nid);      // nid of kernel-mode pc flag of ecall

        dprintf(output_fd, "%lu ite 1 %lu 60 %lu ; activate ecall and keep active while in kernel mode\n",
          current_nid + 2,              // nid of this line
          current_nid,                    // nid of kernel-mode pc flag of ecall
          pc_nid(pcs_nid, from_address)); // nid of pc flag of instruction proceeding here

        dprintf(output_fd, "%lu next 1 %lu %lu ; keep ecall active while in kernel mode\n",
          current_nid + 3,  // nid of this line
          current_nid,        // nid of kernel-mode pc flag of ecall
          current_nid + 2); // nid of previous line

        dprintf(output_fd, "%lu and 1 %lu 62 ; ecall is active but not in kernel mode anymore\n",
          current_nid + 4, // nid of this line
          current_nid);      // nid of kernel-mode pc flag of ecall

        current_nid = current_nid + 5;

        // activate this instruction if ecall is active but not in kernel mode anymore
        control_flow_nid = control_flow(current_nid - 1, control_flow_nid);
      } else {
        if (from_instruction == JAL) dprintf(output_fd, "; jal "); else dprintf(output_fd, "; ");
        dprintf(output_fd, "%lu[0x%lX]", from_address, from_address);
        print_code_line_number_for_instruction(from_address, code_start);println();

        // activate this instruction if instruction proceeding here is active
        control_flow_nid = control_flow(pc_nid(pcs_nid, from_address), control_flow_nid);
      }

      in_edge = (uint64_t*) *in_edge;
    }

    // update pc flag of current instruction
    dprintf(output_fd, "%lu next 1 %lu %lu ; ->%lu[0x%lX]",
      current_nid,         // nid of this line
      pc_nid(pcs_nid, pc), // nid of pc flag of current instruction
      control_flow_nid,    // nid of most recently processed in-edge
      pc, pc);     // address of current instruction
    print_code_line_number_for_instruction(pc, code_start);
    if (control_flow_nid == 10)
      if (pc > code_start)
        // TODO: warn here about unreachable code
        dprintf(output_fd, " (unreachable)");
    println();

    if (current_nid >= pc_nid(control_nid, pc) + 400) {
      // the instruction at pc is reachable by too many other instructions

      //report the error on the console
      output_fd = 1;

      printf("%s: too many in-edges at instruction address 0x%lX detected\n", selfie_name, pc);

      exit(EXITCODE_MODELINGERROR);
    }

    pc = pc + INSTRUCTIONSIZE;
  }

  dprintf(output_fd, "\n; updating registers\n");

  current_nid = pcs_nid * 6;

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    if (i == 0)
      println();
    else
      dprintf(output_fd, "%lu next 2 %lu %lu %s ; register $%lu\n",
        current_nid + i,    // nid of this line
        reg_nids + i,       // nid of register
        *(reg_flow_nids + i), // nid of most recent update to register
        get_register_name(i),         // register name
        i);                   // register index as comment

    i = i + 1;
  }

  if (check_block_access)
    while (i < 3 * NUMBEROFREGISTERS) {
      if (i % NUMBEROFREGISTERS == 0)
        println();
      else {
        dprintf(output_fd, "%lu next 2 %lu %lu ",
          (current_nid + i),     // nid of this line
          (reg_nids + i),        // nid of register
          *(reg_flow_nids + i)); // nid of most recent update to register

        if (i < LO_FLOW + NUMBEROFREGISTERS)
          dprintf(output_fd, "lo-%s ; lower bound on $%lu\n",
            get_register_name(i % NUMBEROFREGISTERS), // register name
            i % NUMBEROFREGISTERS);         // register index as comment
        else if (i < UP_FLOW + NUMBEROFREGISTERS)
          dprintf(output_fd, "up-%s ; upper bound on $%lu\n",
            get_register_name(i % NUMBEROFREGISTERS), // register name
            i % NUMBEROFREGISTERS);         // register index as comment
      }

      i = i + 1;
    }

  dprintf(output_fd, "\n; updating memory\n\n");

  current_nid = pcs_nid * 7;

  dprintf(output_fd, "%lu next 3 %lu %lu memory\n",
      current_nid,      // nid of this line
      memory_nid,       // nid of memory
      memory_flow_nid); // nid of most recent write to memory

  if (check_block_access) {
    dprintf(output_fd, "%lu next 3 %lu %lu lower-bounds\n",
        current_nid + 1,   // nid of this line
        lo_memory_nid,       // nid of lower bounds on addresses in memory
        lo_memory_flow_nid); // nid of most recent write to lower bounds on addresses in memory
    dprintf(output_fd, "%lu next 3 %lu %lu upper-bounds\n",
        current_nid + 2,   // nid of this line
        up_memory_nid,       // nid of upper bounds on addresses in memory
        up_memory_flow_nid); // nid of most recent write to upper bounds on addresses in memory
  }

  dprintf(output_fd, "\n; checking division and remainder by zero\n\n");

  current_nid = pcs_nid * 8;

  check_division_by_zero(1, division_flow_nid);
  check_division_by_zero(0, remainder_flow_nid);

  dprintf(output_fd, "; checking address validity\n\n");

  current_nid = pcs_nid * 9;

  check_address_validity(1, access_flow_start_nid, lo_flow_start_nid, up_flow_start_nid);
  check_address_validity(0, access_flow_end_nid, lo_flow_end_nid, up_flow_end_nid);

  // TODO: check segmentation

  // TODO: check validity of return addresses in jalr

  dprintf(output_fd, "; end of BTOR2 %s\n", model_name);
}

uint64_t selfie_model() {
  if (string_compare(argument, "-")) {
    if (number_of_remaining_arguments() > 0) {
      bad_exit_code = atoi(peek_argument(0));

      check_block_access = 0;

      if (number_of_remaining_arguments() > 1)
        if (string_compare(peek_argument(1), "--check-block-access")) {
          check_block_access = 1;

          get_argument();
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
      reset_microkernel();

      init_memory(1);

      current_context = create_context(MY_CONTEXT, 0);

      // assert: number_of_remaining_arguments() > 0

      boot_loader(current_context);

      run = 0;

      do_switch(current_context, current_context, TIMEROFF);

      output_name = model_name;
      output_fd   = model_fd;

      model = 1;

      modeler();

      model = 0;

      output_name = (char*) 0;
      output_fd   = 1;

      printf("%s: %lu characters of model formulae written into %s\n", selfie_name,
        number_of_written_characters,
        model_name);

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