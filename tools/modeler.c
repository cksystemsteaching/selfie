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

void model_ld();
void model_sd();

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
// 30 is nid of end of code segment which must be a valid address (thus also checked)
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

  printf2("%u constd 2 %u ; SYSCALL_EXIT\n", (char*) current_nid, (char*) SYSCALL_EXIT);
  printf2("%u constd 2 %u ; SYSCALL_READ\n", (char*) (current_nid + 1), (char*) SYSCALL_READ);
  printf2("%u constd 2 %u ; SYSCALL_WRITE\n", (char*) (current_nid + 2), (char*) SYSCALL_WRITE);
  printf2("%u constd 2 %u ; SYSCALL_OPENAT\n", (char*) (current_nid + 3), (char*) SYSCALL_OPENAT);
  printf2("%u constd 2 %u ; SYSCALL_BRK\n\n", (char*) (current_nid + 4), (char*) SYSCALL_BRK);

  printf3("%u eq 1 %u %u ; $a7 == SYSCALL_EXIT\n",
    (char*) (current_nid + 10),  // nid of this line
    (char*) (reg_nids + REG_A7), // nid of current value of $a7 register
    (char*) current_nid);        // nid of SYSCALL_EXIT
  printf3("%u eq 1 %u %u ; $a7 == SYSCALL_READ\n",
    (char*) (current_nid + 11),  // nid of this line
    (char*) (reg_nids + REG_A7), // nid of current value of $a7 register
    (char*) (current_nid + 1));  // nid of SYSCALL_READ
  printf3("%u eq 1 %u %u ; $a7 == SYSCALL_WRITE\n",
    (char*) (current_nid + 12),  // nid of this line
    (char*) (reg_nids + REG_A7), // nid of current value of $a7 register
    (char*) (current_nid + 2));  // nid of SYSCALL_WRITE
  printf3("%u eq 1 %u %u ; $a7 == SYSCALL_OPENAT\n",
    (char*) (current_nid + 13),  // nid of this line
    (char*) (reg_nids + REG_A7), // nid of current value of $a7 register
    (char*) (current_nid + 3));  // nid of SYSCALL_OPENAT
  printf3("%u eq 1 %u %u ; $a7 == SYSCALL_BRK\n\n",
    (char*) (current_nid + 14),  // nid of this line
    (char*) (reg_nids + REG_A7), // nid of current value of $a7 register
    (char*) (current_nid + 4));  // nid of SYSCALL_BRK

  printf2("%u not 1 %u ; $a7 != SYSCALL_EXIT\n",
    (char*) (current_nid + 20),  // nid of this line
    (char*) (current_nid + 10)); // nid of $a7 == SYSCALL_EXIT
  printf3("%u ite 1 %u 10 %u ; ... and $a7 != SYSCALL_READ\n",
    (char*) (current_nid + 21),  // nid of this line
    (char*) (current_nid + 11),  // nid of $a7 == SYSCALL_READ
    (char*) (current_nid + 20)); // nid of preceding line
  printf3("%u ite 1 %u 10 %u ; ... and $a7 != SYSCALL_WRITE\n",
    (char*) (current_nid + 22),  // nid of this line
    (char*) (current_nid + 12),  // nid of $a7 == SYSCALL_WRITE
    (char*) (current_nid + 21)); // nid of preceding line
  printf3("%u ite 1 %u 10 %u ; ... and $a7 != SYSCALL_OPENAT\n",
    (char*) (current_nid + 23),  // nid of this line
    (char*) (current_nid + 13),  // nid of $a7 == SYSCALL_OPENAT
    (char*) (current_nid + 22)); // nid of preceding line
  printf3("%u ite 1 %u 10 %u ; ... and $a7 != SYSCALL_BRK (invalid syscall id in $a7 detected)\n\n",
    (char*) (current_nid + 24),  // nid of this line
    (char*) (current_nid + 14),  // nid of $a7 == SYSCALL_BRK
    (char*) (current_nid + 23)); // nid of preceding line

  // if any ecall is active check if $a7 register contains invalid syscall id
  printf3("%u and 1 %u %u ; ecall is active for invalid syscall id\n",
    (char*) (current_nid + 30),  // nid of this line
    (char*) ecall_flow_nid,      // nid of most recent update of ecall activation
    (char*) (current_nid + 24)); // nid of invalid syscall id check
  printf2("%u bad %u ; ecall invalid syscall id\n\n",
    (char*) (current_nid + 31),  // nid of this line
    (char*) (current_nid + 30)); // nid of preceding line


  // if exit ecall is active check if exit code in $a0 register is not 0
  printf3("%u and 1 %u %u ; exit ecall is active\n",
    (char*) (current_nid + 1000), // nid of this line
    (char*) ecall_flow_nid,       // nid of most recent update of ecall activation
    (char*) (current_nid + 10));  // nid of $a7 == SYSCALL_EXIT
  if (bad_exit_code == 0)
    printf2("%u neq 1 %u 20 ; $a0 != zero exit code\n",
      (char*) (current_nid + 1002), // nid of this line
      (char*) (reg_nids + REG_A0)); // nid of current value of $a0 register
  else {
    printf2("%u constd 2 %d ; bad exit code\n",
      (char*) (current_nid + 1001), // nid of this line
      (char*) bad_exit_code);       // value of bad exit code
    printf3("%u eq 1 %u %u ; $a0 == bad non-zero exit code\n",
      (char*) (current_nid + 1002),  // nid of this line
      (char*) (reg_nids + REG_A0),   // nid of current value of $a0 register
      (char*) (current_nid + 1001)); // nid of value of bad non-zero exit code
  }
  printf3("%u and 1 %u %u ; exit ecall is active with non-zero exit code\n",
    (char*) (current_nid + 1003),  // nid of this line
    (char*) (current_nid + 1000),  // nid of exit ecall is active
    (char*) (current_nid + 1002)); // nid of non-zero exit code
  printf2("%u bad %u ; non-zero exit code\n",
    (char*) (current_nid + 1004),  // nid of this line
    (char*) (current_nid + 1003)); // nid of preceding line

  // if exit ecall is active stay in kernel mode indefinitely
  printf3("%u ite 1 60 %u %u ; stay in kernel mode indefinitely if exit ecall is active\n\n",
    (char*) (current_nid + 1050),  // nid of this line
    (char*) (current_nid + 10),    // nid of $a7 == SYSCALL_EXIT
    (char*) (current_nid + 1000)); // nid of exit ecall is active

  kernel_mode_flow_nid = current_nid + 1050;


  // read ecall
  printf3("%u and 1 %u %u ; read ecall is active\n",
    (char*) (current_nid + 1100), // nid of this line
    (char*) ecall_flow_nid,       // nid of most recent update of ecall activation
    (char*) (current_nid + 11));  // nid of $a7 == SYSCALL_READ

  // if read ecall is active record $a1 register for checking address validity
  printf4("%u ite 2 %u %u %u ; $a1 is start address of write buffer for checking address validity\n",
    (char*) (current_nid + 1101),   // nid of this line
    (char*) (current_nid + 1100),   // nid of read ecall is active
    (char*) (reg_nids + REG_A1),    // nid of current value of $a1 register
    (char*) access_flow_start_nid); // nid of address of most recent memory access

  access_flow_start_nid = current_nid + 1101;

  // if read ecall is active record $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and
  // $a1 otherwise, as address for checking address validity
  printf2("%u dec 2 %u ; $a2 - 1\n",
    (char*) (current_nid + 1102), // nid of this line
    (char*) (reg_nids + REG_A2)); // nid of current value of $a2 register
  printf1("%u not 2 27 ; not 7\n",
    (char*) (current_nid + 1103)); // nid of this line
  printf3("%u and 2 %u %u ; reset 3 LSBs of $a2 - 1\n",
    (char*) (current_nid + 1104),  // nid of this line
    (char*) (current_nid + 1102),  // nid of $a2 - 1
    (char*) (current_nid + 1103)); // nid of not 7
  printf3("%u add 2 %u %u ; $a1 + (($a2 - 1) / 8) * 8\n",
    (char*) (current_nid + 1105),  // nid of this line
    (char*) (reg_nids + REG_A1),   // nid of current value of $a1 register
    (char*) (current_nid + 1104)); // nid of (($a2 - 1) / 8) * 8
  printf2("%u ugt 1 %u 20 ; $a2 > 0\n",
    (char*) (current_nid + 1106), // nid of this line
    (char*) (reg_nids + REG_A2)); // nid of current value of $a2 register
  printf4("%u ite 2 %u %u %u ; $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and $a1 otherwise\n",
    (char*) (current_nid + 1107), // nid of this line
    (char*) (current_nid + 1106), // nid of $a2 > 0
    (char*) (current_nid + 1105), // nid of $a1 + (($a2 - 1) / 8) * 8
    (char*) (reg_nids + REG_A1)); // nid of current value of $a1 register
  printf4("%u ite 2 %u %u %u ; $a1 + (($a2 - 1) / 8) * 8 is end address of write buffer for checking address validity\n",
    (char*) (current_nid + 1108), // nid of this line
    (char*) (current_nid + 1100), // nid of read ecall is active
    (char*) (current_nid + 1107), // nid of $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and $a1 otherwise
    (char*) access_flow_end_nid); // nid of address of most recent memory access

  access_flow_end_nid = current_nid + 1108;

  // if read ecall is active record $a1 bounds for checking address validity
  record_end_bounds(record_start_bounds(1109, current_nid + 1100, REG_A1), current_nid + 1100, REG_A1);

  // TODO: check file descriptor validity, return error codes

  // if read ecall is active go into kernel mode
  printf3("%u ite 1 %u 11 %u ; go into kernel mode if read ecall is active\n",
    (char*) (current_nid + 1150),  // nid of this line
    (char*) (current_nid + 1100),  // nid of read ecall is active
    (char*) kernel_mode_flow_nid); // nid of most recent update of kernel-mode flag

  kernel_mode_flow_nid = current_nid + 1150;

  // if read ecall is active set $a0 (number of read bytes) = 0 bytes
  printf3("%u ite 2 %u 20 %u ; set $a0 = 0 bytes if read ecall is active\n",
    (char*) (current_nid + 1151),       // nid of this line
    (char*) (current_nid + 1100),       // nid of read ecall is active
    (char*) *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_nid + 1151;

  // determine number of bytes to read in next step
  printf3("%u sub 2 %u %u ; $a2 - $a0\n",
    (char*) (current_nid + 1160), // nid of this line
    (char*) (reg_nids + REG_A2),  // nid of current value of $a2 register
    (char*) (reg_nids + REG_A0)); // nid of current value of $a0 register
  printf2("%u ugte 1 %u 28 ; $a2 - $a0 >= 8 bytes\n",
    (char*) (current_nid + 1161),  // nid of this line
    (char*) (current_nid + 1160)); // nid of $a2 - $a0
  printf3("%u ite 2 %u 28 %u ; read 8 bytes if $a2 - $a0 >= 8 bytes, or else $a2 - $a0 bytes\n",
    (char*) (current_nid + 1162),  // nid of this line
    (char*) (current_nid + 1161),  // nid of $a2 - $a0 >= 8 bytes
    (char*) (current_nid + 1160)); // nid of $a2 - $a0

  // compute unsigned-extended input
  printf2("%u eq 1 %u 22 ; increment == 2\n",
    (char*) (current_nid + 1170),  // nid of this line
    (char*) (current_nid + 1162)); // nid of increment
  printf2("%u ite 2 %u 92 91 ; unsigned-extended 2-byte input if increment == 2, or else unsigned-extended 1-byte input\n",
    (char*) (current_nid + 1171),  // nid of this line
    (char*) (current_nid + 1170)); // nid of increment == 2
  printf2("%u eq 1 %u 23 ; increment == 3\n",
    (char*) (current_nid + 1172),  // nid of this line
    (char*) (current_nid + 1162)); // nid of increment
  printf3("%u ite 2 %u 93 %u ; unsigned-extended 3-byte input if increment == 3\n",
    (char*) (current_nid + 1173),  // nid of this line
    (char*) (current_nid + 1172),  // nid of increment == 3
    (char*) (current_nid + 1171)); // nid of unsigned-extended 2-byte input
  printf2("%u eq 1 %u 24 ; increment == 4\n",
    (char*) (current_nid + 1174),  // nid of this line
    (char*) (current_nid + 1162)); // nid of increment
  printf3("%u ite 2 %u 94 %u ; unsigned-extended 4-byte input if increment == 4\n",
    (char*) (current_nid + 1175),  // nid of this line
    (char*) (current_nid + 1174),  // nid of increment == 4
    (char*) (current_nid + 1173)); // nid of unsigned-extended 3-byte input
  printf2("%u eq 1 %u 25 ; increment == 5\n",
    (char*) (current_nid + 1176),  // nid of this line
    (char*) (current_nid + 1162)); // nid of increment
  printf3("%u ite 2 %u 95 %u ; unsigned-extended 5-byte input if increment == 5\n",
    (char*) (current_nid + 1177),  // nid of this line
    (char*) (current_nid + 1176),  // nid of increment == 5
    (char*) (current_nid + 1175)); // nid of unsigned-extended 4-byte input
  printf2("%u eq 1 %u 26 ; increment == 6\n",
    (char*) (current_nid + 1178),  // nid of this line
    (char*) (current_nid + 1162)); // nid of increment
  printf3("%u ite 2 %u 96 %u ; unsigned-extended 6-byte input if increment == 6\n",
    (char*) (current_nid + 1179),  // nid of this line
    (char*) (current_nid + 1178),  // nid of increment == 6
    (char*) (current_nid + 1177)); // nid of unsigned-extended 5-byte input
  printf2("%u eq 1 %u 27 ; increment == 7\n",
    (char*) (current_nid + 1180),  // nid of this line
    (char*) (current_nid + 1162)); // nid of increment
  printf3("%u ite 2 %u 97 %u ; unsigned-extended 7-byte input if increment == 7\n",
    (char*) (current_nid + 1181),  // nid of this line
    (char*) (current_nid + 1180),  // nid of increment == 7
    (char*) (current_nid + 1179)); // nid of unsigned-extended 6-byte input
  printf2("%u eq 1 %u 28 ; increment == 8\n",
    (char*) (current_nid + 1182),  // nid of this line
    (char*) (current_nid + 1162)); // nid of increment
  printf3("%u ite 2 %u 98 %u ; 8-byte input if increment == 8\n",
    (char*) (current_nid + 1183),  // nid of this line
    (char*) (current_nid + 1182),  // nid of increment == 8
    (char*) (current_nid + 1181)); // nid of unsigned-extended 7-byte input

  // write input to memory at address $a1 + $a0
  printf3("%u add 2 %u %u ; $a1 + $a0\n",
    (char*) (current_nid + 1184), // nid of this line
    (char*) (reg_nids + REG_A1),  // nid of current value of $a1 register
    (char*) (reg_nids + REG_A0)); // nid of current value of $a0 register
  printf4("%u write 3 %u %u %u ; memory[$a1 + $a0] = input\n",
    (char*) (current_nid + 1185),  // nid of this line
    (char*) memory_nid,            // nid of memory
    (char*) (current_nid + 1184),  // nid of $a1 + $a0
    (char*) (current_nid + 1183)); // nid of input

  // read ecall is in kernel mode and not done yet
  printf3("%u ult 1 %u %u ; $a0 < $a2\n",
    (char*) (current_nid + 1190), // nid of this line
    (char*) (reg_nids + REG_A0),  // nid of current value of $a0 register
    (char*) (reg_nids + REG_A2)); // nid of current value of $a2 register
  printf3("%u and 1 %u %u ; $a7 == SYSCALL_READ and $a0 < $a2\n",
    (char*) (current_nid + 1191),  // nid of this line
    (char*) (current_nid + 11),    // nid of $a7 == SYSCALL_READ
    (char*) (current_nid + 1190)); // nid of $a0 < $a2
  printf2("%u and 1 60 %u ; read ecall is in kernel mode and not done yet\n",
    (char*) (current_nid + 1192),  // nid of this line
    (char*) (current_nid + 1191)); // nid of $a7 == SYSCALL_READ and $a0 < $a2

  // if read ecall is in kernel mode and not done yet write input to memory at address $a1 + $a0
  printf2("%u ugt 1 %u 20 ; increment > 0\n",
    (char*) (current_nid + 1193),  // nid of this line
    (char*) (current_nid + 1162)); // nid of increment
  printf3("%u and 1 %u %u ; read ecall is in kernel mode and not done yet and increment > 0\n",
    (char*) (current_nid + 1194),  // nid of this line
    (char*) (current_nid + 1192),  // nid of read ecall is in kernel mode and not done yet
    (char*) (current_nid + 1193)); // nid of increment > 0
  printf4("%u ite 3 %u %u %u ; set memory[$a1 + $a0] = input if read ecall is in kernel mode and not done yet and increment > 0\n",
    (char*) (current_nid + 1195), // nid of this line
    (char*) (current_nid + 1194), // nid of read ecall is in kernel mode and not done yet and increment > 0
    (char*) (current_nid + 1185), // nid of memory[$a1 + $a0] = input
    (char*) memory_flow_nid);     // nid of most recent update of memory

  memory_flow_nid = current_nid + 1195;

  // if read ecall is in kernel mode and not done yet increment number of bytes read
  printf3("%u add 2 %u %u ; $a0 + increment\n",
    (char*) (current_nid + 1196),  // nid of this line
    (char*) (reg_nids + REG_A0),   // nid of current value of $a0 register
    (char*) (current_nid + 1162)); // nid of increment
  printf4("%u ite 2 %u %u %u ; set $a0 = $a0 + increment if read ecall is in kernel mode and not done yet\n",
    (char*) (current_nid + 1197),       // nid of this line
    (char*) (current_nid + 1192),       // nid of read ecall is in kernel mode and not done yet
    (char*) (current_nid + 1196),       // nid of $a0 + increment
    (char*) *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_nid + 1197;

  // if read ecall is in kernel mode and not done yet stay in kernel mode
  printf3("%u ite 1 %u 11 %u ; stay in kernel mode if read ecall is in kernel mode and not done yet\n\n",
    (char*) (current_nid + 1198),  // nid of this line
    (char*) (current_nid + 1192),  // nid of read ecall is in kernel mode and not done yet
    (char*) kernel_mode_flow_nid); // nid of most recent update of kernel-mode flag

  kernel_mode_flow_nid = current_nid + 1198;


  // write ecall
  printf3("%u and 1 %u %u ; write ecall is active\n",
    (char*) (current_nid + 1200), // nid of this line
    (char*) ecall_flow_nid,       // nid of most recent update of ecall activation
    (char*) (current_nid + 12));  // nid of $a7 == SYSCALL_WRITE

  // if write ecall is active record $a1 register for checking address validity
  printf4("%u ite 2 %u %u %u ; $a1 is start address of read buffer for checking address validity\n",
    (char*) (current_nid + 1201),   // nid of this line
    (char*) (current_nid + 1200),   // nid of write ecall is active
    (char*) (reg_nids + REG_A1),    // nid of current value of $a1 register
    (char*) access_flow_start_nid); // nid of address of most recent memory access

  access_flow_start_nid = current_nid + 1201;

  // if write ecall is active record $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and
  // $a1 otherwise, as address for checking address validity
  printf2("%u dec 2 %u ; $a2 - 1\n",
    (char*) (current_nid + 1202), // nid of this line
    (char*) (reg_nids + REG_A2)); // nid of current value of $a2 register
  printf1("%u not 2 27 ; not 7\n",
    (char*) (current_nid + 1203)); // nid of this line
  printf3("%u and 2 %u %u ; reset 3 LSBs of $a2 - 1\n",
    (char*) (current_nid + 1204),  // nid of this line
    (char*) (current_nid + 1202),  // nid of $a2 - 1
    (char*) (current_nid + 1203)); // nid of not 7
  printf3("%u add 2 %u %u ; $a1 + (($a2 - 1) / 8) * 8\n",
    (char*) (current_nid + 1205),  // nid of this line
    (char*) (reg_nids + REG_A1),   // nid of current value of $a1 register
    (char*) (current_nid + 1204)); // nid of (($a2 - 1) / 8) * 8
  printf2("%u ugt 1 %u 20 ; $a2 > 0\n",
    (char*) (current_nid + 1206), // nid of this line
    (char*) (reg_nids + REG_A2)); // nid of current value of $a2 register
  printf4("%u ite 2 %u %u %u ; $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and $a1 otherwise\n",
    (char*) (current_nid + 1207), // nid of this line
    (char*) (current_nid + 1206), // nid of $a2 > 0
    (char*) (current_nid + 1205), // nid of $a1 + (($a2 - 1) / 8) * 8
    (char*) (reg_nids + REG_A1)); // nid of current value of $a1 register
  printf4("%u ite 2 %u %u %u ; $a1 + (($a2 - 1) / 8) * 8 is end address of read buffer for checking address validity\n",
    (char*) (current_nid + 1208), // nid of this line
    (char*) (current_nid + 1200), // nid of write ecall is active
    (char*) (current_nid + 1207), // nid of $a1 + (($a2 - 1) / 8) * 8 if $a2 > 0, and $a1 otherwise
    (char*) access_flow_end_nid); // nid of address of most recent memory access

  access_flow_end_nid = current_nid + 1208;

  // if write ecall is active record $a1 bounds for checking address validity
  record_end_bounds(record_start_bounds(1209, current_nid + 1200, REG_A1), current_nid + 1200, REG_A1);

  // TODO: check file descriptor validity, return error codes

  // if write ecall is active set $a0 (written number of bytes) = $a2 (size)
  printf4("%u ite 2 %u %u %u ; set $a0 = $a2 if write ecall is active\n\n",
    (char*) (current_nid + 1250),       // nid of this line
    (char*) (current_nid + 1200),       // nid of write ecall is active
    (char*) (reg_nids + REG_A2),        // nid of current value of $a2 register
    (char*) *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_nid + 1250;


  // openat ecall
  printf3("%u and 1 %u %u ; openat ecall is active\n",
    (char*) (current_nid + 1300), // nid of this line
    (char*) ecall_flow_nid,       // nid of most recent update of ecall activation
    (char*) (current_nid + 13));  // nid of $a7 == SYSCALL_OPENAT

  // if openat ecall is active record $a1 register for checking address validity
  printf4("%u ite 2 %u %u %u ; $a1 is start address of filename for checking address validity\n",
    (char*) (current_nid + 1301),   // nid of this line
    (char*) (current_nid + 1300),   // nid of openat ecall is active
    (char*) (reg_nids + REG_A1),    // nid of current value of $a1 register
    (char*) access_flow_start_nid); // nid of address of most recent memory access

  access_flow_start_nid = current_nid + 1301;

  // if openat ecall is active record $a1 bounds for checking address validity
  record_start_bounds(1302, current_nid + 1300, REG_A1);

  // TODO: check address validity of whole filename, flags and mode arguments

  printf1("%u state 2 fd-bump\n", (char*) (current_nid + 1350));
  printf2("%u init 2 %u 21 ; initial fd-bump is 1 (file descriptor bump pointer)\n",
    (char*) (current_nid + 1351),  // nid of this line
    (char*) (current_nid + 1350)); // nid of fd-bump

  // if openat ecall is active set $a0 (file descriptor) = fd-bump + 1 (next file descriptor)
  printf2("%u inc 2 %u\n",
    (char*) (current_nid + 1352),  // nid of this line
    (char*) (current_nid + 1350)); // nid of fd-bump
  printf4("%u ite 2 %u %u %u ; fd-bump + 1 if openat ecall is active\n",
    (char*) (current_nid + 1353),  // nid of this line
    (char*) (current_nid + 1300),  // nid of openat ecall is active
    (char*) (current_nid + 1352),  // nid of fd-bump + 1
    (char*) (current_nid + 1350)); // nid of fd-bump
  printf3("%u next 2 %u %u ; increment fd-bump if openat ecall is active\n",
    (char*) (current_nid + 1354),  // nid of this line
    (char*) (current_nid + 1350),  // nid of fd-bump
    (char*) (current_nid + 1353)); // nid of fd-bump + 1
  printf4("%u ite 2 %u %u %u ; set $a0 = fd-bump + 1 if openat ecall is active\n\n",
    (char*) (current_nid + 1355),       // nid of this line
    (char*) (current_nid + 1300),       // nid of openat ecall is active
    (char*) (current_nid + 1352),       // nid of fd-bump + 1
    (char*) *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_nid + 1355;


  // is brk ecall is active?
  printf3("%u and 1 %u %u ; brk ecall is active\n",
    (char*) (current_nid + 1400), // nid of this line
    (char*) ecall_flow_nid,       // nid of most recent update of ecall activation
    (char*) (current_nid + 14));  // nid of $a7 == SYSCALL_BRK

  printf1("%u state 2 brk\n", (char*) (current_nid + 1450));
  printf2("%u init 2 %u 31 ; initial program break is end of data segment\n",
    (char*) (current_nid + 1451),  // nid of this line
    (char*) (current_nid + 1450)); // nid of brk

  // if brk ecall is active and $a0 is valid set brk = $a0
  // $a0 is valid if brk <= $a0 < $sp and $a0 is word-aligned
  printf3("%u ulte 1 %u %u ; brk <= $a0\n",
    (char*) (current_nid + 1452), // nid of this line
    (char*) (current_nid + 1450), // nid of brk
    (char*) (reg_nids + REG_A0)); // nid of current value of $a0 register
  printf3("%u ult 1 %u %u ; $a0 < $sp\n",
    (char*) (current_nid + 1453), // nid of this line
    (char*) (reg_nids + REG_A0),  // nid of current value of $a0 register
    (char*) (reg_nids + REG_SP)); // nid of current value of $sp register
  printf3("%u and 1 %u %u ; brk <= $a0 < $sp\n",
    (char*) (current_nid + 1454),  // nid of this line
    (char*) (current_nid + 1452),  // nid of brk <= $a0
    (char*) (current_nid + 1453)); // nid of $a0 < $sp
  printf2("%u and 2 %u 27 ; reset all but 3 LSBs of $a0\n",
    (char*) (current_nid + 1455), // nid of this line
    (char*) (reg_nids + REG_A0)); // nid of current value of $a0 register
  printf2("%u eq 1 %u 20 ; 3 LSBs of $a0 == 0 ($a0 is word-aligned)\n",
    (char*) (current_nid + 1456),  // nid of this line
    (char*) (current_nid + 1455)); // nid of 3 LSBs of current value of $a0 register
  printf3("%u and 1 %u %u ; brk <= $a0 < $sp and $a0 is word-aligned ($a0 is valid)\n",
    (char*) (current_nid + 1457),  // nid of this line
    (char*) (current_nid + 1454),  // nid of brk <= $a0 < $sp
    (char*) (current_nid + 1456)); // nid of $a0 is word-aligned
  printf3("%u and 1 %u %u ; brk ecall is active and $a0 is valid\n",
    (char*) (current_nid + 1458),  // nid of this line
    (char*) (current_nid + 1400),  // nid of brk ecall is active
    (char*) (current_nid + 1457)); // nid of $a0 is valid
  printf4("%u ite 2 %u %u %u ; brk = $a0 if brk ecall is active and $a0 is valid\n",
    (char*) (current_nid + 1459),  // nid of this line
    (char*) (current_nid + 1458),  // nid of brk ecall is active and $a0 is valid
    (char*) (reg_nids + REG_A0),   // nid of current value of $a0 register
    (char*) (current_nid + 1450)); // nid of brk
  printf3("%u next 2 %u %u ; set brk = $a0 if brk ecall is active and $a0 is valid\n",
    (char*) (current_nid + 1460),  // nid of this line
    (char*) (current_nid + 1450),  // nid of brk
    (char*) (current_nid + 1459)); // nid of preceding line

  // if brk ecall is active and $a0 is invalid set $a0 = brk
  printf2("%u not 1 %u ; $a0 is invalid\n",
    (char*) (current_nid + 1461),  // nid of this line
    (char*) (current_nid + 1457)); // nid of $a0 is valid
  printf3("%u and 1 %u %u ; brk ecall is active and $a0 is invalid\n",
    (char*) (current_nid + 1462),  // nid of this line
    (char*) (current_nid + 1400),  // nid of brk ecall is active
    (char*) (current_nid + 1461)); // nid of $a0 is invalid
  printf4("%u ite 2 %u %u %u ; set $a0 = brk if brk ecall is active and $a0 is invalid\n",
    (char*) (current_nid + 1463),       // nid of this line
    (char*) (current_nid + 1462),       // nid of brk ecall is active and $a0 is invalid
    (char*) (current_nid + 1450),       // nid of brk
    (char*) *(reg_flow_nids + REG_A0)); // nid of most recent update of $a0 register

  *(reg_flow_nids + REG_A0) = current_nid + 1463;

  if (check_block_access) {
    printf4("%u ite 2 %u %u %u ; lower bound on $t1 = brk if brk ecall is active and $a0 is valid\n",
      (char*) (current_nid + 1464),                 // nid of this line
      (char*) (current_nid + 1458),                 // nid of brk ecall is active and $a0 is valid
      (char*) (current_nid + 1450),                 // nid of brk
      (char*) *(reg_flow_nids + LO_FLOW + REG_T1)); // nid of most recent update of lower bound on $t1 register

    *(reg_flow_nids + LO_FLOW + REG_T1) = current_nid + 1464;

    printf4("%u ite 2 %u %u %u ; upper bound on $t1 = $a0 if brk ecall is active and $a0 is valid\n",
      (char*) (current_nid + 1465),                 // nid of this line
      (char*) (current_nid + 1458),                 // nid of brk ecall is active and $a0 is valid
      (char*) (reg_nids + REG_A0),                  // nid of current value of $a0 register
      (char*) *(reg_flow_nids + UP_FLOW + REG_T1)); // nid of most recent update of upper bound on $t1 register

    *(reg_flow_nids + UP_FLOW + REG_T1) = current_nid + 1465;

    printf3("%u ite 2 %u 30 %u ; lower bound on $t1 = end of code segment if brk ecall is active and $a0 is invalid\n",
      (char*) (current_nid + 1466),                 // nid of this line
      (char*) (current_nid + 1462),                 // nid of brk ecall is active and $a0 is invalid
      (char*) *(reg_flow_nids + LO_FLOW + REG_T1)); // nid of most recent update of lower bound on $t1 register

    *(reg_flow_nids + LO_FLOW + REG_T1) = current_nid + 1466;

    printf3("%u ite 2 %u 50 %u ; upper bound on $t1 = 4GB of memory addresses if brk ecall is active and $a0 is invalid\n",
      (char*) (current_nid + 1467),                 // nid of this line
      (char*) (current_nid + 1462),                 // nid of brk ecall is active and $a0 is invalid
      (char*) *(reg_flow_nids + UP_FLOW + REG_T1)); // nid of most recent update of upper bound on $t1 register

    *(reg_flow_nids + UP_FLOW + REG_T1) = current_nid + 1467;
  }

  printf2("\n%u next 1 60 %u ; update kernel-mode flag\n",
    (char*) (current_nid + 1500),  // nid of this line
    (char*) kernel_mode_flow_nid); // nid of most recent update of kernel-mode flag
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
    if (to_address < entry_point + code_length) {
      if (validate_procedure_body(from_instruction, from_link, to_address)) {
        in_edge = smalloc(SIZEOFUINT64STAR + 3 * SIZEOFUINT64);

        *in_edge       = *(control_in + (to_address - entry_point) / INSTRUCTIONSIZE);
        *(in_edge + 1) = from_instruction; // from which instruction
        *(in_edge + 2) = from_address;     // at which address
        *(in_edge + 3) = condition_nid;    // under which condition are we coming

        *(control_in + (to_address - entry_point) / INSTRUCTIONSIZE) = (uint64_t) in_edge;

        return;
      }
    } else if (from_address == entry_point + code_length - INSTRUCTIONSIZE)
      // from_instruction is last instruction in binary
      if (*(control_in + (from_address - entry_point) / INSTRUCTIONSIZE) == 0)
        // and unreachable
        return;
  }

  // the instruction at from_address proceeds to an instruction at an invalid to_address

  //report the error on the console
  output_fd = 1;

  printf2("%s: invalid instruction address %x detected\n", selfie_name, (char*) to_address);

  exit(EXITCODE_MODELINGERROR);
}

void reset_bounds() {
  if (check_block_access) {
    // if this instruction is active reset lower bound on $rd register to end of code segment
    printf3("%u ite 2 %u 30 %u\n",
      (char*) current_nid,                      // nid of this line
      (char*) pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
      (char*) *(reg_flow_nids + LO_FLOW + rd)); // nid of most recent update of lower bound on $rd register

    *(reg_flow_nids + LO_FLOW + rd) = current_nid;

    current_nid = current_nid + 1;

    // if this instruction is active reset upper bound on $rd register to 4GB of memory addresses
    printf3("%u ite 2 %u 50 %u\n",
      (char*) current_nid,                      // nid of this line
      (char*) pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
      (char*) *(reg_flow_nids + UP_FLOW + rd)); // nid of most recent update of upper bound on $rd register

    *(reg_flow_nids + UP_FLOW + rd) = current_nid;

    current_nid = current_nid + 1;
  }
}

void model_lui() {
  if (rd != REG_ZR) {
    reset_bounds();

    printf3("%u constd 2 %d ; %x << 12\n", (char*) current_nid, (char*) left_shift(imm, 12), (char*) imm);

    // if this instruction is active set $rd = imm << 12
    printf4("%u ite 2 %u %u %u ; ",
      (char*) (current_nid + 1),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) current_nid,            // nid of immediate argument left-shifted by 12 bits
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_lui();println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void transfer_bounds() {
  if (check_block_access) {
    // if this instruction is active set lower bound on $rd = lower bound on $rs1 register
    printf4("%u ite 2 %u %u %u\n",
      (char*) current_nid,                      // nid of this line
      (char*) pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
      (char*) (reg_nids + LO_FLOW + rs1),       // nid of lower bound on $rs1 register
      (char*) *(reg_flow_nids + LO_FLOW + rd)); // nid of most recent update of lower bound on $rd register

    *(reg_flow_nids + LO_FLOW + rd) = current_nid;

    current_nid = current_nid + 1;

    // if this instruction is active set upper bound on $rd = upper bound on $rs1 register
    printf4("%u ite 2 %u %u %u\n",
      (char*) current_nid,                      // nid of this line
      (char*) pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
      (char*) (reg_nids + UP_FLOW + rs1),       // nid of upper bound on $rs1 register
      (char*) *(reg_flow_nids + UP_FLOW + rd)); // nid of most recent update of upper bound on $rd register

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
      printf3("%u constd 2 %d ; %x\n", (char*) current_nid, (char*) imm, (char*) imm);

      if (rs1 == REG_ZR) {
        result_nid = current_nid;

        current_nid = current_nid + 1;

        if (rd == REG_A7)
          // assert: next instruction is ecall
          reg_a7 = imm;
      } else {
        // compute $rs1 + imm
        printf3("%u add 2 %u %u\n",
          (char*) (current_nid + 1), // nid of this line
          (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
          (char*) current_nid);      // nid of immediate value

        result_nid = current_nid + 1;

        current_nid = current_nid + 2;
      }
    }

    // if this instruction is active set $rd = $rs1 + imm
    printf4("%u ite 2 %u %u %u ; ",
      (char*) current_nid,            // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) result_nid,             // nid of $rs1 + ismm
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid;

    print_addi();println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_add() {
  if (rd != REG_ZR) {
    if (check_block_access) {
      // lower bound on $rs1 register > lower bound on $rs2 register
      printf3("%u ugt 1 %u %u\n",
        (char*) current_nid,                 // nid of this line
        (char*) (reg_nids + LO_FLOW + rs1),  // nid of lower bound on $rs1 register
        (char*) (reg_nids + LO_FLOW + rs2)); // nid of lower bound on $rs2 register

      // greater lower bound of $rs1 and $rs2 registers
      printf4("%u ite 2 %u %u %u\n",
        (char*) (current_nid + 1),           // nid of this line
        (char*) current_nid,                 // nid of lower bound on $rs1 > lower bound on $rs2
        (char*) (reg_nids + LO_FLOW + rs1),  // nid of lower bound on $rs1 register
        (char*) (reg_nids + LO_FLOW + rs2)); // nid of lower bound on $rs2 register

      // if this instruction is active set lower bound on $rd = greater lower bound of $rs1 and $rs2 registers
      printf4("%u ite 2 %u %u %u\n",
        (char*) (current_nid + 2),                // nid of this line
        (char*) pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
        (char*) (current_nid + 1),                // nid of greater lower bound of $rs1 and $rs2 registers
        (char*) *(reg_flow_nids + LO_FLOW + rd)); // nid of most recent update of lower bound on $rd register

      *(reg_flow_nids + LO_FLOW + rd) = current_nid + 2;

      current_nid = current_nid + 3;

      // upper bound on $rs1 register < upper bound on $rs2 register
      printf3("%u ult 1 %u %u\n",
        (char*) current_nid,                 // nid of this line
        (char*) (reg_nids + UP_FLOW + rs1),  // nid of upper bound on $rs1 register
        (char*) (reg_nids + UP_FLOW + rs2)); // nid of upper bound on $rs2 register

      // lesser upper bound of $rs1 and $rs2 registers
      printf4("%u ite 2 %u %u %u\n",
        (char*) (current_nid + 1),           // nid of this line
        (char*) current_nid,                 // nid of upper bound on $rs1 < upper bound on $rs2
        (char*) (reg_nids + UP_FLOW + rs1),  // nid of upper bound on $rs1 register
        (char*) (reg_nids + UP_FLOW + rs2)); // nid of upper bound on $rs2 register

      // if this instruction is active set upper bound on $rd = lesser upper bound of $rs1 and $rs2 registers
      printf4("%u ite 2 %u %u %u\n",
        (char*) (current_nid + 2),                // nid of this line
        (char*) pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
        (char*) (current_nid + 1),                // nid of lesser upper bound of $rs1 and $rs2 registers
        (char*) *(reg_flow_nids + UP_FLOW + rd)); // nid of most recent update of upper bound on $rd register

      *(reg_flow_nids + UP_FLOW + rd) = current_nid + 2;

      current_nid = current_nid + 3;
    }

    // compute $rs1 + $rs2
    printf3("%u add 2 %u %u\n",
      (char*) current_nid,       // nid of this line
      (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
      (char*) (reg_nids + rs2)); // nid of current value of $rs2 register

    // if this instruction is active set $rd = $rs1 + $rs2
    printf4("%u ite 2 %u %u %u ; ",
      (char*) (current_nid + 1),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) current_nid,            // nid of $rs1 + $rs2
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_add_sub_mul_divu_remu_sltu("add");println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_sub() {
  if (rd != REG_ZR) {
    // TODO: check if bounds on $rs2 are really initial bounds
    transfer_bounds();

    // compute $rs1 - $rs2
    printf3("%u sub 2 %u %u\n",
      (char*) current_nid,       // nid of this line
      (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
      (char*) (reg_nids + rs2)); // nid of current value of $rs2 register

    // if this instruction is active set $rd = $rs1 - $rs2
    printf4("%u ite 2 %u %u %u ; ",
      (char*) (current_nid + 1),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) current_nid,            // nid of $rs1 - $rs2
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_add_sub_mul_divu_remu_sltu("sub");println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_mul() {
  if (rd != REG_ZR) {
    // TODO: check if bounds on $rs1 and $rs2 are really initial bounds
    reset_bounds();

    // compute $rs1 * $rs2
    printf3("%u mul 2 %u %u\n",
      (char*) current_nid,       // nid of this line
      (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
      (char*) (reg_nids + rs2)); // nid of current value of $rs2 register

    // if this instruction is active set $rd = $rs1 * $rs2
    printf4("%u ite 2 %u %u %u ; ",
      (char*) (current_nid + 1),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) current_nid,            // nid of $rs1 * $rs2
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_add_sub_mul_divu_remu_sltu("mul");println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_divu() {
  if (rd != REG_ZR) {
    // TODO: check if bounds on $rs1 and $rs2 are really initial bounds
    reset_bounds();

    // if this instruction is active record $rs2 for checking if $rs2 == 0
    printf5("%u ite 2 %u %u %u ; record %s for checking division by zero\n",
      (char*) current_nid,         // nid of this line
      (char*) pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
      (char*) (reg_nids + rs2),    // nid of current value of $rs2 register
      (char*) division_flow_nid,   // nid of divisor of most recent division
      get_register_name(rs2));     // register name

    division_flow_nid = current_nid;

    current_nid = current_nid + 1;

    // compute $rs1 / $rs2
    printf3("%u udiv 2 %u %u\n",
      (char*) current_nid,       // nid of this line
      (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
      (char*) (reg_nids + rs2)); // nid of current value of $rs2 register

    // if this instruction is active set $rd = $rs1 / $rs2
    printf4("%u ite 2 %u %u %u ; ",
      (char*) (current_nid + 1),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) current_nid,            // nid of $rs1 / $rs2
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_add_sub_mul_divu_remu_sltu("divu");println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_remu() {
  if (rd != REG_ZR) {
    // TODO: check if bounds on $rs1 and $rs2 are really initial bounds
    reset_bounds();

    // if this instruction is active record $rs2 for checking if $rs2 == 0
    printf5("%u ite 2 %u %u %u ; record %s for checking remainder by zero\n",
      (char*) current_nid,         // nid of this line
      (char*) pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
      (char*) (reg_nids + rs2),    // nid of current value of $rs2 register
      (char*) remainder_flow_nid,  // nid of divisor of most recent remainder
      get_register_name(rs2));     // register name

    remainder_flow_nid = current_nid;

    current_nid = current_nid + 1;

    // compute $rs1 % $rs2
    printf3("%u urem 2 %u %u\n",
      (char*) current_nid,       // nid of this line
      (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
      (char*) (reg_nids + rs2)); // nid of current value of $rs2 register

    // if this instruction is active set $rd = $rs1 % $rs2
    printf4("%u ite 2 %u %u %u ; ",
      (char*) (current_nid + 1),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) current_nid,            // nid of $rs1 % $rs2
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_add_sub_mul_divu_remu_sltu("remu");println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_sltu() {
  if (rd != REG_ZR) {
    reset_bounds();

    // compute $rs1 < $rs2
    printf3("%u ult 1 %u %u\n",
      (char*) current_nid,       // nid of this line
      (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
      (char*) (reg_nids + rs2)); // nid of current value of $rs2 register

    // unsigned-extend $rs1 < $rs2 by 63 bits to 64 bits
    printf2("%u uext 2 %u 63\n",
      (char*) (current_nid + 1), // nid of this line
      (char*) current_nid);      // nid of $rs1 < $rs2

    // if this instruction is active set $rd = $rs1 < $rs2
    printf4("%u ite 2 %u %u %u ; ",
      (char*) (current_nid + 2),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) (current_nid + 1),      // nid of unsigned-64-bit-extended $rs1 < $rs2
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 2;

    print_add_sub_mul_divu_remu_sltu("sltu");println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

uint64_t record_start_bounds(uint64_t offset, uint64_t activation_nid, uint64_t reg) {
  if (check_block_access) {
    // if current instruction is active record lower bound on $reg register for checking address validity
    printf4("%u ite 2 %u %u %u\n",
      (char*) (current_nid + offset),     // nid of this line
      (char*) activation_nid,             // nid of activation condition of current instruction
      (char*) (reg_nids + LO_FLOW + reg), // nid of current lower bound on $reg register
      (char*) lo_flow_start_nid);         // nid of most recent update of lower bound on memory access

    lo_flow_start_nid = current_nid + offset;

    offset = offset + 1;

    // if current instruction is active record upper bound on $reg register for checking address validity
    printf4("%u ite 2 %u %u %u\n",
      (char*) (current_nid + offset),     // nid of this line
      (char*) activation_nid,             // nid of activation condition of current instruction
      (char*) (reg_nids + UP_FLOW + reg), // nid of current upper bound on $reg register
      (char*) up_flow_start_nid);         // nid of most recent update of upper bound on memory access

    up_flow_start_nid = current_nid + offset;

    return offset + 1;
  } else
    return offset;
}

uint64_t record_end_bounds(uint64_t offset, uint64_t activation_nid, uint64_t reg) {
  if (check_block_access) {
    // if current instruction is active record lower bound on $reg register for checking address validity
    printf4("%u ite 2 %u %u %u\n",
      (char*) (current_nid + offset),     // nid of this line
      (char*) activation_nid,             // nid of activation condition of current instruction
      (char*) (reg_nids + LO_FLOW + reg), // nid of current lower bound on $reg register
      (char*) lo_flow_end_nid);           // nid of most recent update of lower bound on memory access

    lo_flow_end_nid = current_nid + offset;

    offset = offset + 1;

    // if current instruction is active record upper bound on $reg register for checking address validity
    printf4("%u ite 2 %u %u %u\n",
      (char*) (current_nid + offset),     // nid of this line
      (char*) activation_nid,             // nid of activation condition of current instruction
      (char*) (reg_nids + UP_FLOW + reg), // nid of current upper bound on $reg register
      (char*) up_flow_end_nid);           // nid of most recent update of upper bound on memory access

    up_flow_end_nid = current_nid + offset;

    return offset + 1;
  } else
    return offset;
}

uint64_t compute_address() {
  if (imm == 0)
    return reg_nids + rs1; // nid of current value of $rs1 register
  else {
    printf3("%u constd 2 %d ; %x\n", (char*) current_nid, (char*) imm, (char*) imm);

    // compute $rs1 + imm
    printf3("%u add 2 %u %u\n",
      (char*) (current_nid + 1), // nid of this line
      (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
      (char*) current_nid);      // nid of immediate value

    current_nid = current_nid + 2;

    return current_nid - 1; // nid of $rs1 + imm
  }
}

void model_ld() {
  uint64_t address_nid;

  if (rd != REG_ZR) {
    current_nid = current_nid + record_start_bounds(0, pc_nid(pcs_nid, pc), rs1);

    address_nid = compute_address();

    // if this instruction is active record $rs1 + imm for checking address validity
    printf4("%u ite 2 %u %u %u\n",
      (char*) current_nid,            // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) address_nid,            // nid of $rs1 + imm
      (char*) access_flow_start_nid); // nid of address of most recent memory access

    access_flow_start_nid = current_nid;

    current_nid = current_nid + 1;

    if (check_block_access) {
      // read from lower-bounds memory[$rs1 + imm] into lower bound on $rd register
      printf3("%u read 2 %u %u\n",
        (char*) current_nid,   // nid of this line
        (char*) lo_memory_nid, // nid of lower bounds on addresses in memory
        (char*) address_nid);  // nid of $rs1 + imm

      // if this instruction is active set lower bound on $rd = lower-bounds memory[$rs1 + imm]
      printf4("%u ite 2 %u %u %u\n",
        (char*) (current_nid + 1),                // nid of this line
        (char*) pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
        (char*) current_nid,                      // nid of lower-bounds memory[$rs1 + imm]
        (char*) *(reg_flow_nids + LO_FLOW + rd)); // nid of most recent update of lower bound on $rd register

      *(reg_flow_nids + LO_FLOW + rd) = current_nid + 1;

      current_nid = current_nid + 2;

      // read from upper-bounds memory[$rs1 + imm] into upper bound on $rd register
      printf3("%u read 2 %u %u\n",
        (char*) current_nid,   // nid of this line
        (char*) up_memory_nid, // nid of upper bounds on addresses in memory
        (char*) address_nid);  // nid of $rs1 + imm

      // if this instruction is active set upper bound on $rd = upper-bounds memory[$rs1 + imm]
      printf4("%u ite 2 %u %u %u\n",
        (char*) (current_nid + 1),                // nid of this line
        (char*) pc_nid(pcs_nid, pc),              // nid of pc flag of this instruction
        (char*) current_nid,                      // nid of upper-bounds memory[$rs1 + imm]
        (char*) *(reg_flow_nids + UP_FLOW + rd)); // nid of most recent update of upper bound on $rd register

      *(reg_flow_nids + UP_FLOW + rd) = current_nid + 1;

      current_nid = current_nid + 2;
    }

    // read from memory[$rs1 + imm] into $rd register
    printf3("%u read 2 %u %u\n",
      (char*) current_nid,  // nid of this line
      (char*) memory_nid,   // nid of memory
      (char*) address_nid); // nid of $rs1 + imm

    // if this instruction is active set $rd = memory[$rs1 + imm]
    printf4("%u ite 2 %u %u %u ; ",
      (char*) (current_nid + 1),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
      (char*) current_nid,            // nid of memory[$rs1 + imm]
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

    *(reg_flow_nids + rd) = current_nid + 1;

    print_ld();println();
  }

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_sd() {
  uint64_t address_nid;

  current_nid = current_nid + record_start_bounds(0, pc_nid(pcs_nid, pc), rs1);

  address_nid = compute_address();

  // if this instruction is active record $rs1 + imm for checking address validity
  printf4("%u ite 2 %u %u %u\n",
    (char*) current_nid,            // nid of this line
    (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this instruction
    (char*) address_nid,            // nid of $rs1 + imm
    (char*) access_flow_start_nid); // nid of address of most recent memory access

  access_flow_start_nid = current_nid;

  current_nid = current_nid + 1;

  if (check_block_access) {
    // write lower bound on $rs2 register to lower-bounds memory[$rs1 + imm]
    printf4("%u write 3 %u %u %u\n",
      (char*) current_nid,                 // nid of this line
      (char*) lo_memory_nid,               // nid of lower bounds on addresses in memory
      (char*) address_nid,                 // nid of $rs1 + imm
      (char*) (reg_nids + LO_FLOW + rs2)); // nid of lower bound on $rs2 register

    // if this instruction is active set lower-bounds memory[$rs1 + imm] = lower bound on $rs2
    printf4("%u ite 3 %u %u %u\n",
      (char*) (current_nid + 1),   // nid of this line
      (char*) pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
      (char*) current_nid,         // nid of lower-bounds memory[$rs1 + imm]
      (char*) lo_memory_flow_nid); // nid of most recent update of lower-bounds memory

    lo_memory_flow_nid = current_nid + 1;

    current_nid = current_nid + 2;

    // write upper bound on $rs2 register to upper-bounds memory[$rs1 + imm]
    printf4("%u write 3 %u %u %u\n",
      (char*) current_nid,                 // nid of this line
      (char*) up_memory_nid,               // nid of upper bounds on addresses in memory
      (char*) address_nid,                 // nid of $rs1 + imm
      (char*) (reg_nids + UP_FLOW + rs2)); // nid of upper bound on $rs2 register

    // if this instruction is active set upper-bounds memory[$rs1 + imm] = upper bound on $rs2
    printf4("%u ite 3 %u %u %u\n",
      (char*) (current_nid + 1),   // nid of this line
      (char*) pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
      (char*) current_nid,         // nid of upper-bounds memory[$rs1 + imm]
      (char*) up_memory_flow_nid); // nid of most recent update of upper-bounds memory

    up_memory_flow_nid = current_nid + 1;

    current_nid = current_nid + 2;
  }

  // write $rs2 register to memory[$rs1 + imm]
  printf4("%u write 3 %u %u %u\n",
    (char*) current_nid,       // nid of this line
    (char*) memory_nid,        // nid of memory
    (char*) address_nid,       // nid of $rs1 + imm
    (char*) (reg_nids + rs2)); // nid of current value of $rs2 register

  // if this instruction is active set memory[$rs1 + imm] = $rs2
  printf4("%u ite 3 %u %u %u ; ",
    (char*) (current_nid + 1),   // nid of this line
    (char*) pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
    (char*) current_nid,         // nid of memory[$rs1 + imm] = $rs2
    (char*) memory_flow_nid);    // nid of most recent update of memory

  memory_flow_nid = current_nid + 1;

  print_sd();println();

  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, 0);
}

void model_beq() {
  // compute if beq condition is true
  printf3("%u eq 1 %u %u ; ",
    (char*) current_nid,       // nid of this line
    (char*) (reg_nids + rs1),  // nid of current value of $rs1 register
    (char*) (reg_nids + rs2)); // nid of current value of $rs2 register

  print_beq();println();

  // true branch
  go_to_instruction(is, REG_ZR, pc, pc + imm, current_nid);

  // compute if beq condition is false
  printf2("%u not 1 %u\n",
    (char*) current_nid + 1, // nid of this line
    (char*) current_nid);    // nid of preceding line

  // false branch
  go_to_instruction(is, REG_ZR, pc, pc + INSTRUCTIONSIZE, current_nid + 1);
}

void model_jal() {
  if (rd != REG_ZR) {
    // address of next instruction used here and in returning jalr instruction
    printf3("%u constd 2 %u ; %x\n",
      (char*) current_nid,             // nid of this line
      (char*) (pc + INSTRUCTIONSIZE),  // address of next instruction
      (char*) (pc + INSTRUCTIONSIZE)); // address of next instruction

    // if this instruction is active link $rd register to address of next instruction
    printf4("%u ite 2 %u %u %u ; ",
      (char*) (current_nid + 1),      // nid of this line
      (char*) pc_nid(pcs_nid, pc),    // nid of pc flag of this jal instruction
      (char*) current_nid,            // nid of address of next instruction
      (char*) *(reg_flow_nids + rd)); // nid of most recent update of $rd register

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
          if (current_callee > entry_point) {
            // assert: current_callee points to an instruction to which a jal jumps
            *(call_return + (current_callee - entry_point) / INSTRUCTIONSIZE) = pc;

            // assert: next "procedure body" begins right after jalr
            current_callee = pc + INSTRUCTIONSIZE;

            estimated_return = current_callee;

            return;
          }

  //report the error on the console
  output_fd = 1;

  printf3("%s: unsupported jalr at address %x with estimated address %x detected\n", selfie_name, (char*) pc, (char*) estimated_return);

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
  printf3("%u ite 1 %u 11 %u ; ",
    (char*) current_nid,         // nid of this line
    (char*) pc_nid(pcs_nid, pc), // nid of pc flag of this instruction
    (char*) ecall_flow_nid);     // nid of most recent update of ecall activation

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
  else if (is == LD)
    model_ld();
  else if (is == SD)
    model_sd();
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
    printf3("%u ite 1 %u 11 %u\n",
      (char*) current_nid,       // nid of this line
      (char*) activate_nid,      // nid of pc flag of instruction proceeding here
      (char*) control_flow_nid); // nid of previously processed in-edge

    current_nid = current_nid + 1;

    return current_nid - 1;
  }
}

void check_division_by_zero(uint64_t division, uint64_t flow_nid) {
  // check if divisor == 0
  printf2("%u eq 1 %u 20\n",
    (char*) current_nid, // nid of this line
    (char*) flow_nid);   // nid of divisor of most recent division or remainder
  printf2("%u bad %u ; ",
    (char*) (current_nid + 1), // nid of this line
    (char*) current_nid);      // nid of divisor == 0
  if (division)
    print("division by zero\n\n");
  else
    print("remainder by zero\n\n");

  current_nid = current_nid + 2;
}

void check_address_validity(uint64_t start, uint64_t flow_nid, uint64_t lo_flow_nid, uint64_t up_flow_nid) {
  if (start)
    print("; at start of memory block\n\n");
  else
    print("; at end of memory block\n\n");

  // check if address of most recent memory access < current lower bound
  printf3("%u ult 1 %u %u\n",
    (char*) current_nid,  // nid of this line
    (char*) flow_nid,     // nid of address of most recent memory access
    (char*) lo_flow_nid); // nid of current lower bound on memory addresses
  printf2("%u bad %u ; memory access below lower bound\n",
    (char*) (current_nid + 1), // nid of this line
    (char*) current_nid);      // nid of previous check

  current_nid = current_nid + 2;

  // check if address of most recent memory access >= current upper bound
  printf3("%u ugte 1 %u %u\n",
    (char*) current_nid,  // nid of this line
    (char*) flow_nid,     // nid of address of most recent memory access
    (char*) up_flow_nid); // nid of current upper bound on memory addresses
  printf2("%u bad %u ; memory access at or above upper bound\n",
    (char*) (current_nid + 1), // nid of this line
    (char*) current_nid);      // nid of previous check

  current_nid = current_nid + 2;

  // check if address of most recent memory access is word-aligned
  printf2("%u and 2 %u 27\n",
    (char*) current_nid, // nid of this line
    (char*) flow_nid);   // nid of address of most recent memory access
  printf2("%u neq 1 %u 20\n",
    (char*) (current_nid + 1), // nid of this line
    (char*) current_nid);      // nid of 3 LSBs of address of most recent memory access
  printf2("%u bad %u ; word-unaligned memory access\n\n",
    (char*) (current_nid + 2),  // nid of this line
    (char*) (current_nid + 1)); // nid of previous check

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

  printf1("; %s\n\n", SELFIE_URL);

  printf2("; BTOR2 %s generated by %s for\n", model_name, selfie_name);
  printf1("; RISC-V code obtained from %s and\n; invoked as", binary_name);

  i = 0;

  while (i < number_of_remaining_arguments()) {
    printf1(" %s", (char*) *(remaining_arguments() + i));

    i = i + 1;
  }

  print("\n\n1 sort bitvec 1 ; Boolean\n");
  print("2 sort bitvec 64 ; 64-bit machine word\n");
  print("3 sort array 2 2 ; 64-bit memory\n\n");

  print("10 zero 1\n11 one 1\n\n");

  print("20 zero 2\n21 one 2\n22 constd 2 2\n23 constd 2 3\n24 constd 2 4\n25 constd 2 5\n26 constd 2 6\n27 constd 2 7\n28 constd 2 8\n\n");

  print("; word-aligned end of code segment in memory\n\n");

  // end of code segment for checking address validity
  printf2("30 constd 2 %u ; %x\n\n", (char*) (entry_point + code_length), (char*) (entry_point + code_length));

  print("; word-aligned end of data segment in memory (initial program break)\n\n");

  // end of data segment (initial program break) for checking program break validity
  printf2("31 constd 2 %u ; %x\n\n", (char*) (entry_point + binary_length), (char*) (entry_point + binary_length));

  print("; word-aligned initial $sp (stack pointer) value from boot loader\n\n");

  // value in register $sp from boot loader
  printf2("40 constd 2 %u ; %x\n\n", (char*) *(registers + REG_SP), (char*) *(registers + REG_SP));

  print("; 4GB of memory\n\n");

  printf2("50 constd 2 %u ; %x\n\n", (char*) VIRTUALMEMORYSIZE, (char*) VIRTUALMEMORYSIZE);

  print("; kernel-mode flag\n\n");

  print("60 state 1 kernel-mode\n");
  print("61 init 1 60 10 kernel-mode ; initial value is false\n");
  print("62 not 1 60\n\n");

  print("; unsigned-extended inputs for byte-wise reading\n\n");

  print("71 sort bitvec 8 ; 1 byte\n");
  print("72 sort bitvec 16 ; 2 bytes\n");
  print("73 sort bitvec 24 ; 3 bytes\n");
  print("74 sort bitvec 32 ; 4 bytes\n");
  print("75 sort bitvec 40 ; 5 bytes\n");
  print("76 sort bitvec 48 ; 6 bytes\n");
  print("77 sort bitvec 56 ; 7 bytes\n\n");

  print("81 input 71 ; 1 byte\n");
  print("82 input 72 ; 2 bytes\n");
  print("83 input 73 ; 3 bytes\n");
  print("84 input 74 ; 4 bytes\n");
  print("85 input 75 ; 5 bytes\n");
  print("86 input 76 ; 6 bytes\n");
  print("87 input 77 ; 7 bytes\n\n");

  print("91 uext 2 81 56 ; 1 byte\n");
  print("92 uext 2 82 48 ; 2 bytes\n");
  print("93 uext 2 83 40 ; 3 bytes\n");
  print("94 uext 2 84 32 ; 4 bytes\n");
  print("95 uext 2 85 24 ; 5 bytes\n");
  print("96 uext 2 86 16 ; 6 bytes\n");
  print("97 uext 2 87 8 ; 7 bytes\n");
  print("98 input 2 ; 8 bytes\n\n");

  print("; 32 64-bit general-purpose registers\n");

  reg_nids = 100;

  reg_flow_nids = smalloc(3 * NUMBEROFREGISTERS * SIZEOFUINT64STAR);

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    *(reg_flow_nids + i) = reg_nids + i;

    if (i == 0)
      printf2("\n%u zero 2 %s ; register $0 is always 0\n",
        (char*) *(reg_flow_nids + i), // nid of this line
        get_register_name(i));        // register name
    else
      printf3("%u state 2 %s ; register $%u\n",
        (char*) *(reg_flow_nids + i), // nid of this line
        get_register_name(i),         // register name
        (char*) i);                   // register index as comment

    i = i + 1;
  }

  if (check_block_access)
    while (i < 3 * NUMBEROFREGISTERS) {
      *(reg_flow_nids + i) = reg_nids + i;

      if (i == LO_FLOW)
        printf3("\n%u constd 2 %u ; %x\n",
          (char*) *(reg_flow_nids + i),         // nid of this line
          (char*) (entry_point + code_length),  // end of code segment
          (char*) (entry_point + code_length)); // end of code segment
      else if (i == UP_FLOW)
        printf3("\n%u constd 2 %u ; %x\n",
          (char*) *(reg_flow_nids + i), // nid of this line
          (char*) VIRTUALMEMORYSIZE,    // 4GB of memory addresses
          (char*) VIRTUALMEMORYSIZE);   // 4GB of memory addresses
      else {
        printf1("%u state 2 ", (char*) *(reg_flow_nids + i));

        if (i < LO_FLOW + NUMBEROFREGISTERS)
          printf2("lo-%s ; lower bound on $%u\n",
            get_register_name(i % NUMBEROFREGISTERS), // register name
            (char*) (i % NUMBEROFREGISTERS));         // register index as comment
        else if (i < UP_FLOW + NUMBEROFREGISTERS)
          printf2("up-%s ; upper bound on $%u\n",
            get_register_name(i % NUMBEROFREGISTERS), // register name
            (char*) (i % NUMBEROFREGISTERS));         // register index as comment
      }

      i = i + 1;
    }

  print("\n; initializing registers\n");

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    if (i == 0)
      println();
    else if (i == REG_SP)
      printf3("%u init 2 %u 40 %s ; initial value from boot loader\n",
        (char*) (reg_nids * 2 + i), // nid of this line
        (char*) (reg_nids + i),     // nid of $sp register
        get_register_name(i));      // register name as comment
    else
      // ignoring non-zero value in register $a6 from initial context switch
      printf3("%u init 2 %u 20 %s ; initial value is 0\n",
        (char*) (reg_nids * 2 + i), // nid of this line
        (char*) (reg_nids + i),     // nid of to-be-initialized register
        get_register_name(i));      // register name as comment

    i = i + 1;
  }

  if (check_block_access)
    while (i < 3 * NUMBEROFREGISTERS) {
      if (i % NUMBEROFREGISTERS == 0)
        println();
      else if (i < LO_FLOW + NUMBEROFREGISTERS)
        printf3("%u init 2 %u 30 %s ; initial value is end of code segment\n",
          (char*) (reg_nids * 2 + i),                // nid of this line
          (char*) (reg_nids + i),                    // nid of to-be-initialized register
          get_register_name(i % NUMBEROFREGISTERS)); // register name as comment
      else if (i < UP_FLOW + NUMBEROFREGISTERS)
        printf3("%u init 2 %u 50 %s ; initial value is 4GB of memory addresses\n",
          (char*) (reg_nids * 2 + i),                // nid of this line
          (char*) (reg_nids + i),                    // nid of to-be-initialized register
          get_register_name(i % NUMBEROFREGISTERS)); // register name as comment

      i = i + 1;
    }

  print("\n; 64-bit program counter encoded in Boolean flags\n\n");

  // 3 more digits to accommodate binary starting at entry point and stack with
  // 100*4 lines per 32-bit instruction (pc increments by 4) and
  // 100*8 lines per 64-bit machine word in data segment
  pcs_nid = ten_to_the_power_of(
    log_ten(entry_point + binary_length +
      (VIRTUALMEMORYSIZE - *(registers + REG_SP))) + 3);

  while (pc < entry_point + code_length) {
    current_nid = pc_nid(pcs_nid, pc);

    // pc flag of current instruction
    printf1("%u state 1\n", (char*) current_nid);

    if (pc == entry_point)
      // set pc here by initializing pc flag of instruction at address 0 to true
      printf2("%u init 1 %u 11 ; initial program counter\n",
        (char*) (current_nid + 1), // nid of this line
        (char*) current_nid);      // nid of pc flag of current instruction
    else
      // initialize all other pc flags to false
      printf2("%u init 1 %u 10\n",
        (char*) (current_nid + 1), // nid of this line
        (char*) current_nid);      // nid of pc flag of current instruction

    pc = pc + INSTRUCTIONSIZE;
  }

  current_nid = pc_nid(pcs_nid, pc);

  printf1("\n%u state 3 boot-loader\n", (char*) current_nid);

  loader_nid    = current_nid;
  data_flow_nid = current_nid;
  current_nid   = current_nid + 1;

  print("\n; data segment\n\n");

  // assert: pc == entry_point + code_length

  while (pc < VIRTUALMEMORYSIZE) {
    if (pc == entry_point + binary_length) {
      // assert: stack pointer < VIRTUALMEMORYSIZE
      pc = *(registers + REG_SP);

      print("\n; stack\n\n");
    }

    // address in data segment or stack
    printf3("%u constd 2 %u ; %x\n",
      (char*) current_nid,     // nid of this line
      (char*) pc, (char*) pc); // address of current machine word

    machine_word = load_virtual_memory(pt, pc);

    if (machine_word == 0) {
      // load machine word == 0
      printf3("%u write 3 %u %u 20\n",
        (char*) (current_nid + 1), // nid of this line
        (char*) data_flow_nid,     // nid of most recent update to data segment
        (char*) current_nid);      // nid of address of current machine word

      data_flow_nid = current_nid + 1;
    } else {
      // load non-zero machine word, use sign
      printf3("%u constd 2 %d ; %x\n",
        (char*) (current_nid + 1),                   // nid of this line
        (char*) machine_word, (char*) machine_word); // value of machine word at current address
      printf4("%u write 3 %u %u %u\n",
        (char*) (current_nid + 2),  // nid of this line
        (char*) data_flow_nid,      // nid of most recent update to data segment
        (char*) current_nid,        // nid of address of current machine word
        (char*) (current_nid + 1)); // nid of value of machine word at current address

      data_flow_nid = current_nid + 2;
    }

    pc = pc + WORDSIZE;

    if (current_nid == loader_nid + 1)
      current_nid = loader_nid + WORDSIZE;
    else
      current_nid = current_nid + WORDSIZE;
  }

  print("\n; 64-bit memory\n\n");

  memory_nid = pcs_nid * 2;

  current_nid = memory_nid;

  printf1("%u state 3 memory ; data segment, heap, stack\n", (char*) current_nid);
  printf3("%u init 3 %u %u ; loading data segment and stack into memory\n",
    (char*) (current_nid + 1), // nid of this line
    (char*) current_nid,       // nid of memory
    (char*) data_flow_nid);    // nid of most recent update to data segment

  memory_flow_nid = current_nid;

  if (check_block_access) {
    current_nid = current_nid + 2;

    lo_memory_nid = current_nid;

    printf1("\n%u state 3 lower-bounds ; for checking address validity\n", (char*) current_nid);
    printf2("%u init 3 %u 30 ; initializing lower bounds to end of code segment\n",
      (char*) (current_nid + 1), // nid of this line
      (char*) current_nid);      // nid of lower bounds on addresses in memory

    lo_memory_flow_nid = current_nid;

    current_nid = current_nid + 2;

    up_memory_nid = current_nid;

    printf1("\n%u state 3 upper-bounds ; for checking address validity\n", (char*) current_nid);
    printf2("%u init 3 %u 50 ; initializing upper bounds to 4GB of memory addresses\n",
      (char*) (current_nid + 1), // nid of this line
      (char*) current_nid);      // nid of upper bounds on addresses in memory

    up_memory_flow_nid = current_nid;
  }

  print("\n; data flow\n\n");

  code_nid = pcs_nid * 3;

  control_in  = zmalloc(code_length / INSTRUCTIONSIZE * SIZEOFUINT64);
  call_return = zmalloc(code_length / INSTRUCTIONSIZE * SIZEOFUINT64);

  current_callee   = entry_point;
  estimated_return = entry_point;

  pc = get_pc(current_context);

  while (pc < entry_point + code_length) {
    current_nid = pc_nid(code_nid, pc);

    fetch();
    decode();

    translate_to_model();

    pc = pc + INSTRUCTIONSIZE;
  }

  print("\n; syscalls\n\n");

  current_nid = pcs_nid * 4;

  model_syscalls();

  print("\n; control flow\n\n");

  control_nid = pcs_nid * 5;

  pc = get_pc(current_context);

  while (pc < entry_point + code_length) {
    current_nid = pc_nid(control_nid, pc);

    in_edge = (uint64_t*) *(control_in + (pc - entry_point) / INSTRUCTIONSIZE);

    // nid of 1-bit 0
    control_flow_nid = 10;

    while (in_edge != (uint64_t*) 0) {
      from_instruction = *(in_edge + 1);
      from_address     = *(in_edge + 2);
      condition_nid    = *(in_edge + 3);

      if (from_instruction == BEQ) {
        // is beq active and its condition true or false?
        printf5("%u and 1 %u %u ; beq %u[%x]",
          (char*) current_nid,                         // nid of this line
          (char*) pc_nid(pcs_nid, from_address),       // nid of pc flag of instruction proceeding here
          (char*) condition_nid,                       // nid of true or false beq condition
          (char*) from_address, (char*) from_address); // address of instruction proceeding here
        print_code_line_number_for_instruction(from_address, entry_point);println();

        current_nid = current_nid + 1;

        // activate this instruction if beq is active and its condition is true (false)
        control_flow_nid = control_flow(current_nid - 1, control_flow_nid);
      } else if (from_instruction == JALR) {
        jalr_address = *(call_return + (from_address - entry_point) / INSTRUCTIONSIZE);

        if (jalr_address != 0) {
          // is value of $ra register with LSB reset equal to address of this instruction?
          printf3("%u not 2 21 ; jalr %u[%x]",
            (char*) current_nid,                         // nid of this line
            (char*) jalr_address, (char*) jalr_address); // address of instruction proceeding here
          print_code_line_number_for_instruction(jalr_address, entry_point);println();
          printf3("%u and 2 %u %u\n",
            (char*) (current_nid + 1),   // nid of this line
            (char*) (reg_nids + REG_RA), // nid of current value of $ra register
            (char*) current_nid);        // nid of not 1
          printf3("%u eq 1 %u %u\n",
            (char*) (current_nid + 2), // nid of this line
            (char*) (current_nid + 1), // nid of current value of $ra register with LSB reset
            (char*) condition_nid);    // nid of address of this instruction (generated by jal)

          // is jalr active and the previous condition true or false?
          printf3("%u and 1 %u %u\n",
            (char*) (current_nid + 3),             // nid of this line
            (char*) pc_nid(pcs_nid, jalr_address), // nid of pc flag of instruction proceeding here
            (char*) (current_nid + 2));            // nid of return address condition

          current_nid = current_nid + 4;

          // activate this instruction if jalr is active and its condition is true (false)
          control_flow_nid = control_flow(current_nid - 1, control_flow_nid);
        } else {
          // no jalr returning from jal found

          printf2("; exit ecall wrapper call or runaway jal %u[%x]", (char*) from_address, (char*) from_address);
          print_code_line_number_for_instruction(from_address, entry_point);println();

          // this instruction may stay deactivated if there is no more in-edges
        }
      } else if (from_instruction == ECALL) {
        printf3("%u state 1 ; kernel-mode pc flag of ecall %u[%x]",
          (char*) current_nid,                         // nid of this line
          (char*) from_address, (char*) from_address); // address of instruction proceeding here
        print_code_line_number_for_instruction(from_address, entry_point);println();

        printf2("%u init 1 %u 10 ; ecall is initially inactive\n",
          (char*) (current_nid + 1), // nid of this line
          (char*) current_nid);      // nid of kernel-mode pc flag of ecall

        printf3("%u ite 1 %u 60 %u ; activate ecall and keep active while in kernel mode\n",
          (char*) (current_nid + 2),              // nid of this line
          (char*) current_nid,                    // nid of kernel-mode pc flag of ecall
          (char*) pc_nid(pcs_nid, from_address)); // nid of pc flag of instruction proceeding here

        printf3("%u next 1 %u %u ; keep ecall active while in kernel mode\n",
          (char*) (current_nid + 3),  // nid of this line
          (char*) current_nid,        // nid of kernel-mode pc flag of ecall
          (char*) (current_nid + 2)); // nid of previous line

        printf2("%u and 1 %u 62 ; ecall is active but not in kernel mode anymore\n",
          (char*) (current_nid + 4), // nid of this line
          (char*) current_nid);      // nid of kernel-mode pc flag of ecall

        current_nid = current_nid + 5;

        // activate this instruction if ecall is active but not in kernel mode anymore
        control_flow_nid = control_flow(current_nid - 1, control_flow_nid);
      } else {
        if (from_instruction == JAL) print("; jal "); else print("; ");
        printf2("%u[%x]", (char*) from_address, (char*) from_address);
        print_code_line_number_for_instruction(from_address, entry_point);println();

        // activate this instruction if instruction proceeding here is active
        control_flow_nid = control_flow(pc_nid(pcs_nid, from_address), control_flow_nid);
      }

      in_edge = (uint64_t*) *in_edge;
    }

    // update pc flag of current instruction
    printf5("%u next 1 %u %u ; ->%u[%x]",
      (char*) current_nid,         // nid of this line
      (char*) pc_nid(pcs_nid, pc), // nid of pc flag of current instruction
      (char*) control_flow_nid,    // nid of most recently processed in-edge
      (char*) pc, (char*) pc);     // address of current instruction
    print_code_line_number_for_instruction(pc, entry_point);
    if (control_flow_nid == 10)
      if (pc > entry_point)
        // TODO: warn here about unreachable code
        print(" (unreachable)");
    println();

    if (current_nid >= pc_nid(control_nid, pc) + 400) {
      // the instruction at pc is reachable by too many other instructions

      //report the error on the console
      output_fd = 1;

      printf2("%s: too many in-edges at instruction address %x detected\n", selfie_name, (char*) pc);

      exit(EXITCODE_MODELINGERROR);
    }

    pc = pc + INSTRUCTIONSIZE;
  }

  print("\n; updating registers\n");

  current_nid = pcs_nid * 6;

  i = 0;

  while (i < NUMBEROFREGISTERS) {
    if (i == 0)
      println();
    else
      printf5("%u next 2 %u %u %s ; register $%u\n",
        (char*) (current_nid + i),    // nid of this line
        (char*) (reg_nids + i),       // nid of register
        (char*) *(reg_flow_nids + i), // nid of most recent update to register
        get_register_name(i),         // register name
        (char*) i);                   // register index as comment

    i = i + 1;
  }

  if (check_block_access)
    while (i < 3 * NUMBEROFREGISTERS) {
      if (i % NUMBEROFREGISTERS == 0)
        println();
      else {
        printf3("%u next 2 %u %u ",
          (char*) (current_nid + i),     // nid of this line
          (char*) (reg_nids + i),        // nid of register
          (char*) *(reg_flow_nids + i)); // nid of most recent update to register

        if (i < LO_FLOW + NUMBEROFREGISTERS)
          printf2("lo-%s ; lower bound on $%u\n",
            get_register_name(i % NUMBEROFREGISTERS), // register name
            (char*) (i % NUMBEROFREGISTERS));         // register index as comment
        else if (i < UP_FLOW + NUMBEROFREGISTERS)
          printf2("up-%s ; upper bound on $%u\n",
            get_register_name(i % NUMBEROFREGISTERS), // register name
            (char*) (i % NUMBEROFREGISTERS));         // register index as comment
      }

      i = i + 1;
    }

  print("\n; updating memory\n\n");

  current_nid = pcs_nid * 7;

  printf3("%u next 3 %u %u memory\n",
      (char*) current_nid,      // nid of this line
      (char*) memory_nid,       // nid of memory
      (char*) memory_flow_nid); // nid of most recent write to memory

  if (check_block_access) {
    printf3("%u next 3 %u %u lower-bounds\n",
        (char*) (current_nid + 1),   // nid of this line
        (char*) lo_memory_nid,       // nid of lower bounds on addresses in memory
        (char*) lo_memory_flow_nid); // nid of most recent write to lower bounds on addresses in memory
    printf3("%u next 3 %u %u upper-bounds\n",
        (char*) (current_nid + 2),   // nid of this line
        (char*) up_memory_nid,       // nid of upper bounds on addresses in memory
        (char*) up_memory_flow_nid); // nid of most recent write to upper bounds on addresses in memory
  }

  print("\n; checking division and remainder by zero\n\n");

  current_nid = pcs_nid * 8;

  check_division_by_zero(1, division_flow_nid);
  check_division_by_zero(0, remainder_flow_nid);

  print("; checking address validity\n\n");

  current_nid = pcs_nid * 9;

  check_address_validity(1, access_flow_start_nid, lo_flow_start_nid, up_flow_start_nid);
  check_address_validity(0, access_flow_end_nid, lo_flow_end_nid, up_flow_end_nid);

  // TODO: check validity of return addresses in jalr

  printf1("; end of BTOR2 %s\n", model_name);
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

      if (binary_length == 0) {
        printf1("%s: nothing to model\n", selfie_name);

        return EXITCODE_BADARGUMENTS;
      }

      // use extension ".btor2" in name of SMT-LIB file
      model_name = replace_extension(binary_name, "btor2");

      // assert: model_name is mapped and not longer than MAX_FILENAME_LENGTH

      model_fd = open_write_only(model_name);

      if (signed_less_than(model_fd, 0)) {
        printf2("%s: could not create model file %s\n", selfie_name, model_name);

        exit(EXITCODE_IOERROR);
      }

      reset_library();
      reset_interpreter();
      reset_microkernel();

      init_memory(1);

      current_context = create_context(MY_CONTEXT, 0);

      // assert: number_of_remaining_arguments() > 0

      boot_loader(current_context);

      do_switch(current_context, current_context, TIMEROFF);

      output_name = model_name;
      output_fd   = model_fd;

      run = 0;

      model = 1;

      modeler();

      model = 0;

      output_name = (char*) 0;
      output_fd   = 1;

      printf3("%s: %u characters of model formulae written into %s\n", selfie_name,
        (char*) number_of_written_characters,
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