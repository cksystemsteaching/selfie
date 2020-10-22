
/*
Copyright (c) 2015-2020, the Selfie Project authors. All rights reserved.
Please see the AUTHORS file for details. Use of this source code is
governed by a BSD license that can be found in the LICENSE file.

Selfie is a project of the Computational Systems Group at the
Department of Computer Sciences of the University of Salzburg
in Austria. For further information and code please refer to:

http://selfie.cs.uni-salzburg.at
*/

// -----------------------------------------------------------------
// -------------------- RISC-V to x86 TRANSLATOR -------------------
// -----------------------------------------------------------------

// ------------------------ GLOBAL CONSTANTS -----------------------

//prefix
uint64_t REX     = 64;
uint64_t REX_B   = 1;   //Register Field extension First  Operand
uint64_t REX_R   = 4;   //Register Field extension Second Operand
uint64_t REX_W   = 8;   //Operand size is 64 bit wide

// prefix for two byte opcode
uint64_t TWO_BYTE_INSTRUCTION = 15;           //                                         0x0f

// one byte opcodes
uint64_t X86_ADD     = 1;                     //add  x,y      (r/m(x) = r/m(x) + r(y))   0x01
uint64_t X86_SUB     = 41;                    //sub  x,y      (r/m(x) = r/m(x) - r(y))   0x29
uint64_t X86_CMP     = 57;                    //cmp  x,y                                 0x39
uint64_t X86_PUSH    = 80;                    //push x        (m(rsp) = r(x))            0x50
uint64_t X86_POP     = 88;                    //pop  x        (r(x) = m(rsp))            0x58
uint64_t X86_IMM     = 129;                   //addi x,imm    (r/m(x) = r/m(x) + imm)    0x81
uint64_t X86_MOV_R   = 137;                   //mov  x,y      (r/m(x) = r(y))            0x89
uint64_t X86_MOV_M   = 139;                   //mov  x,y      (r(x) = r/m(y))            0x8b
uint64_t X86_LEA     = 141;                   //lea                                      0x8d
uint64_t X86_NOP     = 144;                   //                                         0x90
uint64_t X86_MOVI    = 184;                   //mov  x,imm    (r(x) = imm)               0xb8
uint64_t X86_DIV_NEG = 247;                   //div  x        (rax = rdx:rax / r(x))     0xf7
uint64_t X86_JMPQ    = 233;                   //jmpq  x       (rip = rip + r(x))         0xe9
uint64_t X86_JMPA    = 255;                   //jmpa  x       (rip = r(x))               0xff

//two byte opcodes
uint64_t X86_SYSCALL = 5;                     //syscall                                  0x05
uint64_t X86_JE      = 132;                   //je   imm                                 0x84
uint64_t X86_SETB    = 146;                   //setb x                                   0x92
uint64_t X86_IMUL    = 175;                   //imul x,y      (r(x) = r(x) * r(y))       0xaf

uint64_t REG_RAX  = 0;
uint64_t REG_RCX  = 1;
uint64_t REG_RDX  = 2;
uint64_t REG_RBX  = 3;
uint64_t REG_RSP  = 4;
uint64_t REG_RBP  = 5;
uint64_t REG_RSI  = 6;
uint64_t REG_RDI  = 7;
uint64_t REG_R8   = 8;
uint64_t REG_R9   = 9;
uint64_t REG_R10  = 10;
uint64_t REG_R11  = 11;
uint64_t REG_R12  = 12;
uint64_t REG_R13  = 13;
uint64_t REG_R14  = 14;
uint64_t REG_R15  = 15;

// ------------------------ GLOBAL VARIABLES -----------------------

// holds current x86 translation of a RISC-V instruction
uint64_t* instr_bytes = (uint64_t*) 0;
// points to current byte inside selfies uint64_t type
uint64_t  x86ByteCount = 0;
// holds address of calculated global pointer after translation
uint64_t  binary_gp_address = 0;
// informational counter for amount of emitted x86 instructions
uint64_t x86TotalEmittedInstructions = 0;
// holds data segment size of x86 binary
uint64_t x86DataLength = 0;
//stores the offsets to every x86 instruction
uint64_t* x86_address_fixup_table;
//own program counter for the translator
uint64_t pc_translator;

// -----------------------------------------------------------------
// -------------------------- x86 HANDLING -------------------------
// -----------------------------------------------------------------

void x86SaveAddress();
void x86AdressFix();
uint64_t x86NextByte();
uint64_t x86NextWord();
void x86WriteByte(uint64_t byte);
void x86WriteWord(uint64_t word);
uint64_t x86GetModRMValue(uint64_t x, uint64_t y);
uint64_t x86GetPrefix(uint64_t x, uint64_t y, uint64_t wide);
uint64_t x86GetRegister(uint64_t reg);
uint64_t x86GetSyscallNumber(uint64_t snumber);
void x86emitInstructionBuffer(uint64_t length);
void x86MoveValueToRegister(uint64_t reg, uint64_t value);

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

void translate_lui();
void translate_addi();
void translate_add();
void translate_sub();
void translate_mul();
void translate_divu();
void translate_remu();
void translate_sltu();
void translate_ld();
void translate_sd();
void translate_beq();
void translate_jal();
void translate_jalr();
void translate_ecall();

// -----------------------------------------------------------------
// ----------------------- BINARY TRANSLATOR -----------------------
// -----------------------------------------------------------------

void translate_to_x86_binary();

void selfie_translate();

// -----------------------------------------------------------------
// -------------------------- x86 HANDLING -------------------------
// -----------------------------------------------------------------

void fetch_translator() {
  // assert: is_valid_virtual_address(pc) == 1
  // assert: is_virtual_address_mapped(pt, pc) == 1

  if (pc_translator % WORDSIZE == 0)
    ir = get_low_word(load_virtual_memory(pt, pc_translator));
  else
    ir = get_high_word(load_virtual_memory(pt, pc_translator - INSTRUCTIONSIZE));
}

void x86SaveAddress() {
  uint64_t offset;

  offset = binary_length * SIZEOFUINT64 + x86ByteCount;

  *(x86_address_fixup_table + ((pc_translator - ELF_ENTRY_POINT) / INSTRUCTIONSIZE)) = offset;
}

void x86AdressFix() {
  uint64_t binary_length_backup;
  uint64_t x86ByteCount_backup;
  uint64_t opcode;
  uint64_t target_address_x86;
  uint64_t x86_offset;
  uint64_t jump_target_r5;
  uint64_t x86_current_instruction_address;
  uint64_t i;

  pc_translator = ELF_ENTRY_POINT;
  x86_offset = 0;
  binary_length_backup = binary_length;
  x86ByteCount_backup = x86ByteCount;

  while(pc_translator < code_length + ELF_ENTRY_POINT) {

    pc_translator = pc_translator + INSTRUCTIONSIZE;

    x86_current_instruction_address = *(x86_address_fixup_table + x86_offset);
    binary_length = x86_current_instruction_address / SIZEOFUINT64;
    x86ByteCount = x86_current_instruction_address % SIZEOFUINT64;

    opcode = x86NextByte();

    if (opcode == TWO_BYTE_INSTRUCTION) {
      opcode = x86NextByte();
      if (opcode == X86_JE) {
        x86_current_instruction_address = *(x86_address_fixup_table + x86_offset + 1);
        jump_target_r5 = x86NextWord();
        target_address_x86 = *(x86_address_fixup_table + ((jump_target_r5 - ELF_ENTRY_POINT) / INSTRUCTIONSIZE));
        //replace jump offset with translated x86 jump offset
        x86WriteWord(target_address_x86 - x86_current_instruction_address);
      }
    }
    else if (right_shift(opcode, 4) == 4) { //some REX prefix
      opcode = x86NextByte();
      if (opcode == X86_LEA) {
        i = 0;
        while (i < 6) { //skip lea instruction
          opcode = x86NextByte();
          i = i + 1;
        }
        if (opcode == X86_JMPQ) {
          x86_current_instruction_address = *(x86_address_fixup_table + x86_offset + 1);
          jump_target_r5 = x86NextWord();
          target_address_x86 = *(x86_address_fixup_table + ((jump_target_r5 - ELF_ENTRY_POINT) / INSTRUCTIONSIZE));
          x86WriteWord(target_address_x86 - x86_current_instruction_address);
        }
      }
      else if (opcode == X86_CMP) {
        //skip cmp instruction
        opcode = x86NextByte();
        opcode = x86NextByte();
        if (opcode == TWO_BYTE_INSTRUCTION) {
          opcode = x86NextByte();
          if (opcode == X86_JE) {
            x86_current_instruction_address = *(x86_address_fixup_table + x86_offset + 1);
            jump_target_r5 = x86NextWord();
            target_address_x86 = *(x86_address_fixup_table + ((jump_target_r5 - ELF_ENTRY_POINT) / INSTRUCTIONSIZE));
            x86WriteWord(target_address_x86 - x86_current_instruction_address);
          }
        }
      }
      else if (right_shift(opcode, 4) == 11) { //0xb prefix
        i = 0;
        while (i < 10) { //skip mov instruction
          opcode = x86NextByte();
          i = i + 1;
        }
        if (opcode == X86_CMP) {
          //skip cmp instruction
          opcode = x86NextByte();
          opcode = x86NextByte();
          if (opcode == TWO_BYTE_INSTRUCTION) {
            opcode = x86NextByte();
            if (opcode == X86_JE) {
              x86_current_instruction_address = *(x86_address_fixup_table + x86_offset + 1);
              jump_target_r5 = x86NextWord();
              target_address_x86 = *(x86_address_fixup_table + ((jump_target_r5 - ELF_ENTRY_POINT) / INSTRUCTIONSIZE));
              x86WriteWord(target_address_x86 - x86_current_instruction_address);
            }
          }
        }
      }
    }
    else if (opcode == X86_JMPQ) {
      x86_current_instruction_address = *(x86_address_fixup_table + x86_offset + 1);
      jump_target_r5 = x86NextWord();
      target_address_x86 = *(x86_address_fixup_table + ((jump_target_r5 - ELF_ENTRY_POINT)/ INSTRUCTIONSIZE));
      x86WriteWord(target_address_x86 - x86_current_instruction_address);
    }

    x86_offset = x86_offset + 1;
  }

  binary_length = binary_length_backup;
  x86ByteCount = x86ByteCount_backup;
}

void x86WriteWord(uint64_t word) {
  uint64_t i;
  uint64_t byte;

  i = 0;
  while(i < 4) {
    byte = right_shift(left_shift(word, (7 - i) * 8), 56);
    x86WriteByte(byte);
    i = i + 1;
  }
}

void x86WriteByte(uint64_t byte) {
  uint64_t tmp;

  //set targetbyte to 0
  tmp = *(binary + binary_length) - left_shift(right_shift(left_shift(*(binary + binary_length),
                                                                      (8 - x86ByteCount - 1) * 8), 56), x86ByteCount * 8);

  *(binary + binary_length) = tmp + left_shift(byte, x86ByteCount * 8);

  x86ByteCount = x86ByteCount + 1;
  if (x86ByteCount == 8) {
    x86ByteCount = 0;
    binary_length = binary_length + 1;
  }

}

uint64_t x86NextByte() {
  uint64_t byte;

  byte = right_shift(left_shift(*(binary + binary_length), (SIZEOFUINT64 - x86ByteCount - 1) * SIZEOFUINT64), (SIZEOFUINT64 - 1) * SIZEOFUINT64);

  x86ByteCount = x86ByteCount + 1;
  if (x86ByteCount == 8) {
    x86ByteCount = 0;
    binary_length = binary_length + 1;
  }

  return byte;
}

uint64_t x86NextWord() {
  uint64_t i;
  uint64_t word;
  uint64_t bLengthbackup;
  uint64_t bytecountbackup;

  word = 0;
  bLengthbackup = binary_length;
  bytecountbackup = x86ByteCount;

  i = 0;
  while(i < 4) {
    word = word + left_shift(x86NextByte(), i * SIZEOFUINT64);
    i = i + 1;
  }

  binary_length = bLengthbackup;
  x86ByteCount = bytecountbackup;

  return word;
}

uint64_t x86GetModRMValue(uint64_t x, uint64_t y) {
  return right_shift(left_shift(y,61),58) + right_shift(left_shift(x,61),61); //FIXME: does not handle values > 16 properly!
}

uint64_t x86GetPrefix(uint64_t op1, uint64_t op2, uint64_t wide) {
  uint64_t prefix;

  prefix = REX;

  if (wide)
    prefix = prefix + REX_W;
  if (op1 > 7)
    prefix = prefix + REX_B;
  if (op2 > 7)
    prefix = prefix + REX_R;

  return prefix;
}

uint64_t x86GetRegister(uint64_t reg) {
  if(reg == REG_SP) return REG_RSP;
  if(reg == REG_S0) return REG_RBP;
  if(reg == REG_GP) return REG_RBX;
  if(reg == REG_RA) return REG_R15;
  if(reg == REG_T0) return REG_RCX;
  if(reg == REG_T1) return REG_R10;
  if(reg == REG_T2) return REG_R11;
  if(reg == REG_T3) return REG_R13;
  if(reg == REG_T4) return REG_R14;
  if(reg == REG_A0) return REG_RDI; //RDI because first argument of syscall
  if(reg == REG_A1) return REG_RSI;
  if(reg == REG_A2) return REG_RDX;
  if(reg == REG_A3) return REG_R10;
  if(reg == REG_A4) return REG_R8;
  if(reg == REG_A5) return REG_R9;
  if(reg == REG_A7) return REG_RAX;

  if(reg == REG_ZR) {
    print("Register $zero encountered in x86GetRegister(). This should not happen! "); //FIXME: more information
    println();
  }

  return reg;
}

uint64_t x86GetSyscallNumber(uint64_t snumber) {
  if (snumber == SYSCALL_EXIT)
    return 60;
  if (snumber == SYSCALL_READ)
    return 0;
  if (snumber == SYSCALL_WRITE)
    return 1;
  if (snumber == SYSCALL_OPENAT)
    return 257;
  if (snumber == SYSCALL_BRK)
    return 12; //sys_brk
  if (snumber == SYSCALL_SWITCH)
    return snumber;
  print("Syscall number could not be translated\n");
  return 0;
}

void x86emitInstructionBuffer(uint64_t length) {
  uint64_t i;

  i = 0;
  while(i < length) {
    *(binary + binary_length) = *(binary + binary_length) + left_shift(*(instr_bytes + i), x86ByteCount * 8);
    x86ByteCount = x86ByteCount + 1;
    i = i + 1;
    if(x86ByteCount == 8){
      binary_length = binary_length + 1;
      x86ByteCount = 0;
    }
  }
}

void x86MoveValueToRegister(uint64_t reg, uint64_t value) {
  *(instr_bytes + 0) = x86GetPrefix(reg, 0, 1);
  *(instr_bytes + 1) = X86_MOVI + right_shift(left_shift(reg,61),61);
  *(instr_bytes + 2) = right_shift(left_shift(value, 56), 56);
  *(instr_bytes + 3) = right_shift(left_shift(value, 48), 56);
  *(instr_bytes + 4) = right_shift(left_shift(value, 40), 56);
  *(instr_bytes + 5) = right_shift(left_shift(value, 32), 56);
  *(instr_bytes + 6) = right_shift(left_shift(value, 24), 56);
  *(instr_bytes + 7) = right_shift(left_shift(value, 16), 56);
  *(instr_bytes + 8) = right_shift(left_shift(value, 8),  56);
  *(instr_bytes + 9) = right_shift(value, 56);

  x86emitInstructionBuffer(10);
  x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
}

// -----------------------------------------------------------------
// ------------------------- INSTRUCTIONS --------------------------
// -----------------------------------------------------------------

void translate_lui() {
  uint64_t op1;
  uint64_t value;

  if (rd == REG_ZR) {
    return;
  }

  value = left_shift(imm, 12);
  op1 = x86GetRegister(rd);

  // look forward to check if we are calculating global pointer
  pc_translator = pc_translator + INSTRUCTIONSIZE;
  fetch_translator();
  pc_translator = pc_translator - INSTRUCTIONSIZE;
  if (get_opcode(ir) == OP_IMM) {
    pc_translator = pc_translator + 2 * INSTRUCTIONSIZE;
    fetch_translator();
    pc_translator = pc_translator - 2 * INSTRUCTIONSIZE;
    if (get_opcode(ir) == OP_IMM) {
      decode_i_format();
      if (rd == REG_GP) {
        if (binary_gp_address == 0) {
          value = 0;
          op1 = x86GetRegister(rd);
          pc_translator = pc_translator + INSTRUCTIONSIZE;
          x86SaveAddress();
          pc_translator = pc_translator + INSTRUCTIONSIZE;
          binary_gp_address = binary_length * SIZEOFUINT64 + x86ByteCount + 2; //address where later the real value needs to be filled in
        }
      }
    }
  }

  *(instr_bytes + 0) = x86GetPrefix(op1, 0, 1);
  *(instr_bytes + 1) = X86_MOVI + right_shift(left_shift(op1,61),61);
  *(instr_bytes + 2) = right_shift(left_shift(value, 56), 56);
  *(instr_bytes + 3) = right_shift(left_shift(value, 48), 56);
  *(instr_bytes + 4) = right_shift(left_shift(value, 40), 56);
  *(instr_bytes + 5) = right_shift(left_shift(value, 32), 56);
  *(instr_bytes + 6) = right_shift(left_shift(value, 24), 56);
  *(instr_bytes + 7) = right_shift(left_shift(value, 16), 56);
  *(instr_bytes + 8) = right_shift(left_shift(value, 8),  56);
  *(instr_bytes + 9) = right_shift(value,56);

  x86emitInstructionBuffer(10);
  x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
}

void translate_nop() {
  *(instr_bytes + 0) = X86_NOP;

  x86emitInstructionBuffer(1);
  x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
}

void translate_addi() {
  uint64_t op1;
  uint64_t op2;
  uint64_t length;

  if (rd == REG_ZR) {
    translate_nop();
    return;
  }

  //if syscall number is set here then change syscall number for x86-64 platform
  if (rd == REG_A7) {

    pc_translator = pc_translator + INSTRUCTIONSIZE;
    fetch_translator();
    pc_translator = pc_translator - INSTRUCTIONSIZE;

    if (ir == 115) //ecall
      imm = x86GetSyscallNumber(imm);
  }

  //if this is an allocation of a word on the stack we can skip translating this
  if (imm == (uint64_t) -8) {
    if (rs1 == REG_SP) {
      if (rd == REG_SP) {

        pc_translator = pc_translator + INSTRUCTIONSIZE;
        fetch_translator();
        pc_translator = pc_translator - INSTRUCTIONSIZE;

        if (get_opcode(ir) == OP_SD) {
          return;
        }
      }
    }
  }

  op1 = x86GetRegister(rd);
  if(rs1 == REG_ZR) {
    length = 10;
    *(instr_bytes + 0) = x86GetPrefix(op1, 0, 1);
    *(instr_bytes + 1) = X86_MOVI + right_shift(left_shift(op1, 61), 61);
    *(instr_bytes + 2) = right_shift(left_shift(imm, 56), 56);
    *(instr_bytes + 3) = right_shift(left_shift(imm, 48), 56);
    *(instr_bytes + 4) = right_shift(left_shift(imm, 40), 56);
    *(instr_bytes + 5) = right_shift(left_shift(imm, 32), 56);
    *(instr_bytes + 6) = right_shift(left_shift(imm, 24), 56);
    *(instr_bytes + 7) = right_shift(left_shift(imm, 16), 56);
    *(instr_bytes + 8) = right_shift(left_shift(imm, 8),  56);
    *(instr_bytes + 9) = right_shift(imm,56);
    x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
  }
  else {
    op2 = x86GetRegister(rs1);
    length = 10;
    *(instr_bytes + 0) = x86GetPrefix(op1, op2, 1);
    *(instr_bytes + 1) = X86_MOV_R;
    *(instr_bytes + 2) = 192 + x86GetModRMValue(op1,op2); //mov rd,rs1

    *(instr_bytes + 3) = x86GetPrefix(op1, 0, 1);
    *(instr_bytes + 4) = X86_IMM;
    *(instr_bytes + 5) = 192 + x86GetModRMValue(op1, 0); //opcode extension = 0 -> addi
    *(instr_bytes + 6) = right_shift(left_shift(imm, 56), 56);
    *(instr_bytes + 7) = right_shift(left_shift(imm, 48), 56);
    *(instr_bytes + 8) = right_shift(left_shift(imm, 40), 56);
    *(instr_bytes + 9) = right_shift(left_shift(imm, 32), 56);
    x86TotalEmittedInstructions = x86TotalEmittedInstructions + 2;
  }

  x86emitInstructionBuffer(length);

}

void translate_add() {
  uint64_t op1;
  uint64_t op2;
  uint64_t op3;
  uint64_t length;

  op1 = x86GetRegister(rd);
  op3 = x86GetRegister(rs2);
  if(rs1 == 0) {
    length = 3;
    *(instr_bytes + 0) = x86GetPrefix(op1, op3, 1);
    *(instr_bytes + 1) = X86_MOV_R;
    *(instr_bytes + 2) = 192 + x86GetModRMValue(op1, op3);
    x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
  }
  else if (op1 == op3) {
    op2 = x86GetRegister(rs1);
    length = 3;
    *(instr_bytes + 0) = x86GetPrefix(op3, op2, 1);
    *(instr_bytes + 1) = X86_ADD;
    *(instr_bytes + 2) = 192 + x86GetModRMValue(op3, op2);
    x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
  }
  else {
    op2 = x86GetRegister(rs1);
    length = 6;
    *(instr_bytes + 0) = x86GetPrefix(op1, op2, 1);
    *(instr_bytes + 1) = X86_MOV_R;
    *(instr_bytes + 2) = 192 + x86GetModRMValue(op1, op2); //rd = rs1

    *(instr_bytes + 3) = x86GetPrefix(op1, op3, 1);
    *(instr_bytes + 4) = X86_ADD;
    *(instr_bytes + 5) = 192 + x86GetModRMValue(op1, op3);
    x86TotalEmittedInstructions = x86TotalEmittedInstructions + 2;
  }

  x86emitInstructionBuffer(length);
}

void translate_sub() {
  uint64_t length;
  uint64_t op1;
  uint64_t op2;
  uint64_t op3;

  op1 = x86GetRegister(rd);
  op3 = x86GetRegister(rs2);

  if (rs1 == REG_ZR) {
    length = 6;
    *(instr_bytes + 0) = x86GetPrefix(op1, op3, 1);
    *(instr_bytes + 1) = X86_MOV_R;
    *(instr_bytes + 2) = 192 + x86GetModRMValue(op1, op3);

    *(instr_bytes + 3) = x86GetPrefix(op1, 0, 1);
    *(instr_bytes + 4) = X86_DIV_NEG;
    *(instr_bytes + 5) = 192 + x86GetModRMValue(op1, 3); //opcode extension = 3 -> NEG
    x86TotalEmittedInstructions = x86TotalEmittedInstructions + 2;
  }
  else if (op1 == op3) {
    length = 6;
    op2 = x86GetRegister(rs1);
    *(instr_bytes + 0) = x86GetPrefix(op3, 0, 1);
    *(instr_bytes + 1) = X86_DIV_NEG;
    *(instr_bytes + 2) = 192 + x86GetModRMValue(op3, 3); //opcode extension = 3 -> NEG

    *(instr_bytes + 3) = x86GetPrefix(op3, op2, 1);
    *(instr_bytes + 4) = X86_ADD;
    *(instr_bytes + 5) = 192 + x86GetModRMValue(op3, op2);
    x86TotalEmittedInstructions = x86TotalEmittedInstructions + 2;
  }
  else {
    length = 6;
    op2 = x86GetRegister(rs1);
    *(instr_bytes + 0) = x86GetPrefix(op1, op2, 1);
    *(instr_bytes + 1) = X86_MOV_R;
    *(instr_bytes + 2) = 192 + x86GetModRMValue(op1, op2); //rd = rs1

    *(instr_bytes + 3) = x86GetPrefix(op1, op3, 1);
    *(instr_bytes + 4) = X86_SUB;
    *(instr_bytes + 5) = 192 + x86GetModRMValue(op1, op3);
    x86TotalEmittedInstructions = x86TotalEmittedInstructions + 2;
  }

  x86emitInstructionBuffer(length);
}

void translate_mul() {
  uint64_t op1;
  uint64_t op2;
  uint64_t op3;

  op1 = x86GetRegister(rd);
  op2 = x86GetRegister(rs1);
  op3 = x86GetRegister(rs2);

  *(instr_bytes + 0) = x86GetPrefix(op1, op2, 1);
  *(instr_bytes + 1) = X86_MOV_R;
  *(instr_bytes + 2) = 192 + x86GetModRMValue(op1, op2); //rd = rs1

  *(instr_bytes + 3) = x86GetPrefix(op3, op1, 1);
  *(instr_bytes + 4) = TWO_BYTE_INSTRUCTION;
  *(instr_bytes + 5) = X86_IMUL;
  *(instr_bytes + 6) = 192 + x86GetModRMValue(op3, op1);

  x86emitInstructionBuffer(7);
  x86TotalEmittedInstructions = x86TotalEmittedInstructions + 2;
}

void translate_divu() {
  uint64_t op1;
  uint64_t op2;
  uint64_t op3;
  uint64_t length;

  op1 = x86GetRegister(rd);
  op2 = x86GetRegister(rs1);
  op3 = x86GetRegister(rs2);

  if (op1 != REG_RAX) {
    length = 23;
    *(instr_bytes + 0) = X86_PUSH + REG_RDX;
    *(instr_bytes + 1) = X86_PUSH + REG_RAX;

    *(instr_bytes + 2) = x86GetPrefix(0, 0, 1);
    *(instr_bytes + 3) = X86_MOVI + REG_RDX;
    *(instr_bytes + 4) = 0;
    *(instr_bytes + 5) = 0;
    *(instr_bytes + 6) = 0;
    *(instr_bytes + 7) = 0;
    *(instr_bytes + 8) = 0;
    *(instr_bytes + 9) = 0;
    *(instr_bytes + 10) = 0;
    *(instr_bytes + 11) = 0;

    *(instr_bytes + 12) = x86GetPrefix(REG_RAX, op2, 1); //mov rax,rs1
    *(instr_bytes + 13) = X86_MOV_R;
    *(instr_bytes + 14) = 192 + x86GetModRMValue(REG_RAX, op2);

    *(instr_bytes + 15) = x86GetPrefix(op3, 0, 1); //div rs2
    *(instr_bytes + 16) = X86_DIV_NEG; //FIXME signed div?
    *(instr_bytes + 17) = 192 + x86GetModRMValue(op3, 0) + left_shift(6, 3);

    *(instr_bytes + 18) = x86GetPrefix(op1, REG_RAX, 1); //mov rd,rax
    *(instr_bytes + 19) = X86_MOV_R;
    *(instr_bytes + 20) = 192 + x86GetModRMValue(op1, REG_RAX);

    *(instr_bytes + 21) = X86_POP + REG_RAX;
    *(instr_bytes + 22) = X86_POP + REG_RDX;
    x86TotalEmittedInstructions = x86TotalEmittedInstructions + 8;
  }
  else {
    print("could not translate divu because destination register is the RAX register");
    println();
    return;
  }

  x86emitInstructionBuffer(length);
}

void translate_remu() {
  uint64_t op1;
  uint64_t op2;
  uint64_t op3;
  uint64_t length;

  op1 = x86GetRegister(rd);
  op2 = x86GetRegister(rs1);
  op3 = x86GetRegister(rs2);

  if (op1 != REG_RDX) {
    length = 23;
    *(instr_bytes + 0) = X86_PUSH + REG_RDX;
    *(instr_bytes + 1) = X86_PUSH + REG_RAX;

    *(instr_bytes + 2) = x86GetPrefix(0, 0, 1);
    *(instr_bytes + 3) = X86_MOVI + REG_RDX;
    *(instr_bytes + 4) = 0;
    *(instr_bytes + 5) = 0;
    *(instr_bytes + 6) = 0;
    *(instr_bytes + 7) = 0;
    *(instr_bytes + 8) = 0;
    *(instr_bytes + 9) = 0;
    *(instr_bytes + 10) = 0;
    *(instr_bytes + 11) = 0;

    *(instr_bytes + 12) = x86GetPrefix(REG_RAX, op2, 1); //mov rax,rs1
    *(instr_bytes + 13) = X86_MOV_R;
    *(instr_bytes + 14) = 192 + x86GetModRMValue(REG_RAX, op2);

    *(instr_bytes + 15) = x86GetPrefix(op3, 0, 1); //div rs2
    *(instr_bytes + 16) = X86_DIV_NEG; //FIXME signed div?
    *(instr_bytes + 17) = 192 + x86GetModRMValue(op3, 0) + left_shift(6, 3);

    *(instr_bytes + 18) = x86GetPrefix(op1, REG_RDX, 1); //mov rd,rdx
    *(instr_bytes + 19) = X86_MOV_R;
    *(instr_bytes + 20) = 192 + x86GetModRMValue(op1, REG_RDX);

    *(instr_bytes + 21) = X86_POP + REG_RAX;
    *(instr_bytes + 22) = X86_POP + REG_RDX;
    x86TotalEmittedInstructions = x86TotalEmittedInstructions + 8;
  }
  else {
    print("could not translate remu because destination register is the RDX register");
    println();
    return;
  }

  x86emitInstructionBuffer(length);
}

void translate_sltu() {
  uint64_t length;
  uint64_t op1;
  uint64_t op2;
  uint64_t op3;

  if (rd != REG_ZR) {
    op1 = x86GetRegister(rd);
    if (rs1 == REG_ZR) {
      op2 = REG_R14; //FIXME hardcoded value

      x86MoveValueToRegister(op2, 0);

      length = 3;
      op3 = x86GetRegister(rs2);

      *(instr_bytes + 0) = x86GetPrefix(op2, op3, 1);
      *(instr_bytes + 1) = X86_CMP;
      *(instr_bytes + 2) = 192 + x86GetModRMValue(op2, op3);
      x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
    }
    else {
      length = 3;
      op2 = x86GetRegister(rs1);
      op3 = x86GetRegister(rs2);

      *(instr_bytes + 0) = x86GetPrefix(op2, op3, 1);
      *(instr_bytes + 1) = X86_CMP;
      *(instr_bytes + 2) = 192 + x86GetModRMValue(op2, op3);
      x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
    }

    x86emitInstructionBuffer(length);
    x86MoveValueToRegister(op1, 0);

    *(instr_bytes + 0) = x86GetPrefix(op1, 0, 0);
    *(instr_bytes + 1) = TWO_BYTE_INSTRUCTION;
    *(instr_bytes + 2) = X86_SETB;
    *(instr_bytes + 3) = 192 + x86GetModRMValue(op1, 0);
    x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;

    x86emitInstructionBuffer(4);
  }
  else
    translate_nop();
}

void translate_ld() {
  uint64_t op1;
  uint64_t op2;
  uint64_t length;
  uint64_t imm_bkup;

  if (rd == REG_ZR) {
    translate_nop();
    return;
  }

  op1 = x86GetRegister(rd);
  op2 = x86GetRegister(rs1);

  imm_bkup = imm;

  if (imm == 0) {
    if (rs1 == REG_SP) {

      pc_translator = pc_translator + INSTRUCTIONSIZE;
      fetch_translator();

      if (get_opcode(ir) == OP_IMM) {
        decode_i_format();
        if (funct3 == F3_ADDI) {
          if (op1 > 7) {
            length = 2;
            *(instr_bytes + 0) = x86GetPrefix(op1, 0, 0);
            *(instr_bytes + 1) = X86_POP + x86GetModRMValue(op1, 0);
            x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
          }
          else {
            length = 1;
            *(instr_bytes + 0) = X86_POP + op1;
            x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
          }
          x86SaveAddress();

          x86emitInstructionBuffer(length);

          if (imm == 8) {
            return;
          }

          if (imm > 8)
            imm = imm - 8;

          op1 = x86GetRegister(rd);
          *(instr_bytes + 0) = x86GetPrefix(op1, 0, 1);
          *(instr_bytes + 1) = X86_IMM;
          *(instr_bytes + 2) = 192 + x86GetModRMValue(op1, 0); //opcode extension = 0 -> addi
          *(instr_bytes + 3) = right_shift(left_shift(imm, 56), 56);
          *(instr_bytes + 4) = right_shift(left_shift(imm, 48), 56);
          *(instr_bytes + 5) = right_shift(left_shift(imm, 40), 56);
          *(instr_bytes + 6) = right_shift(left_shift(imm, 32), 56);
          x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;

          x86emitInstructionBuffer(7);

          return;
        }
        else
          pc_translator = pc_translator - INSTRUCTIONSIZE;
      }
      else
        pc_translator = pc_translator - INSTRUCTIONSIZE;
    }
  }

  if (signed_less_than(imm_bkup, 128)) {
    if (signed_less_than(-129, imm_bkup)) {
      length = 4;
      *(instr_bytes + 0) = x86GetPrefix(op2, op1, 1);
      *(instr_bytes + 1) = X86_MOV_M;
      *(instr_bytes + 2) = 64 + x86GetModRMValue(op2, op1);
      *(instr_bytes + 3) = right_shift(left_shift(imm_bkup, 56), 56);
      x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
    }
    else {
      length = 7;
      *(instr_bytes + 0) = x86GetPrefix(op2, op1, 1);
      *(instr_bytes + 1) = X86_MOV_M;
      *(instr_bytes + 2) = 128 + x86GetModRMValue(op2, op1);
      *(instr_bytes + 3) = right_shift(left_shift(imm_bkup, 56), 56);
      *(instr_bytes + 4) = right_shift(left_shift(imm_bkup, 48), 56);
      *(instr_bytes + 5) = right_shift(left_shift(imm_bkup, 40), 56);
      *(instr_bytes + 6) = right_shift(left_shift(imm_bkup, 32), 56);
      x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
    }
  }
  else {
    length = 7;
    *(instr_bytes + 0) = x86GetPrefix(op2, op1, 1);
    *(instr_bytes + 1) = X86_MOV_M;
    *(instr_bytes + 2) = 128 + x86GetModRMValue(op2, op1);
    *(instr_bytes + 3) = right_shift(left_shift(imm_bkup, 56), 56);
    *(instr_bytes + 4) = right_shift(left_shift(imm_bkup, 48), 56);
    *(instr_bytes + 5) = right_shift(left_shift(imm_bkup, 40), 56);
    *(instr_bytes + 6) = right_shift(left_shift(imm_bkup, 32), 56);
    x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
  }

  x86emitInstructionBuffer(length);
}

void translate_sd() {
  uint64_t op1;
  uint64_t op2;
  uint64_t length;

  op1 = x86GetRegister(rs1);
  op2 = x86GetRegister(rs2);

  if (imm == 0) {
    if (rs1 == REG_SP) {
      if (op2 > 7) {
        length = 2;
        *(instr_bytes + 0) = x86GetPrefix(op2, 0, 0);
        *(instr_bytes + 1) = X86_PUSH + x86GetModRMValue(op2, 0);
        x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
      }
      else {
        length = 1;
        *(instr_bytes + 0) = X86_PUSH + x86GetModRMValue(op2, 0);
        x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
      }

      x86emitInstructionBuffer(length);

      return;
    }
  }

  if (signed_less_than(imm, 128)) {
    if (signed_less_than(-129, imm)) {
      length = 4;
      *(instr_bytes + 0) = x86GetPrefix(op1, op2, 1);
      *(instr_bytes + 1) = X86_MOV_R;
      *(instr_bytes + 2) = 64 + x86GetModRMValue(op1, op2);
      *(instr_bytes + 3) = right_shift(left_shift(imm, 56), 56);
      x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
    }
    else {
      length = 7;
      *(instr_bytes + 0) = x86GetPrefix(op1, op2, 1);
      *(instr_bytes + 1) = X86_MOV_R;
      *(instr_bytes + 2) = 128 + x86GetModRMValue(op1, op2);
      *(instr_bytes + 3) = right_shift(left_shift(imm, 56), 56);
      *(instr_bytes + 4) = right_shift(left_shift(imm, 48), 56);
      *(instr_bytes + 5) = right_shift(left_shift(imm, 40), 56);
      *(instr_bytes + 6) = right_shift(left_shift(imm, 32), 56);
      x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
    }
  }
  else {
    length = 7;
    *(instr_bytes + 0) = x86GetPrefix(op1, op2, 1);
    *(instr_bytes + 1) = X86_MOV_R;
    *(instr_bytes + 2) = 128 + x86GetModRMValue(op1, op2);
    *(instr_bytes + 3) = right_shift(left_shift(imm, 56), 56);
    *(instr_bytes + 4) = right_shift(left_shift(imm, 48), 56);
    *(instr_bytes + 5) = right_shift(left_shift(imm, 40), 56);
    *(instr_bytes + 6) = right_shift(left_shift(imm, 32), 56);
    x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
  }

  x86emitInstructionBuffer(length);
}

void translate_beq() {
  uint64_t offset;
  uint64_t op2;
  uint64_t op3;

  if (rs1 == REG_ZR) {
    op2 = REG_R14; //FIXME hardcoded value
  }
  else {
    op2 = x86GetRegister(rs1);
  }

  if (rs2 == REG_ZR) {
    op3 = REG_R13; //FIXME hardcoded value
    x86MoveValueToRegister(op3, 0);
  }
  else {
    op3 = x86GetRegister(rs2);
  }

  *(instr_bytes + 0) = x86GetPrefix(op2, op3, 1); //FIXME rd is not set
  *(instr_bytes + 1) = X86_CMP;
  *(instr_bytes + 2) = 192 + x86GetModRMValue(op2, op3);

  offset = pc_translator + imm;

  *(instr_bytes + 3)  = TWO_BYTE_INSTRUCTION;
  *(instr_bytes + 4)  = X86_JE;
  *(instr_bytes + 5)  = right_shift(left_shift(offset, 56), 56); //FIXME adress fixup chain
  *(instr_bytes + 6)  = right_shift(left_shift(offset, 48), 56);
  *(instr_bytes + 7)  = right_shift(left_shift(offset, 40), 56);
  *(instr_bytes + 8)  = right_shift(left_shift(offset, 32), 56);

  x86emitInstructionBuffer(9);
  x86TotalEmittedInstructions = x86TotalEmittedInstructions + 2;
}

void translate_jal() {
  uint64_t address;
  uint64_t length;
  uint64_t op1;

  length = 0;
  address = pc_translator + imm;

  if (rd != REG_ZR) {
    length = 7;
    op1 = x86GetRegister(rd);

    *(instr_bytes + 0)  = x86GetPrefix(0, op1, 1);
    *(instr_bytes + 1)  = X86_LEA;
    *(instr_bytes + 2)  = x86GetModRMValue(5, op1); // access $rip
    *(instr_bytes + 3)  = 5; //skip following jmpq instruction
    *(instr_bytes + 4)  = 0;
    *(instr_bytes + 5)  = 0;
    *(instr_bytes + 6)  = 0;
    x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;
  }

  *(instr_bytes + length + 0) = X86_JMPQ;
  *(instr_bytes + length + 1) = right_shift(left_shift(address, 56), 56);
  *(instr_bytes + length + 2) = right_shift(left_shift(address, 48), 56);
  *(instr_bytes + length + 3) = right_shift(left_shift(address, 40), 56);
  *(instr_bytes + length + 4) = right_shift(left_shift(address, 32), 56);
  x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;

  x86emitInstructionBuffer(length + 5);
}

void translate_jalr() {

  if (imm == 0) {
    *(instr_bytes + 0) = REX + REX_B;
    *(instr_bytes + 1) = X86_JMPA;
    *(instr_bytes + 2) = 192 + x86GetModRMValue(REG_R15, 4);
    x86TotalEmittedInstructions = x86TotalEmittedInstructions + 1;

    x86emitInstructionBuffer(3);
  }
  else {
    print("jalr found with imm != 0");
    println();
  }
}

void translate_ecall() {
  *(instr_bytes + 0) = TWO_BYTE_INSTRUCTION;
  *(instr_bytes + 1) = X86_SYSCALL;

  *(instr_bytes + 2) = x86GetPrefix(0, 0, 1);
  *(instr_bytes + 3) = X86_MOV_R;
  *(instr_bytes + 4) = 192 + x86GetModRMValue(REG_RDI, REG_RAX);

  x86TotalEmittedInstructions = x86TotalEmittedInstructions + 2;
  x86emitInstructionBuffer(5);
}

// -----------------------------------------------------------------
// ----------------------- BINARY TRANSLATOR -----------------------
// -----------------------------------------------------------------

void translate_to_x86_binary() {
  // assert: 1 <= is <= number of RISC-U instructions
  if (is == ADDI)
    translate_addi();
  else if (is == LD)
    translate_ld();
  else if (is == SD)
    translate_sd();
  else if (is == ADD)
    translate_add();
  else if (is == SUB)
    translate_sub();
  else if (is == MUL)
    translate_mul();
  else if (is == DIVU)
    translate_divu();
  else if (is == REMU)
    translate_remu();
  else if (is == SLTU)
    translate_sltu();
  else if (is == BEQ)
    translate_beq();
  else if (is == JAL)
    translate_jal();
  else if (is == JALR)
    translate_jalr();
  else if (is == LUI)
    translate_lui();
  else if (is == ECALL)
    translate_ecall();
}

void selfie_translate() {
  uint64_t size;
  uint64_t x86binaryLength;
  uint64_t i;

  if (binary_length == 0) {
    printf1("%s: nothing to translate\n", selfie_name);

    exit(EXITCODE_BADARGUMENTS);
  }

  // use extension ".x86" in name of x86-64 binary file
  binary_name = replace_extension(binary_name, "x86");

  reset_library();
  reset_interpreter();
  reset_microkernel();

  init_memory(2);

  current_context = create_context(MY_CONTEXT, 0);

  // assert: number_of_remaining_arguments() > 0

  boot_loader(current_context);

  run = 0;

  debug    = 0;
  symbolic = 0;

  do_switch(current_context, current_context, TIMEROFF);

  x86DataLength = binary_length - code_length;
  binary_length = 0;

  // reuse binary

  i = 0;

  while (i < MAX_BINARY_LENGTH / SIZEOFUINT64) {
    *(binary + i) = 0;

    i = i + 1;
  }

  printf1("%s: translating RISC-V binary to x86-64\n", selfie_name);

  size = 30;
  pc_translator = ELF_ENTRY_POINT;
  instr_bytes = smalloc(size * SIZEOFUINT64);
  x86_address_fixup_table = smalloc(MAX_BINARY_LENGTH);

  while(pc_translator < code_length + ELF_ENTRY_POINT) {
    fetch_translator();
    x86SaveAddress();
    decode();
    translate_to_x86_binary();
    pc_translator = pc_translator + INSTRUCTIONSIZE;
  }

  x86AdressFix();

  // copy data segment of binary
  while (pc_translator  < code_length + x86DataLength + ELF_ENTRY_POINT) {
    fetch_translator();
    *(instr_bytes + 0) = right_shift(left_shift(ir, 56), 56);
    *(instr_bytes + 1) = right_shift(left_shift(ir, 48), 56);
    *(instr_bytes + 2) = right_shift(left_shift(ir, 40), 56);
    *(instr_bytes + 3) = right_shift(left_shift(ir, 32), 56);
    pc_translator = pc_translator + INSTRUCTIONSIZE;

    x86emitInstructionBuffer(4);
  }

  x86binaryLength = binary_length * SIZEOFUINT64 + x86ByteCount;

  binary_length = binary_gp_address / SIZEOFUINT64;
  x86ByteCount = binary_gp_address % SIZEOFUINT64;
  // now global pointer can be inserted into the code
  x86WriteWord(ELF_ENTRY_POINT + x86binaryLength);

  binary_length = x86binaryLength;

  *(ELF_header + 2)  = 4299030530;    //machine flag 0x3e
  *(ELF_header + 5)  = 120;
  *(ELF_header + 7)  = 1
    + left_shift(64, 16)
    + left_shift(3, 32)               // 3 section headers
    + left_shift(2, 48);              // shstrtab section index
  *(ELF_header + 12) = x86binaryLength;
  *(ELF_header + 13) = x86binaryLength;

  //first section header is always null
  *(ELF_header + 15) = 0;
  *(ELF_header + 16) = 0;
  *(ELF_header + 17) = 0;
  *(ELF_header + 18) = 0;
  *(ELF_header + 19) = 0;
  *(ELF_header + 20) = 0;
  *(ELF_header + 21) = 0;
  *(ELF_header + 22) = 0;

  *(ELF_header + 23) = 4294967297;
  *(ELF_header + 24) = 6;
  *(ELF_header + 25) = ELF_ENTRY_POINT;
  *(ELF_header + 26) = ELF_HEADER_LEN;
  *(ELF_header + 27) = x86binaryLength;
  *(ELF_header + 28) = 0;
  *(ELF_header + 29) = 2;
  *(ELF_header + 30) = 0;

  *(ELF_header + 31) = 12884901895;
  *(ELF_header + 32) = 0;
  *(ELF_header + 33) = 0;
  *(ELF_header + 34) = 312; //begin of .shstrtab (39 * 8 = 312 )
  *(ELF_header + 35) = 24;
  *(ELF_header + 36) = 0;
  *(ELF_header + 37) = 1;
  *(ELF_header + 38) = 0;

  //content of section .shstrtab
  *(ELF_header + 39) = 3314777386191695360; //0.text0.
  *(ELF_header + 40) = 7089075323386685555; //shstrtab
  *(ELF_header + 41) = 0;

  // assert: binary_name is mapped and not longer than MAX_FILENAME_LENGTH

  selfie_output(binary_name);
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

  if (exit_code == EXITCODE_NOERROR)
    selfie_translate();

  return exit_selfie(exit_code, "");
}