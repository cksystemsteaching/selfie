import struct


EXITCODE_NOERROR = 0
EXITCODE_BADARGUMENTS = 1
EXITCODE_IOERROR = 2
EXITCODE_SCANNERERROR = 3
EXITCODE_PARSERERROR = 4
EXITCODE_COMPILERERROR = 5
EXITCODE_OUTOFVIRTUALMEMORY = 6
EXITCODE_OUTOFPHYSICALMEMORY = 7
EXITCODE_DIVISIONBYZERO = 8
EXITCODE_UNKNOWNINSTRUCTION = 9
EXITCODE_UNKNOWNSYSCALL = 10
EXITCODE_MULTIPLEEXCEPTIONERROR = 11
EXITCODE_SYMBOLICEXECUTIONERROR = 12
EXITCODE_UNCAUGHTEXCEPTION = 13

EXITCODE_ERROR_RANGE = range(
    EXITCODE_BADARGUMENTS, EXITCODE_UNCAUGHTEXCEPTION + 1)



INSTRUCTIONSIZE = 4  # in bytes
WORDSIZE = 8  # in bytes

OP_OP = 51
OP_AMO = 47
OP_IMM = 19

F3_SLL = 1
F3_SRL = 5
F3_OR = 6
F3_AND = 7
F3_XORI = 4
F3_LR = 3
F3_SC = 3

F5_LR = 2
F5_SC = 3

F7_SLL = 0
F7_SRL = 0
F7_AND = 0
F7_OR = 0


def read_instruction(file):
    b = file.read(INSTRUCTIONSIZE)

    if len(b) != INSTRUCTIONSIZE:
        return 0

    return struct.unpack('<i', b)[0]


def read_data(file):
    b = file.read(WORDSIZE)

    if len(b) != WORDSIZE:
        return 0

    return struct.unpack('<Q', b)[0]


def encode_i_format(immediate, funct3, opcode):
    return ((((immediate << 5) << 3) + funct3 << 5) << 7) + opcode


def encode_r_format(funct7, funct3, opcode):
    return (((((funct7 << 5) << 5) << 3) + funct3 << 5) << 7) + opcode


def encode_amo_format(funct5, funct3):
    return (((((funct5 << 7) << 5) << 3) + funct3 << 5) << 7) + OP_AMO


NOT_FORMAT_MASK = 0b1111_1111_1111_0000_0111_0000_0111_1111
R_FORMAT_MASK   = 0b1111_1110_0000_0000_0111_0000_0111_1111
AMO_FORMAT_MASK = 0b1111_1000_0000_0000_0111_0000_0111_1111
LR_FORMAT_MASK  = 0b1111_1001_1111_0000_0111_0000_0111_1111

REGISTER_REGEX = '(zero|ra|sp|gp|tp|t[0-6]|s[0-9]|s10|s11|a[0-7])'

SLL_INSTRUCTION = ('left-shift', encode_r_format(F7_SLL, F3_SLL, OP_OP), R_FORMAT_MASK,
                   '^sll\\s+' + REGISTER_REGEX + ',' + REGISTER_REGEX + ',' + REGISTER_REGEX + '$')
SRL_INSTRUCTION = ('right-shift', encode_r_format(F7_SRL, F3_SRL, OP_OP), R_FORMAT_MASK,
                   '^srl\\s+' + REGISTER_REGEX + ',' + REGISTER_REGEX + ',' + REGISTER_REGEX + '$')
OR_INSTRUCTION = ('or', encode_r_format(F7_OR, F3_OR, OP_OP), R_FORMAT_MASK,
                  '^or\\s+' + REGISTER_REGEX + ',' + REGISTER_REGEX + ',' + REGISTER_REGEX + '$')
AND_INSTRUCTION = ('and', encode_r_format(F7_AND, F3_AND, OP_OP), R_FORMAT_MASK,
                   '^and\\s+' + REGISTER_REGEX + ',' + REGISTER_REGEX + ',' + REGISTER_REGEX + '$')
NOT_INSTRUCTION = ('not', encode_i_format(4095, F3_XORI, OP_IMM), NOT_FORMAT_MASK,
                   '^xori\\s+' + REGISTER_REGEX + ',' + REGISTER_REGEX + ',-1$')
LR_INSTRUCTION = ('load-reserved', encode_amo_format(F5_LR, F3_LR), LR_FORMAT_MASK,
                  '^lr\\.d\\s+' + REGISTER_REGEX + ',\\(' + REGISTER_REGEX + '\\)$')
SC_INSTRUCTION = ('store-conditional', encode_amo_format(F5_SC, F3_SC), AMO_FORMAT_MASK,
                  '^sc\\.d\\s+' + REGISTER_REGEX + ',' + REGISTER_REGEX + ',\\(' + REGISTER_REGEX + '\\)$')



