from typing import List, Dict
from qiskit import QuantumRegister, QuantumCircuit


def read_file(filename: str, modify_memory_sort: bool = False, setting: Dict[str, int] = None):
    """
    updates the static variable Instruction.all_instructions
    :param setting:
    :param modify_memory_sort:
    :param filename: btor2 file
    :return:
    """
    file = open(filename, 'r')
    result = {}
    for line in file.readlines():

        comment_index = line.find(";")
        if comment_index > -1:
            cleaned_line = line[:comment_index]
        else:
            cleaned_line = line

        temp = cleaned_line.lower().split()
        if len(temp) > 0:
            if (int(temp[0]) == 3 or int(temp[0]) == 5) and modify_memory_sort:
                # this is memory sort. We need to modify this so it matches with our definition of memory
                memory_size = setting['word_size'] * (setting['size_datasegment'] + setting['size_heap']
                                                      + setting['size_stack'])
                temp = [temp[0], "sort", "bitvec", str(memory_size)]
                print("sort memory modified to be bitvector of size: ", memory_size)

            result[int(temp[0])] = temp
    file.close()
    return result


def get_bit_repr_of_number(number: int, size_in_bits: int = 64) -> List[int]:
    if number > (2 ** size_in_bits - 1):
        raise Exception(f"{number} cannot be represented with {size_in_bits} bits")
    s = bin(number & int("1" * size_in_bits, 2))[2:]
    str_repr = ("{0:0>%s}" % size_in_bits).format(s)

    bits = []

    # index 0 contains the least significant bit
    for c in str_repr[::-1]:
        bits.append(int(c))

    return bits


def get_decimal_representation(binary_repr: List[int]) -> int:
    result = 0

    for (index, value) in enumerate(binary_repr):
        result += value * (2 ** index)

    return result


def bit_level_sum(bits1: List[int], bits2: List[int]) -> List[int]:
    """
    LSB is at index 0
    :param bits1:
    :param bits2:
    :return:
    """

    carry = 0
    result = []
    for (bit1, bit2) in zip(bits1, bits2):
        current = (bit1 + bit2 + carry) % 2
        carry = (bit1 + bit2 + carry) > 1
        result.append(current)

    if carry == 1:
        print(f"WARNING {carry}: overflow at tools.bit_level_sum")
    return result

def get_btor2_settings(filename: str) -> Dict[str, int]:
    WORD_SIZE = 64
    file = open(filename, 'r')
    result = {"begin_datasegment": 0, "begin_heap": 0, "size_datasegment": 0, "size_heap": 0, 'size_stack':0}

    is_4_bit_address_space = False
    is_29_bit_address_space = False
    is_constant_propagation = False
    lines = file.readlines()

    for i in range(len(lines)):
        line = lines[i]
        if "./beator-32" in line:
            WORD_SIZE = 32
        elif "with --constant-propagation" in line:
            is_constant_propagation = True
        elif  "; with --MMU" in line:
            is_4_bit_address_space = True
        elif "; with --RAM" in line:
            is_4_bit_address_space = True
        elif "; with --linear-address-space" in line:
            is_29_bit_address_space = True
        elif "total memory" in line and "data" in line and "heap" in line and "stack" in line:
            elements = line.split(",")
            #assert len(elements) == 4
            for element in elements:
                if 'data' in element:
                    more_elements = element.split('B')
                    result["size_datasegment"] = int(int(more_elements[0]) / (WORD_SIZE/8))
                elif 'heap' in element:
                    more_elements = element.split('B')
                    result['size_heap'] = int(int(more_elements[0]) / (WORD_SIZE/8))
                elif 'stack' in element:
                    more_elements = element.split('B')
                    result["size_stack"] = int(int(more_elements[0]) / (WORD_SIZE/8))
        elif not is_4_bit_address_space:
            if is_29_bit_address_space:
                if WORD_SIZE == 64:
                    n = 29
                else:
                    n = 30
            else:
                n = 64
            if f"start of data segment in {n}-bit" in line or (WORD_SIZE == 32 and f"start of data segment in 32-bit" in line):
                next_line = lines[i+1].split()
                result['begin_datasegment'] = int(next_line[3])
            elif f"start of heap segment in {n}-bit" in line or (WORD_SIZE == 32 and f"start of heap segment in 32-bit" in line):
                next_line = lines[i+1].split()
                result['begin_heap'] = int(next_line[3])
    file.close()
    result["word_size"] = WORD_SIZE
    if is_4_bit_address_space:
        result["address_word_size"] = 4
        result["address_step_size"] = 1
        result["begin_datasegment"] = 0
        result["begin_heap"] = result["size_datasegment"]
        result["begin_stack"] = result["size_datasegment"] + result["size_heap"] + result["size_stack"]
    elif is_29_bit_address_space:

        result["address_step_size"] = 1
        if WORD_SIZE == 64:
            result["address_word_size"] = 29
            result["begin_stack"] = 4294967296 >> 3
        else:
            result["address_word_size"] = 30
            result["begin_stack"] = 4294967296 >> 2
    else:
        # if is_constant_propagation:
        #     result["address_word_size"] = 32
        # else:
        result["address_word_size"] = WORD_SIZE
        result["address_step_size"] = int(WORD_SIZE/8)
        result["begin_stack"] = 4294967296
    # assert len(result.keys()) == 9
    return result


def apply_amplitude_amplification(qubits: QuantumRegister, circuit: QuantumCircuit, apply_last_h=True):

    circuit.h(qubits)
    circuit.x(qubits)

    # multi-controlled Z
    circuit.h(qubits[0])
    circuit.mcx(qubits[1:], qubits[0])
    circuit.h(qubits[0])

    circuit.x(qubits)
    if apply_last_h:
        circuit.h(qubits)

def must_target_be_flipped(controls):
    for c in controls:
        if c == -1:
            return False
        if c == 0:
            return False
    return True
