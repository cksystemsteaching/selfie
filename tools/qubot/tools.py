from enum import Enum
from typing import List, Optional, Dict
from settings import *
import time
import json
from z3 import BitVecNumRef


class Format(Enum):
    DECIMAL = 1
    BINARY = 2


class GlobalIndexer:
    name_index = -1
    name_index2 = -1

    @staticmethod
    def get_name_index():
        GlobalIndexer.name_index += 1
        return GlobalIndexer.name_index

    @staticmethod
    def get_name2_index():
        GlobalIndexer.name_index2 += 1
        return str(GlobalIndexer.name_index2)


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

            if int(temp[0]) == 3 or int(temp[0]) == 5 and modify_memory_sort:
                # this is memory sort. We need to modify this so it matches with our definition of memory
                memory_size = setting['word_size'] * (setting['size_datasegment'] + setting['size_heap'] + setting['size_stack'])
                temp = [temp[0], "sort", "bitvec", str(memory_size)]
                print("sort memory modified to be bitvector of size: ", memory_size)

            result[int(temp[0])] = temp
    file.close()
    return result

def get_btor2_settings(filename: str) -> Dict[str, int]:
    WORD_SIZE = 64
    file = open(filename, 'r')
    result = {}

    is_4_bit_address_space = False
    is_29_bit_address_space = False
    is_constant_propagation = False
    lines = file.readlines()
    for i in range(len(lines)):
        line = lines[i]
        if "./modeler-32" in line:
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

    assert len(result.keys()) == 9
    return result


def get_qubit_name() -> int:
    return GlobalIndexer.get_name_index()


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


def get_lsb_index(number: int) -> Optional[int]:
    bits = get_bit_repr_of_number(number)

    for (index, bit) in enumerate(bits):
        if bit == 1:
            return index

    return None


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


def get_time():
    return round(time.perf_counter(), 2)


def get_settings(path):
    with open(f"{path}") as json_file:
        setting = json.load(json_file)
    return setting


def get_rule_value(rule, inputs, qubits_to_fix):
    if rule == NAND:
        value1 = qubits_to_fix[inputs[0]]
        value2 = qubits_to_fix[inputs[1]]
        return not (value1 and value2)
    elif rule == R_AND:
        assert len(inputs) == 2
        value1 = qubits_to_fix[inputs[0]]
        value2 = qubits_to_fix[inputs[1]]
        if value1 is None or value2 is None:
            return None

        return value1 and value2
    elif rule == OR:
        assert len(inputs) == 2
        value1 = qubits_to_fix[inputs[0]]
        value2 = qubits_to_fix[inputs[1]]
        if value1 is None or value2 is None:
            return None
        return value1 or value2
    elif rule == XNOR:
        value1 = qubits_to_fix[inputs[0]]
        value2 = qubits_to_fix[inputs[1]]
        return value1 == value2
    elif rule == XOR:
        value1 = qubits_to_fix[inputs[0]]
        value2 = qubits_to_fix[inputs[1]]
        return value1 != value2
    elif rule == AUX_HALF_ADDER:
        value1 = qubits_to_fix[inputs[0]]
        value2 = qubits_to_fix[inputs[1]]
        if value1 is None or value2 is None:
            return None
        return value1 and (not value2)
    elif rule == AUX_FULL_ADDER:
        value_input1 = qubits_to_fix[inputs[0]]
        value_input2 = qubits_to_fix[inputs[1]]
        value_input3 = qubits_to_fix[inputs[2]]
        if value_input1 == 0:
            if value_input2 == 0:
                return 0
            else:
                # in2 = 1
                if value_input3 == 0:
                    return 1
                else:
                    return 0
        else:
            # in1 == 1
            if value_input2 == 1:
                return 1
            else:
                # in2 == 0
                if value_input3 == 1:
                    return 0
                else:
                    return 1
    elif rule == R_NOT:
        value1 = qubits_to_fix[inputs[0]]
        return not value1
    elif rule == CARRY_HALF_ADDER:
        return get_rule_value(R_AND, inputs, qubits_to_fix)
    elif rule == CARRY_FULL_ADDER:
        value_input1 = qubits_to_fix[inputs[0]]
        value_input2 = qubits_to_fix[inputs[1]]
        value_input3 = qubits_to_fix[inputs[2]]
        return (value_input1 + value_input2 + value_input3) > 1
    elif rule == RESULT_HALF_ADDER:
        value_input1 = qubits_to_fix[inputs[0]]
        value_input2 = qubits_to_fix[inputs[1]]
        return (value_input1 + value_input2) % 2
    elif rule == RESULT_FULL_ADDER:
        value_input1 = qubits_to_fix[inputs[0]]
        value_input2 = qubits_to_fix[inputs[1]]
        value_input3 = qubits_to_fix[inputs[2]]
        return (value_input1 + value_input2 + value_input3) % 2
    elif rule == MATRIARCH1:
        value1 = qubits_to_fix[inputs[0]]
        value2 = qubits_to_fix[inputs[1]]
        if value1 is None or value2 is None:
            return None
        return (not value1) and value2
    else:
        raise Exception("UNKNOWN RULE")



def get_rule_value_from_values(rule, inputs):
    if rule == NAND:
        value1 = inputs[0]
        value2 = inputs[1]
        return not (value1 and value2)
    elif rule == R_AND:
        assert len(inputs) == 2
        value1 = inputs[0]
        value2 = inputs[1]
        if value1 is None or value2 is None:
            return None

        return value1 and value2
    elif rule == OR:
        assert len(inputs) == 2
        value1 = inputs[0]
        value2 = inputs[1]
        if value1 is None or value2 is None:
            return None
        return value1 or value2
    elif rule == XNOR:
        value1 = inputs[0]
        value2 = inputs[1]
        return value1 == value2
    elif rule == XOR:
        value1 = inputs[0]
        value2 = inputs[1]
        return value1 != value2
    elif rule == AUX_HALF_ADDER:
        value1 = inputs[0]
        value2 = inputs[1]
        if value1 is None or value2 is None:
            return None
        return value1 and (not value2)
    elif rule == AUX_FULL_ADDER:
        value_input1 = inputs[0]
        value_input2 = inputs[1]
        value_input3 = inputs[2]
        if value_input1 == 0:
            if value_input2 == 0:
                return 0
            else:
                # in2 = 1
                if value_input3 == 0:
                    return 1
                else:
                    return 0
        else:
            # in1 == 1
            if value_input2 == 1:
                return 1
            else:
                # in2 == 0
                if value_input3 == 1:
                    return 0
                else:
                    return 1
    elif rule == R_NOT:
        value1 = inputs[0]
        return not value1
    elif rule == CARRY_HALF_ADDER:
        return get_rule_value_from_values(R_AND, inputs)
    elif rule == CARRY_FULL_ADDER:
        value_input1 = inputs[0]
        value_input2 = inputs[1]
        value_input3 = inputs[2]
        return (value_input1 + value_input2 + value_input3) > 1
    elif rule == RESULT_HALF_ADDER:
        value_input1 = inputs[0]
        value_input2 = inputs[1]
        return (value_input1 + value_input2) % 2
    elif rule == RESULT_FULL_ADDER:
        value_input1 = inputs[0]
        value_input2 = inputs[1]
        value_input3 = inputs[2]
        return (value_input1 + value_input2 + value_input3) % 2
    elif rule == MATRIARCH1:
        value1 = inputs[0]
        value2 = inputs[1]
        if value1 is None or value2 is None:
            return None
        return (not value1) and value2
    else:
        raise Exception("UNKNOWN RULE")


def get_decimal_from_z3(z3_expr):
    if type(z3_expr) != BitVecNumRef:
        return None

    binary_repr = [int(x) for x in z3_expr.as_binary_string()[::-1]]

    return get_decimal_representation(binary_repr)

def get_decimal_from_qubo(names, qubits_to_fix):
    binary_repr = []
    for name in names:
        if name not in qubits_to_fix.keys():
            return None
        binary_repr.append(qubits_to_fix[name])
    return get_decimal_representation(binary_repr)

def get_values_from_qubo(names, qubits_to_fix):
    binary_repr = []
    for name in names:
        if name not in qubits_to_fix.keys():
            binary_repr.append(None)
        else:
            binary_repr.append(qubits_to_fix[name])
    return binary_repr

def compare_qubo_z3_results(z3_expr, names, qubits_to_fix):
    z3_value = get_decimal_from_z3(z3_expr)
    qubo_value = get_decimal_from_qubo(names, qubits_to_fix)
    if z3_value is None or qubo_value is None:
        # print("none values", z3_value," - ", qubo_value)
        # if z3_value != qubo_value:
        #     return False
        return True
    # print("values: ", z3_value, qubo_value)
    return z3_value == qubo_value

